import OAI.MeasureTheory.Falconer.Estimates.FarRebin

namespace OAI

/-! # Borel dyadic bands for the two original comparable displacements

The finite cover has the exact constants used by the far-cell partner
geometry. Nonnegative integration only needs a cover, so no arbitrary
choice of a depth or additional measurability hypothesis is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def comparableLengthBand (d b : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < dist z.1.1 z.1.2 ∧
          dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) ∧
        (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < dist z.2.1 z.2.2 ∧
          dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)))}

theorem comparableLengthBand_measurable (d b : ℕ) :
    MeasurableSet (comparableLengthBand d b) := by
  have h₁ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.1.1 z.1.2) := by fun_prop
  have h₂ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.2.1 z.2.2) := by fun_prop
  exact ((measurableSet_lt measurable_const h₁).inter
    (measurableSet_le h₁ measurable_const)).inter
    ((measurableSet_lt measurable_const h₂).inter
      (measurableSet_le h₂ measurable_const))

def comparableFarRegion (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤
          2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) ∧
        8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤ 2*dist z.1.1 z.1.2 ∧
        max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤ 2*dist z.2.1 z.2.2}

theorem comparableFarRegion_measurable (d a h : ℕ) :
    MeasurableSet (comparableFarRegion d a h) := by
  have h₁ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.1.1 z.1.2) := by fun_prop
  have h₂ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.2.1 z.2.2) := by fun_prop
  have hm := h₁.max h₂
  exact (measurableSet_le hm measurable_const).inter
    ((measurableSet_lt measurable_const hm).inter
      ((measurableSet_le hm (measurable_const.mul h₁)).inter
        (measurableSet_le hm (measurable_const.mul h₂))))

theorem comparableFarRegion_covered (d a h : ℕ)
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableFarRegion d a h) :
    ∃ b ∈ Finset.Icc (a+9) (h+6), z ∈ comparableLengthBand d b := by
  obtain ⟨b,hba,hbh,h₁,h₂⟩ := comparable_displacement_depth_dimensional d hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact ⟨b,Finset.mem_Icc.mpr ⟨hba,hbh⟩,h₁,h₂⟩

theorem comparableLengthBand_dist_lower {d b : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableLengthBand d b) :
    (2:ℝ)^(-(b:ℝ)) ≤ dist z.1.1 z.1.2 ∧
      (2:ℝ)^(-(b:ℝ)) ≤ dist z.2.1 z.2.2 := by
  have hp : 0 ≤ (2:ℝ)^(-(b:ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hd : 1 ≤ 256*((d:ℝ)+1) := by have h := Nat.cast_nonneg (α := ℝ) d; linarith
  have hscale := mul_le_mul_of_nonneg_right hd hp
  exact ⟨(by simpa only [one_mul] using hscale.trans hz.1.1.le),
    (by simpa only [one_mul] using hscale.trans hz.2.1.le)⟩

theorem descendant_common_band_scale {d a b : ℕ} (Q : DyadicCube d)
    (hQ : Q.side = 1) (X : List (Fin d → Bool)) (hX : X.length = a) (hab : a ≤ b) :
    (Q.descendant X).side/(2:ℝ)^(b-a) = (2:ℝ)^(-(b:ℝ)) := by
  rw [Q.descendant_side,hQ,hX,div_div,← pow_add,Nat.add_sub_of_le hab]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]

theorem comparableLengthBand_descendants {d a b : ℕ} (Q : DyadicCube d)
    (hQ : Q.side = 1) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) (hab : a ≤ b)
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableLengthBand d b) :
    (256*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^(b-a)) < dist z.1.1 z.1.2 ∧
      dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^(b-a))) ∧
    (256*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^(b-a)) < dist z.2.1 z.2.2 ∧
      dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^(b-a))) := by
  rwa [descendant_common_band_scale Q hQ X hX hab,
    descendant_common_band_scale Q hQ Y hY hab]

theorem lintegral_comparable_bands_le (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞)
    {U : Set ((Space d × Space d) × (Space d × Space d))}
    (hU : U ⊆ comparableFarRegion d a h) :
    (∫⁻ z in U, F z ∂μ) ≤ ∑ b ∈ Finset.Icc (a+9) (h+6),
      ∫⁻ z in U ∩ comparableLengthBand d b, F z ∂μ := by
  let B := Finset.Icc (a+9) (h+6)
  have hcover : U ⊆ ⋃ b : B, U ∩ comparableLengthBand d b.1 := by
    intro z hz
    obtain ⟨b,hb,hzb⟩ := comparableFarRegion_covered d a h (hU hz)
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,hz,hzb⟩
  calc
    _ ≤ ∫⁻ z in ⋃ b : B, U ∩ comparableLengthBand d b.1, F z ∂μ :=
      lintegral_mono' (Measure.restrict_mono_set μ hcover) (fun _ => le_rfl)
    _ ≤ ∑' b : B, ∫⁻ z in U ∩ comparableLengthBand d b.1, F z ∂μ :=
      lintegral_iUnion_le _ _
    _ = _ := by rw [tsum_fintype]; exact Finset.sum_attach B (fun b => ∫⁻ z in U ∩ comparableLengthBand d b, F z ∂μ)

end Falconer

end OAI
