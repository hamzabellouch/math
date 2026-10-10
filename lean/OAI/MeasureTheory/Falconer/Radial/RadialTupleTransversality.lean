import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtVolume
import OAI.MeasureTheory.Falconer.Geometry.PiCoordinateSections

namespace OAI

/-! # Quantitative radial pin transversality from original-law slab bounds -/

namespace Falconer
open Set MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}

noncomputable def radialPinTuple (c : Space (n+1)) (w : Fin (n+1) → Space (n+1)) :=
  fun i => normalize (c-w i)

def radialResidualBad (c : Space (n+1)) (r : ℝ) (i : Fin (n+1)) :
    Set (Fin (n+1) → Space (n+1)) :=
  {w | ‖gramSchmidt ℝ (radialPinTuple c w) i‖ < r}

theorem radialPinTuple_measurable (c : Space (n+1)) : Measurable (radialPinTuple c) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold radialPinTuple NormedSpace.normalize
  fun_prop

theorem radialResidualBad_measurable (c : Space (n+1)) (r : ℝ) (i : Fin (n+1)) :
    MeasurableSet (radialResidualBad c r i) :=
  measurableSet_lt ((gramSchmidt_measurable i).comp (radialPinTuple_measurable c)).norm
    measurable_const

theorem radial_residual_bad_mass (μ : Measure (Space (n+1))) [IsFiniteMeasure μ]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 ≤ r)
    (hR : ∀ᵐ x ∂μ, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      μ {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (radialResidualBad c r i) ≤ K*(μ univ)^n := by
  apply pi_measure_le_of_coordinate_sections μ i _ (radialResidualBad_measurable c r i) K
  intro y
  let v := radialPinTuple c (i.insertNth 0 y)
  obtain ⟨u,hu,hinner⟩ := small_residual_fixed_slab v i
  apply (measure_mono_ae (t := {x | |inner ℝ u x-inner ℝ u c| ≤ R*r}) ?_).trans (hslab u hu)
  filter_upwards [hR] with x hx
  intro hb
  have hprefix : ∀ j < i, radialPinTuple c (i.insertNth x y) j = v j := by
    intro j hj
    dsimp [radialPinTuple,v]
    rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
  have hi := hinner (radialPinTuple c (i.insertNth x y)) hprefix
  have hb' : ‖gramSchmidt ℝ (radialPinTuple c (i.insertNth x y)) i‖ < r := hb
  have hsmall := hi.trans hb'.le
  simp only [radialPinTuple,Fin.insertNth_apply_same] at hsmall
  exact normalized_direction_slab u c x hx hr hsmall

def radialTupleBad (c : Space (n+1)) (r : ℝ) : Set (Fin (n+1) → Space (n+1)) :=
  ⋃ i : Fin (n+1), radialResidualBad c r i

theorem radialTupleBad_measurable (c : Space (n+1)) (r : ℝ) :
    MeasurableSet (radialTupleBad c r) :=
  MeasurableSet.iUnion (radialResidualBad_measurable c r)

theorem radial_bad_tuple_mass (μ : Measure (Space (n+1))) [IsFiniteMeasure μ]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 ≤ r)
    (hR : ∀ᵐ x ∂μ, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      μ {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (radialTupleBad c r) ≤
      (n+1:ℝ≥0∞)*K*(μ univ)^n := by
  calc
    _ ≤ ∑ i : Fin (n+1),
        (Measure.pi (fun _ : Fin (n+1) => μ)) (radialResidualBad c r i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n+1), K*(μ univ)^n := Finset.sum_le_sum
      (fun i _ => radial_residual_bad_mass μ c hr hR K hslab i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one,mul_assoc]

theorem radial_good_tuple_gram (c : Space (n+1)) {r : ℝ} (hr : 0 < r)
    (w : Fin (n+1) → Space (n+1)) (hw : w ∉ radialTupleBad c r) :
    (∀ i, ‖radialPinTuple c w i‖ = 1) ∧
      r^(n+1) ≤ Real.sqrt (Matrix.gram ℝ (radialPinTuple c w)).det := by
  have hn (i : Fin (n+1)) : r ≤ ‖gramSchmidt ℝ (radialPinTuple c w) i‖ := by
    by_contra! hi
    exact hw (mem_iUnion.mpr ⟨i,hi⟩)
  constructor
  · intro i
    have hne : c-w i ≠ 0 := by
      intro hz
      have hv : radialPinTuple c w i = 0 := by simp [radialPinTuple,hz]
      have hg : gramSchmidt ℝ (radialPinTuple c w) i = 0 := by
        rw [gramSchmidt_def,hv]
        simp
      have hi := hn i
      rw [hg,norm_zero] at hi
      exact (not_le_of_gt hr) hi
    exact norm_normalize hne
  · rw [gram_volume_eq_residual_product]
    calc
      r^(n+1) = ∏ _i : Fin (n+1), r := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hr.le) (fun i _ => hn i)

end Falconer

end OAI
