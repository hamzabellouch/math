import Mathlib

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section
namespace RadialActualSweep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compact_projected_image (u : E) {S : Set E} (hS : IsCompact S) :
    IsCompact ((fun x : E => x - (inner ℝ u x) • u) '' S) := by
  apply hS.image
  exact continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)

theorem projected_image_perpendicular {u : E} (hu : ‖u‖ = 1) (S : Set E) :
    ∀ z ∈ (fun x : E => x - (inner ℝ u x) • u) '' S, inner ℝ u z = 0 := by
  rintro z ⟨x, hx, rfl⟩
  simp [inner_sub_right, inner_smul_right, hu]

theorem subset_projected_cylinder (u : E) (S : Set E) :
    S ⊆ {x | ∃ b ∈ (fun y : E => y - (inner ℝ u y) • u) '' S,
      ∃ r : ℝ, x = b + r • u} := by
  intro x hx
  exact ⟨x - (inner ℝ u x) • u, ⟨x, hx, rfl⟩, inner ℝ u x, by simp⟩

theorem projection_add_axis {u : E} (hu : ‖u‖ = 1) (x : E) (r : ℝ) :
    (x + r • u) - (inner ℝ u (x + r • u)) • u = x - (inner ℝ u x) • u := by
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu,
    one_pow, mul_one, add_smul]
  abel

theorem projected_image_subset_of_intercepts {u : E} (hu : ‖u‖ = 1)
    {S T : Set E}
    (hST : ∀ x ∈ S, ∃ t ∈ T, ∃ r : ℝ, x = t + r • u) :
    (fun x : E => x - (inner ℝ u x) • u) '' S ⊆
      (fun x : E => x - (inner ℝ u x) • u) '' T := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨t, ht, r, rfl⟩ := hST x hx
  exact ⟨t, ht, (projection_add_axis hu t r).symm⟩

theorem actual_area_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X} (hAB : A ⊆ B) (hB : μ B ≠ ⊤) :
    μ A ≠ ⊤ ∧ μ.real A ≤ μ.real B := by
  exact ⟨ne_top_of_le_ne_top hB (measure_mono hAB), measureReal_mono hAB hB⟩

theorem limsup_le_of_nonneg_of_le_tendsto {cost bound : ℕ → ℝ} {A : ℝ}
    (hcost : ∀ n, 0 ≤ cost n) (hle : cost ≤ᶠ[atTop] bound)
    (hbound : Tendsto bound atTop (𝓝 A)) :
    limsup cost atTop ≤ A := by
  calc
    limsup cost atTop ≤ limsup bound atTop :=
      limsup_le_limsup hle (isCoboundedUnder_le_of_le atTop hcost)
        hbound.isBoundedUnder_le
    _ = A := hbound.limsup_eq

theorem sum_actual_area_le {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) (A B : Fin n → Set X)
    (hAB : ∀ i, A i ⊆ B i) (hB : ∀ i, μ i (B i) ≠ ⊤) :
    (∑ i, (μ i).real (A i)) ≤ ∑ i, (μ i).real (B i) := by
  exact Finset.sum_le_sum fun i _ => measureReal_mono (hAB i) (hB i)

theorem actual_area_limsup_le {X : Type*} [MeasurableSpace X]
    (μ : (n : ℕ) → Fin n → Measure X)
    (A B : (n : ℕ) → Fin n → Set X) {L : ℝ}
    (hAB : ∀ n i, A n i ⊆ B n i)
    (hB : ∀ n i, μ n i (B n i) ≠ ⊤)
    (hcost : Tendsto (fun n => ∑ i, (μ n i).real (B n i)) atTop (𝓝 L)) :
    limsup (fun n => ∑ i, (μ n i).real (A n i)) atTop ≤ L := by
  apply limsup_le_of_nonneg_of_le_tendsto
  · intro n
    exact Finset.sum_nonneg fun i _ => measureReal_nonneg
  · exact Eventually.of_forall fun n => sum_actual_area_le (μ n) (A n) (B n) (hAB n) (hB n)
  · exact hcost

theorem compact_radial_sweep {J : Set ℝ} (hJ : IsCompact J)
    (R : ℝ → ℝ) (w : ℝ → E) (hR : ContinuousOn R J) (hw : ContinuousOn w J)
    (hRnonneg : ∀ t ∈ J, 0 ≤ R t) (p₀ a b e : E) (L : ℝ) :
    IsCompact {x : E | ∃ t ∈ J, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ R t ∧
      ∃ s : ℝ, |s| ≤ L ∧ x = p₀ + ρ • (a + t • b) + s • (e + w t)} := by
  let D : Set (ℝ × ℝ × ℝ) := J ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (-L) L)
  let F : ℝ × ℝ × ℝ → E := fun p =>
    p₀ + (p.2.1 * R p.1) • (a + p.1 • b) + p.2.2 • (e + w p.1)
  have hD : IsCompact D := hJ.prod (isCompact_Icc.prod isCompact_Icc)
  have hRD : ContinuousOn (fun p : ℝ × ℝ × ℝ => R p.1) D :=
    hR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hwD : ContinuousOn (fun p : ℝ × ℝ × ℝ => w p.1) D :=
    hw.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hF : ContinuousOn F D := by
    dsimp [F]
    exact (continuousOn_const.add
      ((continuous_snd.fst.continuousOn.mul hRD).smul
        (continuousOn_const.add (continuous_fst.continuousOn.smul continuousOn_const)))).add
      (continuous_snd.snd.continuousOn.smul (continuousOn_const.add hwD))
  have heq : F '' D = {x : E | ∃ t ∈ J, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ R t ∧
      ∃ s : ℝ, |s| ≤ L ∧ x = p₀ + ρ • (a + t • b) + s • (e + w t)} := by
    ext x
    constructor
    · rintro ⟨⟨t, q, s⟩, hp, rfl⟩
      rcases hp with ⟨ht, hq, hs⟩
      exact ⟨t, ht, q * R t, mul_nonneg hq.1 (hRnonneg t ht),
        by simpa using mul_le_mul_of_nonneg_right hq.2 (hRnonneg t ht), s, abs_le.mpr hs, rfl⟩
    · rintro ⟨t, ht, ρ, hρ, hρR, s, hs, rfl⟩
      by_cases hRt : R t = 0
      · have hρ0 : ρ = 0 := by linarith
        refine ⟨(t, 0, s), ⟨ht, ⟨by norm_num, by norm_num⟩, abs_le.mp hs⟩, ?_⟩
        simp [F, hρ0]
      · have hRtpos : 0 < R t := lt_of_le_of_ne (hRnonneg t ht) (Ne.symm hRt)
        refine ⟨(t, ρ / R t, s), ⟨ht, ⟨div_nonneg hρ hRtpos.le,
          (div_le_one hRtpos).mpr hρR⟩, abs_le.mp hs⟩, ?_⟩
        simp [F, div_mul_cancel₀ ρ hRt]
  rw [← heq]
  exact hD.image_of_continuousOn hF

theorem actual_projection_cover [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (u : Fin n → E) (hu : ∀ i, ‖u i‖ = 1)
    (S T : Fin n → Set E) (hS : ∀ i, IsCompact (S i))
    (μ : Fin n → Measure E)
    (hTfinite : ∀ i, μ i ((fun x : E => x - (inner ℝ (u i) x) • u i) '' T i) ≠ ⊤)
    (hST : ∀ i, ∀ x ∈ S i, ∃ t ∈ T i, ∃ r : ℝ, x = t + r • u i)
    {K : Set E} (hK : K ⊆ ⋃ i, S i) :
    ∃ B : Fin n → Set E,
      (∀ i, B i = (fun x : E => x - (inner ℝ (u i) x) • u i) '' S i) ∧
      (∀ i, IsCompact (B i) ∧ MeasurableSet (B i) ∧
        (∀ z ∈ B i, inner ℝ (u i) z = 0) ∧ μ i (B i) ≠ ⊤) ∧
      (K ⊆ ⋃ i, {x | ∃ b ∈ B i, ∃ r : ℝ, x = b + r • u i}) ∧
      (∑ i, (μ i).real (B i)) ≤
        ∑ i, (μ i).real ((fun x : E => x - (inner ℝ (u i) x) • u i) '' T i) := by
  let B : Fin n → Set E := fun i =>
    (fun x : E => x - (inner ℝ (u i) x) • u i) '' S i
  have hsubset (i : Fin n) : B i ⊆
      (fun x : E => x - (inner ℝ (u i) x) • u i) '' T i :=
    projected_image_subset_of_intercepts (hu i) (hST i)
  refine ⟨B, fun _ => rfl, ?_, ?_, ?_⟩
  · intro i
    have hc : IsCompact (B i) := compact_projected_image (u i) (hS i)
    exact ⟨hc, hc.measurableSet, projected_image_perpendicular (hu i) (S i),
      (actual_area_le (μ i) (hsubset i) (hTfinite i)).1⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hK hx)
    exact mem_iUnion.mpr ⟨i, subset_projected_cylinder (u i) (S i) hi⟩
  · exact sum_actual_area_le μ B
      (fun i => (fun x : E => x - (inner ℝ (u i) x) • u i) '' T i)
      hsubset hTfinite

end RadialActualSweep

end

end OAI
