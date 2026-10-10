import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityParameter
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicGlobalization

namespace OAI

/-! Finite smooth patching of local positive density solutions. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {ι : Type*} [Fintype ι]

/-- Nonnegative smooth weights preserve both positivity and the linear moments;
normalization gives mass one on the open region where some weight is positive. -/
theorem patch_densities
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (ρ : ι → B × ℝ → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (U i ×ˢ univ))
    (hpos : ∀ i b, b ∈ U i → ∀ t, 0 < ρ i (b, t))
    (hper : ∀ i b, Function.Periodic (fun t => ρ i (b, t)) 1)
    (hmom : ∀ i b, b ∈ U i →
      (∫ t in 0..1, ρ i (b, t) • augment (p b t)) = augment (c b))
    (ψ : ι → B → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hn : ∀ i b, 0 ≤ ψ i b) (hsupp : ∀ i, tsupport (ψ i) ⊆ U i) :
    ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ ({b | 0 < ∑ i, ψ i b} ×ˢ univ) ∧
      (∀ b, 0 < ∑ i, ψ i b → ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b, 0 < ∑ i, ψ i b →
        (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      σ = (fun z => (∑ i, ψ i z.1 * ρ i z) / (∑ i, ψ i z.1)) := by
  let w : ι → B × ℝ → ℝ := fun i z => ψ i z.1 * ρ i z
  have hw (i : ι) : ContDiff ℝ ∞ (w i) := by
    apply LocalPeriodicExpansion.contDiff_of_zero_off_closed (hU i)
      (((hψ i).comp contDiff_fst).contDiffOn.mul (hρ i)) (isClosed_tsupport _) (hsupp i)
    intro b hb t
    have hz : ψ i b = 0 := image_eq_zero_of_notMem_tsupport hb
    change ψ i b * ρ i (b, t) = 0
    rw [hz, zero_mul]
  let S : B → ℝ := fun b => ∑ i, ψ i b
  let W : B × ℝ → ℝ := fun z => ∑ i, w i z
  let σ : B × ℝ → ℝ := fun z => W z / S z.1
  have hS : ContDiff ℝ ∞ S := ContDiff.sum (fun i _ => hψ i)
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ => hw i)
  have hUof (i : ι) (b : B) (hne : ψ i b ≠ 0) : b ∈ U i :=
    hsupp i (subset_tsupport _ (Function.mem_support.mpr hne))
  have hterm (i : ι) (b : B) (t : ℝ) : 0 ≤ w i (b, t) := by
    by_cases hz : ψ i b = 0
    · simp [w, hz]
    · exact mul_nonneg (hn i b) (hpos i b (hUof i b hz) t).le
  refine ⟨σ, ?_, ?_, ?_, ?_, rfl⟩
  · exact hW.contDiffOn.div (hS.comp contDiff_fst).contDiffOn (fun z hz => hz.1.ne')
  · intro b hb t
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hn j b)).mp hb
    have hwi : 0 < w i (b, t) := mul_pos hi (hpos i b (hUof i b hi.ne') t)
    exact div_pos (lt_of_lt_of_le hwi (Finset.single_le_sum (fun j _ => hterm j b t)
      (Finset.mem_univ i))) hb
  · intro b t
    change (∑ i, ψ i b * ρ i (b, t + 1)) / S b = (∑ i, ψ i b * ρ i (b, t)) / S b
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : ℝ => ψ i b * x) (hper i b t)
  · intro b hb
    have hpc : Continuous (fun t => augment (p b t)) :=
      augment_continuous.comp (hp.continuous.comp (continuous_const.prodMk continuous_id))
    have hint (i : ι) : IntervalIntegrable (fun t => w i (b, t) • augment (p b t))
        MeasureTheory.volume 0 1 :=
      (((hw i).continuous.comp (continuous_const.prodMk continuous_id)).smul hpc).intervalIntegrable _ _
    have hmean : (∫ t in 0..1, W (b, t) • augment (p b t)) = S b • augment (c b) := by
      change (∫ t in 0..1, (∑ i, w i (b, t)) • augment (p b t)) = _
      simp_rw [Finset.sum_smul]
      rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz : ψ i b = 0
      · simp [w, hz]
      · change (∫ t in 0..1, (ψ i b * ρ i (b, t)) • augment (p b t)) = _
        simp_rw [mul_smul]
        rw [intervalIntegral.integral_smul, hmom i b (hUof i b hz)]
    change (∫ t in 0..1, (W (b, t) / S b) • augment (p b t)) = _
    simp_rw [div_eq_inv_mul, mul_smul]
    rw [intervalIntegral.integral_smul, hmean, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]

end ClosedSurfaceR4.LoopDensity

end

end OAI
