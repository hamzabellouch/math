import OAI.Analysis.LipschitzEquivalence.MolecularApproximation

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped NNReal Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_unit_pos_of_lt_norm (T : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (hT : c < ‖T‖) :
    ∃ x : E, ‖x‖ = 1 ∧ c < T x := by
  have hnot : ¬ ∀ x : E, ‖T x‖ ≤ c*‖x‖ := by
    intro h
    exact (not_le.mpr hT) (T.opNorm_le_bound hc h)
  push Not at hnot
  obtain ⟨x,hx⟩ := hnot
  have hxnorm : 0 < ‖x‖ := by
    by_contra! h
    have : x = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    simp [this] at hx
  let y : E := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    rw [norm_smul,norm_inv,Real.norm_of_nonneg hxnorm.le,inv_mul_cancel₀ hxnorm.ne']
  have hTy : c < |T y| := by
    change c < |T (‖x‖⁻¹ • x)|
    rw [map_smul,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hxnorm]
    rw [← Real.norm_eq_abs]
    have h := mul_lt_mul_of_pos_left hx (inv_pos.mpr hxnorm)
    have he : ‖x‖⁻¹ * (c * ‖x‖) = c := by
      rw [mul_left_comm,inv_mul_cancel₀ hxnorm.ne',mul_one]
    rwa [he] at h
  rcases le_total 0 (T y) with hpos | hneg
  · exact ⟨y,hy,by simpa only [abs_of_nonneg hpos] using hTy⟩
  · exact ⟨-y,by simpa using hy,by simpa only [map_neg,abs_of_nonpos hneg] using hTy⟩

theorem bidual_separate_finite (φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) {d : ℝ} (hd : 0 < d)
    (hfar : ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖)
    {n : ℕ} (x : Fin n → E) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ (∀ i, f (x i) = 0) ∧ d/2 < φ f := by
  classical
  let A : (E →L[ℝ] ℝ) →ₗ[ℝ] (Fin n → ℝ) := {
    toFun := fun f i => f (x i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let p : Submodule ℝ (E →L[ℝ] ℝ) := A.ker
  let : NormedAddCommGroup p := inferInstance
  let : NormedSpace ℝ p := inferInstance
  let φp : p →L[ℝ] ℝ := φ.comp p.subtypeL
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq p φp
  have hann : (φ-ψ).toLinearMap ∈ (A.ker).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro f hf
    change φ f-ψ f = 0
    exact sub_eq_zero.mpr (hψ ⟨f,hf⟩).symm
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker A] at hann
  obtain ⟨l,hl⟩ := hann
  let z : E := ∑ i, l (Pi.single i 1) • x i
  have heq : φ-ψ = NormedSpace.inclusionInDoubleDual ℝ E z := by
    ext f
    have hlf := DFunLike.congr_fun hl f
    change l (A f) = φ f-ψ f at hlf
    change φ f-ψ f = f z
    rw [← hlf]
    change l (fun i => f (x i)) = f (∑ i, l (Pi.single i 1) • x i)
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
    have hexp : (fun i => f (x i)) = ∑ i, f (x i) • (Pi.single i 1 : Fin n → ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hexp,map_sum]
    simp only [map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdnorm : d ≤ ‖φp‖ := by
    have h := hfar z
    rw [← heq] at h
    have he : φ-(φ-ψ) = ψ := by ext f; simp
    rw [he,hψnorm] at h
    exact h
  obtain ⟨f,hfnorm,hfφ⟩ := exists_unit_pos_of_lt_norm φp (half_pos hd).le (by linarith)
  refine ⟨f.val,hfnorm,?_,hfφ⟩
  intro i
  exact congr_fun f.property i

theorem nonconvergent_biddual_gap [CompleteSpace E] {u : ℕ → E} (hu : WeakCauchy u)
    (hno : ¬ ∃ x : E, ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    ∃ (φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) (d : ℝ), 0 < d ∧
      (∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f))) ∧
      ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖ := by
  obtain ⟨φ,hφ⟩ := weakCauchy_biddual_limit hu
  let I : E →ₗᵢ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := NormedSpace.inclusionInDoubleDualLi ℝ
  have hnot : φ ∉ Set.range I := by
    rintro ⟨x,hx⟩
    apply hno
    refine ⟨x,fun f => ?_⟩
    simpa [← hx,I,NormedSpace.inclusionInDoubleDualLi,NormedSpace.inclusionInDoubleDual] using hφ f
  have hI : Isometry (I : E → ((E →L[ℝ] ℝ) →L[ℝ] ℝ)) := I.isometry
  have hclosed : IsClosed (Set.range I) := hI.isClosedEmbedding.isClosed_range
  have hnot' : φ ∉ closure (Set.range I) := by rwa [hclosed.closure_eq]
  rw [@Metric.mem_closure_iff ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance] at hnot'
  push Not at hnot'
  obtain ⟨d,hd,hgap⟩ := hnot'
  refine ⟨φ,d,hd,hφ,fun x => ?_⟩
  have h := hgap (I x) ⟨x,rfl⟩
  rw [show dist φ (I x) = ‖φ-I x‖ from
    @dist_eq_norm ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance φ (I x)] at h
  exact h

end LipschitzCounterexample.WeakSequences
end

end OAI
