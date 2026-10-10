import OAI.Probability.SignedSweeps.EndpointKernels

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_representation_adjoint {G : Type*} [Group G] (ρ : Representation ℂ G E)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact representation_inner_inverse ρ hρ g y x

lemma adjoint_finiteMean {A : Type*} [Fintype A] (T : A → E →ₗ[ℂ] E) :
    (finiteMean ℂ T).adjoint = finiteMean ℂ (fun a => (T a).adjoint) := by
  simp only [finiteMean, map_smulₛₗ, map_sum, map_inv₀, map_natCast]

lemma unitary_finiteMean_adjoint {G A : Type*} [Group G] [Fintype A]
    (ρ : Representation ℂ G E) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (f : A → G) :
    (finiteMean ℂ (fun a => ρ (f a))).adjoint = finiteMean ℂ (fun a => ρ ((f a)⁻¹)) := by
  rw [adjoint_finiteMean]
  apply finiteMean_congr
  intro a
  exact unitary_representation_adjoint ρ hρ _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_kernel_apply {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (f : X → ℂ) :
    (∑ y, (finiteProb (fun a => s a = y) : ℂ) * f y) = finiteMean ℂ (fun a => f (s a)) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma tupleRepresentation_norm {I : Type*} [Fintype I] {n : ℕ}
    (g : SymmetricGroup n) (f : TupleSpace I n) :
    ‖tupleRepresentation I n g f‖ = ‖f‖ := (tupleIsometry g).norm_map f

theorem tupleSweep_adjoint_eq_endpointKernel {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) :
    (tupleSweep I d).adjoint = kernelOperator (subsetEndpointKernel (I := I) d Finset.univ) := by
  rw [tupleSweep_eq_sampleMean, ← finiteMean_equiv ℂ (physicalSettingsEquiv d)
    (fun a => tupleRepresentation I (2 ^ d) (sampleSweep d a))]
  rw [unitary_finiteMean_adjoint (tupleRepresentation I (2 ^ d))
    (fun g f => tupleRepresentation_norm g f)]
  ext f x
  change (finiteMean ℂ (fun p : PhysicalSettings d =>
      tupleRepresentation I (2 ^ d) (sampleSweep d (physicalSettingsEquiv d p))⁻¹) f) x = _
  have hk (y : InjectiveTuple I (2 ^ d)) : subsetEndpointKernel d Finset.univ x y =
      finiteProb (fun p : PhysicalSettings d =>
        tupleEquiv (sampleSweep d (physicalSettingsEquiv d p)) x = y) := by
    rw [subsetEndpointKernel_full]
    apply finiteProb_congr
    intro p
    simp only [Finset.mem_univ, forall_true_left]
    constructor
    · intro h
      exact Function.Embedding.ext h
    · intro h a
      exact congrArg (fun t : InjectiveTuple I (2 ^ d) => t a) h
  rw [kernelOperator_apply]
  simp only [hk]
  rw [finiteProb_kernel_apply]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, tupleRepresentation_apply, inv_inv]

lemma tupleRealization_intertwines_adjoint_sweep {d : ℕ} (lam : Partition (2 ^ d))
    (v : Specht lam) :
    tupleRealization lam ((sweepOperator lam).adjoint v) =
      (tupleSweep (OffFirstRow lam) d).adjoint (tupleRealization lam v) := by
  rw [sweepOperator_eq_sampleMean, tupleSweep_eq_sampleMean,
    unitary_finiteMean_adjoint (spechtRepresentation lam)
      (fun g f => spechtRepresentation_norm lam g f),
    unitary_finiteMean_adjoint (tupleRepresentation (OffFirstRow lam) (2 ^ d))
      (fun g f => tupleRepresentation_norm g f)]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    tupleRealization_intertwines]

theorem sweep_norm_le_of_adjoint_tuple_bound {d : ℕ} (lam : Partition (2 ^ d))
    {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ v : Specht lam, ‖(tupleSweep (OffFirstRow lam) d).adjoint (tupleRealization lam v)‖ ≤
      a * ‖tupleRealization lam v‖) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤ a := by
  have hn : ‖(sweepOperator lam).adjoint.toContinuousLinearMap‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_bound _ ha
    intro v
    change ‖(sweepOperator lam).adjoint v‖ ≤ a * ‖v‖
    have hh := h v
    rw [← tupleRealization_intertwines_adjoint_sweep] at hh
    have hc : (0 : ℝ) < Fintype.card (firstRowStabilizer lam) := by exact_mod_cast Fintype.card_pos
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hc.le
    rw [mul_pow, ← mul_assoc, mul_comm (Fintype.card (firstRowStabilizer lam) : ℝ) (a ^ 2),
      mul_assoc, ← tupleRealization_norm_sq, ← tupleRealization_norm_sq] at hs
    nlinarith [norm_nonneg ((sweepOperator lam).adjoint v), norm_nonneg v,
      mul_nonneg ha (norm_nonneg v)]
  rwa [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map] at hn

end SignedSweeps
end

end OAI
