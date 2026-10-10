import OAI.Analysis.CircleDomains.Sobolev.LocalPairChainWitness
import OAI.Analysis.CircleDomains.Sobolev.CompactWeakDerivativeIntegral
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! A compact cutoff of the two continued model coordinates is globally
Sobolev. Its actual gradient is the product/chain-rule field on the
working disk and vanishes outside that disk. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_pair_cutoff_witness
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    {p q : EuclideanPlane → ℝ} (hp : Continuous p) (hq : Continuous q)
    (Wp : DeGiorgi.MemW1pWitness 2 p univ) (Wq : DeGiorgi.MemW1pWitness 2 q univ)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ U) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => θ x*Φ (planePair (p x) (q x))) univ,
      (∀ i : Fin 2, ∀ᵐ x ∂volume.restrict U,
        W.weakGrad x i = θ x*(
          fderiv ℝ Φ (planePair (p x) (q x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wp.weakGrad x i+
          fderiv ℝ Φ (planePair (p x) (q x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wq.weakGrad x i)+
          fderiv ℝ θ x (EuclideanSpace.single i 1)*Φ (planePair (p x) (q x))) ∧
      (∀ i : Fin 2, ∀ᵐ x ∂volume, x ∉ U → W.weakGrad x i = 0) := by
  let P := fun x => Φ (planePair (p x) (q x))
  let A := localPairChainWitness hU hUf hp hq (Wp.restrict hU (subset_univ U))
    (Wq.restrict hU (subset_univ U)) hΦ hB hC hΦb hΦd
  obtain ⟨C₀,hC₀⟩ := hθ.continuous.bounded_above_of_compact_support hsθ
  obtain ⟨C₁,hC₁⟩ := (hθ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hsθ.fderiv ℝ)
  let J := A.mul_smooth_bounded_p (by norm_num) hU hθ
    (le_max_right C₀ 0) (le_max_right C₁ 0)
    (fun x => by simpa only [Real.norm_eq_abs] using (hC₀ x).trans (le_max_left C₀ 0))
    (fun x => (hC₁ x).trans (le_max_left C₁ 0))
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness hU A.memW1p hθ hsθ hθU
  have hW := (W.restrict hU (subset_univ U)).ae_eq hU J
  refine ⟨W,?_,?_⟩
  · intro i
    filter_upwards [hW] with x hx
    have hi := congrArg (fun v : EuclideanPlane => v i) hx
    simpa only [DeGiorgi.MemW1pWitness.restrict,J,DeGiorgi.MemW1pWitness.mul_smooth_bounded_p,
      A,localPairChainWitness,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using hi
  · intro i
    filter_upwards [compact_weakGradient_zero_off W i] with x hx hxu
    apply hx
    exact fun ht => hxu (hθU (tsupport_mul_subset_left ht))

end CircleDomainRigidity

end

end OAI
