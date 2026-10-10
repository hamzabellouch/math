import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskMap
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative

namespace OAI

/-! The disk map retains its actual holomorphic inverse and the exact
inverse identities needed for conformal circularization. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma exists_riemann_disk_inverse {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f g : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧
      BijOn f U (ball 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      MapsTo g (ball 0 1) U ∧ (∀ z ∈ U, g (f z)=z) ∧
      (∀ w ∈ ball 0 1, f (g w)=w) ∧ (∀ z ∈ U, deriv f z ≠ 0) := by
  obtain ⟨f,hf,hbij,_⟩ := exists_normalized_riemann_disk_map hU hc hproper ha
  let g := invFunOn f U
  have hleft : ∀ z ∈ U, g (f z)=z := hf.injective.leftInvOn_invFunOn
  have hright : ∀ w ∈ ball 0 1, f (g w)=w := fun w hw => invFunOn_eq (hbij.surjOn hw)
  refine ⟨f,g,hf,hbij,?_,?_,hleft,hright,?_⟩
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := hbij.surjOn hw
    exact (holomorphicInjOn_inverse_differentiableAt hU hf.holomorphic hf.injective hz).differentiableWithinAt
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := hbij.surjOn hw
    rwa [hleft z hz]
  · intro z hz
    exact holomorphicInjOn_deriv_ne_zero hU hf.holomorphic hf.injective hz

end CircleDomainRigidity

end

end OAI
