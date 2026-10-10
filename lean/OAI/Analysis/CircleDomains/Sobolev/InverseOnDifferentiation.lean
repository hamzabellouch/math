import OAI.Analysis.CircleDomains.Sobolev.WeightedLipschitzCurve
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

namespace OAI

/-! Inverses on bi-Lipschitz measurable pieces retain the exact within-set derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverseOn_lipschitz {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) :
    LipschitzOnWith K (invFunOn F S) (F '' S) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have h := hF.le_mul_dist ⟨invFunOn F S y, invFunOn_mem hy⟩
    ⟨invFunOn F S z, invFunOn_mem hz⟩
  simpa only [Subtype.dist_eq, domRestrict_apply, invFunOn_eq hy, invFunOn_eq hz] using h

lemma inverseOn_injOn {F : ℂ → ℂ} {S : Set ℂ} : InjOn (invFunOn F S) (F '' S) := by
  intro y hy z hz he
  have h := congrArg F he
  rwa [invFunOn_eq hy, invFunOn_eq hz] at h

lemma inverseOn_hasFDerivWithinAt {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) {y : ℂ} (hy : y ∈ F '' S)
    (A : ℂ ≃L[ℝ] ℂ)
    (hd : HasFDerivWithinAt F (A : ℂ →L[ℝ] ℂ) S (invFunOn F S y)) :
    HasFDerivWithinAt (invFunOn F S) (A.symm : ℂ →L[ℝ] ℂ) (F '' S) y := by
  have hc := (inverseOn_lipschitz hF).continuousOn y hy
  have hm : MapsTo (invFunOn F S) (F '' S) S := fun _ hv => invFunOn_mem hv
  apply HasFDerivWithinAt.of_local_left_inverse (hc.tendsto_nhdsWithin hm) hd hy
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact invFunOn_eq hz

end CircleDomainRigidity

end

end OAI
