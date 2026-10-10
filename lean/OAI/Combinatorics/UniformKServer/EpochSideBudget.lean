import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaBudget
import OAI.Combinatorics.UniformKServer.EpochSideCharge

namespace OAI

                                      
section

/-! Summed actual side parameter jumps, including wholesale epochs, with no
per-epoch additive loss. -/
noncomputable section
namespace UniformKServer.EpochSideBudget
open Finset UniformKServer.EpochSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem charge_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {K : ℝ} (hK : 0 ≤ K) (H : ℕ) :
    (∑ t ∈ range H, 480*K*(EpochAlphaCharge.sizeCharge (a t) (a (t+1))+
      SideReferenceSchedule.wholesale a p t)) ≤
      97920*K*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (a t) (a (t+1)))+
      480*K*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  have hV := sum_le_sum (s:=range H) (fun t _ => EpochAlphaBudget.variation_le (ha t) (ha (t+1)))
  have hW := SideReferenceSchedule.wholesale_budget ha p H
  have hV' := mul_le_mul_of_nonneg_left hV hK
  have hW' := mul_le_mul_of_nonneg_left hW hK
  simp only [←mul_sum,sum_add_distrib]
  nlinarith

theorem jump_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    (ell cw : ℝ) (b : ℕ → ℝ)
    (hb : ∀ t, SideReferenceSchedule.reset a p t=false → b t=b (t+1))
    (hp : ∀ t, AdaptiveSide.valid (param a p ell cw b t))
    (B v : ℕ → ι → ℝ) (D : ℕ → ℝ) (hD : ∀ t, 0 ≤ D t)
    (hB : ∀ t i, 0 ≤ B t i) (hBb : ∀ t i, B t i ≤ 40*a (t+1) i)
    (hv : ∀ t, DomainTransport.domain (param a p ell cw b (t+1)).active 11 (v t))
    (hf : ∀ t i, D t*v t i ≤ ((param a p ell cw b t).b+AdaptiveSide.theta (param a p ell cw b t) i)*B t i)
    (H : ℕ) :
    (∑ t ∈ range H, |AdaptiveSide.potential (param a p ell cw b (t+1)) (B t) (D t) (v t)-
        AdaptiveSide.potential (param a p ell cw b t) (B t) (D t) (v t)|) ≤
      97920*(2000*(ell/cw+1))*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (a t) (a (t+1)))+
      480*(2000*(ell/cw+1))*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  exact (sum_le_sum (s:=range H) fun t _ => EpochSideCharge.jump ha p ell cw b hb hp t
    (B t) (v t) (hD t) (hB t) (hBb t) (hv t) (hf t)).trans
    (charge_budget ha p (AdaptiveSide.slope_nonneg (hp 0)) H)

end UniformKServer.EpochSideBudget

end


end

end OAI
