import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaCharge

namespace OAI

                                       
section

/-! Summing actual sparse, side-reference and wholesale alpha jump charges.
There is no additive restart amount for individual epochs. -/
noncomputable section
namespace UniformKServer.EpochAlphaBudget
open Finset UniformKServer.EpochAlphaCharge
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem variation_le {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    EpochGeometry.variation a b ≤ sizeCharge a b := by
  apply sum_le_sum
  intro i _
  unfold AllocationSchedule.charge
  split_ifs with he
  · simp [he]
  · exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hb i),abs_of_nonneg (ha i)]; ring_nf; rfl)

theorem charge_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {K : ℝ} (hK : 0 ≤ K) (H : ℕ) :
    (∑ t ∈ range H, (320*K*sizeCharge (a t) (a (t+1))+
        1600*K*SideReferenceSchedule.charge a p t+1200*K*SideReferenceSchedule.wholesale a p t)) ≤
      4100000*K*(∑ t ∈ range H, sizeCharge (a t) (a (t+1)))+
      4400*K*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  have hV := sum_le_sum (s:=range H) (fun t _ => variation_le (ha t) (ha (t+1)))
  have hS := SideReferenceSchedule.budget ha p H
  have hW := SideReferenceSchedule.wholesale_budget ha p H
  have hV' := mul_le_mul_of_nonneg_left hV hK
  have hS' := mul_le_mul_of_nonneg_left hS hK
  have hW' := mul_le_mul_of_nonneg_left hW hK
  have hx : 0 ≤ K*(∑ t ∈ range H, sizeCharge (a t) (a (t+1))) :=
    mul_nonneg hK (sum_nonneg fun t _ => size_nonneg (ha t) (ha (t+1)))
  simp only [sum_add_distrib,←mul_sum]
  nlinarith

theorem jump_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hp : ∀ t, AlphaEmpty.valid (param a p ell ct C t)) (B v : ℕ → ι → ℝ)
    (hB : ∀ t i, 0 ≤ B t i) (hBb : ∀ t i, B t i ≤ 40*a (t+1) i)
    (hpa : ∀ t, DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C t)) (B t))
    (hqa : ∀ t, DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C (t+1))) (B t))
    (hv : ∀ t, AlphaEmpty.state (param a p ell ct C (t+1)) (v t))
    (hf : ∀ t i, (∑ j, B t j)*v t i ≤ (1+AlphaEmpty.eta (param a p ell ct C t) i)*B t i)
    (H : ℕ) :
    (∑ t ∈ range H, |AlphaEmpty.potential (param a p ell ct C (t+1)) (B t) (v t)-
        AlphaEmpty.potential (param a p ell ct C t) (B t) (v t)|) ≤
      4100000*(C*ell)*(∑ t ∈ range H, sizeCharge (a t) (a (t+1)))+
      4400*(C*ell)*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  exact (sum_le_sum (s:=range H) fun t _ => jump ha p hsc hct hp t (B t) (v t)
    (hB t) (hBb t) (hpa t) (hqa t) (hv t) (hf t)).trans (charge_budget ha p hsc H)

end UniformKServer.EpochAlphaBudget

end


end

end OAI
