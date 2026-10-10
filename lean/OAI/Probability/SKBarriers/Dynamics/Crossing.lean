import Mathlib
import OAI.Probability.SKBarriers.Dynamics.BackwardBarrier

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def lastCrossing (f : ℕ → ℝ) (r : ℝ) (u : ℕ) : ℕ :=
  Nat.findGreatest (fun k => f k ≤ r) u

theorem lastCrossing_le (f : ℕ → ℝ) (r : ℝ) (u : ℕ) : lastCrossing f r u ≤ u :=
  Nat.findGreatest_le u

theorem lastCrossing_spec (f : ℕ → ℝ) (r : ℝ) (u : ℕ)
    (hex : ∃ k ≤ u,f k ≤ r) : f (lastCrossing f r u) ≤ r := by
  obtain ⟨k,hk,h⟩ := hex
  exact Nat.findGreatest_spec (P:=fun k => f k ≤ r) hk h

theorem lastCrossing_after (f : ℕ → ℝ) (r : ℝ) (u k : ℕ)
    (hk : lastCrossing f r u < k) (hku : k ≤ u) : r < f k := by
  exact lt_of_not_ge ((Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest (fun k => f k ≤ r) u = _)).2.2 hk hku)

theorem lastCrossing_band (f : ℕ → ℝ) (r d : ℝ) (u : ℕ)
    (hend : r < f u) (hex : ∃ k ≤ u,f k ≤ r)
    (hjump : ∀ k, k < u → |f (k+1)-f k| ≤ d) :
    f (lastCrossing f r u) ∈ Icc (r-d) r := by
  have hl := lastCrossing_le f r u
  have hs := lastCrossing_spec f r u hex
  have hlt : lastCrossing f r u < u := lt_of_le_of_ne hl (by intro he; rw [he] at hs; linarith)
  have ha := lastCrossing_after f r u (lastCrossing f r u+1) (by omega) (by omega)
  have hj := hjump _ hlt
  exact ⟨by linarith only [ha,(abs_le.mp hj).2],hs⟩

theorem lastCrossing_search (f : ℕ → ℝ) (r d : ℝ) (u : ℕ)
    (hd : 0 ≤ d) (hend : r < f u)
    (hjump : ∀ k, k < u → |f (k+1)-f k| ≤ d) :
    ∀ k,lastCrossing f r u ≤ k → k ≤ u → r-d ≤ f k := by
  intro k hk hku
  by_cases hex : ∃ i ≤ u,f i ≤ r
  · by_cases he : lastCrossing f r u=k
    · rw [← he]; exact (lastCrossing_band f r d u hend hex hjump).1
    · exact (by linarith only [lastCrossing_after f r u k (lt_of_le_of_ne hk he) hku,hd])
  · have h : r < f k := lt_of_not_ge (by intro h; exact hex ⟨k,hku,h⟩)
    linarith only [h,hd]

theorem lastCrossing_zero_of_none (f : ℕ → ℝ) (r : ℝ) (u : ℕ)
    (h : ¬∃ k ≤ u,f k ≤ r) : lastCrossing f r u=0 := by
  apply Nat.findGreatest_eq_zero_iff.mpr
  intro k _ hk hkr
  exact h ⟨k,hk,hkr⟩

theorem anchored_backwards_crossing {n : ℕ} (μ : ProbabilityMeasure ℝ)
    (v w : Config n) (x : ℕ → Config n) (t₀ ρ E d rᵢ rⱼ q : ℝ) (u : ℕ)
    (ht : 0 < t₀) (hρ : 0 < ρ) (hri : rᵢ ∈ Icc t₀ (2*t₀))
    (hspacing : 3*ρ ≤ rⱼ-rᵢ) (hwidth : ρ^8 < t₀/2)
    (hsmall : E+ρ^20+d/2 < ρ^8) (hsep : E+ρ^20+3*d/2 ≤ 2*ρ)
    (hd : 0 ≤ d) (hd' : d/2 ≤ ρ^20) (hq : rᵢ+E+2*ρ^20 < q)
    (hmass : (μ : Measure ℝ).real (Icc (rᵢ-2*ρ^8) (rᵢ+2*ρ^8)) ≤ ρ^4)
    (href : |overlap v w-rᵢ| ≤ E)
    (hanchor : q ≤ overlap v (x 0)) (_htarget : rⱼ < overlap w (x u))
    (hend : |overlap v (x u)-overlap v w| < 2*ρ^20)
    (hjump : ∀ z k, k < u → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (havoid : ∀ k, k ≤ u → (![v,x k,w] : ReplicaConfig n 3)∉narrowLockingSet n μ t₀ ρ) :
    ∃ k ≤ u,overlap w (x k) ≤ rⱼ := by
  by_contra H
  have hs : ∀ k,0 ≤ k → k ≤ u → rⱼ-d ≤ overlap w (x k) := by
    intro k _ hk
    have hh : rⱼ < overlap w (x k) := lt_of_not_ge (fun hh => H ⟨k,hk,hh⟩)
    linarith only [hh,hd]
  have HH := narrow_backwards_transfer μ v w x t₀ ρ E d rᵢ rⱼ (Nat.zero_le u)
    ht hρ hri hspacing hwidth hsmall hsep hd' hmass href hend
    (fun k _ hk => hjump v k hk) hs (fun k _ hk => havoid k hk) 0 (by omega) (by omega)
  linarith only [(abs_lt.mp HH).2,(abs_le.mp href).2,hanchor,hq]

def firstCrossing (f : ℕ → ℝ) (r : ℝ) (m : ℕ) : ℕ :=
  if h : ∃ k, k ≤ m ∧ f k ≤ r then Nat.find h else 0

theorem firstCrossing_band (f : ℕ → ℝ) (r d : ℝ) (m : ℕ)
    (hstart : r < f 0) (hend : f m ≤ r)
    (hjump : ∀ k, k < m → |f (k+1)-f k| ≤ d) :
    firstCrossing f r m ≤ m ∧ f (firstCrossing f r m) ∈ Icc (r-d) r := by
  have hex : ∃ k, k ≤ m ∧ f k ≤ r := ⟨m,le_rfl,hend⟩
  rw [firstCrossing,dite_eq_left hex]
  have hs := Nat.find_spec hex
  have hz : 0 < Nat.find hex := by
    by_contra H
    have he : Nat.find hex=0 := by omega
    rw [he] at hs
    linarith only [hs.2,hstart]
  have hp : r < f (Nat.find hex-1) := by
    apply lt_of_not_ge
    intro h
    exact Nat.find_min hex (by omega : Nat.find hex-1 < Nat.find hex) ⟨by omega,h⟩
  have hj := hjump (Nat.find hex-1) (by omega)
  rw [Nat.sub_add_cancel hz] at hj
  exact ⟨hs.1,by linarith only [hp,(abs_le.mp hj).1],hs.2⟩

end SK.Analytic

end
end

end OAI
