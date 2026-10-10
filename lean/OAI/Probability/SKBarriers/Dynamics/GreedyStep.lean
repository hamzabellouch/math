import Mathlib
import OAI.Probability.SKBarriers.Dynamics.Crossing
import OAI.Probability.SKBarriers.Dynamics.ConflictSuffix
import OAI.Probability.SKBarriers.Dynamics.ProtectedStep

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem greedy_locking_step {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    (v : ℕ → Config n) (w : Config n) (x : ℕ → Config n) (A : Finset ℕ)
    (r : ℕ → ℝ) (B H j u : ℕ) (t ρ E d b b' q : ℝ)
    (hj : 0 < j) (hB : 0 < B) (hHB : H < B) (hH : ⌈2/b^2⌉₊ ≤ H)
    (ht : 0 < t) (hρ : 0 < ρ) (hE : 0 ≤ E) (hd : 0 ≤ d) (hb : 0 < b)
    (hpack : 3*t < b^2/2) (hcsmall : 3*t < b) (hEst : E < t)
    (hsmall' : 2*t+E+2*(n:ℝ)^(-(1:ℝ)/100) < b')
    (hsep' : 2*E+4*(n:ℝ)^(-(1:ℝ)/100) < 3*ρ)
    (hwidth : ρ^8 < t/2)
    (hsmall : E+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2 < ρ^8)
    (hsep : E+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2 ≤ 2*ρ)
    (hd' : d/2 ≤ ρ^20) (heta : 2*(n:ℝ)^(-(1:ℝ)/100) < 2*ρ^20)
    (hq : 2*t+E+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 < q)
    (hr : ∀ i ≤ j, r i ∈ Icc t (2*t))
    (hspacing : ∀ i k, i < k → k ≤ j → 3*ρ ≤ r k-r i)
    (hmass : ∀ i < j, (μ : Measure ℝ).real (Icc (r i-2*ρ^8) (r i+2*ρ^8)) ≤ ρ^4)
    (hA : ∀ i ∈ A, i < j) (hblock : BlockProtected B j A)
    (hpath : ∀ i ∈ A, |overlap (v i) (x u)-r i| ≤ E)
    (hpair : ∀ i ∈ A, ∀ k ∈ A, i < k → |overlap (v i) (v k)-r i| ≤ E)
    (hanchor : q ≤ overlap (v 0) (x 0)) (htarget : q ≤ overlap w (x u))
    (hcell : j%B ≠ 0 → |overlap (v (j-1)) w| ≤ 3*t)
    (hjump : ∀ z k, k < u → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (hsigned : ∀ i ∈ A, (![v i,w,x u] : ReplicaConfig n 3) ∉ signedLockingSet n q b)
    (hbank : ∀ i ∈ A, ∀ k ∈ A, i < k →
      (![v k,v i,w] : ReplicaConfig n 3) ∉ signedLockingSet n b b' ∧
      (![v k,v i,flip w] : ReplicaConfig n 3) ∉ signedLockingSet n b b')
    (hnarrow : ∀ i ∈ A, ∀ k ≤ u,
      (![v i,x k,w] : ReplicaConfig n 3) ∉ narrowLockingSet n μ t ρ) :
    let D := A.filter (fun i => b < |overlap (v i) w|)
    let C := A\D
    let τ := lastCrossing (fun k => overlap w (x k)) (r j) u
    IsRetainedSuffix A D ∧ D.card ≤ H ∧ BlockProtected B (j+1) (insert j C) ∧
      0 ∈ C ∧ τ ≤ u ∧ overlap w (x τ) ∈ Icc (r j-d) (r j) ∧
      (∀ i ∈ C, |overlap (v i) w-r i| ≤ E+2*(n:ℝ)^(-(1:ℝ)/100)) ∧
      (∀ i ∈ C, |overlap (v i) (x τ)-r i| ≤ E+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20) := by
  classical
  let F := 2*(n:ℝ)^(-(1:ℝ)/100)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let D := A.filter (fun i => b < |overlap (v i) w|)
  let C := A\D
  have hc (i : ℕ) (hi : i ∈ C) : i ∈ A ∧ |overlap (v i) w| ≤ b := by
    have H := Finset.mem_sdiff.mp hi
    exact ⟨H.1,le_of_not_gt (fun hh => H.2 (Finset.mem_filter.mpr ⟨H.1,hh⟩))⟩
  have htransfer (i : ℕ) (hi : i ∈ A) (hcomp : |overlap (v i) w| ≤ b) :
      |overlap (v i) w-overlap (v i) (x u)| ≤ F := by
    apply signed_locking_of_not_mem (v i) w (x u) q b htarget hcomp _ (hsigned i hi)
    have hh := abs_add_le (overlap (v i) (x u)-r i) (r i)
    have hri := hr i (hA i hi).le
    rw [sub_add_cancel,abs_of_pos (ht.trans_le hri.1)] at hh
    linarith only [hh,hpath i hi,hri.2,hEst,hcsmall]
  have href (i : ℕ) (hi : i ∈ A) (hcomp : |overlap (v i) w| ≤ b) :
      |overlap (v i) w-r i| ≤ E+F := by
    have hh := abs_add_le (overlap (v i) w-overlap (v i) (x u)) (overlap (v i) (x u)-r i)
    rw [sub_add_sub_cancel] at hh
    linarith only [hh,htransfer i hi hcomp,hpath i hi]
  have hs : IsRetainedSuffix A D := by
    apply conflicts_are_suffix A v w r b b' t E F ρ hE ht.le hsmall' (by dsimp [F]; linarith only [hsep'])
      (fun i hi => hr i (hA i hi).le) (fun i hi k hk hik => hspacing i k hik (hA k hk).le) hpair href _ hF
    intro i hi k hk hik hconf hki hkw
    exact magnitude_locking_of_signed_avoid (v k) (v i) w b b' hconf.le hki hkw
      (hbank i hi k hk hik).1 (hbank i hi k hk hik).2
  have hcard : D.card ≤ H := by
    apply (conflict_filter_card hn A v w b (3*t) hb (by positivity) hpack _).trans hH
    intro i hi k hk hik
    have HH : |overlap (v i) (v k)-r (min i k)| ≤ E := by
      rcases lt_or_gt_of_ne hik with h | h
      · simpa only [min_eq_left h.le] using hpair i hi k hk h
      · simpa only [min_eq_right h.le,overlap_comm (v k) (v i)] using hpair k hk i hi h
    have hm : min i k ≤ j := (min_le_left _ _).trans (hA i hi).le
    have hh := abs_add_le (overlap (v i) (v k)-r (min i k)) (r (min i k))
    rw [sub_add_cancel,abs_of_pos (ht.trans_le (hr _ hm).1)] at hh
    linarith only [hh,HH,(hr _ hm).2,hEst]
  have hp := protected_block_step B H j hB hHB A D hA hblock hs hcard (by
    intro hmod hmem
    have hh := (Finset.mem_filter.mp hmem).2
    linarith only [hh,hcell hmod,hcsmall])
  have hzero : 0 ∈ C := hp.2 hj
  have hqj : r j < overlap w (x u) := by
    have hpow : 0 ≤ ρ^20 := by positivity
    dsimp [F] at hF
    linarith only [(hr j le_rfl).2,htarget,hq,hE,hF,hpow]
  have hsend (i : ℕ) (hi : i ∈ C) : |overlap (v i) (x u)-overlap (v i) w| < 2*ρ^20 := by
    rw [abs_sub_comm]
    exact (htransfer i (hc i hi).1 (hc i hi).2).trans_lt heta
  have hex := anchored_backwards_crossing μ (v 0) w x t ρ (E+F) d (r 0) (r j) q u
    ht hρ (hr 0 (by omega)) (hspacing 0 j hj le_rfl) hwidth hsmall hsep hd hd'
    (by dsimp [F]; linarith only [(hr 0 (by omega)).2,hq]) (hmass 0 hj)
    (href 0 (hc 0 hzero).1 (hc 0 hzero).2) hanchor hqj (hsend 0 hzero) hjump
    (hnarrow 0 (hc 0 hzero).1)
  have hlu := lastCrossing_le (fun k => overlap w (x k)) (r j) u
  refine ⟨hs,hcard,hp.1,hzero,hlu,lastCrossing_band _ _ _ _ hqj hex (hjump w),?_,?_⟩
  · intro i hi
    exact href i (hc i hi).1 (hc i hi).2
  · intro i hi
    have hiA := (hc i hi).1
    have Hn := narrow_backwards_transfer μ (v i) w x t ρ (E+F) d (r i) (r j) hlu
      ht hρ (hr i (hA i hiA).le) (hspacing i j (hA i hiA) le_rfl) hwidth hsmall hsep hd'
      (hmass i (hA i hiA)) (href i hiA (hc i hi).2) (hsend i hi)
      (fun k _ hk => hjump (v i) k hk)
      (lastCrossing_search _ _ _ _ hd hqj (hjump w))
      (fun k _ hk => hnarrow i hiA k hk) _ le_rfl hlu
    have HH := abs_add_le (overlap (v i) (x (lastCrossing (fun k => overlap w (x k)) (r j) u))-overlap (v i) w)
      (overlap (v i) w-r i)
    rw [sub_add_sub_cancel] at HH
    have HH2 := href i hiA (hc i hi).2
    dsimp [F] at HH2
    linarith only [HH,Hn,HH2]

end SK.Analytic

end
end

end OAI
