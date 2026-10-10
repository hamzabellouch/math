import OAI.Analysis.FourierLLogL.Compress.Schedule
import OAI.Analysis.FourierLLogL.Compress.Phase
import OAI.Analysis.FourierLLogL.Compress.Low

open Function Filter Set
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A G Θ : Type} [Fintype A] [Fintype G] [DecidableEq G]
    [AddCommGroup G] [Nonempty A] [Fintype Θ]

omit [Nonempty A] in
lemma init_gap (tag : A → G) (hi : Injective tag) (P : Law A) :
    fundG tag (initial P) 1 = P.entropy := by
  rw [G_initial]
  let Q := iid P 1
  have h : Q.send (fun x => x 0) = P := marginalPack (fun _ => P) _
  change Q.H _ = _; rw [← h]
  refine H_partition Q (X:=tot tag) (Y:=fun x => x 0) (fun _ _ => ?_)
  simp only [tot,Fin.sum_univ_one,hi.eq_iff]

/-- Finite compression from schedule and numerical constraints, before a
choice of scales in terms of height. -/
lemma compress_arrays (tag : A → G) (hi : Injective tag) (q : Law G)
    (hq : ∀ x, 0 < q x) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x) (hc0 : c 0=0)
    (Q : Law Θ) (χ : Θ → AddChar G ℂ) (hn : ∀ t x, ‖χ t x‖=1)
    (hrq : ∀ g, (↑(exp (-c g)):ℂ)=Q.Cx fun t => χ t g)
    (hlog : ∀ g, -log (q g) = -log (q 0) + c g)
    (F L C : ℝ) (hF : 1 ≤ F) (hL : 0 ≤ L)
    (T N m : ℕ) (hm : 0 < m) (hN : m ≤ N) (hT : 3*N ≤ T) (S : Schedule)
    (l u r : ℕ → ℕ)
    (hl : ∀ i, i < S.size → l i ≤ u i ∧ u i ≤ m ∧ 0 < u i ∧ 0 < r i ∧
      2*r i*l i ≤ N ∧ L ≤ (r i:ℝ)*(u i:ℝ))
    (hp : ∀ i j, i < j → j < S.size → u j ≤ l i ∧ r i ≤ r j)
    (hg : ∀ P : Law A, exp (-F) ≤ heatMoment (Fin T) P tag c)
    (hC : 10*F+2*(-log (q 0))+1 ≤ C)
    (hh : ∀ i, i < S.size → 0 < l i)
    (hs : ∀ i, i < S.size →
      2*m*√F/N*lnS (Fin (u i)) tag ≤ F ∧
      log (Fintype.card (Ticket (r i) (2*r i))) + r i +
        2*(2*m*√F/N)*lnS (Fin (r i*l i)) tag ≤ 6*F) :
    ∃ (a : A) (s : Finset A), s.Nonempty ∧
      log (Fintype.card A)-log (s.card:ℝ) ≤
        8*(3*(F/N)+S.loss*C*C/F)+2 ∧ small_defects tag χ Q L s a (350*F) := by
  have hFp : 0 < F := by linarith
  have hCp : 0 < C := by
    have hh := Real.log_nonpos (q.nonneg 0) (q.le_one 0)
    linarith
  have hNp : (0:ℝ)< N := by
    exact_mod_cast (Nat.lt_of_lt_of_le hm hN)
  obtain ⟨p,R,h1,h2,h3,h4,h5⟩ := select_context tag c hc T N m hm hN hT F hFp hg
  let ε := 2*m*√F/N
  let x : Starting tag c N m (3*F) ε := ⟨p,R,h1,h2,h4,hN,h5⟩
  let W := initial p
  have ha (i) (hh : i < S.size) : fundG tag W (u i) ≤ C := by
    have H := x.G_upper hc q hq (-log (q 0)) hlog _ (hl i hh).2.1
    apply H.trans
    unfold ε
    have hj := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    linarith [(hs i hh).1]
  have hb (i) (hh : i < S.size) (hle : 1 ≤ l i) : fundI tag W (r i) ≤ C := by
    refine (x.I_upper hc q hq (-log (q 0)) hlog _ ?_).trans ?_
    · have := (hl i hh).2.2.2.2.1
      nlinarith
    linarith

  obtain ⟨P,hv,hW,i,hi',hK⟩ :=
    reach tag hi c hc W C F hCp hFp S m l u r hm (fun i h => ⟨(hl i h).1,(hl i h).2.1⟩)
      hp ha (fun i h => hb i h (hh i h))
  obtain ⟨hi1,hi2,hu',hr',hn',hL'⟩ := hl i hi'
  have HK : fundK tag c P (u i) (r i) ≤ 10*F := by
    have H := x.K_upper hc hc0 (l i) (r i) hr' (le_trans hi1 hi2) hn'
    have HH := K_anti tag c hv (l i) (r i)
    change fundK tag c W _ _ ≤ _ at H
    dsimp only [ε] at H
    linarith [(hs i hi').2]
  let D := 3*(F/N)+S.loss*C*C/F
  have hD : 0 < D := by unfold D; have := S.loss_pos; positivity
  have Hd : log (Fintype.card A) - fundG tag P 1 ≤ D := by
    rw [show fundG tag W 1 = _ from init_gap tag hi p] at hW
    linarith
  obtain ⟨p',z,hz,hz'⟩ := freeze tag hi c hc P (u i) (r i) hu' hr' (10*F) D
    (by positivity) hD HK Hd
  have : NeZero (r i) := ⟨hr'.ne'⟩
  have : NeZero (u i) := ⟨hu'.ne'⟩
  have H0 := alignment tag c Q χ hn hrq p' z (10*F) D L (by linarith) hD hL
    (by simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]) hz (by
      simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul])
  rwa [show 350*F = 35*(10*F) by ring]
end FourierLLogL.Compress

end OAI
