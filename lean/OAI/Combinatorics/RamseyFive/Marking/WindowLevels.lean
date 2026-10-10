import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Repair
import OAI.Combinatorics.RamseyFive.Marking.WindowReciprocalScores
import OAI.Combinatorics.RamseyFive.Entropy.WindowVariation

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance windowLevelsBlockDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance windowLevelsIndexDE : DecidableEq (Slots w r) := Classical.decEq _

structure ReciprocalWindows (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (e : I→Fin w) (s : ℝ) where
  early : ∀ i,ReciprocalLevels (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s
  late : ∀ i,ReciprocalLevels (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s
  early_half : ∀ i,(1:ℝ)/2 ≤ eventMass (first (map p (fun x=>x (earlySlot sel (e i)))))
    (reciprocalGoodA (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s)
  late_half : ∀ i,(1:ℝ)/2 ≤ eventMass (second (map p (fun x=>x (lateSlot sel (e i)))))
    (reciprocalGoodB (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s)

namespace ReciprocalWindows
variable {p : Law (Slots w r→FlagPair K V)} {u : Slots w r→ℝ}
  {sel : (Fin w×Bool)→Fin r} {e : I→Fin w} {s : ℝ}
  (W : ReciprocalWindows p u sel e s)

def firstReference (i : I) : Law (ℙ K V) :=
  conditionOn (first (map p (fun x=>x (earlySlot sel (e i)))))
    (reciprocalGoodA (map p (fun x=>x (earlySlot sel (e i)))) (u (earlySlot sel (e i))) s)
    (lt_of_lt_of_le (by norm_num) (W.early_half i))
def secondReference (i : I) : Law (ℙ K (Dual K V)) :=
  conditionOn (second (map p (fun x=>x (lateSlot sel (e i)))))
    (reciprocalGoodB (map p (fun x=>x (lateSlot sel (e i)))) (u (lateSlot sel (e i))) s)
    (lt_of_lt_of_le (by norm_num) (W.late_half i))
def firstSupport (i : I) (A : Finset (ℙ K V)) : Finset (ℙ K V) :=
  (W.early i).firstLaw.repair A
def secondSupport (i : I) (B : Finset (ℙ K (Dual K V))) : Finset (ℙ K (Dual K V)) :=
  (W.late i).secondLaw.repair B

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma first_nonempty (i : I) (A : Finset (ℙ K V)) : (W.firstSupport i A).Nonempty :=
  ((W.early i).first_good _ ((W.early i).firstLaw.repair_positive A)).1
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma second_nonempty (i : I) (B : Finset (ℙ K (Dual K V))) : (W.secondSupport i B).Nonempty :=
  ((W.late i).second_good _ ((W.late i).secondLaw.repair_positive B)).1
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma first_domination (i : I) (a : ℙ K V) :
    (∑ A,(W.early i).firstLaw A*uniformWeight (W.firstSupport i A) a) ≤
      (4*Real.exp 1)*W.firstReference i a := by
  exact repaired_levels_conditioned_domination _ _ _ _ _ (by positivity)
    (fun A h=>((W.early i).first_good A h).2.1) (W.early i).first_dom a
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma second_domination (i : I) (b : ℙ K (Dual K V)) :
    (∑ B,(W.late i).secondLaw B*uniformWeight (W.secondSupport i B) b) ≤
      (4*Real.exp 1)*W.secondReference i b := by
  exact repaired_levels_conditioned_domination _ _ _ _ _ (by positivity)
    (fun B h=>((W.late i).second_good B h).2.1) (W.late i).second_dom b

omit [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma support_product (k : ℝ) (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
    (i : I) (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    (Nat.card K:ℝ)^5*Real.exp (-(k+2*s+Real.log 4)) ≤
      ((W.firstSupport i A).card:ℝ)*(W.secondSupport i B).card := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=pivot_support_product (Nat.card K) (u (earlySlot sel (e i))) (u (lateSlot sel (e i)))
    s k (W.firstSupport i A).card (W.secondSupport i B).card hq (hdrop i)
    ((W.early i).first_size _ ((W.early i).firstLaw.repair_positive A))
    ((W.late i).second_size _ ((W.late i).secondLaw.repair_positive B))
  have he : Real.exp (-(k+2*s+Real.log 4))=Real.exp (-k-2*s)/4 := by
    rw [show -(k+2*s+Real.log 4)=(-k-2*s)-Real.log 4 by ring,
      Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)]
  simpa only [he,mul_div_assoc] using hh

omit [Finite K] [Nonempty (Fin r)] in
lemma reference_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i<slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel (e i))=0)
    (i j : I) (hij : i ≤ j) :
    relationMass Incident (W.firstReference i) (W.secondReference j) ≤ 320016*ε := by
  exact window_reference_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij)
    (hgood i) (W.early_half i) (W.late_half j)

omit [Finite K] [Nonempty (Fin r)] in
lemma target_right_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i<slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (i j : I) (hij : i ≤ j) (t : Fin (2*r))
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot (e i) t)=0) :
    relationMass Incident
      (fun a=>if a∈reciprocalGoodA (map p (fun x=>x (middleSlot (e i) t))) (u (middleSlot (e i) t)) s
        then first (map p (fun x=>x (middleSlot (e i) t))) a else 0)
      (W.secondReference j) ≤ 160008*ε :=
  window_target_right_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij) t hgood (W.late_half j)

omit [Finite K] [Nonempty (Fin r)] in
lemma target_left_sparse [Preorder I] (hdim : finrank K V=5) (he : Monotone e)
    (d ε : ℝ)
    (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i<slotEmbedding j → Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
    (i j : I) (hij : i ≤ j) (t : Fin (2*r))
    (hgood : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot (e j) t)=0) :
    relationMass Incident (W.firstReference i)
      (fun b=>if b∈reciprocalGoodB (map p (fun x=>x (middleSlot (e j) t))) (u (middleSlot (e j) t)) s
        then second (map p (fun x=>x (middleSlot (e j) t))) b else 0) ≤ 160008*ε :=
  window_target_left_sparse hdim p u sel _ d s ε hcons (e i) (e j) (he hij) t hgood (W.early_half i)
end ReciprocalWindows

omit [Nonempty (Fin r)] in
theorem reciprocal_windows_exist (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (e : I→Fin w) (s d ε C₀ : ℝ) (hs : 0<s)
    (hinc : ∀ x,0<p x → ∀ i,Incident (x i).1 (x i).2)
    (hA : ∀ i,((support (first (map p (fun x=>x i)))).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u i))
    (hB : ∀ i,((support (second (map p (fun x=>x i)))).card:ℝ) ≤ 32*Real.exp (u i))
    (hflag : ∀ i,((support (map p (fun x=>x i))).card:ℝ) ≤ C₀*(Nat.card K:ℝ)^4)
    (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel (e i))=0 ∧
      indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (lateSlot sel (e i))=0)
    (hmass : reciprocalBadMass s d C₀ ≤ (1:ℝ)/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C₀ ≤ (1:ℝ)/2) :
    Nonempty (ReciprocalWindows p u sel e s) := by
  have hend (i : Slots w r) (h : indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel i=0) :
      4*Real.log (Nat.card K)-entropy (map p (fun x=>x i)) ≤ d :=
    (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel i h).1
  have hi (i : Slots w r) : ∀ z,0 < map p (fun x=>x i) z → Incident z.1 z.2 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=map_positive p (fun x=>x i) z hz
    exact hinc x hx i
  let L (i : I) := Classical.choice (reciprocal_levels_exist hdim _ _ s d C₀ (hi _) hs
    (hA _) (hB _) (hflag _) (hend _ (hgood i).1) hsmall)
  let R (i : I) := Classical.choice (reciprocal_levels_exist hdim _ _ s d C₀ (hi _) hs
    (hA _) (hB _) (hflag _) (hend _ (hgood i).2) hsmall)
  refine ⟨⟨L,R,?_,?_⟩⟩
  · intro i
    exact (reciprocal_good_mass _ _ s d C₀ hs (hA _) (hB _) (hflag _) (hend _ (hgood i).1) hmass).1
  · intro i
    exact (reciprocal_good_mass _ _ s d C₀ hs (hA _) (hB _) (hflag _) (hend _ (hgood i).2) hmass).2
end
end SharpRamseyFive.Marking

end OAI
