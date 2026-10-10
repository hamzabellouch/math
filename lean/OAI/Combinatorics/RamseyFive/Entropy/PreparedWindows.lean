import Mathlib
import OAI.Combinatorics.RamseyFive.Streams.PreparedStream
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalDomainCaps

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance pwBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance pwTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance pwIDE : DecidableEq (Slots w n) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma Prepared.window_deficit
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M) :
    mean (first (pair S.law ctx (windowTuple S))) (fun c=>activeDeficit
      (fiber (pair S.law ctx (windowTuple S)) c) (blockActive (fun _=>Finset.univ)) J)≤B := by
  rw [window_posterior_deficit]
  have h:=P.deficit
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  have he : psFinDE (w*(4*n)) = (inferInstance : DecidableEq (Fin (w*(4*n)))) := Subsingleton.elim _ _
  rw [he] at h
  exact h
end
end SharpRamseyFive.SelectedTuple

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ B A T β : Type} [Fintype κ] [Fintype B] [Fintype A] [Fintype T]
  [Fintype β] [Nonempty A]
local instance chosenRoundDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

lemma FixedOutside.totalCorrelation_le_active {ι : Type} [Fintype ι]
    (p : Law (ι→β)) (U : Finset ι) (J : ℝ) (hfix : FixedOutside p U)
    (hc : ∀i∈U,entropy (map p (fun x=>x i))≤J) :
    totalCorrelation p≤activeDeficit p U J := by
  unfold totalCorrelation activeDeficit
  apply sub_le_sub_right
  calc
    _ = ∑i∈U,entropy (map p (fun x=>x i)) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=>hfix.entropy_zero i hi)
    _ ≤ ∑_i∈U,J := Finset.sum_le_sum hc
    _ = _ := by simp

theorem exists_small_deletion_round (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (rounds rem : ℕ) (hrounds : 0<rounds) (hrem : 0<rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(S a b).card)
    (J d ε budget C : ℝ) (hd : 0<d) (hε : 0<ε)
    (D : κ→((B×A)⊕T)→Finset β) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (S a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)≤budget)
    (c : (i : Fin rounds)→κ→BlockHistory B A T β i.val→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀i a h x y,0≤c i a h x y)
    (hC : ∀i a,0<μ a→∀h,0<historyLaw (p a) (S a) i.val h→
      (∑x∈blockActive (historyUnused (S a) h),∑y∈blockActive (historyUnused (S a) h),c i a h x y)≤C) :
    ∃i : Fin rounds,mean (preRoundLaw μ p S i.val) (fun z=>
      ∑j∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S i.val J d ε (c i) z j)≤
      budget/d+(2*budget/rounds+C/rem)/ε := by
  obtain ⟨i,hi⟩:=exists_preRoundLaw_information μ p S rounds hrounds
    (fun a ha b=>by have := hS a ha b;omega)
  refine ⟨i,?_⟩
  have htc : mean μ (fun a=>totalCorrelation (p a))≤budget := by
    apply (mean_mono_pos μ (fun a ha=>FixedOutside.totalCorrelation_le_active (p a) _ J
      (hfix a ha) (fun j _=>(hp a ha).entropy_cap J (hJ a) j))).trans hbudget
  have hi' : mean (preRoundLaw μ p S i.val) (fun z=>blockAllInformation
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤2*budget/rounds :=
    hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htc (by norm_num)) (by positivity))
  have h:=preRound_bad_budget μ p S i.val rem hrem
    (fun a ha b=>by have := hS a ha b;have:=i.isLt;omega) J d ε hd hε D hJ hp hfix
    (c i) (hc i) C (hC i)
  exact h.trans (add_le_add (div_le_div_of_nonneg_right hbudget hd.le)
    (div_le_div_of_nonneg_right (add_le_add hi' le_rfl) hε.le))
end
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows LowConflict CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]
local instance rcrBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance rcrTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance rcrIDE : DecidableEq (Slots w n) := Classical.decEq _

omit [Nonempty (Fin n)] in
lemma historyCollision_closed_budget (hd : finrank K V=5)
    (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ) (s width M : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : ∀i,BandCondition (Real.log (Nat.card K)) width (u i) b)
    (heven : b.val%2=0) (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
    (hocc : ∀x,0<p x→∀S : Submodule K (Dual K V),
      (∑i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M)
    (steps : ℕ) (h : BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps)
    (U : Finset (Slots w n)) :
    (∑i∈U,∑j∈U,orderedCollision (historyPosterior p h) (slotEquiv w n) u s i j)≤
      4*(w*(4*n):ℝ)*M := by
  apply (ordered_collision_subset _ _ _ _ U).trans
  have hn : ((w*(4*n):ℕ):ℝ) = w*(4*n) := by push_cast; rfl
  rw [←hn]
  apply ordered_closed_collision_budget hd _ _ u s width M b hs hband heven hsmall
  · intro x hx i
    exact hinc x (history_support p steps h x hx) i
  · intro x hx S
    exact hocc x (history_support p steps h x hx) S

theorem exists_closed_reciprocal_round (hd : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (elig : κ→(Fin w×Bool)→Finset (Fin n)) (rounds rem : ℕ)
    (hrounds : 0<rounds) (hrem : 0<rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
    (J d ε budget s width M : ℝ) (hdpos : 0<d) (hε : 0<ε)
    (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
    (u : κ→Slots w n→ℝ) (b : Fin 7) (hs : 2 ≤ s)
    (hband : ∀a,0<μ a→∀i,BandCondition (Real.log (Nat.card K)) width (u a i) b)
    (heven : b.val%2=0) (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hinc : ∀a,0<μ a→∀x,0<p a x→∀i,Incident (x i).1 (x i).2)
    (hocc : ∀a,0<μ a→∀x,0<p a x→∀S : Submodule K (Dual K V),
      (∑i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
      ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
        preRoundBad μ p elig i.val J d ε (historyCollision p u s) z j)≤
      budget/d+(2*budget/rounds+(4*(w*(4*n):ℝ)*M)/rem)/ε := by
  apply exists_small_deletion_round μ p elig rounds rem hrounds hrem hS J d ε budget
    (4*(w*(4*n):ℝ)*M) hdpos hε D hJ hp hfix hbudget
    (fun i=>historyCollision p u s (steps:=i.val))
  · intro i a h x y
    exact orderedCollision_nonneg _ _ _ _ _ _
  · intro i a ha h hh
    exact historyCollision_closed_budget hd (p a) (u a) s width M b hs (hband a ha)
      heven hsmall (hinc a ha) (hocc a ha) i.val h _

theorem exists_open_reciprocal_round (hd : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (elig : κ→(Fin w×Bool)→Finset (Fin n)) (rounds rem : ℕ)
    (hrounds : 0<rounds) (hrem : 0<rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
    (J d ε budget s width : ℝ) (hdpos : 0<d) (hε : 0<ε)
    (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
    (u : κ→Slots w n→ℝ) (b : Fin 7) (hs : 2 ≤ s)
    (hband : ∀a,0<μ a→∀i,BandCondition (Real.log (Nat.card K)) width (u a i) b)
    (hodd : b.val%2≠0) (hwide : Real.log 32+3*s<width) :
    ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
      ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
        preRoundBad μ p elig i.val J d ε (historyCollision p u s) z j)≤
      budget/d+(2*budget/rounds)/ε := by
  have hh:=exists_small_deletion_round μ p elig rounds rem hrounds hrem hS J d ε budget
    0 hdpos hε D hJ hp hfix hbudget (fun i=>historyCollision p u s (steps:=i.val))
    (fun i a h x y=>orderedCollision_nonneg _ _ _ _ _ _) (by
      intro i a ha h hh
      have hz : ∀x y,historyCollision p u s a h x y=0 := by
        intro x y
        exact ordered_open_collision_zero hd _ _ (u a) s width b hs (hband a ha) hodd hwide x y
      simp only [hz,Finset.sum_const_zero,le_refl])
  simpa only [zero_div,add_zero] using hh
end
end SharpRamseyFive.Marking

end OAI
