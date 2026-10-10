import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.History
import OAI.Combinatorics.RamseyFive.Marking.HighDomainEndpoints

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I : Type} [Fintype I] {n : ℕ}
lemma sum_symm_reindex (e : I≃Fin n) (c : Fin n→Fin n→ℝ) :
    (∑ i,∑ j,(c (e i) (e j)+c (e j) (e i)))=2*∑ i,∑ j,c i j := by
  have h1 : (∑ i,∑ j,c (e i) (e j))=∑ i,∑ j,c i j := by
    calc
      _ = ∑ i,∑ j,c (e i) j := Finset.sum_congr rfl (fun i _=>e.sum_comp (c (e i)))
      _ = _ := e.sum_comp (fun i=>∑ j,c i j)
  have h2 : (∑ i,∑ j,c (e j) (e i))=∑ i,∑ j,c i j := by
    rw [Finset.sum_comm]
    exact h1
  simp only [Finset.sum_add_distrib,h1,h2]
  ring
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def orderedHighCollision (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) : ℝ :=
  highCollision (orderedLaw p e) s (e i) (e j)+highCollision (orderedLaw p e) s (e j) (e i)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedHighCollision_nonneg (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) :
    0≤orderedHighCollision p e s i j := add_nonneg (high_collision_nonneg ..) (high_collision_nonneg ..)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedHighCollision_symm (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) :
    orderedHighCollision p e s i j=orderedHighCollision p e s j i := add_comm _ _

omit [Finite K] [FiniteDimensional K V] in
lemma orderedLaw_consistent (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2) :
    ∀ x,0<orderedLaw p e x→TupleConsistent x := by
  intro x hx a b hab hf
  obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
  have h:=hcons y hy (e.symm a) (e.symm b) (by simpa using hab)
  simpa only [←he,Equiv.apply_symm_apply] using h (by simpa only [←he,Equiv.apply_symm_apply] using hf)

lemma orderedHigh_collision_budget (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s M : ℝ)
    (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→∀ i,Incident (x i).1 (x i).2)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,orderedHighCollision p e s i j)≤4*n*M := by
  have hi : ∀ x,0<orderedLaw p e x→TupleIncident x := by
    intro x hx i
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    simpa only [←he,Equiv.apply_symm_apply] using hinc y hy (e.symm i)
  have ho : ∀ x,0<orderedLaw p e x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M := by
    intro x hx S
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    have heq : (∑ i,if InRectangle S (y i).1.rep (y i).2.rep then (1:ℝ) else 0)=
        (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0) := by
      simpa only [he] using e.sum_comp
        (fun i=>if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)
    rw [←heq]
    exact hocc y hy S
  have h:=high_three_collisions hdim (orderedLaw p e) s M hs hsmall hi ho
  simp only [orderedHighCollision]
  rw [sum_symm_reindex]
  linarith

lemma orderedHigh_pair_impossible (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (hA : (3:ℝ)/4≤eventMass (first (map p (fun x=>x i))) (highThreeLeft (map p (fun x=>x i)) s))
    (hB : (3:ℝ)/4≤eventMass (second (map p (fun x=>x j))) (highThreeRight (map p (fun x=>x j)) s))
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*(Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedHighCollision p e s i j≤ε)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ))) : False := by
  apply high_three_pair_impossible hdim (orderedLaw p e) s ε (orderedLaw_consistent p e hcons)
    (e i) (e j) hij
  · simpa only [tupleMarginal,orderedLaw_marginal] using hA
  · simpa only [tupleMarginal,orderedLaw_marginal] using hB
  · exact hvar
  · simp only [tupleMarginal,orderedLaw_marginal,orderedLaw_pair]
    apply le_trans _ hgood
    dsimp only [orderedHighCollision]
    linarith [high_collision_nonneg (orderedLaw p e) s (e j) (e i)]
  · exact hsmall
end
end SharpRamseyFive.Marking

end

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]
local instance highDomainThreeBlockDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance highDomainThreeIndexDE : DecidableEq (Slots w r) := Classical.decEq _

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
  [Nonempty (Fin r)] in
theorem high_three_domain_good_pair_impossible (hdim : finrank K V=5)
    (D : Slots w r→Finset (FlagPair K V))
    (p : Law (Slots w r→FlagPair K V))
    (hD : ∀i,support (map p (fun x=>x i))⊆D i)
    (hcap : ∀i,HighCaps (D i) 3 3)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i<slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0<s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (sel : (Fin w×Bool)→Fin r) (v : Fin w) (t : Fin (2*r))
    (hgoodE : indexBad J d ε p (orderedHighCollision p (slotEquiv w r) s) sel
      (Sum.inl ((v,false),sel (v,false)))=0)
    (hgoodM : indexBad J d ε p (orderedHighCollision p (slotEquiv w r) s) sel
      (Sum.inr (v,t))=0) : False := by
  let i : Slots w r:=Sum.inl ((v,false),sel (v,false))
  let j : Slots w r:=Sum.inr (v,t)
  have hi:=good_index_scores J d ε p _ (orderedHighCollision_nonneg p (slotEquiv w r) s) sel i hgoodE
  have hj:=good_index_scores J d ε p _ (orderedHighCollision_nonneg p (slotEquiv w r) s) sel j hgoodM
  have hA:=(hcap i).three_mass (map p (fun x=>x i)) (hD i) s d hs (by linarith [hi.1]) hbad
  have hB:=(hcap j).three_mass (map p (fun x=>x j)) (hD j) s d hs (by linarith [hj.1]) hbad
  apply orderedHigh_pair_impossible hdim p (slotEquiv w r) s ε hcons i j
    (representative_early v (sel (v,false)) t) hA.1 hB.2 hvar ?_ hsmall
  exact good_index_scores_reverse J d ε p _
    (orderedHighCollision_nonneg p (slotEquiv w r) s)
    (orderedHighCollision_symm p (slotEquiv w r) s) sel j hgoodM (v,false) trivial

omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_three_domain_preRound_impossible {κ : Type} [Fintype κ] {n rem : ℕ}
    (hdim : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w r→FlagPair K V))
    (D : κ→Slots w r→Finset (FlagPair K V))
    (hD : ∀a,0<μ a→InDomains (p a) (D a))
    (hcap : ∀a,0<μ a→∀i,HighCaps (D a i) 3 3)
    (hcons : ∀ a,0<μ a→∀ x,0<p a x→∀ i j,slotEmbedding i<slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (S : κ→(Fin w×Bool)→Finset (Fin r)) (hrem : 0<rem) (hr : r≤2*rem)
    (hS : ∀ a,0<μ a→∀ b,rem+n≤(S a b).card)
    (J d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hs : 0<s)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*
      (Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ)))
    (hbudget : 5*mean (preRoundLaw μ p S n) (fun z=>
      ∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
        preRoundBad μ p S n J d ε
          (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w r) s) z i)<2*r*w) :
    False := by
  obtain ⟨z,hz,v,t,hM,hE⟩:=preRound_good_early_middle (n:=n) (rem:=rem) μ p S hrem hr hS J d ε
    (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w r) s) hbudget
  have ha:=(preRound_positive μ p S n z hz).1
  apply high_three_domain_good_pair_impossible hdim (D z.1.1)
    (historyPosterior (p z.1.1) z.1.2) _ (hcap _ ha) _
    J d s ε hJ hs hbad hvar hsmall z.2 v t hE hM
  · intro i
    exact marginal_support_subset _ _ (history_in_domains _ _ (hD _ ha) n z.1.2) i
  · intro x hx i j hij hi
    exact hcons _ ha x (history_support (p z.1.1) n z.1.2 x hx) i j hij hi

end
end SharpRamseyFive.Marking

end OAI
