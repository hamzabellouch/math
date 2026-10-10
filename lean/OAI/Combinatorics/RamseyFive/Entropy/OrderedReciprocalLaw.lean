import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.Windows
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalLowConflict

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I β : Type} [Fintype I] [Fintype β] {n : ℕ}

def orderedLaw (p : Law (I→β)) (e : I≃Fin n) : Law (Fin n→β) :=
  map p (fun x i=>x (e.symm i))
lemma orderedLaw_marginal (p : Law (I→β)) (e : I≃Fin n) (i : I) :
    map (orderedLaw p e) (fun x=>x (e i))=map p (fun x=>x i) := by
  rw [orderedLaw,map_comp]
  simp only [Function.comp_def,Equiv.symm_apply_apply]
lemma orderedLaw_pair (p : Law (I→β)) (e : I≃Fin n) (i j : I) :
    pair (orderedLaw p e) (fun x=>x (e i)) (fun x=>x (e j))=
      pair p (fun x=>x i) (fun x=>x j) := by
  rw [pair,orderedLaw,map_comp]
  simp only [Function.comp_def,Equiv.symm_apply_apply,pair]
lemma orderedLaw_positive (p : Law (I→β)) (e : I≃Fin n)
    (x : Fin n→β) (hx : 0<orderedLaw p e x) :
    ∃ y,0<p y ∧ ∀ i,x (e i)=y i := by
  obtain ⟨y,hy,rfl⟩:=map_positive p (fun x i=>x (e.symm i)) x hx
  exact ⟨y,hy,fun i=>by simp only [Equiv.symm_apply_apply]⟩
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Windows
noncomputable def slotEquiv (w r : ℕ) : Slots w r≃Fin (w*(4*r)) :=
  Equiv.ofBijective slotEmbedding (slotEmbedding_bijective w r)
lemma slotEquiv_apply {w r : ℕ} (i : Slots w r) : slotEquiv w r i=slotEmbedding i := rfl
end SharpRamseyFive.Windows
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def orderedCollision (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (i j : I) : ℝ :=
  let q:=orderedLaw p e
  let good:=reciprocalGood q (u∘e.symm) s
  tupleCollision q Projectivization.rep Projectivization.rep good (e i) (e j)+
    tupleCollision q Projectivization.rep Projectivization.rep good (e j) (e i)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedCollision_nonneg (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) (i j : I) : 0≤orderedCollision p e u s i j :=
  add_nonneg (tupleCollision_nonneg ..) (tupleCollision_nonneg ..)
omit [Finite K] [FiniteDimensional K V] in
lemma orderedCollision_symm (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) (i j : I) : orderedCollision p e u s i j=orderedCollision p e u s j i :=
  add_comm _ _
omit [Finite K] [FiniteDimensional K V] in
lemma orderedCollision_sum (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) :
    (∑ i,∑ j,orderedCollision p e u s i j)=
      2*∑ i,∑ j,tupleCollision (orderedLaw p e) Projectivization.rep Projectivization.rep
        (reciprocalGood (orderedLaw p e) (u∘e.symm) s) i j := by
  let c:=tupleCollision (orderedLaw p e) Projectivization.rep Projectivization.rep
    (reciprocalGood (orderedLaw p e) (u∘e.symm) s)
  change (∑ i,∑ j,(c (e i) (e j)+c (e j) (e i)))=2*∑ i,∑ j,c i j
  have h1 : (∑ i,∑ j,c (e i) (e j))=∑ i,∑ j,c i j := by
    calc
      _ = ∑ i,∑ j,c (e i) j := Finset.sum_congr rfl (fun i _=>e.sum_comp (c (e i)))
      _ = _ := e.sum_comp (fun i=>∑ j,c i j)
  have h2 : (∑ i,∑ j,c (e j) (e i))=∑ i,∑ j,c i j := by
    rw [Finset.sum_comm]
    exact h1
  simp only [Finset.sum_add_distrib,h1,h2]
  ring

omit [Finite K] in
lemma ordered_reciprocal_low_conflict (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j) :
    relationMass (fun a b=>a∈goodFirstEndpoints (map p (fun x=>x i))
        (32*Real.exp (5*Real.log (Nat.card K)-u i)) ((Nat.card K:ℝ)^4) s ∧
      b∈goodFirstEndpoints (swap (map p (fun x=>x j))) (32*Real.exp (u j)) ((Nat.card K:ℝ)^4) s ∧ Incident a b)
      (first (map p (fun x=>x i))) (second (map p (fun x=>x j)))≤
      80004*(entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
        entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j) := by
  have hc : ∀ x,0<orderedLaw p e x→TupleConsistent x := by
    intro x hx a b hab hf
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    have h:=hcons y hy (e.symm a) (e.symm b) (by simpa using hab)
    simpa only [←he,Equiv.apply_symm_apply] using h (by simpa only [←he,Equiv.apply_symm_apply] using hf)
  have h:=reciprocal_low_conflict hdim (orderedLaw p e) (u∘e.symm) s hc (e i) (e j) hij
  unfold reciprocalGood tupleMarginal at h
  simp only [orderedLaw_marginal,orderedLaw_pair,Function.comp_apply,Equiv.symm_apply_apply] at h
  apply h.trans
  have hn:=tupleCollision_nonneg (orderedLaw p e) Projectivization.rep Projectivization.rep
    (reciprocalGood (orderedLaw p e) (u∘e.symm) s) (e j) (e i)
  dsimp only [orderedCollision]
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact add_le_add le_rfl (le_add_of_nonneg_right hn)

lemma ordered_closed_collision_budget (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s width M : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : ∀ i,BandCondition (Real.log (Nat.card K)) width (u i) b)
    (heven : b.val%2=0) (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→∀ i,Incident (x i).1 (x i).2)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,orderedCollision p e u s i j)≤4*n*M := by
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
  have h:=reciprocal_closed_collisions hdim (orderedLaw p e) (u∘e.symm) s width M b
    hs (fun i=>hband (e.symm i)) heven hsmall hi ho
  rw [orderedCollision_sum]
  linarith

lemma ordered_open_collision_zero (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s width : ℝ) (b : Fin 7)
    (hs : 2 ≤ s) (hband : ∀ i,BandCondition (Real.log (Nat.card K)) width (u i) b)
    (hodd : b.val%2≠0) (hwide : Real.log 32+3*s<width) (i j : I) :
    orderedCollision p e u s i j=0 := by
  have h:=reciprocal_open_collisions hdim (orderedLaw p e) (u∘e.symm) s width b
    hs (fun i=>hband (e.symm i)) hodd hwide
  dsimp only [orderedCollision]
  rw [h,h,add_zero]

omit [Finite K] [FiniteDimensional K V] in
lemma ordered_collision_subset (p : Law (I→FlagPair K V)) (e : I≃Fin n)
    (u : I→ℝ) (s : ℝ) (S : Finset I) :
    (∑ i∈S,∑ j∈S,orderedCollision p e u s i j)≤∑ i,∑ j,orderedCollision p e u s i j := by
  apply (Finset.sum_le_sum (fun i hi=>Finset.sum_le_univ_sum_of_nonneg
    (fun j=>orderedCollision_nonneg p e u s i j))).trans
  exact Finset.sum_le_univ_sum_of_nonneg
    (fun i=>Finset.sum_nonneg fun j _=>orderedCollision_nonneg p e u s i j)

end
end SharpRamseyFive.Marking

end OAI
