import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RevealDomains
import OAI.Combinatorics.RamseyFive.Entropy.EventWeight
import OAI.Combinatorics.RamseyFive.Geometry.OrientedTreeDomains
import OAI.Combinatorics.RamseyFive.Geometry.OrderedTargetRetention

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]

lemma eventWeight_mean (p : Law A) (P : A→Prop) :
    eventWeight p P=mean p (fun a=>if P a then 1 else 0) := by
  simp only [eventWeight,mean,mul_ite,mul_one,mul_zero]

lemma eventWeight_le_one (p : Law A) (P : A→Prop) : eventWeight p P≤1 := by
  rw [eventWeight_mean]
  calc
    _ ≤ mean p (fun _=>1) := mean_mono _ (fun a=>by split_ifs <;> norm_num)
    _ = 1 := mean_const p 1

lemma eventWeight_exists_le (p : Law A) (P : I→A→Prop) :
    eventWeight p (fun a=>∃ i,P i a)≤∑ i,eventWeight p (P i) := by
  simp_rw [eventWeight_mean]
  rw [←mean_sum]
  apply mean_mono
  intro a
  by_cases h : ∃ i,P i a
  · obtain ⟨i,hi⟩:=h
    rw [ite_eq_left ⟨i,hi⟩]
    calc
      (1:ℝ) = (if P i a then 1 else 0) := by rw [ite_eq_left hi]
      _ ≤ ∑ j,if P j a then 1 else 0 := Finset.single_le_sum (f:=fun j=>if P j a then (1:ℝ) else 0)
        (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun j _=>by split_ifs <;> norm_num

lemma iid_eval_mean [DecidableEq I] (p : Law A) (i : I) (f : A→ℝ) :
    mean (iid p I) (fun x=>f (x i))=mean p f := by
  exact piLaw_eval_expectation (fun _ : I=>p) i f

lemma iid_eval_event [DecidableEq I] (p : Law A) (i : I) (P : A→Prop) :
    eventWeight (iid p I) (fun x=>P (x i))=eventWeight p P := by
  simp_rw [eventWeight_mean]
  exact iid_eval_mean p i (fun a=>if P a then (1:ℝ) else 0)

lemma iid_exists_event [DecidableEq I] (p : Law A) (P : A→Prop) :
    eventWeight (iid p I) (fun x=>∃ i,P (x i))≤Fintype.card I*eventWeight p P := by
  apply (eventWeight_exists_le (iid p I) (fun (i:I) (x:I→A)=>P (x i))).trans
  simp only [iid_eval_event,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,le_refl]

lemma iid_nested_exists_event [DecidableEq I] [DecidableEq J]
    (p : Law A) (P : A→Prop) :
    eventWeight (iid (iid p I) J) (fun x=>∃ j i,P (x j i))≤
      Fintype.card J*(Fintype.card I*eventWeight p P) := by
  exact (iid_exists_event (iid p I) (fun x=>∃ i,P (x i))).trans
    (mul_le_mul_of_nonneg_left (iid_exists_event p P) (Nat.cast_nonneg _))
end

noncomputable section
variable {α : Type*} [Fintype α]
lemma eventMass_filter_mean (p : Law α) (P : α→Prop) :
    eventMass p (Finset.univ.filter P)=mean p (fun a=>if P a then 1 else 0) := by
  simp only [eventMass,Finset.sum_filter,mean,mul_ite,mul_one,mul_zero]
lemma mean_congr_pos (p : Law α) {f g : α→ℝ} (h : ∀a,0<p a→f a=g a) : mean p f=mean p g :=
  le_antisymm (mean_mono_pos p (fun a ha=>(h a ha).le))
    (mean_mono_pos p (fun a ha=>(h a ha).ge))
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

omit [Finite K] [FiniteDimensional K V] in
lemma variableTreeLaw_mean (w : ℕ) (m : Fin (w+1))
    (g : OrientedPivotTreeTape f r (finiteBalanced m.val)→ℝ) :
    mean (variableTreeLaw f r w) (fun t=>g (t m))=
      mean (orientedPivotTreeLaw f r (finiteBalanced m.val)) g := by
  rw [←mean_map,variableTreeLaw_eval]

theorem variable_table_target_failure (w : ℕ) (m : Fin (w+1))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (μ : Fin (m.val+1)→Law (Finset (ℙ K V)))
    (ν : Fin (m.val+1)→Law (Finset (ℙ K (Dual K V))))
    (X : Fin (m.val+1)→Finset (ℙ K V)→Finset (ℙ K V))
    (Y : Fin (m.val+1)→Finset (ℙ K (Dual K V))→Finset (ℙ K (Dual K V)))
    (hX : ∀i a,(X i a).Nonempty) (hY : ∀i b,(Y i b).Nonempty)
    (γ : Law Ω) (a : Ω→ℙ K V) (b : Ω→ℙ K (Dual K V))
    (hinc : ∀z,0<γ z→Incident (a z) (b z))
    (c δ τ P : ℝ) (hδ : 0<δ) (j : Fin m.val) :
    mean (adaptiveLaw γ (fun _=>adaptiveLaw (originalLevelLaw μ ν)
      (fun _=>variableTreeLaw f r w))) (fun z=>
        if (a z.1,b z.1)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
          (variableTreeEncoded f r z.2.2 (Finset.univ,Finset.univ) m σ hσ hq hd
            (fun i=>X i (z.2.1.1 i)) (fun i=>Y i (z.2.1.2 i))
            (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
          ⟨j.val,lt_trans j.isLt m.isLt⟩ then 1 else 0)=
      orientedTargetFailure f r σ hσ hq hd μ ν X Y hX hY γ a b
        c δ τ P hδ (finiteBalanced m.val) ((finiteRankEquiv m.val).symm j) := by
  rw [orientedTargetFailure,eventMass_filter_mean,mean_adaptive,mean_adaptive]
  apply mean_congr_pos
  intro z hz
  rw [mean_adaptive,mean_adaptive]
  apply mean_congr
  intro lev
  have he : ∀t : VariableTreeTape f r w,
      ((a z,b z)∉variableTreeDomain f r t (Finset.univ,Finset.univ)
        (variableTreeEncoded f r t (Finset.univ,Finset.univ) m σ hσ hq hd
          (fun i=>X i (lev.1 i)) (fun i=>Y i (lev.2 i))
          (fun i=>hX i _) (fun i=>hY i _) c δ τ P hδ)
        ⟨j.val,lt_trans j.isLt m.isLt⟩) ↔
      ¬TargetCovered
        (orientedPivotContextAt f r σ hσ hq hd (fun i=>X i (lev.1 i))
          (fun i=>Y i (lev.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ (finiteBalanced m.val) (t m) (Finset.univ,Finset.univ)
          ((finiteRankEquiv m.val).symm j))
        (orientedPivotCapsAt f r σ hσ hq hd (fun i=>X i (lev.1 i))
          (fun i=>Y i (lev.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ (finiteBalanced m.val) (t m) (Finset.univ,Finset.univ)
          ((finiteRankEquiv m.val).symm j)) (a z) (b z) := by
    intro t
    rw [variableTreeDomain_coverage]
    simp only [hinc z hz,true_and]
  simp_rw [he]
  rw [←variableTreeLaw_eval f r w m,mean_map]
  congr 1
  funext t
  congr 1
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
