import Mathlib
import OAI.Probability.SKBarriers.Scalar.RankOneMatrix
import OAI.Probability.SKBarriers.Replicas.VectorBranch

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

def chainSum (l : List (ℝ × E)) : E := (l.map Prod.snd).sum

def chainPotentialPenalty (F : E → ℝ) : List (ℝ × E) → E → ℝ
  | [], _ => 0
  | p::l, Q => p.1*(F (Q+p.2)-F Q)+chainPotentialPenalty F l (Q+p.2)

@[simp] theorem chainSum_nil : chainSum ([] : List (ℝ × E))=0 := rfl
@[simp] theorem chainSum_cons (p : ℝ × E) (l : List (ℝ × E)) :
    chainSum (p::l)=p.2+chainSum l := rfl

theorem chainSum_append (l r : List (ℝ × E)) : chainSum (l++r)=chainSum l+chainSum r := by
  simp [chainSum,List.sum_append]

theorem chainPotentialPenalty_append (F : E → ℝ) (l r : List (ℝ × E)) (Q : E) :
    chainPotentialPenalty F (l++r) Q=chainPotentialPenalty F l Q+
      chainPotentialPenalty F r (Q+chainSum l) := by
  induction l generalizing Q with
  | nil => simp [chainPotentialPenalty]
  | cons p l ih => simp only [List.cons_append,chainPotentialPenalty,ih,chainSum_cons,add_assoc]

theorem chainSum_ofFn (n : ℕ) (p : Fin n → ℝ × E) : chainSum (List.ofFn p)=∑ i,(p i).2 := by
  simp [chainSum,List.map_ofFn,List.sum_ofFn,Function.comp_def]

def strictPrefix {n : ℕ} (v : Fin n → E) (i : Fin n) : E := ∑ j,if j < i then v j else 0

theorem strictPrefix_castSucc {n : ℕ} (v : Fin (n+1) → E) (i : Fin n) :
    strictPrefix v i.castSucc=strictPrefix (fun j => v j.castSucc) i := by
  simp [strictPrefix,Fin.sum_univ_castSucc,not_lt_of_ge (Fin.le_last i.castSucc)]

theorem strictPrefix_last (n : ℕ) (v : Fin (n+1) → E) :
    strictPrefix v (Fin.last n)=∑ j : Fin n,v j.castSucc := by
  simp [strictPrefix,Fin.sum_univ_castSucc]

theorem chainPotentialPenalty_ofFn (n : ℕ) (F : E → ℝ) (p : Fin n → ℝ × E) (Q : E) :
    chainPotentialPenalty F (List.ofFn p) Q=
      ∑ i,(p i).1*(F (Q+strictPrefix (fun j => (p j).2) i+(p i).2)-
        F (Q+strictPrefix (fun j => (p j).2) i)) := by
  induction n with
  | zero => simp [chainPotentialPenalty]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,chainPotentialPenalty_append,ih]
    simp only [chainPotentialPenalty,add_zero,chainSum_ofFn,Fin.sum_univ_castSucc,
      strictPrefix_castSucc,strictPrefix_last]
end Penalty

def rankOneMatrix {d : ℕ} (b : Fin d → ℝ) : Fin d → Fin d → ℝ := fun i j => b i*b j

def matrixChainCovariance {d : ℕ} (l : List (ℝ × (Fin d → ℝ))) : Fin d → Fin d → ℝ :=
  chainSum (l.map (fun p => (p.1,rankOneMatrix p.2)))

def matrixChainPenalty {d : ℕ} (l : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) : ℝ :=
  chainPotentialPenalty (matrixSquare d) (l.map (fun p => (p.1,rankOneMatrix p.2))) Q

theorem rankOnePath_cons_castSucc {n d : ℕ} (b : Fin n → Fin d → ℝ) (i : Fin n) :
    rankOnePath d (Fin.cons 0 b) i.castSucc=strictPrefix (fun j => rankOneMatrix (b j)) i := by
  funext u v
  simp only [rankOnePath,strictPrefix,Fin.sum_univ_succ,Fin.cons_zero,Pi.zero_apply,
    zero_mul,ite_self,zero_add,Fin.cons_succ,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have he : j.succ ≤ i.castSucc ↔ j < i := by exact Fin.succ_le_castSucc_iff
  simp only [he]
  split_ifs <;> rfl

theorem rankOnePath_cons_succ {n d : ℕ} (b : Fin n → Fin d → ℝ) (i : Fin n) :
    rankOnePath d (Fin.cons 0 b) i.succ=
      strictPrefix (fun j => rankOneMatrix (b j)) i+rankOneMatrix (b i) := by
  have H : rankOnePath d (Fin.cons 0 b) i.succ=
      rankOnePath d (Fin.cons 0 b) i.castSucc+rankOneMatrix (b i) := by
    funext u v
    let c : Fin (n+1) → Fin d → ℝ := Fin.cons 0 b
    have HH := finitePrefix_succ n (fun j => c j u*c j v) i
    simpa only [rankOnePath,finitePrefix,Pi.add_apply,rankOneMatrix,c,Fin.cons_succ] using HH
  rw [H,rankOnePath_cons_castSucc]

theorem rankOnePath_cons_last {n d : ℕ} (b : Fin n → Fin d → ℝ) :
    rankOnePath d (Fin.cons 0 b) (Fin.last n)=∑ i,rankOneMatrix (b i) := by
  funext u v
  simp only [rankOnePath,Fin.le_last,ite_true,Fin.sum_univ_succ,Fin.cons_zero,
    Pi.zero_apply,zero_mul,zero_add,Fin.cons_succ,Finset.sum_apply,rankOneMatrix]

theorem matrixConstrainedPressure_chain {N d : ℕ} (hN : 0<N) (β : ℝ)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (l : List (ℝ × (Fin d → ℝ))) (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1)
    (hmono : l.Pairwise (fun p q => p.1≤q.1)) :
    matrixConstrainedPressure N d β D ≤
      vectorIncrementChain (l.map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0+
      β^2/4*matrixSquare d (fun i j => D i j-matrixChainCovariance l i j)-
      β^2/4*matrixChainPenalty l 0 := by
  let m : Fin (l.length+1) → ℝ := Fin.cons 0 (fun i => (l.get i).1)
  let b : Fin (l.length+1) → Fin d → ℝ := Fin.cons 0 (fun i => (l.get i).2)
  have hm' : ∀ i,m i∈Icc (0:ℝ) 1 := by
    intro i
    refine Fin.cases (by norm_num [m]) (fun j => ?_) i
    exact hm _ (List.get_mem l j)
  have hs : Monotone m := by
    have H : ((0,0)::l).Pairwise (fun p q => p.1≤q.1) :=
      List.pairwise_cons.mpr ⟨fun p hp => (hm p hp).1,hmono⟩
    have HL : List.ofFn (Fin.cons (0,0) l.get)=(0,0)::l := by simp [List.ofFn_succ]
    rw [← HL,List.pairwise_ofFn] at H
    intro i j hij
    rcases lt_or_eq_of_le hij with hij|rfl
    · have hh := H hij
      have he (a : Fin (l.length+1)) : m a=((Fin.cons (0,0) l.get : Fin (l.length+1) → ℝ × (Fin d → ℝ)) a).1 := by
        refine Fin.cases rfl (fun _ => rfl) a
      simpa only [← he] using hh
    · exact le_rfl
  have H := matrixConstrainedPressure_rankOne hN β D hD m rfl hm' hs b
  have hv : vectorHierarchy (l.length+1) m (fun i => β • b i)
      (fun x => ∑ u,scalarSpinTerminal (x u))=
      vectorIncrementChain (l.map (fun p => (p.1,β • p.2))) (fun x => ∑ u,scalarSpinTerminal (x u)) := by
    rw [← vectorIncrementChain_ofFn]
    have he : (fun i => (m i,β • b i))=Fin.cons (0,0) (fun i => ((l.get i).1,β • (l.get i).2)) := by
      funext i; refine Fin.cases ?_ (fun _ => rfl) i
      simp [m,b]
    rw [he,List.ofFn_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,vectorIncrementChain,vectorStep_zero]
    congr 1
    simpa only [List.ofFn_get,Function.comp_def] using (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,β • p.2))).symm
  have hc : rankOnePath d b (Fin.last l.length)=matrixChainCovariance l := by
    rw [rankOnePath_cons_last]
    unfold matrixChainCovariance
    have he : l.map (fun p => (p.1,rankOneMatrix p.2))=
        List.ofFn (fun i => ((l.get i).1,rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get,Function.comp_def] using
        (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,rankOneMatrix p.2)))
    rw [he,chainSum_ofFn]
  have hp : (∑ i : Fin l.length,m i.succ*(matrixSquare d (rankOnePath d b i.succ)-
      matrixSquare d (rankOnePath d b i.castSucc)))=matrixChainPenalty l 0 := by
    unfold matrixChainPenalty
    have he : l.map (fun p => (p.1,rankOneMatrix p.2))=
        List.ofFn (fun i => ((l.get i).1,rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get,Function.comp_def] using
        (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,rankOneMatrix p.2)))
    rw [he,chainPotentialPenalty_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [m,Fin.cons_succ,b,rankOnePath_cons_succ,rankOnePath_cons_castSucc,zero_add]
  rw [hv,hc,hp] at H
  exact H

end SK.Analytic

end
end

end OAI
