import Mathlib
import OAI.Probability.LogConcave.Sampling.CoordinateRank

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

inductive TensorExpression : ℕ → Type
  | jet (q : ℕ) : TensorExpression (q+2)
  | perm {n : ℕ} (e : Fin n ≃ Fin n) (A : TensorExpression n) : TensorExpression n
  | contract {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
      (A : TensorExpression (m+1)) (B : TensorExpression (n+1)) : TensorExpression (m+n)
  | adjoint {n : ℕ} (hn : 2≤n) (A : TensorExpression (n+1)) : TensorExpression n

namespace TensorExpression

def weight {n : ℕ} : TensorExpression n → ℕ
  | .jet q => q
  | .perm _ A => A.weight
  | .contract _ _ A B => A.weight+B.weight
  | .adjoint _ A => A.weight+1

def eval {d : ℕ} (base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ)
    (H : Point d → ℝ) {n : ℕ} : TensorExpression n → (Fin n → Fin d) → Point d → ℝ
  | .jet q,c => base q c
  | .perm e A,c => A.eval base H (c ∘ e)
  | .contract (m:=m) (n:=n) _ _ A B,c => fun y =>
      ∑z : Fin d,A.eval base H (Fin.snoc (fun i : Fin m => c (Fin.castAdd n i)) z) y*
        B.eval base H (Fin.snoc (fun i : Fin n => c (Fin.natAdd m i)) z) y
  | .adjoint _ A,c => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => A.eval base H (Fin.snoc c z))

lemma eval_polySmooth {d : ℕ} {base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ}
    {H : Point d → ℝ} (hbase : ∀q c,PolySmooth (base q c)) (hH : PolySmooth H)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) : PolySmooth (A.eval base H c) := by
  induction A with
  | jet q => exact hbase q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    exact PolySmooth.sum Finset.univ (fun z _ => (ihA _).mul (ihB _))
  | adjoint hn A ih => exact hH.tensorAdjoint (fun z => ih _) _

def physicalBase {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (q : ℕ) (c : Fin (q+2) → Fin d) (y : Point d) : ℝ :=
  normalizedTensor F x r ρ L y (fun i => decide (i=Fin.last (q+1))) (List.finRange (q+2)) c

lemma physicalBase_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q : ℕ) (c : Fin (q+2) → Fin d) : PolySmooth (physicalBase F x r ρ ((lam:ℝ)*r) q c) := by
  exact normalizedTensor_polySmooth hF x hr hlam hl hρ0 hρ1 _ _
    (List.nodup_finRange _) (by simp) (by simp) c

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

lemma physicalBase_eq_U {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) (y : Point d) :
    physicalBase F x r ρ L q c y=
      L⁻¹*conditionalU F x r ρ y (JetCalculus.spaceBasis d (c (Fin.last (q+1)))) L
        (fun j : Fin (q+1) => JetCalculus.spaceBasis d (c j.castSucc)) (List.finRange (q+1)) := by
  unfold physicalBase normalizedTensor conditionalU
  rw [List.finRange_succ_last,JetCalculus.jet_append,JetCalculus.jet_map]
  simp only [Fintype.card_fin,Nat.add_sub_cancel,List.length_finRange,Function.comp_def]
  have hv : (fun j : Fin (q+1) => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc))=
      fun j : Fin (q+1) => jointPosition d (JetCalculus.spaceBasis d (c j.castSucc)) := by
    funext j
    have he : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c j.castSucc=
        Sum.inl (c j.castSucc) := by simp [conditionalSlotEmbedding]
    rw [he]
    exact (jointPosition_basis _).symm
  rw [hv]
  have hf : conditionalSlotEmbedding d (fun i => decide (i=Fin.last (q+1))) c (Fin.last (q+1))=
      Sum.inr (c (Fin.last (q+1))) := by simp [conditionalSlotEmbedding]
  simp only [JetCalculus.jet,hf]
  rw [←jointField_basis]
  field_simp

def jointBase {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (q : ℕ) (c : Fin (q+2) → Fin d) (p : ℝ × Point d) : ℝ :=
  L⁻¹*jointU F x r L (fun j : Fin (q+1) => JetCalculus.spaceBasis d (c j.castSucc))
    (List.finRange (q+1)) (c (Fin.last (q+1))) p

lemma jointBase_slice {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (hL : L≠0) (q : ℕ) (c : Fin (q+2) → Fin d) :
    (fun y => jointBase F x r L q c (ρ,y))=physicalBase F x r ρ L q c := by
  funext y
  exact (physicalBase_eq_U F x r ρ L hL q c y).symm

lemma jointBase_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (q : ℕ) (c : Fin (q+2) → Fin d) :
    JetCalculus.TimeSmooth (jointBase F x r ((lam:ℝ)*r) q c) := by
  intro p h0 h1
  exact contDiffAt_const.mul (jointU_timeSmooth hF x hr hlam hl _ _
    (List.nodup_finRange _) _ p h0 h1)

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

def jointEval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {n : ℕ} : TensorExpression n → (Fin n → Fin d) → (ℝ × Point d) → ℝ
  | .jet q,c => jointBase F x r L q c
  | .perm e A,c => A.jointEval F x r L (c ∘ e)
  | .contract (m:=m) (n:=n) _ _ A B,c => fun p =>
      ∑z : Fin d,A.jointEval F x r L (Fin.snoc (fun i : Fin m => c (Fin.castAdd n i)) z) p*
        B.jointEval F x r L (Fin.snoc (fun i : Fin n => c (Fin.natAdd m i)) z) p
  | .adjoint _ A,c => JetCalculus.gadj jointSpace (jointScore F x r)
      (fun z => A.jointEval F x r L (Fin.snoc c z))

lemma jointEval_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) {n : ℕ} (A : TensorExpression n)
    (c : Fin n → Fin d) : JetCalculus.TimeSmooth (A.jointEval F x r ((lam:ℝ)*r) c) := by
  induction A with
  | jet q => exact jointBase_timeSmooth hF x hr hlam hl q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    intro p h0 h1
    exact ContDiffAt.sum (fun z _ => (ihA _ p h0 h1).mul (ihB _ p h0 h1))
  | adjoint hn A ih =>
    intro p h0 h1
    exact JetCalculus.smooth_gadj_at jointSpace (jointScore_smooth_at hF x hr.le hl (by nlinarith))
      (fun z => ih _ p h0 h1)

lemma jointEval_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {n : ℕ} (A : TensorExpression n) (c : Fin n → Fin d) :
    (fun y => A.jointEval F x r ((lam:ℝ)*r) c (ρ,y))=
      A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) c := by
  induction A with
  | jet q => exact jointBase_slice F x r ρ _ (by positivity) q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    funext y
    simp only [jointEval,eval]
    apply Finset.sum_congr rfl
    intro z _
    rw [congrFun (ihA _) y,congrFun (ihB _) y]
  | adjoint hn A ih =>
    funext y
    dsimp only [jointEval,eval]
    rw [joint_gadj_slice hF x hr.le hl hρ0 hρ1 (fun z =>
      (A.jointEval_timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp))]
    have he : (fun z y => A.jointEval F x r ((lam:ℝ)*r) (Fin.snoc c z) (ρ,y))=
        fun z => A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ) (Fin.snoc c z) := by
      funext z
      exact ih _
    rw [he]

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

structure TensorAtom (S : Type) where
  rank : ℕ
  expression : TensorExpression rank
  labels : Fin rank ≃ S

namespace TensorAtom

variable {S T : Type}

def eval {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) : ℝ × Point d → ℝ := A.expression.jointEval F x r L (c ∘ A.labels)

def relabel (A : TensorAtom S) (e : S ≃ T) : TensorAtom T :=
  ⟨A.rank,A.expression,A.labels.trans e⟩

lemma relabel_eval {d : ℕ} (A : TensorAtom S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

def reindex (A : TensorAtom S) {n : ℕ} (e : Fin n ≃ S) : TensorExpression n := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  exact .perm (eA.trans e.symm) A

lemma reindex_eval {d n : ℕ} (A : TensorAtom S) (e : Fin n ≃ S) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : Fin n → Fin d) :
    (A.reindex e).jointEval F x r L c=A.eval F x r L (c ∘ e.symm) := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  rfl

lemma reindex_weight (A : TensorAtom S) {n : ℕ} (e : Fin n ≃ S) :
    (A.reindex e).weight=A.expression.weight := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  rfl

def lastEquiv {n : ℕ} (e : Fin n ≃ S) : Fin (n+1) ≃ S ⊕ Unit :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr e (Equiv.ofUnique (Fin 1) Unit))

@[simp] lemma lastEquiv_castSucc {n : ℕ} (e : Fin n ≃ S) (j : Fin n) :
    lastEquiv e j.castSucc=Sum.inl (e j) := by simp [lastEquiv]

@[simp] lemma lastEquiv_last {n : ℕ} (e : Fin n ≃ S) :
    lastEquiv e (Fin.last n)=Sum.inr () := by simp [lastEquiv,Equiv.ofUnique]

lemma lastEquiv_snoc {d n : ℕ} (e : Fin n ≃ S) (c : S → Fin d) (k : Fin d) :
    (Fin.snoc (c ∘ e) k) ∘ (lastEquiv e).symm=Sum.elim c (fun _ => k) := by
  funext s
  apply Equiv.surjective (lastEquiv e) |>.forall.mpr ?_ s
  intro j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  induction j using Fin.lastCases <;> simp

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) : TensorAtom (S ⊕ T) :=
  let eS := (Fintype.equivFin S).symm
  let eT := (Fintype.equivFin T).symm
  ⟨Fintype.card S+Fintype.card T,
    .contract (Fintype.card_pos) (Fintype.card_pos) (A.reindex (lastEquiv eS)) (B.reindex (lastEquiv eT)),
    finSumFinEquiv.symm.trans (Equiv.sumCongr eS eT)⟩

lemma contract_weight [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) :
    (A.contract B).expression.weight=A.expression.weight+B.expression.weight := by
  simp only [contract,TensorExpression.weight,reindex_weight]

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑ k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p *
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  dsimp only [contract,eval,TensorExpression.jointEval]
  apply Finset.sum_congr rfl
  intro k _
  rw [reindex_eval,reindex_eval]
  congr 1
  · congr 1
    convert lastEquiv_snoc (Fintype.equivFin S).symm (fun s => c (Sum.inl s)) k using 1
    congr 1
    funext j
    simp [Function.comp_def]
  · congr 1
    convert lastEquiv_snoc (Fintype.equivFin T).symm (fun t => c (Sum.inr t)) k using 1
    congr 1
    funext j
    simp [Function.comp_def]

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit)) : TensorAtom S :=
  ⟨Fintype.card S,.adjoint hn (A.reindex (lastEquiv (Fintype.equivFin S).symm)),
    (Fintype.equivFin S).symm⟩

lemma adjoint_weight [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit)) :
    (A.adjoint hn).expression.weight=A.expression.weight+1 := by
  simp only [adjoint,TensorExpression.weight,reindex_weight]

lemma adjoint_eval {d : ℕ} [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) :
    (A.adjoint hn).eval F x r L c=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r L (Sum.elim c (fun _ => k))) := by
  dsimp only [adjoint,eval,TensorExpression.jointEval]
  congr 1
  funext k
  rw [reindex_eval,lastEquiv_snoc]
  rfl

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
