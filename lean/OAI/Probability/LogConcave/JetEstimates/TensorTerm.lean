import Mathlib
import OAI.Probability.LogConcave.JetEstimates.SplitIndex

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

lemma polynomialTime_smooth {d : ℕ} (P : Polynomial ℝ) :
    ContDiff ℝ (⊤:ℕ∞) (fun p : ℝ × Point d => P.eval p.1) := by
  have hP : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => P.eval t) := by
    simpa using P.contDiff_aeval (𝕜:=ℝ) (⊤:ℕ∞)
  exact hP.comp contDiff_fst

structure TensorTerm (S : Type) where
  power : ℕ
  coefficient : Polynomial ℝ
  atom : TensorAtom S

namespace TensorTerm
variable {S T : Type}

def eval {d : ℕ} (A : TensorTerm S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) : ℝ :=
  (r*L)^A.power*A.coefficient.eval p.1*A.atom.eval F x r L c p

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorTerm S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact (contDiffAt_const.mul ((polynomialTime_smooth A.coefficient).contDiffAt)).mul
    (A.atom.expression.jointEval_timeSmooth hF x hr hlam hl _ p h0 h1)

def relabel (A : TensorTerm S) (e : S ≃ T) : TensorTerm T :=
  ⟨A.power,A.coefficient,A.atom.relabel e⟩

lemma relabel_eval {d : ℕ} (A : TensorTerm S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

def scale (A : TensorTerm S) (n : ℕ) (P : Polynomial ℝ) : TensorTerm S :=
  ⟨n+A.power,P*A.coefficient,A.atom⟩

lemma scale_eval {d : ℕ} (A : TensorTerm S) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (A.scale n P).eval F x r L c p=(r*L)^n*P.eval p.1*A.eval F x r L c p := by
  simp only [scale,eval,pow_add,Polynomial.eval_mul]
  ring

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorTerm (S ⊕ Unit)) : TensorTerm S :=
  ⟨A.power,A.coefficient,A.atom.adjoint hn⟩

lemma adjoint_eval {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    [Fintype S] (hn : 2≤Fintype.card S) (A : TensorTerm (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.adjoint hn).eval F x r ((lam:ℝ)*r) c (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) := by
  have hA (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞)
      (A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) :=
    A.atom.expression.jointEval_timeSmooth hF x hr hlam hl
    ((Sum.elim c (fun _ => k)) ∘ A.atom.labels) (ρ,y) (by dsimp; linarith) hρ1
  unfold eval adjoint
  rw [TensorAtom.adjoint_eval]
  have he : (fun k p => (r*((lam:ℝ)*r))^A.power*A.coefficient.eval p.1*
      A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p)=
      fun k p => (r*((lam:ℝ)*r))^A.power*(A.coefficient.eval p.1*
        A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p) := by
    funext k p; ring
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    (((polynomialTime_smooth A.coefficient).contDiffAt).mul (hA k)).differentiableAt (by simp)),
    JetCalculus.gadj_time_at _ _ (fun k => (hA k).differentiableAt (by simp))]
  ring

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorTerm (S ⊕ Unit)) (B : TensorTerm (T ⊕ Unit)) : TensorTerm (S ⊕ T) :=
  ⟨A.power+B.power,A.coefficient*B.coefficient,A.atom.contract B.atom⟩

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorTerm (S ⊕ Unit)) (B : TensorTerm (T ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  simp only [contract,eval,TensorAtom.contract_eval,pow_add,Polynomial.eval_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end TensorTerm

structure TensorSum (S : Type) where
  index : Type
  finite : Fintype index
  term : index → TensorTerm S

namespace TensorSum
variable {S T : Type}
instance (A : TensorSum S) : Fintype A.index := A.finite

def eval {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) : ℝ := ∑i,(A.term i).eval F x r L c p

def weightLE (A : TensorSum S) (w : ℕ) : Prop := ∀i,(A.term i).atom.expression.weight≤w

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorSum S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact ContDiffAt.sum (fun i _ => (A.term i).timeSmooth hF x hr hlam hl c p h0 h1)

def pure (A : TensorAtom S) : TensorSum S := ⟨Unit,inferInstance,fun _ => ⟨0,1,A⟩⟩
lemma pure_eval {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) : (pure A).eval F x r L c=A.eval F x r L c := by
  funext p
  change (∑ _ : Unit, (r*L)^0*(1 : Polynomial ℝ).eval p.1*A.eval F x r L c p)=_
  simp

def add (A B : TensorSum S) : TensorSum S := ⟨A.index ⊕ B.index,inferInstance,Sum.elim A.term B.term⟩
lemma add_eval {d : ℕ} (A B : TensorSum S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) :
    (A.add B).eval F x r L c p=A.eval F x r L c p+B.eval F x r L c p := by
  change (∑ i : A.index ⊕ B.index, (Sum.elim A.term B.term i).eval F x r L c p)=_
  rw [Fintype.sum_sum_type]
  rfl

def relabel (A : TensorSum S) (e : S ≃ T) : TensorSum T :=
  ⟨A.index,A.finite,fun i => (A.term i).relabel e⟩
lemma relabel_eval {d : ℕ} (A : TensorSum S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

def scale (A : TensorSum S) (n : ℕ) (P : Polynomial ℝ) : TensorSum S :=
  ⟨A.index,A.finite,fun i => (A.term i).scale n P⟩
lemma scale_eval {d : ℕ} (A : TensorSum S) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (A.scale n P).eval F x r L c p=(r*L)^n*P.eval p.1*A.eval F x r L c p := by
  simp only [scale,eval,TensorTerm.scale_eval,Finset.mul_sum]
  rfl

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorSum (S ⊕ Unit)) : TensorSum S :=
  ⟨A.index,A.finite,fun i => (A.term i).adjoint hn⟩

lemma adjoint_eval {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    [Fintype S] (hn : 2≤Fintype.card S) (A : TensorSum (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.adjoint hn).eval F x r ((lam:ℝ)*r) c (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) := by
  unfold eval adjoint
  simp_rw [TensorTerm.adjoint_eval hF x hr hlam hl hρ0 hρ1]
  symm
  apply JetCalculus.gadj_sum_at
  intro i _ k
  exact ((A.term i).timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorSum (S ⊕ Unit)) (B : TensorSum (T ⊕ Unit)) : TensorSum (S ⊕ T) :=
  ⟨A.index × B.index,inferInstance,fun i => (A.term i.1).contract (B.term i.2)⟩

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorSum (S ⊕ Unit)) (B : TensorSum (T ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  change (∑ i : A.index × B.index, ((A.term i.1).contract (B.term i.2)).eval F x r L c p)=_
  simp only [TensorTerm.contract_eval,Fintype.sum_prod_type,eval,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

lemma jointMean_direction {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) (i k : Fin d) :
    JetCalculus.dir (jointSpace i) (jointMean F x r k) (ρ,y)=
      ρ*jointU F x r ((lam:ℝ)*r) (fun _ : Unit => JetCalculus.spaceBasis d i) [()] k (ρ,y) := by
  have hm := jointMean_timeSmooth hF x hr.le hl k (ρ,y) (by dsimp; linarith) hρ1
  change JetCalculus.dir (0,JetCalculus.spaceBasis d i) (jointMean F x r k) (ρ,y)=_
  rw [←JetCalculus.dir_right_slice_at (hm.differentiableAt (by simp))]
  have hh := congrFun (mean_jet_eq_scaled_U hF x hr hlam hl hρ0 hρ1
    (fun _ : Unit => JetCalculus.spaceBasis d i) [()] k) y
  simpa only [JetCalculus.jet,List.length_cons,List.length_nil,zero_add,pow_one,jointU] using hh

namespace TensorAtom

def one : TensorAtom (Unit ⊕ Unit) :=
  (jetList [()] (by simp) (by intro s; cases s; simp) (by simp)).relabel (Equiv.sumComm Unit Unit)

lemma one_weight : one.expression.weight=0 := rfl

lemma one_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Unit ⊕ Unit → Fin d) :
    one.eval F x r L c=fun p => L⁻¹*jointU F x r L
      (fun _ : Unit => JetCalculus.spaceBasis d (c (Sum.inr ()))) [()] (c (Sum.inl ())) p := by
  rw [one,relabel_eval,jetList_eval]
  rfl

variable {S : Type} [Fintype S] [Nonempty S]

def insertOne (A : TensorAtom (S ⊕ Unit)) : TensorAtom (S ⊕ Unit) :=
  (one.contract A).relabel (Equiv.sumComm Unit S)

lemma insertOne_weight (A : TensorAtom (S ⊕ Unit)) :
    (A.insertOne).expression.weight=A.expression.weight := by
  simp only [insertOne,relabel,contract_weight,one_weight,zero_add]

lemma insertOne_eval {d : ℕ} (A : TensorAtom (S ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    A.insertOne.eval F x r L c p=∑i : Fin d,
      (L⁻¹*jointU F x r L (fun _ : Unit => JetCalculus.spaceBasis d i) [()] (c (Sum.inr ())) p)*
      A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) p := by
  rw [insertOne,relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_eval]
  rfl

lemma insertOne_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (A : TensorAtom (S ⊕ Unit)) (c : S ⊕ Unit → Fin d) (y : Point d) :
    ∑i : Fin d,JetCalculus.dir (jointSpace i) (jointMean F x r (c (Sum.inr ()))) (ρ,y)*
      A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) (ρ,y)=
      ((lam:ℝ)*r)*ρ*A.insertOne.eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  rw [insertOne_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointMean_direction hF x hr hlam hl hρ0 hρ1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  field_simp

end TensorAtom

namespace JetCalculus
lemma gadj_slice_congr_at {d : ℕ} (s : Fin d → ℝ × Point d → ℝ)
    {V W : Fin d → ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) (ρ,y)) (hW : ∀i,DifferentiableAt ℝ (W i) (ρ,y))
    (he : ∀i z,V i (ρ,z)=W i (ρ,z)) : gadj jointSpace s V (ρ,y)=gadj jointSpace s W (ρ,y) := by
  unfold gadj cadj
  apply Finset.sum_congr rfl
  intro i _
  change -dir (0,spaceBasis d i) (V i) (ρ,y)+_ = -dir (0,spaceBasis d i) (W i) (ρ,y)+_
  rw [←dir_right_slice_at (hV i),←dir_right_slice_at (hW i),show (fun z => V i (ρ,z))=(fun z => W i (ρ,z)) from funext (he i),he i y]
end JetCalculus
end LogConcaveSampling

end

end

end

end OAI
