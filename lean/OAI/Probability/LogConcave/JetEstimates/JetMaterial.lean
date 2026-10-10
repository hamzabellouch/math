import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Material

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S T : Type}

@[simp] lemma lastEquiv_symm_inl {n : ℕ} (e : Fin n ≃ S) (s : S) :
    (lastEquiv e).symm (Sum.inl s)=(e.symm s).castSucc := by
  apply (lastEquiv e).injective
  simp
@[simp] lemma lastEquiv_symm_inr {n : ℕ} (e : Fin n ≃ S) (s : Unit) :
    (lastEquiv e).symm (Sum.inr s)=Fin.last n := by
  cases s
  apply (lastEquiv e).injective
  simp

lemma HasMaterial.congr {A A' : TensorAtom S} {B : TensorSum S}
    (h : A.HasMaterial B)
    (he : ∀{d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d),
      A'.eval F x r L c=A.eval F x r L c) : A'.HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [he]
  exact h hF x hr hlam hl h0 h1 c y

variable [Fintype S]
def jetMaterial (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) : TensorSum (S ⊕ Unit) :=
  (TensorSum.pure ((extendedU l hN hall).adjoint (jetCard l hN hall hne))).add
    ⟨SplitIndex l,inferInstance,fun a => ⟨1,Polynomial.C 2*Polynomial.X,splitAtom l hN hall a⟩⟩

lemma jetMaterial_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetMaterial l hN hall hne).weightLE ((jetList l hN hall hne).expression.weight+2) := by
  apply TensorSum.weightLE_add
  · apply TensorSum.weightLE_pure
    rw [adjoint_weight,extendedU_weight,jetList_weight]
    have := List.length_pos_iff.mpr hne
    omega
  · intro a
    change (splitAtom l hN hall a).expression.weight≤_
    rw [splitAtom_weight,jetList_weight]
    omega

lemma hasMaterial_jetList (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetList l hN hall hne).HasMaterial (jetMaterial l hN hall hne) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [material_jetList hF x hr hlam hl h0 h1]
  unfold jetMaterial
  rw [TensorSum.add_eval,TensorSum.pure_eval]
  congr 1
  change 2*(r*((lam:ℝ)*r))*ρ*(∑a : SplitIndex l,(splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y))=
    ∑a : SplitIndex l,(r*((lam:ℝ)*r))^1*(Polynomial.C (2:ℝ)*Polynomial.X).eval ρ*
      (splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,pow_one]
  ring
end TensorAtom

namespace TensorExpression

def atom {n : ℕ} (A : TensorExpression n) : TensorAtom (Fin n) := ⟨n,A,Equiv.refl _⟩
lemma atom_eval {d n : ℕ} (A : TensorExpression n) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Fin n → Fin d) : A.atom.eval F x r L c=A.jointEval F x r L c := rfl
@[simp] lemma atom_weight {n : ℕ} (A : TensorExpression n) : A.atom.expression.weight=A.weight := rfl

lemma jet_atom_eval {d : ℕ} (q : ℕ) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Fin (q+2) → Fin d) :
    (jet q).atom.eval F x r L c=
      ((TensorAtom.jetList (List.finRange (q+1)) (List.nodup_finRange _) (by simp) (by simp)).relabel (TensorAtom.lastEquiv (Equiv.refl (Fin (q+1)))).symm).eval F x r L c := by
  rw [TensorAtom.relabel_eval,TensorAtom.jetList_eval]
  change (fun p => L⁻¹*jointU F x r L _ _ _ p)=_
  simp only [Function.comp_apply,TensorAtom.lastEquiv_symm_inl,TensorAtom.lastEquiv_symm_inr,Equiv.refl_symm,Equiv.refl_apply]
  rfl

lemma jet_hasMaterial (q : ℕ) : ∃B : TensorSum (Fin (q+2)),
    B.weightLE (q+2) ∧ (jet q).atom.HasMaterial B := by
  let l := List.finRange (q+1)
  let hN : l.Nodup := List.nodup_finRange _
  let hall : ∀s,s∈l := by simp [l]
  let hne : l≠[] := by simp [l]
  let e := (TensorAtom.lastEquiv (Equiv.refl (Fin (q+1)))).symm
  refine ⟨(TensorAtom.jetMaterial l hN hall hne).relabel e,?_,?_⟩
  · have h := TensorSum.weightLE_relabel (TensorAtom.jetMaterial_weight l hN hall hne) e
    simpa only [TensorAtom.jetList_weight,l,List.length_finRange,Nat.add_sub_cancel] using h
  · exact TensorAtom.HasMaterial.congr
      (TensorAtom.HasMaterial.relabel (TensorAtom.hasMaterial_jetList l hN hall hne) e) (jet_atom_eval q)
end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorExpression

lemma atom_contract_eval {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    [Nonempty (Fin m)] [Nonempty (Fin n)] (A : TensorExpression (m+1)) (B : TensorExpression (n+1))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : Fin (m+n) → Fin d) :
    (TensorExpression.contract hm hn A B).atom.eval F x r L c=
      (((A.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin m)))).contract
        (B.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin n))))).relabel finSumFinEquiv).eval F x r L c := by
  rw [TensorAtom.relabel_eval]
  funext p
  rw [TensorAtom.contract_eval]
  change (∑k : Fin d,A.jointEval F x r L _ p*B.jointEval F x r L _ p)=_
  apply Finset.sum_congr rfl
  intro k _
  simp only [TensorAtom.relabel_eval,atom_eval]
  congr 2
  · funext j
    induction j using Fin.lastCases <;> simp [TensorExpression.atom]
    rfl
  · funext j
    induction j using Fin.lastCases <;> simp [TensorExpression.atom]
    rfl

lemma atom_adjoint_eval {d n : ℕ} (hn : 2≤n) (A : TensorExpression (n+1))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : Fin n → Fin d) :
    (TensorExpression.adjoint hn A).atom.eval F x r L c=
      ((A.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin n)))).adjoint
        (by simpa using hn)).eval F x r L c := by
  rw [TensorAtom.adjoint_eval]
  change JetCalculus.gadj jointSpace (jointScore F x r) (fun k => A.jointEval F x r L (Fin.snoc c k))=_
  congr 1
  funext k
  rw [TensorAtom.relabel_eval,atom_eval]
  congr 1
  funext j
  induction j using Fin.lastCases <;> simp

theorem hasMaterial {n : ℕ} (A : TensorExpression n) :
    ∃B : TensorSum (Fin n), B.weightLE (A.weight+2) ∧ A.atom.HasMaterial B := by
  induction A with
  | jet q => exact jet_hasMaterial q
  | perm e A ih =>
    obtain ⟨B,hB,h⟩ := ih
    refine ⟨B.relabel e,TensorSum.weightLE_relabel hB e,?_⟩
    apply TensorAtom.HasMaterial.congr (TensorAtom.HasMaterial.relabel h e)
    intros
    rfl
  | @contract m n hm hn A B ihA ihB =>
    let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    obtain ⟨DA,hDA,hA⟩ := ihA
    obtain ⟨DB,hDB,hB⟩ := ihB
    let eA := TensorAtom.lastEquiv (Equiv.refl (Fin m))
    let eB := TensorAtom.lastEquiv (Equiv.refl (Fin n))
    let AA := A.atom.relabel eA
    let BB := B.atom.relabel eB
    let RA := DA.relabel eA
    let RB := DB.relabel eB
    let D := (RA.contract (TensorSum.pure BB)).add ((TensorSum.pure AA).contract RB)
    refine ⟨D.relabel finSumFinEquiv,?_,?_⟩
    · apply TensorSum.weightLE_relabel
      apply TensorSum.weightLE_add
      · have hh := TensorSum.weightLE_contract (TensorSum.weightLE_relabel hDA eA)
          (TensorSum.weightLE_pure BB (Nat.le_refl BB.expression.weight))
        convert hh using 1
        simp only [BB,TensorAtom.relabel,atom_weight,weight]
        omega
      · have hh := TensorSum.weightLE_contract (TensorSum.weightLE_pure AA (Nat.le_refl AA.expression.weight))
          (TensorSum.weightLE_relabel hDB eB)
        convert hh using 1
        simp only [AA,TensorAtom.relabel,atom_weight,weight]
        omega
    · exact TensorAtom.HasMaterial.congr
        (TensorAtom.HasMaterial.relabel
          (TensorAtom.HasMaterial.contract (TensorAtom.HasMaterial.relabel hA eA)
            (TensorAtom.HasMaterial.relabel hB eB)) finSumFinEquiv)
        (atom_contract_eval hm hn A B)
  | @adjoint n hn A ih =>
    let : NeZero n := ⟨by omega⟩
    obtain ⟨DA,hDA,hA⟩ := ih
    let e := TensorAtom.lastEquiv (Equiv.refl (Fin n))
    let AA := A.atom.relabel e
    let hcard : 2≤Fintype.card (Fin n) := by simpa using hn
    refine ⟨((DA.relabel e).adjoint hcard).add
      ((TensorSum.pure (AA.insertOne.adjoint hcard)).scale 1 Polynomial.X),?_,?_⟩
    · apply TensorSum.weightLE_add
      · simpa only [weight,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          TensorSum.weightLE_adjoint hcard (TensorSum.weightLE_relabel hDA e)
      · apply TensorSum.weightLE_scale
        apply TensorSum.weightLE_pure
        rw [TensorAtom.adjoint_weight,TensorAtom.insertOne_weight]
        change A.weight+1≤A.weight+1+2
        omega
    · exact TensorAtom.HasMaterial.congr
        (TensorAtom.HasMaterial.adjoint hcard (TensorAtom.HasMaterial.relabel hA e))
        (atom_adjoint_eval hn A)
end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S : Type}
theorem hasMaterial (A : TensorAtom S) : ∃B : TensorSum S,
    B.weightLE (A.expression.weight+2) ∧ A.HasMaterial B := by
  obtain ⟨B,hB,h⟩ := A.expression.hasMaterial
  refine ⟨B.relabel A.labels,TensorSum.weightLE_relabel hB A.labels,?_⟩
  exact TensorAtom.HasMaterial.congr (TensorAtom.HasMaterial.relabel h A.labels) (by intros; rfl)
end TensorAtom

namespace TensorSum
variable {S : Type}

def combine {I : Type} [Fintype I] (f : I → TensorSum S) : TensorSum S :=
  ⟨(i : I) × (f i).index,inferInstance,fun a => (f a.1).term a.2⟩

lemma combine_eval {I : Type} [Fintype I] (f : I → TensorSum S) {d : ℕ}
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (combine f).eval F x r L c p=∑i,(f i).eval F x r L c p := by
  change (∑a : (i : I) × (f i).index,((f a.1).term a.2).eval F x r L c p)=_
  rw [Fintype.sum_sigma]
  rfl
lemma weightLE_combine {I : Type} [Fintype I] {f : I → TensorSum S} {w : ℕ}
    (h : ∀i,(f i).weightLE w) : (combine f).weightLE w := fun a => h a.1 a.2

def HasMaterial (A B : TensorSum S) : Prop :=
  ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
    ∀(x : Point d) {r ρ : ℝ}, 0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
      ∀(c : S → Fin d) (y : Point d),
        JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
          (A.eval F x r ((lam:ℝ)*r) c) (ρ,y)=B.eval F x r ((lam:ℝ)*r) c (ρ,y)

lemma HasMaterial.pure {A : TensorAtom S} {B : TensorSum S} (h : A.HasMaterial B) :
    (pure A).HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [pure_eval]
  exact h hF x hr hlam hl h0 h1 c y

lemma HasMaterial.scale {A B : TensorSum S} (h : A.HasMaterial B) (n : ℕ) (P : Polynomial ℝ) :
    (A.scale n P).HasMaterial ((A.scale n P.derivative).add (B.scale n P)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have hS := A.timeSmooth hF x hr hlam hl c (ρ,y) (by dsimp; linarith) h1
  have hP := (polynomialTime_smooth (d:=d) P).contDiffAt (x:=(ρ,y))
  have he : (A.scale n P).eval F x r ((lam:ℝ)*r) c=fun p =>
      (r*((lam:ℝ)*r))^n*(P.eval p.1*A.eval F x r ((lam:ℝ)*r) c p) := by
    funext p
    rw [scale_eval]
    ring
  rw [he,JetCalculus.mdir_const_mul_at _ _ _ _ ((hP.mul hS).differentiableAt (by simp)),
    JetCalculus.mdir_mul_at _ _ _ _ (hP.differentiableAt (by simp)) (hS.differentiableAt (by simp)),
    JetCalculus.mdir_time,h hF x hr hlam hl h0 h1,add_eval,scale_eval,scale_eval]
  ring

lemma HasMaterial.combine {I : Type} [Fintype I] {f g : I → TensorSum S}
    (h : ∀i,(f i).HasMaterial (g i)) : (combine f).HasMaterial (combine g) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have he : (TensorSum.combine f).eval F x r ((lam:ℝ)*r) c=fun p => ∑i,(f i).eval F x r ((lam:ℝ)*r) c p :=
    funext (fun p => combine_eval f F x r ((lam:ℝ)*r) c p)
  rw [he,JetCalculus.mdir_sum_at Finset.univ _ _ _ _ (fun i _ =>
    ((f i).timeSmooth hF x hr hlam hl c (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp)),TensorSum.combine_eval]
  apply Finset.sum_congr rfl
  intro i _
  exact h i hF x hr hlam hl h0 h1 c y

lemma HasMaterial.congr {A A' B : TensorSum S} (h : A.HasMaterial B)
    (he : ∀{d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d),
      A'.eval F x r L c=A.eval F x r L c) : A'.HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [he]
  exact h hF x hr hlam hl h0 h1 c y

theorem hasMaterial (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    ∃B : TensorSum S,B.weightLE (w+2) ∧ A.HasMaterial B := by
  have hf (i : A.index) := (A.term i).atom.hasMaterial
  choose B hB h using hf
  let f : A.index → TensorSum S := fun i => (pure (A.term i).atom).scale (A.term i).power (A.term i).coefficient
  let g : A.index → TensorSum S := fun i =>
    ((pure (A.term i).atom).scale (A.term i).power (A.term i).coefficient.derivative).add
      ((B i).scale (A.term i).power (A.term i).coefficient)
  refine ⟨combine g,?_,?_⟩
  · apply weightLE_combine
    intro i
    apply weightLE_add
    · exact weightLE_scale (weightLE_pure _ ((hw i).trans (by omega))) _ _
    · exact weightLE_scale (weightLE_mono (hB i) (Nat.add_le_add_right (hw i) 2)) _ _
  · have hh : (combine f).HasMaterial (combine g) := HasMaterial.combine (fun i =>
      HasMaterial.scale (HasMaterial.pure (h i)) _ _)
    apply hh.congr
    intro d F x r L c
    funext p
    rw [combine_eval]
    change (∑i,(A.term i).eval F x r L c p)=∑i,(f i).eval F x r L c p
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [scale_eval,pure_eval]
    rfl
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma dir_congr_nonneg_time {f g : ℝ × E → ℝ} (hf : TimeSmooth f) (hg : TimeSmooth g)
    (he : ∀{t : ℝ},0≤t → t<1 → ∀z,f (t,z)=g (t,z))
    {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ<1) (v : ℝ × E) (y : E) : dir v f (ρ,y)=dir v g (ρ,y) := by
  have hp {t : ℝ} (ht0 : 0<t) (ht1 : t<1) (z : E) : dir v f (t,z)=dir v g (t,z) := by
    have hh : f=ᶠ[nhds (t,z)]g := by
      have ha := (continuousAt_fst (p:=(t,z))).eventually (Ioo_mem_nhds ht0 ht1)
      filter_upwards [ha] with p hp
      exact he hp.1.le hp.2 p.2
    exact (dir_eventuallyEq hh v).eq_of_nhds
  rcases h0.eq_or_lt with hzero | hpos
  · subst ρ
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 := continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (f:=fun t => dir v f (t,y)) (g:=fun t => dir v g (t,y))
      ((smooth_dir_at (hf (0,y) (by norm_num) (by norm_num)) v).continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      ((smooth_dir_at (hg (0,y) (by norm_num) (by norm_num)) v).continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (fun t ht0 ht1 => hp ht0 ht1 y)
  · exact hp hpos h1 y

lemma mdir_congr_nonneg_time (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {f g : ℝ × E → ℝ} (hf : TimeSmooth f) (hg : TimeSmooth g)
    (he : ∀{t : ℝ},0≤t → t<1 → ∀z,f (t,z)=g (t,z))
    {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ<1) (y : E) : mdir w b r M f (ρ,y)=mdir w b r M g (ρ,y) := by
  unfold mdir
  rw [dir_congr_nonneg_time hf hg he h0 h1]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [dir_congr_nonneg_time hf hg he h0 h1]

def materialIter (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ) : ℕ → (E → ℝ) → E → ℝ
  | 0,f => f
  | n+1,f => mdir w b r M (materialIter w b r M n f)

lemma materialIter_timeSmooth (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ)
    {M : ι → ℝ × E → ℝ} (hM : ∀i,TimeSmooth (M i)) {f : ℝ × E → ℝ}
    (hf : TimeSmooth f) (n : ℕ) : TimeSmooth (materialIter w b r M n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro p h0 h1
    exact smooth_mdir_at w b r (fun i => hM i p h0 h1) (ih p h0 h1)
end JetCalculus

namespace TensorSum
variable {S : Type}

def RepresentsMaterial (A : TensorSum S) (n : ℕ) (B : TensorSum S) : Prop :=
  ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
    ∀(x : Point d) {r ρ : ℝ}, 0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
      ∀(c : S → Fin d) (y : Point d),
        JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
          (A.eval F x r ((lam:ℝ)*r) c) (ρ,y)=B.eval F x r ((lam:ℝ)*r) c (ρ,y)

theorem representsMaterial (A : TensorSum S) {w : ℕ} (hA : A.weightLE w) (n : ℕ) :
    ∃B : TensorSum S,B.weightLE (w+2*n) ∧ A.RepresentsMaterial n B := by
  induction n with
  | zero =>
    refine ⟨A,by simpa using hA,?_⟩
    intro d F lam hF x r ρ hr hlam hl h0 h1 c y
    rfl
  | succ n ih =>
    obtain ⟨B,hB,he⟩ := ih
    obtain ⟨C,hC,hD⟩ := B.hasMaterial hB
    refine ⟨C,by convert hC using 1,?_⟩
    intro d F lam hF x r ρ hr hlam hl h0 h1 c y
    change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n (A.eval F x r ((lam:ℝ)*r) c)) (ρ,y)=_
    rw [JetCalculus.mdir_congr_nonneg_time (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.materialIter_timeSmooth _ _ _ (fun i => jointMean_timeSmooth hF x hr.le hl i)
        (A.timeSmooth hF x hr hlam hl c) n) (B.timeSmooth hF x hr hlam hl c)
        (fun ht0 ht1 z => he hF x hr hlam hl ht0 ht1 c z) h0 h1 y]
    exact hD hF x hr hlam hl h0 h1 c y
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
lemma gadj_add_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : ι → E) (s : ι → E → ℝ) {V W : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) (hW : ∀i,DifferentiableAt ℝ (W i) p) :
    gadj b s (fun i y => V i y+W i y) p=gadj b s V p+gadj b s W p := by
  unfold gadj cadj
  simp_rw [dir_add_at (hV _) (hW _)]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
end JetCalculus

namespace TensorSum
variable {S : Type} [Fintype S] [Nonempty S]

def insertOne (A : TensorSum (S ⊕ Unit)) : TensorSum (S ⊕ Unit) :=
  ((pure TensorAtom.one).contract A).relabel (Equiv.sumComm Unit S)

lemma weightLE_insertOne {A : TensorSum (S ⊕ Unit)} {w : ℕ} (hw : A.weightLE w) :
    A.insertOne.weightLE w := by
  unfold insertOne
  apply weightLE_relabel
  simpa only [zero_add] using weightLE_contract (weightLE_pure TensorAtom.one (by rfl : _≤0)) hw

lemma insertOne_eval {d : ℕ} (A : TensorSum (S ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    A.insertOne.eval F x r L c p=∑i : Fin d,
      (L⁻¹*jointU F x r L (fun _ : Unit => JetCalculus.spaceBasis d i) [()] (c (Sum.inr ())) p)*
      A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) p := by
  rw [insertOne,relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [pure_eval,TensorAtom.one_eval]
  rfl

lemma insertOne_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (S ⊕ Unit)) (c : S ⊕ Unit → Fin d) (y : Point d) :
    ∑i : Fin d,JetCalculus.dir (jointSpace i) (jointMean F x r (c (Sum.inr ()))) (ρ,y)*
      A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) (ρ,y)=
      ((lam:ℝ)*r)*ρ*A.insertOne.eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  rw [insertOne_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointMean_direction hF x hr hlam hl h0 h1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  field_simp

def outer {d : ℕ} (A : TensorSum (S ⊕ Unit)) (F : Point d → ℝ) (x : Point d)
    (r L : ℝ) (c : S → Fin d) : ℝ × Point d → ℝ :=
  JetCalculus.gadj jointSpace (jointScore F x r)
    (fun k => A.eval F x r L (Sum.elim c (fun _ => k)))

omit [Fintype S] [Nonempty S] in
lemma outer_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2)
    (A : TensorSum (S ⊕ Unit)) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.outer F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact JetCalculus.smooth_gadj_at _ (fun k => jointScore_timeSmooth hF x hr.le hl k p h0 h1)
    (fun k => A.timeSmooth hF x hr hlam hl _ p h0 h1)

omit [Fintype S] [Nonempty S] in
lemma outer_add {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A B : TensorSum (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.add B).outer F x r ((lam:ℝ)*r) c (ρ,y)=
      A.outer F x r ((lam:ℝ)*r) c (ρ,y)+B.outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  have he : (fun k => (A.add B).eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)))=
      fun k p => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p+
        B.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p := by
    funext k p
    exact add_eval A B F x r ((lam:ℝ)*r) _ p
  unfold outer
  rw [he]
  exact JetCalculus.gadj_add_at _ _ (fun k =>
    (A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))
    (fun k => (B.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp))

omit [Fintype S] [Nonempty S] in
lemma outer_scale {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum (S ⊕ Unit)) (n : ℕ) (P : Polynomial ℝ) (c : S → Fin d) (y : Point d) :
    (A.scale n P).outer F x r ((lam:ℝ)*r) c (ρ,y)=
      (r*((lam:ℝ)*r))^n*P.eval ρ*A.outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  have hA k := A.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have he : (fun k => (A.scale n P).eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)))=
      fun k p => (r*((lam:ℝ)*r))^n*(P.eval p.1*A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p) := by
    funext k p
    rw [scale_eval]
    ring
  unfold outer
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    (((polynomialTime_smooth P).contDiffAt).mul (hA k)).differentiableAt (by simp)),
    JetCalculus.gadj_time_at _ _ (fun k => (hA k).differentiableAt (by simp))]
  ring

theorem outer_material {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    {A B : TensorSum (S ⊕ Unit)} (hAB : A.HasMaterial B) (c : S → Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (A.outer F x r ((lam:ℝ)*r) c) (ρ,y)=
      (B.add (A.insertOne.scale 1 Polynomial.X)).outer F x r ((lam:ℝ)*r) c (ρ,y) := by
  let L : ℝ := (lam:ℝ)*r
  let V : Fin d → ℝ × Point d → ℝ := fun k => A.eval F x r L (Sum.elim c (fun _ => k))
  let W : Fin d → ℝ × Point d → ℝ := fun k => B.eval F x r L (Sum.elim c (fun _ => k))
  have hV (k : Fin d) := A.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hW (k : Fin d) := B.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hp : ρ^2<1 := by nlinarith
  have hM := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp
  have hda : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) W (ρ,y) := by
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (JetCalculus.smooth_mdir_at _ _ _ hM (hV k)).differentiableAt (by simp)
    · intro k; exact (hW k).differentiableAt (by simp)
    · intro k z; exact hAB hF x hr hlam hl h0 h1 _ z
  let I : Fin d → ℝ × Point d → ℝ := fun k => A.insertOne.eval F x r L (Sum.elim c (fun _ => k))
  have hI (k : Fin d) := A.insertOne.timeSmooth hF x hr hlam hl (Sum.elim c (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hdi : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=
      L*ρ*JetCalculus.gadj jointSpace (jointScore F x r) I (ρ,y) := by
    rw [←JetCalculus.gadj_scalar_at _ _ (fun k => (hI k).differentiableAt (by simp)) (L*ρ)]
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (ContDiffAt.sum (fun i _ =>
        (JetCalculus.smooth_dir_at (hM k) _).mul (hV i))).differentiableAt (by simp)
    · intro k; exact (contDiffAt_const.mul (hI k)).differentiableAt (by simp)
    · intro k z
      simpa only [Sum.elim_inl,Sum.elim_inr] using
        insertOne_mean hF x hr hlam hl h0 h1 A (Sum.elim c (fun _ => k)) z
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
    (JetCalculus.gadj jointSpace (jointScore F x r) V) (ρ,y)=_
  rw [physical_material_adjoint_nonneg hF x hr hlam hl h0 h1 hV,hda,hdi,
    outer_add hF x hr hlam hl h0 h1,outer_scale hF x hr hlam hl h0 h1]
  simp only [pow_one,Polynomial.eval_X]
  change B.outer F x r L c (ρ,y)+r*(L*ρ*A.insertOne.outer F x r L c (ρ,y))=_
  dsimp only [L]
  ring
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
