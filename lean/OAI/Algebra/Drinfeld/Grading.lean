import OAI.Algebra.Drinfeld.Ordering

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem piece_homogeneous {wt : α → ℕ} {k : ℕ} {p : A R α}
    (hp : p∈homogeneous wt k) (n : ℕ) : piece wt n p=if k=n then p else 0 := by
  by_cases h : k=n
  · subst k
    exact (project_eq_self hp).trans (ite_eq_left rfl).symm
  · rw [ite_eq_right h]
    exact project_eq_zero hp (by intro w hw hn; exact h (hw.symm.trans hn))

theorem piece_mem (wt : α → ℕ) (n : ℕ) (p : A R α) : piece wt n p∈homogeneous wt n :=
  project_mem _ p

theorem piece_eq_self_iff (wt : α → ℕ) (n : ℕ) (p : A R α) :
    piece wt n p=p ↔ p∈homogeneous wt n := by
  constructor
  · intro h; rw [← h]; exact piece_mem wt n p
  · exact project_eq_self

theorem project_degree_homogeneous (wt : α → ℕ) (P : ℕ → Prop) [DecidablePred P]
    {k : ℕ} {p : A R α} (hp : p∈homogeneous wt k) :
    project (fun w => P (degree wt w)) p=if P k then p else 0 := by
  by_cases h : P k
  · rw [ite_eq_left h]
    exact project_eq_self (space_mono (by intro w hw; exact hw ▸ h) hp)
  · rw [ite_eq_right h]
    exact project_eq_zero hp (by intro w hw; simpa only [hw] using h)

theorem algHom_project (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (P : ℕ → Prop) [DecidablePred P]
    (p : A R α) :
    f (project (fun w => P (degree wa w)) p)=project (fun w => P (degree wb w)) (f p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change f (project _ (word w))=project _ (f (word w))
    rw [project_word,project_degree_homogeneous wb P
      (algHom_homogeneous f wa wb hf (word_mem w rfl))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem algHom_piece (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (n : ℕ) (p : A R α) :
    f (piece wa n p)=piece wb n (f p) := algHom_project f wa wb hf (fun k => k=n) p

theorem homogeneous_reflect (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (hi : Function.Injective f)
    {n : ℕ} {p : A R α} (hp : f p∈homogeneous wb n) : p∈homogeneous wa n := by
  apply (piece_eq_self_iff wa n p).mp
  apply hi
  rw [algHom_piece f wa wb hf,piece_homogeneous hp,ite_eq_left rfl]

theorem project_preserves {P Q : FreeMonoid α → Prop} [DecidablePred Q]
    {p : A R α} (hp : p∈space P) : project Q p∈space P := by
  apply mem_space
  intro w hw
  rw [project_coeff] at hw
  split_ifs at hw with h
  · exact (mem_space_iff.mp hp) w hw
  · exact (hw rfl).elim

theorem subtract_piece_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : p-piece wt n p∈above wt (n+1) := by
  apply mem_space
  intro w hw
  change (p-piece wt n p).coeff w≠0 at hw
  simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply] at hw
  change p.coeff w-(project (fun w => degree wt w=n) p).coeff w≠0 at hw
  rw [project_coeff] at hw
  have hn : n≤degree wt w := by
    by_contra h
    have hz := coeff_support hp w h
    simp [hz] at hw
  by_cases he : degree wt w=n
  · simp [he] at hw
  · omega
end WordGrading

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

def treeDegree (wt : α → ℕ) (t : UniversalEmbedding.Tree α) : ℕ := (t.leaves.map wt).sum

@[simp] theorem treeDegree_leaf (wt : α → ℕ) (a : α) : treeDegree wt (.leaf a)=wt a := by
  simp [treeDegree,Tree.leaves]
@[simp] theorem treeDegree_node (wt : α → ℕ) (t u : UniversalEmbedding.Tree α) :
    treeDegree wt (.node t u)=treeDegree wt t+treeDegree wt u := by
  simp [treeDegree,Tree.leaves]

theorem embed_eval_homogeneous (wt : α → ℕ) (t : UniversalEmbedding.Tree α) :
    embed (t.eval : FreeLieAlgebra R α)∈homogeneous wt (treeDegree wt t) := by
  induction t with
  | leaf a =>
    simp only [Tree.eval,embed_of,treeDegree_leaf]
    exact word_mem (FreeMonoid.of a) (degree_of wt a)
  | node t u ht hu =>
    simp only [Tree.eval,treeDegree_node,LieHom.map_lie]
    change embed t.eval*embed u.eval-embed u.eval*embed t.eval∈_
    exact (homogeneous _ _).sub_mem (homogeneous_mul ht hu)
      (by simpa only [Nat.add_comm] using homogeneous_mul hu ht)

def homogeneousLie (wt : α → ℕ) (n : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  Submodule.span R {p | ∃ t : UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p}

theorem piece_exists (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    ∃ q : FreeLieAlgebra R α,q∈homogeneousLie wt n ∧ embed q=piece wt n (embed p) := by
  obtain ⟨k,hk⟩ := small_exists p
  induction hk using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,_,rfl⟩ := hp
    rw [piece_homogeneous (embed_eval_homogeneous (R:=R) wt t)]
    split_ifs with h
    · exact ⟨t.eval,Submodule.subset_span ⟨t,h,rfl⟩,rfl⟩
    · exact ⟨0,(homogeneousLie wt n).zero_mem,map_zero _⟩
  | zero => exact ⟨0,(homogeneousLie wt n).zero_mem,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨p',hp',he⟩ := hp
    obtain ⟨q',hq',hf⟩ := hq
    exact ⟨p'+q',(homogeneousLie wt n).add_mem hp' hq',by simp only [map_add,he,hf]⟩
  | smul c p _ hp =>
    obtain ⟨p',hp',he⟩ := hp
    exact ⟨c • p',(homogeneousLie wt n).smul_mem c hp',by simp only [map_smul,he]⟩

def piece (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) : FreeLieAlgebra R α :=
  (piece_exists wt n p).choose

theorem piece_spec (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    piece wt n p∈homogeneousLie wt n ∧ embed (piece wt n p)=WordGrading.piece wt n (embed p) :=
  (piece_exists wt n p).choose_spec

@[simp] theorem embed_piece (wt : α → ℕ) (n : ℕ) (p : FreeLieAlgebra R α) :
    embed (piece wt n p)=WordGrading.piece wt n (embed p) := (piece_spec wt n p).2

theorem homogeneousLie_embed {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra R α}
    (hp : p∈homogeneousLie wt n) : embed p∈homogeneous wt n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨t,ht,rfl⟩ := hp
      simpa only [ht] using embed_eval_homogeneous (R:=R) wt t
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (homogeneous _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (homogeneous _ _).smul_mem c hp

theorem homogeneous_iff {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra R α} :
    p∈homogeneousLie wt n ↔ embed p∈homogeneous wt n := by
  constructor
  · exact homogeneousLie_embed
  · intro hp
    have h : piece wt n p=p := by
      apply UniversalEmbedding.injective
      rw [embed_piece]
      exact WordGrading.project_eq_self hp
    rw [← h]
    exact (piece_spec wt n p).1

end LieGrading
end

namespace TensorProjection
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]

abbrev len {α : Type*} (w : FreeMonoid α) : ℕ := degree (fun _ => 1) w
abbrev piece {α : Type*} (n : ℕ) : A R α →ₗ[R] A R α := WordGrading.piece (fun _ => 1) n

def totalPiece (n : ℕ) : A R α⊗[R]A R β →ₗ[R] A R α⊗[R]A R β :=
  ∑ i∈Finset.range (n+1),TensorProduct.map (piece i) (piece (n-i))

theorem totalPiece_word (n : ℕ) (u : FreeMonoid α) (v : FreeMonoid β) :
    totalPiece (R:=R) n (word u⊗ₜ[R]word v)=
      if len u+len v=n then word u⊗ₜ[R]word v else 0 := by
  classical
  simp only [totalPiece,LinearMap.sum_apply,TensorProduct.map_tmul,piece,WordGrading.piece,project_word]
  change (∑ i∈Finset.range (n+1),(if len u=i then word u else 0)⊗ₜ[R]
    (if len v=n-i then word v else 0))=_
  by_cases hu : len u≤n
  · rw [Finset.sum_eq_single (len u)]
    · simp only [ite_true]
      by_cases h : len u+len v=n
      · have hv : len v=n-len u := by omega
        rw [ite_eq_left hv,ite_eq_left h]
      · have hv : len v≠n-len u := by omega
        rw [ite_eq_right hv,ite_eq_right h,TensorProduct.tmul_zero]
    · intro b hb hbu
      rw [ite_eq_right (Ne.symm hbu),TensorProduct.zero_tmul]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right (by have hi' := Finset.mem_range.mp hi; omega),TensorProduct.zero_tmul]

theorem totalPiece_homogeneous {k : ℕ} {p : A R α⊗[R]A R β}
    (hp : p∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) k) (n : ℕ) :
    totalPiece n p=if k=n then p else 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,v,huv,rfl⟩ := hp
    change len u+len v=k at huv
    rw [totalPiece_word,huv]
  | zero => simp
  | add p q _ _ hp hq => rw [map_add,hp,hq]; split_ifs <;> simp
  | smul c p _ hp => rw [map_smul,hp]; split_ifs <;> simp

theorem homogeneous_mul {n m : ℕ} {p q : A R α⊗[R]A R β}
    (hp : p∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) n)
    (hq : q∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) m) :
    p*q∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) (n+m) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,v,huv,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨s,t,hst,rfl⟩ := hq
      rw [Algebra.TensorProduct.tmul_mul_tmul,←word_mul,←word_mul]
      apply TensorGrading.tmul_word_mem
      change len u+len v=n at huv
      change len s+len t=m at hst
      change len (u*s)+len (v*t)=n+m
      simp only [len,degree_mul] at *
      omega
    | zero => simp
    | add q r _ _ hq hr => rw [mul_add]; exact Submodule.add_mem _ hq hr
    | smul c q _ hq => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hq
  | zero => simp
  | add p r _ _ hp hr => rw [add_mul]; exact Submodule.add_mem _ hp hr
  | smul c p _ hp => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hp

def coproduct : A R α →ₐ[R] A R α⊗[R]A R α :=
  AssociativeElimination.lift (fun a => atom a⊗ₜ[R]1+(1:A R α)⊗ₜ[R]atom a)

@[simp] theorem coproduct_atom (a : α) : (coproduct (R:=R) (α:=α)) (atom (R:=R) a)=atom a⊗ₜ[R]1+(1:A R α)⊗ₜ[R]atom a :=
  AssociativeElimination.lift_atom _ _

theorem coproduct_word_homogeneous (u : FreeMonoid α) :
    (coproduct (R:=R) (α:=α)) (word (R:=R) u)∈TensorGrading.homogeneous (fun _ => 1) (fun _ => 1) (len u) := by
  induction u using FreeMonoid.inductionOn' with
  | one =>
    rw [word_one,map_one]
    exact TensorGrading.tmul_word_mem 1 1 (by simp [len])
  | of_mul a u ih =>
    rw [word_mul,word_of,map_mul,coproduct_atom]
    apply homogeneous_mul _ ih
    apply Submodule.add_mem
    · exact TensorGrading.tmul_word_mem (FreeMonoid.of a) 1 (by simp)
    · exact TensorGrading.tmul_word_mem 1 (FreeMonoid.of a) (by simp)

theorem coproduct_piece (n : ℕ) (p : A R α) :
    (coproduct (R:=R) (α:=α)) (piece n p)=totalPiece n ((coproduct (R:=R) (α:=α)) p) := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change (coproduct (R:=R) (α:=α)) (piece n (word u))=totalPiece n ((coproduct (R:=R) (α:=α)) (word u))
    rw [totalPiece_homogeneous (coproduct_word_homogeneous u)]
    rw [piece,WordGrading.piece,project_word]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem totalPiece_left (n : ℕ) (p : A R α) : totalPiece n (p⊗ₜ[R](1:A R β))=piece n p⊗ₜ[R]1 := by
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change totalPiece n (word u⊗ₜ[R]word 1)=piece n (word u)⊗ₜ[R]1
    rw [totalPiece_word]
    have hz : len (1:FreeMonoid β)=0 := by simp [len]
    rw [hz,Nat.add_zero]
    rw [piece,WordGrading.piece,project_word]
    by_cases h : len u=n
    · rw [ite_eq_left h,ite_eq_left h,word_one]
    · rw [ite_eq_right h,ite_eq_right h,TensorProduct.zero_tmul]
  | add p q hp hq => simp only [TensorProduct.add_tmul,map_add,hp,hq]
  | smul c p hp => simp only [←TensorProduct.smul_tmul',map_smul,hp]

theorem totalPiece_right (n : ℕ) (p : A R β) : totalPiece n ((1:A R α)⊗ₜ[R]p)=1⊗ₜ[R]piece n p := by
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change totalPiece n (word 1⊗ₜ[R]word v)=1⊗ₜ[R]piece n (word v)
    rw [totalPiece_word,piece,WordGrading.piece,project_word]
    simp only [len,degree_one,Nat.zero_add,word_one]
    split_ifs <;> simp
  | add p q hp hq => simp only [TensorProduct.tmul_add,map_add,hp,hq]
  | smul c p hp => simp only [TensorProduct.tmul_smul,map_smul,hp]
end TensorProjection

namespace PrimitiveWords
open AssociativeElimination
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing Classical.propDecidable

abbrev W (α : Type*) := FreeMonoid α
abbrev B (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α × FreeMonoid α)

def word (w : W α) : A R α := MonoidAlgebra.single w 1

def pair (u v : W α) : B R α := MonoidAlgebra.single (u,v) 1

def linear {M : Type*} [AddCommGroup M] [Module R M] (f : W α → M) : A R α →ₗ[R] M :=
  (Finsupp.linearCombination R f).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

def bilinear {M : Type*} [AddCommGroup M] [Module R M] (f : W α → W α → M) : B R α →ₗ[R] M :=
  (Finsupp.linearCombination R (fun p => f p.1 p.2)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem linear_single {M : Type*} [AddCommGroup M] [Module R M]
    (f : W α → M) (w : W α) (r : R) : linear f (MonoidAlgebra.single w r)=r • f w := by
  change Finsupp.linearCombination R f (Finsupp.single w r) = _; simp
@[simp] theorem bilinear_single {M : Type*} [AddCommGroup M] [Module R M]
    (f : W α → W α → M) (u v : W α) (r : R) : bilinear f (MonoidAlgebra.single (u,v) r)=r • f u v := by
  change Finsupp.linearCombination R (fun pair => f pair.1 pair.2) (Finsupp.single (u,v) r) = _; simp

@[simp] theorem word_one : word (R:=R) (1 : W α)=1 := rfl
@[simp] theorem word_mul (u v : W α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]
@[simp] theorem pair_one : pair (R:=R) (1 : W α) 1=1 := rfl
@[simp] theorem pair_mul (u v s t : W α) : pair (R:=R) (u*s) (v*t)=pair u v*pair s t := by
  simp [pair,MonoidAlgebra.single_mul_single]

def coproduct : A R α →ₐ[R] B R α :=
  lift (fun a => pair (FreeMonoid.of a) 1+pair 1 (FreeMonoid.of a))

def left : A R α →ₗ[R] B R α := linear (fun w => pair w 1)
def right : A R α →ₗ[R] B R α := linear (fun w => pair 1 w)

def Primitive (p : A R α) : Prop := coproduct p=left p+right p

def antipodeWord (w : W α) : A R α :=
  (-1 : R)^w.toList.length • word (FreeMonoid.ofList w.toList.reverse)

def counitConvolution : B R α →ₗ[R] A R α := bilinear (fun u v => word u*antipodeWord v)
def dynkinConvolution : B R α →ₗ[R] A R α :=
  bilinear (fun u v => (u.toList.length : R) • (word u*antipodeWord v))

@[simp] theorem antipodeWord_one : antipodeWord (R:=R) (1 : W α)=1 := by simp [antipodeWord]
theorem antipodeWord_cons (a : α) (w : W α) :
    antipodeWord (R:=R) (FreeMonoid.of a*w) = -(antipodeWord w*atom a) := by
  simp only [antipodeWord,FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,
    List.length_cons,List.reverse_cons,pow_succ,FreeMonoid.ofList_append]
  simp [word,atom,MonoidAlgebra.single_mul_single]

@[simp] theorem coproduct_atom (a : α) :
    coproduct (atom (R:=R) a)=pair (FreeMonoid.of a) 1+pair 1 (FreeMonoid.of a) := by
  simp [coproduct]

theorem counitConvolution_left (a : α) (b : B R α) :
    counitConvolution (pair (FreeMonoid.of a) 1*b)=atom a*counitConvolution b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [mul_add,hb,hc]
  | single p r =>
    rcases p with ⟨u,v⟩
    simp only [counitConvolution,pair,MonoidAlgebra.single_mul_single,
      Prod.mk_mul_mk,one_mul,bilinear_single,word_mul]
    change r • ((atom a*word u)*antipodeWord v)=atom a*(r • (word u*antipodeWord v))
    rw [mul_assoc,mul_smul_comm]

theorem counitConvolution_right (a : α) (b : B R α) :
    counitConvolution (pair 1 (FreeMonoid.of a)*b)=-(counitConvolution b*atom a) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc,add_mul]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp [counitConvolution,pair,MonoidAlgebra.single_mul_single,antipodeWord_cons,mul_assoc]

theorem dynkinConvolution_left (a : α) (b : B R α) :
    dynkinConvolution (pair (FreeMonoid.of a) 1*b)=
      atom a*dynkinConvolution b+atom a*counitConvolution b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp only [dynkinConvolution,counitConvolution,pair,MonoidAlgebra.single_mul_single,
      one_mul,Prod.mk_mul_mk,one_mul,bilinear_single,FreeMonoid.toList_mul,
      FreeMonoid.toList_of,List.singleton_append,List.length_cons,Nat.cast_add,Nat.cast_one,
      add_smul,one_smul,smul_add,word_mul]
    change r • ((u.toList.length : R) • ((atom a*word u)*antipodeWord v))+
      r • ((atom a*word u)*antipodeWord v)=_
    simp only [mul_assoc,mul_smul_comm,smul_smul]

theorem dynkinConvolution_right (a : α) (b : B R α) :
    dynkinConvolution (pair 1 (FreeMonoid.of a)*b)=-(dynkinConvolution b*atom a) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [mul_add,map_add,hb,hc,add_mul]; abel
  | single p r =>
    rcases p with ⟨u,v⟩
    simp [dynkinConvolution,pair,MonoidAlgebra.single_mul_single,antipodeWord_cons,
      mul_assoc]

@[simp] theorem counitConvolution_one : counitConvolution (1 : B R α)=1 := by
  change bilinear _ (MonoidAlgebra.single (1,1) 1)=1
  simp
@[simp] theorem dynkinConvolution_one : dynkinConvolution (1 : B R α)=0 := by
  change bilinear _ (MonoidAlgebra.single (1,1) 1)=0
  simp

@[simp] theorem word_of (a : α) : word (R:=R) (FreeMonoid.of a)=atom a := rfl

theorem counit_coproduct_word (w : W α) :
    counitConvolution (coproduct (word (R:=R) w))=if w=1 then 1 else 0 := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    have hne : FreeMonoid.of a*w≠1 := by
      intro h
      have h' := congrArg FreeMonoid.toList h
      simp at h'
    rw [word_mul,word_of,map_mul,coproduct_atom,add_mul,map_add,
      counitConvolution_left,counitConvolution_right,ih,ite_eq_right hne]
    split_ifs <;> simp

def dynkinWord : List α → FreeLieAlgebra R α
  | [] => 0
  | [a] => FreeLieAlgebra.of R a
  | a::b::w => ⁅FreeLieAlgebra.of R a,dynkinWord (b::w)⁆

def dynkin : A R α →ₗ[R] FreeLieAlgebra R α := linear (fun w => dynkinWord w.toList)

def euler : A R α →ₗ[R] A R α := linear (fun w => (w.toList.length : R) • word w)

theorem dynkin_coproduct_word (w : W α) :
    dynkinConvolution (coproduct (word (R:=R) w))=embed (dynkinWord w.toList) := by
  classical
  induction w using FreeMonoid.inductionOn' with
  | one => simp [dynkinWord]
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,coproduct_atom,add_mul,map_add,
      dynkinConvolution_left,dynkinConvolution_right,ih,counit_coproduct_word]
    by_cases hw : w=1
    · subst w
      simp [dynkinWord]
    · rw [ite_eq_right hw,mul_zero,add_zero]
      have hw' : w.toList≠[] := by
        intro hh
        exact hw (FreeMonoid.toList.injective hh)
      have hc : dynkinWord (R:=R) (a::w.toList)=
          ⁅FreeLieAlgebra.of R a,dynkinWord w.toList⁆ := by
        cases h : w.toList with
        | nil => exact (hw' h).elim
        | cons b v => rfl
      simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,List.singleton_append,hc,
        LieHom.map_lie,embed_of,Ring.lie_def,sub_eq_add_neg]

theorem dynkin_coproduct (p : A R α) : dynkinConvolution (coproduct p)=embed (dynkin p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change dynkinConvolution (coproduct (word w))=embed (dynkin (word w))
    simpa only [dynkin,word,linear_single,one_smul] using dynkin_coproduct_word (R:=R) w
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul r p hp => simp only [map_smul,hp]

theorem dynkin_left (p : A R α) : dynkinConvolution (left p)=euler p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | single w r => simp [left,linear_single,pair,dynkinConvolution,euler]

theorem dynkin_right (p : A R α) : dynkinConvolution (right p)=0 := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add,hp,hq,add_zero]
  | single w r => simp [right,linear_single,pair,dynkinConvolution]

theorem dynkin_primitive {p : A R α} (hp : Primitive p) : embed (dynkin p)=euler p := by
  rw [←dynkin_coproduct,hp,map_add,dynkin_left,dynkin_right,add_zero]

theorem euler_homogeneous {p : A R α} {n : ℕ}
    (hp : p∈WordGrading.homogeneous (fun _ => 1) n) : euler p=(n : R) • p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    have hh : w.toList.length=n := by simpa [WordGrading.degree] using hw
    simp [euler,WordGrading.word,hh,word]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul r p _ hp => simp only [map_smul,hp,smul_comm r (n : R) p]

theorem exists_lie_of_primitive {K : Type*} [Field K] [CharZero K]
    {p : A K α} {n : ℕ} (hn : 0<n)
    (hh : p∈WordGrading.homogeneous (fun _ => 1) n) (hp : Primitive p) :
    ∃ q : FreeLieAlgebra K α, q∈LieGrading.homogeneousLie (fun _ => 1) n ∧ embed q=p := by
  have hn' : (n : K)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he : embed ((n : K)⁻¹ • dynkin p)=p := by
    rw [map_smul,dynkin_primitive hp,euler_homogeneous hh,smul_smul,inv_mul_cancel₀ hn',one_smul]
  exact ⟨(n : K)⁻¹ • dynkin p,LieGrading.homogeneous_iff.mpr (by rw [he]; exact hh),he⟩

end PrimitiveWords

namespace WordCoordinates
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

def coordinates (P : FreeMonoid α → Prop) : space (R:=R) P →ₗ[R] ({w // P w} → R) where
  toFun p w := p.val.coeff w.val
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem coordinates_injective (P : FreeMonoid α → Prop) : Function.Injective (coordinates (R:=R) P) := by
  intro p q h
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_cases hw : P w
  · exact congrFun h ⟨w,hw⟩
  · rw [coeff_support p.property w hw,coeff_support q.property w hw]

variable (P : FreeMonoid α → Prop) [Fintype {w // P w}]

def assembly (c : {w // P w} → R) : space (R:=R) P :=
  ⟨∑ w, c w • word w.val,Submodule.sum_mem _ (fun w _ => (space P).smul_mem _ (word_mem _ w.property))⟩

theorem coordinates_assembly (c : {w // P w} → R) : coordinates P (assembly P c)=c := by
  classical
  ext w
  change (∑ v : {w // P w},c v • word v.val).coeff w.val=c w
  simp [word,Finsupp.single_apply,Subtype.val_inj]

def equiv : space (R:=R) P ≃ₗ[R] ({w // P w} → R) :=
  LinearEquiv.ofBijective (coordinates P) ⟨coordinates_injective P,fun c => ⟨assembly P c,coordinates_assembly P c⟩⟩

@[simp] theorem equiv_apply (p : space (R:=R) P) (w : {w // P w}) : equiv P p w=p.val.coeff w.val := rfl

instance finite_space [Module.Finite R R] : Module.Finite R (space (R:=R) P) :=
  Module.Finite.equiv (equiv P).symm

variable {P}

theorem length_le_degree (wt : α → ℕ) (hpos : ∀ a,0<wt a) (w : FreeMonoid α) :
    w.toList.length≤degree wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [degree]
  | of_mul a w ih =>
    rw [degree_mul,degree_of]
    change w.toList.length+1≤wt a+degree wt w
    have := hpos a
    omega

theorem letter_le_degree (wt : α → ℕ) (w : FreeMonoid α) {a : α} (ha : a∈w.toList) :
    wt a≤degree wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp at ha
  | of_mul b w ih =>
    rw [degree_mul,degree_of]
    rcases List.mem_cons.mp ha with h | h
    · subst a; omega
    · have := ih h; omega

theorem finite_degree (wt : α → ℕ) (hpos : ∀ a,0<wt a) (n : ℕ)
    (hf : {a | wt a≤n}.Finite) : {w | degree wt w=n}.Finite := by
  classical
  let : Finite {a // wt a≤n} := hf.to_subtype
  apply Set.Finite.subset ((List.finite_length_le {a // wt a≤n} n).image
    (fun l => FreeMonoid.ofList (l.map Subtype.val)))
  intro w hw
  let l : List {a // wt a≤n} := w.toList.attach.map (fun a => ⟨a.val,(letter_le_degree wt w a.property).trans_eq hw⟩)
  refine ⟨l,?_,?_⟩
  · simpa [l] using (length_le_degree wt hpos w).trans_eq hw
  · simp [l,List.map_map]

theorem finite_degree_finite_alphabet [Finite α] (wt : α → ℕ) (hpos : ∀ a,0<wt a) (n : ℕ) :
    {w | degree wt w=n}.Finite := finite_degree wt hpos n (Set.toFinite _)

end WordCoordinates

end DeligneDrinfeld

end

end OAI
