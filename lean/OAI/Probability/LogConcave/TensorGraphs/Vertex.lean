import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

section
namespace LogConcaveSampling.TraceOpening

abbrev Vertex (n : ℕ) (H : Type*) := Sum (Fin (n+1)) H

def level {n : ℕ} {H : Type*} (left : H → Fin (n+1)) : Vertex n H → ℕ
  | Sum.inl i => 2*i.val
  | Sum.inr h => 2*(left h).val+1

lemma auxiliary_between {n : ℕ} {H : Type*} (left right : H → Fin (n+1))
    (hpair : ∀h,left h<right h) (h : H) :
    level left (Sum.inl (left h))<level left (Sum.inr h) ∧
    level left (Sum.inr h)<level left (Sum.inl (right h)) := by
  have hp := hpair h
  simp only [Fin.lt_def] at hp
  simp only [level]
  omega

def Allowed {n : ℕ} {H : Type*} : Vertex n H → Vertex n H → Prop
  | Sum.inl i, Sum.inl j => i≠j
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => False

lemma edge_levels_distinct {n : ℕ} {H : Type*} (left : H → Fin (n+1))
    {u v : Vertex n H} (h : Allowed u v) : level left u≠level left v := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      simp only [Allowed] at h
      have : i.val≠j.val := fun he => h (Fin.ext he)
      simp only [level]
      omega
    | inr j => simp only [level]; omega
  | inr i =>
    cases v with
    | inl j => simp only [level]; omega
    | inr j => exact False.elim h

theorem all_vertex_splits_nontrivial {n : ℕ} {H : Type*}
    (left right : H → Fin (n+1)) (hpair : ∀h,left h<right h)
    (R : Vertex n H → Vertex n H → Prop)
    (hchain : ∀i : Fin n,R (Sum.inl i.castSucc) (Sum.inl i.succ))
    (hleft : ∀h,R (Sum.inl (left h)) (Sum.inr h))
    (hright : ∀h,R (Sum.inr h) (Sum.inl (right h))) :
    ∀v : Vertex n H,
      (v=Sum.inl 0 ∨ ∃u,R u v ∧ level left u<level left v) ∧
      (v=Sum.inl (Fin.last n) ∨ ∃w,R v w ∧ level left v<level left w) := by
  intro v
  cases v with
  | inr h =>
    exact ⟨Or.inr ⟨_,hleft h,(auxiliary_between left right hpair h).1⟩,
      Or.inr ⟨_,hright h,(auxiliary_between left right hpair h).2⟩⟩
  | inl i =>
    constructor
    · by_cases hi : i=0
      · exact Or.inl (congrArg Sum.inl hi)
      · right
        have hi0 : 0 < (i : Fin (n+1)).val := by
          have : i.val ≠ 0 := fun he => hi (Fin.ext (by simpa only [Fin.val_zero] using he))
          omega
        let j : Fin n := ⟨i.val-1,by omega⟩
        have he : j.succ=i := Fin.ext (by dsimp [j]; omega)
        refine ⟨Sum.inl j.castSucc,?_,?_⟩
        · simpa only [he] using hchain j
        · simp only [level,Fin.val_castSucc]
          dsimp [j]
          omega
    · by_cases hi : i=Fin.last n
      · exact Or.inl (congrArg Sum.inl hi)
      · right
        have hin : i.val<n := by
          have : i.val≠n := fun he => hi (Fin.ext he)
          omega
        let j : Fin n := ⟨i.val,hin⟩
        have he : j.castSucc=i := Fin.ext rfl
        refine ⟨Sum.inl j.succ,?_,?_⟩
        · simpa only [he] using hchain j
        · simp only [level,Fin.val_succ]
          dsimp [j]
          omega

def orderKey {V : Type*} [Fintype V] (r : V → ℕ) (v : V) : ℕ :=
  r v*(Fintype.card V+1)+(Fintype.equivFin V v).val

lemma orderKey_strict {V : Type*} [Fintype V] (r : V → ℕ) {u v : V}
    (h : r u<r v) : orderKey r u<orderKey r v := by
  have hu := (Fintype.equivFin V u).isLt
  have hv := (Fintype.equivFin V v).isLt
  dsimp only [orderKey]
  nlinarith

lemma orderKey_div {V : Type*} [Fintype V] (r : V → ℕ) (v : V) :
    orderKey r v/(Fintype.card V+1)=r v := by
  unfold orderKey
  have hv : (Fintype.equivFin V v).val<Fintype.card V+1 :=
    lt_trans (Fintype.equivFin V v).isLt (Nat.lt_succ_self _)
  rw [Nat.mul_comm (r v), Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt hv, Nat.add_zero]

lemma orderKey_injective {V : Type*} [Fintype V] (r : V → ℕ) :
    Function.Injective (orderKey r) := by
  intro u v he
  have hr : r u=r v := by
    simpa only [orderKey_div] using congrArg (fun k => k/(Fintype.card V+1)) he
  have hc : (Fintype.equivFin V u).val=(Fintype.equivFin V v).val := by
    simp only [orderKey,hr] at he
    omega
  exact (Fintype.equivFin V).injective (Fin.ext hc)

theorem ordered_nontrivial_splits {n : ℕ} {H : Type*} [Fintype H]
    (left right : H → Fin (n+1)) (hpair : ∀h,left h<right h)
    (R : Vertex n H → Vertex n H → Prop)
    (hchain : ∀i : Fin n,R (Sum.inl i.castSucc) (Sum.inl i.succ))
    (hleft : ∀h,R (Sum.inl (left h)) (Sum.inr h))
    (hright : ∀h,R (Sum.inr h) (Sum.inl (right h))) :
    ∃ key : Vertex n H → ℕ, Function.Injective key ∧
      ∀v : Vertex n H,
        (v=Sum.inl 0 ∨ ∃u,R u v ∧ key u<key v) ∧
        (v=Sum.inl (Fin.last n) ∨ ∃w,R v w ∧ key v<key w) := by
  refine ⟨orderKey (level left),orderKey_injective _,fun v => ?_⟩
  obtain ⟨hv₁,hv₂⟩ := all_vertex_splits_nontrivial left right hpair R hchain hleft hright v
  constructor
  · rcases hv₁ with h | ⟨u,hu,huv⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,hu,orderKey_strict _ huv⟩
  · rcases hv₂ with h | ⟨w,hw,hvw⟩
    · exact Or.inl h
    · exact Or.inr ⟨w,hw,orderKey_strict _ hvw⟩
end LogConcaveSampling.TraceOpening

end
section
namespace LogConcaveSampling

def traceMomentOrder (d j : ℕ) (c p : ℝ) : ℕ :=
  ⌈p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1)⌉₊

lemma traceMomentOrder_bounds {d j : ℕ} {c p : ℝ} (hc : 1≤c) (hp : 2≤p) :
    0<traceMomentOrder d j c p ∧ p≤2*(traceMomentOrder d j c p:ℝ) ∧
    ((j:ℝ)+c)*Real.log ((d:ℝ)+1)≤(traceMomentOrder d j c p:ℝ) ∧
    (traceMomentOrder d j c p:ℝ)≤c*(p+((j:ℝ)+1)*Real.log ((d:ℝ)+1)) := by
  have ht : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hj : (0:ℝ)≤j := Nat.cast_nonneg j
  have ha : 0≤p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1) := by positivity
  have hlo := Nat.le_ceil (p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))
  have hhi := (Nat.ceil_lt_add_one ha).le
  change (p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))≤(traceMomentOrder d j c p:ℝ) at hlo
  change (traceMomentOrder d j c p:ℝ)≤(p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1))+1 at hhi
  have hn : 0<traceMomentOrder d j c p := by
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨hn,?_,?_,?_⟩
  · have := mul_nonneg (by linarith : 0≤(j:ℝ)+c) ht
    linarith
  · linarith
  · have h₁ : (j:ℝ)+c≤c*((j:ℝ)+1) := by nlinarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht
    have h₃ := mul_le_mul_of_nonneg_right hc (by linarith : 0≤p)
    nlinarith

lemma traceMomentOrder_polynomial {d j : ℕ} {c p : ℝ} (hc : 1≤c) (hp : 2≤p) :
    (traceMomentOrder d j c p:ℝ)≤c*(p+(j:ℝ)+Real.log ((d:ℝ)+1))^2 := by
  have hh := (traceMomentOrder_bounds (d:=d) (j:=j) hc hp).2.2.2
  have ht : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hj : (0:ℝ)≤j := Nat.cast_nonneg j
  have hcross : 0≤(p-1)*Real.log ((d:ℝ)+1) := mul_nonneg (by linarith) ht
  have h1 : p+((j:ℝ)+1)*Real.log ((d:ℝ)+1)≤
      (p+(j:ℝ)+Real.log ((d:ℝ)+1))^2 := by nlinarith [sq_nonneg (p-1),sq_nonneg (j:ℝ)]
  exact hh.trans (mul_le_mul_of_nonneg_left h1 (by linarith))

lemma traceMomentOrder_dimension_root {d j : ℕ} {c p : ℝ}
    (hd : 1≤d) (hc : 1≤c) (hp : 2≤p) :
    (d:ℝ)^(((j:ℝ)+c)/(2*(traceMomentOrder d j c p:ℝ)))≤Real.exp (1/2) := by
  have hs := traceMomentOrder_bounds (d:=d) (j:=j) hc hp
  have hsp : 0<(traceMomentOrder d j c p:ℝ) := by exact_mod_cast hs.1
  have hd0 : 0<(d:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hd)
  have hlog : Real.log (d:ℝ)≤Real.log ((d:ℝ)+1) := Real.log_le_log hd0 (by linarith)
  have hnum : ((j:ℝ)+c)*Real.log (d:ℝ)≤(traceMomentOrder d j c p:ℝ) :=
    (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hs.2.2.1
  rw [Real.rpow_def_of_pos hd0]
  apply Real.exp_le_exp.mpr
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<2*(traceMomentOrder d j c p:ℝ))).mpr
  nlinarith
end LogConcaveSampling

end
section
open scoped Matrix.Norms.L2Operator

namespace LogConcaveSampling.TraceMoment
open Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma psd_norm_le_trace {A : Matrix I I ℝ} (hA : A.PosSemidef) : ‖A‖≤A.trace := by
  have hn : 0≤∑i,hA.1.eigenvalues i := Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i)
  rw [hA.1.trace_eq_sum_eigenvalues]
  conv_lhs => rw [hA.1.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ←Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hn).mpr
  intro i
  simpa only [Function.comp_apply,RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (hA.eigenvalues_nonneg i)] using
    (Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i))

lemma hermitian_norm_eigenvalues {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    ‖A‖=‖hA.eigenvalues‖ := by
  calc
    ‖A‖=‖Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))‖ := congrArg norm hA.spectral_theorem
    _=‖hA.eigenvalues‖ := by
      simp only [Unitary.conjStarAlgAut_apply, ←Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal,
        RCLike.ofReal_real_eq_id,Function.id_comp]

lemma hermitian_trace_pow {A : Matrix I I ℝ} (hA : A.IsHermitian) (s : ℕ) :
    (A^s).trace=∑i,(hA.eigenvalues i)^s := by
  have he : A^s=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (hA.eigenvalues^s)) := by
    calc
      A^s=(Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)))^s := congrArg (fun B => B^s) hA.spectral_theorem
      _=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))^s) := (map_pow _ _ _).symm
      _=_ := by simp only [RCLike.ofReal_real_eq_id,Function.id_comp,diagonal_pow]
  rw [he]
  simp only [Unitary.conjStarAlgAut_apply,trace_mul_cycle,Unitary.coe_star_mul_self,
    one_mul,trace_diagonal,Pi.pow_apply]

lemma psd_norm_pow_le_trace_pow {A : Matrix I I ℝ} (hA : A.PosSemidef)
    {s : ℕ} (hs : 0<s) : ‖A‖^s≤(A^s).trace := by
  cases isEmpty_or_nonempty I with
  | inl hi =>
    have he : A=0 := Subsingleton.elim _ _
    simp [he,hs.ne']
  | inr hi =>
    rw [hermitian_norm_eigenvalues hA.1,hermitian_trace_pow hA.1]
    obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
    have hb : ‖hA.1.eigenvalues‖≤hA.1.eigenvalues i := by
      apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr
      intro j
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg j)] using hmax j (Finset.mem_univ j)
    exact (pow_le_pow_left₀ (norm_nonneg _) hb s).trans
      (Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) s) (Finset.mem_univ i))

theorem rectangular_trace_moment (A : Matrix I J ℝ) {s : ℕ} (hs : 0<s) :
    ‖A‖^(2*s)≤((A*A.transpose)^s).trace := by
  have hN := l2_opNorm_conjTranspose_mul_self A.conjTranspose
  simp only [conjTranspose_conjTranspose,l2_opNorm_conjTranspose] at hN
  have hh := psd_norm_pow_le_trace_pow (posSemidef_self_mul_conjTranspose A) hs
  rw [hN,←pow_two,←pow_mul] at hh
  simpa only [conjTranspose_eq_transpose_of_trivial] using hh
end LogConcaveSampling.TraceMoment

end
section
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

structure Hessian (P : Type*) where
  first : P
  second : P
  extra : List P
  deriving DecidableEq

def Hessian.degree (h : Hessian P) : ℕ := h.extra.length+2

def Hessian.hit (h : Hessian P) (i : P) : Hessian P :=
  ⟨h.first,h.second,i::h.extra⟩

structure State (P : Type*) [DecidableEq P] where
  pending : Finset P
  derivatives : P → List P
  hessians : Multiset (Hessian P)

def State.degree (S : State P) : ℕ :=
  S.pending.card+(∑j,(S.derivatives j).length)+(S.hessians.map Hessian.degree).sum

def initial : State P := ⟨Finset.univ,fun _ => [],0⟩

lemma initial_degree : (initial (P:=P)).degree=Fintype.card P := by
  simp [State.degree,initial]

def hitPrimary (S : State P) (i j : P) : State P :=
  ⟨S.pending.erase i,Function.update S.derivatives j (i::S.derivatives j),S.hessians⟩

def pair (S : State P) (i j : P) : State P :=
  ⟨(S.pending.erase i).erase j,S.derivatives,⟨i,j,[]⟩::ₘS.hessians⟩

def hitHessian (S : State P) (i : P) (h : Hessian P) : State P :=
  ⟨S.pending.erase i,S.derivatives,h.hit i::ₘS.hessians.erase h⟩

lemma hitPrimary_degree (S : State P) {i j : P} (hi : i∈S.pending) :
    (hitPrimary S i j).degree=S.degree := by
  have he : (∑k,(Function.update S.derivatives j (i::S.derivatives j) k).length)=
      (∑k,(S.derivatives k).length)+1 := by
    have hl : (fun k => (Function.update S.derivatives j (i::S.derivatives j) k).length)=
        Function.update (fun k => (S.derivatives k).length) j ((S.derivatives j).length+1) := by
      funext k
      by_cases hk : k=j
      · subst k; simp
      · simp [Function.update_of_ne hk]
    rw [hl,Finset.sum_update_of_mem (Finset.mem_univ j),Finset.sdiff_singleton_eq_erase]
    have hs := Finset.add_sum_erase Finset.univ (fun k => (S.derivatives k).length) (Finset.mem_univ j)
    omega
  simp only [State.degree,hitPrimary,he,Finset.card_erase_of_mem hi]
  have hp := Finset.card_pos.mpr ⟨i,hi⟩
  omega

lemma pair_degree (S : State P) {i j : P} (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) :
    (pair S i j).degree=S.degree := by
  have hj' : j∈S.pending.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hp := Finset.card_pos.mpr ⟨j,hj'⟩
  simp only [Finset.card_erase_of_mem hi] at hp
  simp only [State.degree,pair,Multiset.map_cons,Multiset.sum_cons,Hessian.degree,List.length_nil,
    zero_add,Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
  omega

lemma hitHessian_degree (S : State P) {i : P} (hi : i∈S.pending)
    {h : Hessian P} (hh : h∈S.hessians) : (hitHessian S i h).degree=S.degree := by
  have hm := congrArg (fun t : Multiset (Hessian P) => (t.map Hessian.degree).sum)
    (Multiset.cons_erase hh)
  simp only [Multiset.map_cons,Multiset.sum_cons] at hm
  have hp := Finset.card_pos.mpr ⟨i,hi⟩
  simp only [State.degree,hitHessian,Finset.card_erase_of_mem hi,Multiset.map_cons,
    Multiset.sum_cons,Hessian.degree,Hessian.hit,List.length_cons]
  simp only [Hessian.degree] at *
  omega

inductive Step : State P → State P → Prop
  | primary (S : State P) (i j : P) (hi : i∈S.pending) (hij : i≠j) : Step S (hitPrimary S i j)
  | pair (S : State P) (i j : P) (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) : Step S (pair S i j)
  | hessian (S : State P) (i : P) (h : Hessian P) (hi : i∈S.pending) (hh : h∈S.hessians) :
      Step S (hitHessian S i h)

lemma Step.degree_eq {S T : State P} (h : Step S T) : T.degree=S.degree := by
  cases h with
  | primary i j hi hij => exact hitPrimary_degree S hi
  | pair i j hi hj hij => exact pair_degree S hi hj hij
  | hessian i h hi hh => exact hitHessian_degree S hi hh

omit [Fintype P] in
lemma Step.pending_lt {S T : State P} (h : Step S T) : T.pending.card<S.pending.card := by
  cases h with
  | primary i j hi hij => exact Finset.card_erase_lt_of_mem hi
  | pair i j hi hj hij =>
    exact (Finset.card_erase_le).trans_lt (Finset.card_erase_lt_of_mem hi)
  | hessian i h hi hh => exact Finset.card_erase_lt_of_mem hi

theorem reachable_degree {S : State P} (h : Relation.ReflTransGen Step initial S) :
    S.degree=Fintype.card P := by
  induction h with
  | refl => exact initial_degree
  | tail hstep h ih => exact h.degree_eq.trans ih

def State.good (S : State P) : Prop :=
  (∀j i,i∈S.derivatives j → i≠j) ∧ ∀h∈S.hessians,h.first≠h.second

lemma initial_good : (initial (P:=P)).good := by simp [State.good,initial]

omit [Fintype P] in
lemma Step.good {S T : State P} (ht : Step S T) (hS : S.good) : T.good := by
  cases ht with
  | primary i j hi hij =>
    constructor
    · intro k a ha
      change a∈Function.update S.derivatives j (i::S.derivatives j) k at ha
      by_cases hk : k=j
      · subst k
        simp only [Function.update_self,List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hij
        · exact hS.1 j a ha
      · rw [Function.update_of_ne hk] at ha
        exact hS.1 k a ha
    · exact hS.2
  | pair i j hi hj hij =>
    refine ⟨hS.1,?_⟩
    intro h hh
    change h∈(⟨i,j,[]⟩:Hessian P)::ₘS.hessians at hh
    rcases Multiset.mem_cons.mp hh with he | hh
    · subst h; exact hij
    · exact hS.2 h hh
  | hessian i h hi hh =>
    refine ⟨hS.1,?_⟩
    intro g hg
    change g∈h.hit i::ₘS.hessians.erase h at hg
    rcases Multiset.mem_cons.mp hg with he | hg
    · subst g; exact hS.2 h hh
    · exact hS.2 g (Multiset.mem_of_mem_erase hg)

theorem reachable_good {S : State P} (h : Relation.ReflTransGen Step initial S) : S.good := by
  induction h with
  | refl => exact initial_good
  | tail hstep h ih => exact h.good ih

lemma degree_identity (S : State P) (hp : S.pending=∅) :
    S.degree=(∑j,(S.derivatives j).length)+
      (S.hessians.map (fun h => h.extra.length)).sum+2*S.hessians.card := by
  have hm : (S.hessians.map Hessian.degree).sum=
      (S.hessians.map (fun h => h.extra.length)).sum+2*S.hessians.card := by
    induction S.hessians using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Hessian.degree]
      omega
  simp only [State.degree,hp,Finset.card_empty,zero_add,hm]
  omega

theorem terminal_degree_count {S : State P}
    (h : Relation.ReflTransGen Step initial S) (hp : S.pending=∅) :
    (∑j,(S.derivatives j).length)+(S.hessians.map (fun h => h.extra.length)).sum+
      2*S.hessians.card=Fintype.card P := by
  rw [←degree_identity S hp]
  exact reachable_degree h

def branches (S : State P) (i : P) : List (State P) :=
  ((Finset.univ.erase i).toList.map (hitPrimary S i))++
  ((S.pending.erase i).toList.map (pair S i))++
  (S.hessians.toList.map (hitHessian S i))

lemma branches_step (S : State P) {i : P} (hi : i∈S.pending) {T : State P}
    (hT : T∈branches S i) : Step S T := by
  simp only [branches,List.mem_append,List.mem_map] at hT
  rcases hT with (⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩) | ⟨h,hh,rfl⟩
  · have hj' := Finset.mem_erase.mp (Finset.mem_toList.mp hj)
    exact Step.primary S i j hi hj'.1.symm
  · have hj' := Finset.mem_erase.mp (Finset.mem_toList.mp hj)
    exact Step.pair S i j hi hj'.2 hj'.1.symm
  · exact Step.hessian S i h hi (Multiset.mem_toList.mp hh)

omit [Fintype P] in
lemma hessian_degree_lower (S : State P) :
    2*S.hessians.card≤(S.hessians.map Hessian.degree).sum := by
  induction S.hessians using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Hessian.degree]
    omega

lemma branches_length (S : State P) (i : P) (hdeg : S.degree=Fintype.card P) :
    (branches S i).length≤3*Fintype.card P := by
  simp only [branches,List.length_append,List.length_map,Finset.length_toList,Multiset.length_toList]
  have hp : (Finset.univ.erase i).card≤Fintype.card P := by simp
  have hd : S.pending.card≤Fintype.card P := Finset.card_le_univ _
  have hp' : (S.pending.erase i).card≤S.pending.card := Finset.card_erase_le
  have hh := hessian_degree_lower S
  unfold State.degree at hdeg
  omega

def expand : ℕ → State P → List (State P)
  | 0,S => [S]
  | n+1,S => if hp : S.pending.Nonempty then
      (branches S (Classical.choose hp)).flatMap (expand n)
    else [S]

lemma mem_expand_reachable {n : ℕ} {S T : State P} (h : T∈expand n S) :
    Relation.ReflTransGen Step S T := by
  induction n generalizing S with
  | zero =>
    simp only [expand,List.mem_singleton] at h
    subst T
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [expand] at h
    split_ifs at h with hp
    · obtain ⟨U,hU,hT⟩ := List.mem_flatMap.mp h
      exact (Relation.ReflTransGen.single (branches_step S (Classical.choose_spec hp) hU)).trans (ih hT)
    · simp only [List.mem_singleton] at h
      subst T
      exact Relation.ReflTransGen.refl

lemma mem_expand_terminal {n : ℕ} {S T : State P} (hn : S.pending.card≤n)
    (h : T∈expand n S) : T.pending=∅ := by
  induction n generalizing S with
  | zero =>
    simp only [expand,List.mem_singleton] at h
    subst T
    exact Finset.card_eq_zero.mp (by omega)
  | succ n ih =>
    simp only [expand] at h
    split_ifs at h with hp
    · obtain ⟨U,hU,hT⟩ := List.mem_flatMap.mp h
      have hh := (branches_step S (Classical.choose_spec hp) hU).pending_lt
      exact ih (by omega) hT
    · simp only [List.mem_singleton] at h
      subst T
      exact Finset.not_nonempty_iff_eq_empty.mp hp

omit [Fintype P] [DecidableEq P] in
lemma list_sum_constant {α : Type*} (L : List α) (b : ℕ) :
    (L.map (fun _ => b)).sum=L.length*b := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

lemma expand_length (n : ℕ) (S : State P) (hdeg : S.degree=Fintype.card P) :
    (expand n S).length≤(3*Fintype.card P+1)^n := by
  induction n generalizing S with
  | zero => simp [expand]
  | succ n ih =>
    simp only [expand]
    split_ifs with hp
    · rw [List.length_flatMap]
      have h₁ : ((branches S (Classical.choose hp)).map (fun U => (expand n U).length)).sum≤
          ((branches S (Classical.choose hp)).map (fun _ => (3*Fintype.card P+1)^n)).sum := by
        apply List.sum_le_sum
        intro U hU
        exact ih U ((branches_step S (Classical.choose_spec hp) hU).degree_eq.trans hdeg)
      have h₂ := branches_length S (Classical.choose hp) hdeg
      have hpow := Nat.mul_le_mul_right ((3*Fintype.card P+1)^n) h₂
      change ((branches S (Classical.choose hp)).map (fun U => (expand n U).length)).sum≤
        ((branches S (Classical.choose hp)).map (fun _ => (3*Fintype.card P+1)^n)).sum at h₁
      rw [list_sum_constant] at h₁
      rw [pow_succ]
      exact h₁.trans (hpow.trans (by
        rw [Nat.mul_comm ((3*Fintype.card P+1)^n)]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)))
    · simp only [List.length_singleton]
      exact Nat.one_le_pow _ _ (by omega)

theorem full_expansion_bookkeeping :
    (expand (Fintype.card P) (initial (P:=P))).length≤
      (3*Fintype.card P+1)^(Fintype.card P) ∧
    ∀S∈expand (Fintype.card P) (initial (P:=P)),S.pending=∅ ∧ S.good ∧
      (∑j,(S.derivatives j).length)+(S.hessians.map (fun h => h.extra.length)).sum+
      2*S.hessians.card=Fintype.card P := by
  refine ⟨expand_length _ _ initial_degree,fun S hS => ?_⟩
  have hr := mem_expand_reachable hS
  have ht := mem_expand_terminal (by simp [initial]) hS
  exact ⟨ht,reachable_good hr,terminal_degree_count hr ht⟩
end LogConcaveSampling.AdjointRemoval

end
section
namespace LogConcaveSampling.TraceWords
open Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def paths : ℕ → I → I → List (List (I×J))
  | 0,i,k => if i=k then [[]] else []
  | n+1,i,k => (Finset.univ.toList).flatMap (fun l : I =>
      (Finset.univ.toList).flatMap (fun j : J =>
        (paths n l k).map (fun w => (i,j)::(l,j)::w)))

def eval (A : Matrix I J ℝ) (w : List (I×J)) : ℝ :=
  (w.map (fun ij => A ij.1 ij.2)).prod

def closed (n : ℕ) : List (List (I×J)) :=
  (Finset.univ.toList).flatMap (fun i : I => paths n i i)

lemma sum_flatMap {α β : Type*} (L : List α) (f : α → List β) (g : β → ℝ) :
    ((L.flatMap f).map g).sum=(L.map (fun a => ((f a).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma sum_univ_list {α : Type*} [Fintype α] (f : α → ℝ) :
    (Finset.univ.toList.map f).sum=∑a,f a := by simp

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma eval_cons (A : Matrix I J ℝ) (a : I×J) (w : List (I×J)) :
    eval A (a::w)=A a.1 a.2*eval A w := by simp [eval]

omit [DecidableEq J] in
lemma paths_length {n : ℕ} {i k : I} {w : List (I×J)} (hw : w∈paths n i k) :
    w.length=2*n := by
  induction n generalizing i k w with
  | zero =>
    simp only [paths] at hw
    split_ifs at hw with he
    · simp only [List.mem_singleton] at hw
      subst w
      rfl
    · simp at hw
  | succ n ih =>
    simp only [paths,List.mem_flatMap,List.mem_map] at hw
    obtain ⟨l,_,j,_,v,hv,rfl⟩ := hw
    simp only [List.length_cons,ih hv]
    omega

omit [DecidableEq J] in
lemma closed_length {n : ℕ} {w : List (I×J)} (hw : w∈closed (I:=I) (J:=J) n) :
    w.length=2*n := by
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hw
  exact paths_length hi

omit [DecidableEq J] in

theorem power_entry (A : Matrix I J ℝ) (n : ℕ) (i k : I) :
    ((A*A.transpose)^n) i k=((paths n i k).map (eval A)).sum := by
  induction n generalizing i k with
  | zero =>
    simp only [pow_zero,Matrix.one_apply,paths]
    split_ifs <;> simp [eval]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    simp only [paths,sum_flatMap,List.map_map,Function.comp_def,eval_cons]
    rw [sum_univ_list]
    apply Finset.sum_congr rfl
    intro l _
    rw [Matrix.mul_apply,Finset.sum_mul,sum_univ_list]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.transpose_apply,ih]
    have hh (L : List (List (I×J))) :
        (L.map (fun w => A i j*(A l j*eval A w))).sum=
          A i j*A l j*(L.map (eval A)).sum := by
      induction L with
      | nil => simp
      | cons w L ih => simp only [List.map_cons,List.sum_cons,ih]; ring
    exact (hh _).symm

omit [DecidableEq J] in

theorem trace_power (A : Matrix I J ℝ) (n : ℕ) :
    ((A*A.transpose)^n).trace=((closed (I:=I) (J:=J) n).map (eval A)).sum := by
  simp only [closed,sum_flatMap,sum_univ_list,Matrix.trace,Matrix.diag,power_entry]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma eval_eq_prod_get (A : Matrix I J ℝ) (w : List (I×J)) :
    eval A w=∏p : Fin w.length,A (w.get p).1 (w.get p).2 := by
  unfold eval
  rw [←List.prod_ofFn]
  congr 1
  simpa only [List.map_ofFn,Function.comp_def,List.get_eq_getElem] using
    (congrArg (List.map (fun ij : I×J => A ij.1 ij.2)) (List.ofFn_getElem (xs:=w))).symm
end LogConcaveSampling.TraceWords

end
section
open MeasureTheory
open scoped ENNReal NNReal

namespace LogConcaveSampling.NetworkMoments

theorem lintegral_prod_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → Ω → ℝ≥0∞} {M : ι → ℝ≥0∞}
    (hf : ∀i∈s,AEMeasurable (f i) μ)
    (hm : ∀i∈s,(∫⁻x,(f i x)^s.card ∂μ)≤(M i)^s.card) :
    (∫⁻x,∏i∈s,f i x ∂μ)≤∏i∈s,M i := by
  have hc : 0<(s.card:ℝ) := by exact_mod_cast hs.card_pos
  have hp : (∑_i∈s,1/(s.card:ℝ))=1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hc.ne'
  have hr (z : ℝ≥0∞) : (z^s.card)^(1/(s.card:ℝ))=z := by
    rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul]
    simp only [mul_one_div_cancel hc.ne',ENNReal.rpow_one]
  have hh := ENNReal.lintegral_prod_norm_pow_le s
    (fun i hi => (hf i hi).pow_const s.card) hp
    (fun _ _ => (div_nonneg (by norm_num) hc.le))
  simp only [hr] at hh
  calc
    (∫⁻x,∏i∈s,f i x ∂μ)≤∏i∈s,(∫⁻x,(f i x)^s.card ∂μ)^(1/(s.card:ℝ)) := hh
    _ ≤ ∏i∈s,((M i)^s.card)^(1/(s.card:ℝ)) := by
      apply Finset.prod_le_prod
      intro i hi
      exact ENNReal.rpow_le_rpow (hm i hi) (by positivity)
    _ = ∏i∈s,M i := by simp only [hr]

theorem lintegral_prod_norm_le
    {Ω ι : Type*} {E : ι → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [∀i,NormedAddCommGroup (E i)] (s : Finset ι) (hs : s.Nonempty)
    {f : ∀i,Ω → E i} {M : ι → ℝ≥0∞}
    (hf : ∀i∈s,AEStronglyMeasurable (f i) μ)
    (hm : ∀i∈s,(∫⁻x,(‖f i x‖ₑ)^s.card ∂μ)≤(M i)^s.card) :
    (∫⁻x,∏i∈s,‖f i x‖ₑ ∂μ)≤∏i∈s,M i :=
  lintegral_prod_le s hs (fun i hi => (hf i hi).enorm) hm

end LogConcaveSampling.NetworkMoments

end
end UpperProof
end
end
end

end OAI
