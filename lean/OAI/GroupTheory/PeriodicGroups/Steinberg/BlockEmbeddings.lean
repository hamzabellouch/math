import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.KernelRelations

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def blockIndex (i : Fin n) (s : Fin N) : Fin (n*N) := finProdFinEquiv (i,s)
lemma blockIndex_ne {i j : Fin n} (h : i≠j) (s t : Fin N) : blockIndex i s≠blockIndex j t := by
  intro he
  exact h (congrArg Prod.fst (finProdFinEquiv.injective he))
def blockPosition (p : Root n) (st : Fin N × Fin N) : Root (n*N) :=
  ⟨blockIndex p.row st.1,blockIndex p.col st.2,blockIndex_ne p.ne _ _⟩
lemma block_factors_commute (p : Root n) (st uv : Fin N×Fin N) (a b : R) :
    Commute (Steinberg.x (blockPosition p st) a) (Steinberg.x (blockPosition p uv) b) := by
  apply Steinberg.x_commute
  · exact blockIndex_ne p.ne.symm _ _
  · exact blockIndex_ne p.ne _ _
def blockHom (p : Root n) : (Fin N×Fin N → Multiplicative R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod (fun st=>rootHom (blockPosition p st))
    (fun st uv _ a b=>block_factors_commute p st uv a.toAdd b.toAdd)

def blockRoot (p : Root n) (A : Matrix (Fin N) (Fin N) R) : Steinberg (n*N) R :=
  blockHom p (fun st=>Multiplicative.ofAdd (A st.1 st.2))
lemma blockRoot_zero (p : Root n) : blockRoot p (0 : Matrix (Fin N) (Fin N) R)=1 :=
  map_one (blockHom p)
lemma blockRoot_add (p : Root n) (A B : Matrix (Fin N) (Fin N) R) :
    blockRoot p (A+B)=blockRoot p A*blockRoot p B :=
  map_mul (blockHom p) _ _
lemma blockRoot_single (p : Root n) (s t : Fin N) (a : R) :
    blockRoot p (Matrix.single s t a)=Steinberg.x (blockPosition p (s,t)) a := by
  have he : (fun st : Fin N×Fin N=>Multiplicative.ofAdd ((Matrix.single s t a) st.1 st.2))=
      Pi.mulSingle (s,t) (Multiplicative.ofAdd a) := by
    funext st
    rcases st with ⟨u,v⟩
    by_cases hs : s=u <;> by_cases ht : t=v <;>
      simp_all [Matrix.single,Prod.ext_iff,eq_comm]
  rw [blockRoot,he]
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _
lemma blockRoot_commute (p q : Root n) (h₁ : p.col≠q.row) (h₂ : p.row≠q.col)
    (A B : Matrix (Fin N) (Fin N) R) : Commute (blockRoot p A) (blockRoot q B) := by
  apply MonoidHom.commute_noncommPiCoprod
  intro st a
  apply Commute.symm
  apply MonoidHom.commute_noncommPiCoprod
  intro uv b
  apply Steinberg.x_commute
  · exact blockIndex_ne h₂.symm _ _
  · exact blockIndex_ne h₁.symm _ _

lemma blockRoot_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (A B : Matrix (Fin N) (Fin N) R) :
    bracket (blockRoot ⟨i,j,hij⟩ A) (blockRoot ⟨j,k,hjk⟩ B)=blockRoot ⟨i,k,hik⟩ (A*B) := by
  induction A using Matrix.induction_on' with
  | h_zero => simp [blockRoot_zero,bracket]
  | h_add A A' hA hA' =>
    rw [blockRoot_add,CommutatorCalculus.mul_left,hA,hA',Matrix.add_mul]
    have hc := blockRoot_commute ⟨i,j,hij⟩ ⟨i,k,hik⟩ hij.symm hik A (A'*B)
    rw [CommutatorCalculus.conj_of_commute hc,←blockRoot_add,add_comm]
  | h_std_basis s t a =>
    induction B using Matrix.induction_on' with
    | h_zero => simp [blockRoot_zero,bracket]
    | h_add B B' hB hB' =>
      rw [blockRoot_add,CommutatorCalculus.mul_right,hB,hB',Matrix.mul_add]
      have hc := blockRoot_commute ⟨j,k,hjk⟩ ⟨i,k,hik⟩ hik.symm hjk
        B (Matrix.single s t a*B')
      calc
        _ = blockRoot ⟨i,k,hik⟩ (Matrix.single s t a*B) *
          (blockRoot ⟨j,k,hjk⟩ B*blockRoot ⟨i,k,hik⟩ (Matrix.single s t a*B')*(blockRoot ⟨j,k,hjk⟩ B)⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [CommutatorCalculus.conj_of_commute hc,←blockRoot_add]
    | h_std_basis u v b =>
      rw [blockRoot_single,blockRoot_single]
      by_cases htu : t=u
      · subst u
        rw [Matrix.single_mul_single_same,blockRoot_single]
        exact Steinberg.x_mul _ _ _ (blockIndex_ne hij s t) (blockIndex_ne hjk t v) (blockIndex_ne hik s v) a b
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ htu,blockRoot_zero]
        apply (bracket_eq_one_iff _ _).mpr
        apply Steinberg.x_commute
        · intro he
          exact htu (congrArg Prod.snd (finProdFinEquiv.injective he))
        · exact blockIndex_ne hik s v

def blockMap : Steinberg n (Matrix (Fin N) (Fin N) R) →* Steinberg (n*N) R :=
  Steinberg.lift blockRoot (fun p A B=>blockRoot_add p A B)
    (fun p q h₁ h₂ A B=>blockRoot_commute p q h₁ h₂ A B)
    (fun i j k hij hjk hik A B=>blockRoot_mul i j k hij hjk hik A B)
@[simp] lemma blockMap_x (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    blockMap (Steinberg.x p A)=blockRoot p A := Steinberg.lift_x _ _ _ _ p A
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def flattenRing : Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) R) ≃+* Matrix (Fin (n*N)) (Fin (n*N)) R :=
  (Matrix.compRingEquiv (Fin n) (Fin N) R).trans (Matrix.reindexRingEquiv R finProdFinEquiv)
lemma flatten_single (i j : Fin n) (s t : Fin N) (a : R) :
    flattenRing (Matrix.single i j (Matrix.single s t a))=Matrix.single (blockIndex i s) (blockIndex j t) a := by
  ext u v
  obtain ⟨⟨i',s'⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j',t'⟩,rfl⟩ := finProdFinEquiv.surjective v
  simp only [flattenRing,RingEquiv.trans_apply,Matrix.coe_reindexRingEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.compRingEquiv_apply,Matrix.comp_apply]
  by_cases hi : i=i' <;> by_cases hj : j=j' <;> by_cases hs : s=s' <;> by_cases ht : t=t' <;>
    simp_all [Matrix.single,blockIndex,Prod.ext_iff]

lemma representation_blockRoot (p : Root n) (A : Matrix (Fin N) (Fin N) R) :
    Elementary.representation (blockRoot p A)=Units.map flattenRing.toMonoidHom (Elementary.e p A) := by
  induction A using Matrix.induction_on' with
  | h_zero => simp [blockRoot_zero]
  | h_add A B hA hB => rw [blockRoot_add,map_mul,hA,hB,Elementary.e_add,map_mul]
  | h_std_basis s t a =>
    rw [blockRoot_single,Elementary.representation_x]
    apply Units.ext
    change 1+Matrix.single (blockIndex p.row s) (blockIndex p.col t) a=
      flattenRing (1+Matrix.single p.row p.col (Matrix.single s t a))
    rw [map_add,map_one,flatten_single]
lemma block_representation :
    Elementary.representation.comp (blockMap (n:=n) (N:=N) (R:=R))=
      (Units.map flattenRing.toMonoidHom).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p A
  simp only [MonoidHom.comp_apply,blockMap_x,Elementary.representation_x,representation_blockRoot]
lemma blockMap_kernel (g : Steinberg n (Matrix (Fin N) (Fin N) R))
    (hg : Elementary.representation g=1) : Elementary.representation (blockMap g)=1 := by
  have he := DFunLike.congr_fun (block_representation (n:=n) (N:=N) (R:=R)) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]

def rowFixed (i : Fin n) : Subgroup (Matrix (Fin n) (Fin n) R)ˣ where
  carrier := {u | ∀j,u.val i j=(1 : Matrix (Fin n) (Fin n) R) i j}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv j
    change (u.val*v.val) i j=_
    change ∑ z, u.val i z*v.val z j=(1 : Matrix (Fin n) (Fin n) R) i j
    calc
      _ = ∑ z, (1 : Matrix (Fin n) (Fin n) R) i z*v.val z j :=
        Finset.sum_congr rfl (fun z _=>congrArg (fun a : R=>a*v.val z j) (hu z))
      _ = v.val i j := by simp [Matrix.one_apply]
      _ = _ := hv j
  inv_mem' := by
    intro u hu j
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) R=>M i j) u.val_inv
    change (u.val*u.inv) i j=_ at he
    change ∑ z,u.val i z*u.inv z j=(1 : Matrix (Fin n) (Fin n) R) i j at he
    calc
      _ = ∑ z,(1 : Matrix (Fin n) (Fin n) R) i z*u.inv z j := by simp [Matrix.one_apply]
      _ = ∑ z,u.val i z*u.inv z j :=
        Finset.sum_congr rfl (fun z _=>congrArg (fun a : R=>a*u.inv z j) (hu z).symm)
      _ = _ := he
lemma root_rowFixed (i : Fin n) (p : Root n) (h : p.row≠i) (a : R) :
    Elementary.representation (Steinberg.x p a)∈rowFixed i := by
  intro j
  simp [Elementary.representation_x,Elementary.coe_e,Matrix.single,h]
lemma strip_eq_one_of_rows (H L : Finset (Fin n)) (hd : Disjoint H L)
    {g : Steinberg n R} (hg : g∈Strip H L hd)
    (hrows : ∀i∈H,Elementary.representation g∈rowFixed i) : g=1 := by
  obtain ⟨A,rfl⟩ := strip_le_range H L hd hg
  have hA : A=1 := by
    funext p
    have he := hrows p.1.val p.1.property p.2.val
    rw [←MonoidHom.comp_apply,representation_rectRoot] at he
    change (1+rectMatrix H L A) p.1.val p.2.val=(1 : Matrix (Fin n) (Fin n) R) p.1.val p.2.val at he
    rw [Matrix.add_apply,rectMatrix_entry] at he
    apply Multiplicative.toAdd.injective
    exact add_left_cancel (he.trans (add_zero _).symm)
  rw [hA,map_one]

lemma right_conjugate_strip_root (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈L) (hc : p.col∈L) (a : R)
    (q : RectIndex H L) (b : R) :
    Steinberg.x p a*Steinberg.x (rectPosition H L hd q) b*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have hcol : p.col≠q.1.val := fun he=>Finset.disjoint_left.mp hd q.1.property (he ▸ hc)
  by_cases he : p.row=q.2.val
  · have hp : p=⟨q.2.val,p.col,he ▸ p.ne⟩ := by cases p;cases he;rfl
    rw [hp]
    dsimp only [rectPosition]
    rw [Steinberg.conjugate_reverse q.1.val q.2.val p.col (rectPosition H L hd q).ne (he ▸ p.ne) hcol.symm b a]
    apply (Strip H L hd).mul_mem
    · exact Subgroup.subset_closure ⟨(q.1,⟨p.col,hc⟩),-(b*a),rfl⟩
    · exact Subgroup.subset_closure ⟨q,b,rfl⟩
  · rw [Steinberg.conjugate_commute p (rectPosition H L hd q) hcol he]
    exact Subgroup.subset_closure ⟨q,b,rfl⟩
lemma right_conjugate_strip (H L : Finset (Fin n)) (hd : Disjoint H L)
    (p : Root n) (hr : p.row∈L) (hc : p.col∈L) (a : R)
    {g : Steinberg n R} (hg : g∈Strip H L hd) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈Strip H L hd := by
  have Hle : Strip H L hd ≤ (Strip H L hd).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,rfl⟩
    exact right_conjugate_strip_root H L hd p hr hc a q b
  exact Hle hg

def triangular (height : Fin n→ℕ) (k : ℕ) : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃(p : Root n)(a : R),k≤height p.row ∧ height p.row<height p.col ∧ g=Steinberg.x p a}
def layer (height : Fin n→ℕ) (k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i=>height i=k)
def above (height : Fin n→ℕ) (k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i=>k<height i)
lemma layer_above_disjoint (height : Fin n→ℕ) (k : ℕ) : Disjoint (layer height k) (above height k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [layer,above,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  omega
lemma deeper_normalizes_strip (height : Fin n→ℕ) (k : ℕ) :
    triangular (R:=R) height (k+1)≤Subgroup.normalizer
      (Strip (layer height k) (above height k) (layer_above_disjoint height k) (R:=R) : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hk,hp,rfl⟩
  have hr : p.row∈above height k := by simp [above];omega
  have hc : p.col∈above height k := by simp [above];omega
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact right_conjugate_strip _ _ _ p hr hc a
  · intro hx
    have hx' := right_conjugate_strip _ _ (layer_above_disjoint height k) p hr hc (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hx'
lemma deeper_fixes_layer (height : Fin n→ℕ) (k : ℕ) (i : Fin n) (hi : i∈layer height k) :
    triangular (R:=R) height (k+1)≤(rowFixed i).comap Elementary.representation := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hk,hp,rfl⟩
  apply root_rowFixed
  intro he
  simp only [layer,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  rw [he,hi] at hk
  omega
lemma triangular_split (height : Fin n→ℕ) (k : ℕ) {g : Steinberg n R}
    (hg : g∈triangular height k) :
    ∃a∈Strip (layer height k) (above height k) (layer_above_disjoint height k),
      ∃b∈triangular height (k+1),g=a*b := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨p,a,hk,hp,rfl⟩ := hg
    by_cases he : height p.row=k
    · refine ⟨Steinberg.x p a,?_,1,Subgroup.one_mem _,(mul_one _).symm⟩
      apply Subgroup.subset_closure
      have hr : p.row∈layer height k := by simp [layer,he]
      have hc : p.col∈above height k := by simp [above];omega
      exact ⟨(⟨p.row,hr⟩,⟨p.col,hc⟩),a,by congr⟩
    · refine ⟨1,Subgroup.one_mem _,Steinberg.x p a,?_,(one_mul _).symm⟩
      exact Subgroup.subset_closure ⟨p,a,by omega,hp,rfl⟩
  | one => exact ⟨1,Subgroup.one_mem _,1,Subgroup.one_mem _,(one_mul _).symm⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a,ha,b,hb,rfl⟩ := ihx
    obtain ⟨c,hc,d,hd,rfl⟩ := ihy
    have hbc : b*c*b⁻¹∈Strip (layer height k) (above height k) (layer_above_disjoint height k) :=
      (Subgroup.mem_normalizer_iff.mp (deeper_normalizes_strip height k hb) c).mp hc
    exact ⟨a*(b*c*b⁻¹),Subgroup.mul_mem _ ha hbc,b*d,Subgroup.mul_mem _ hb hd,by simp [mul_assoc]⟩
  | inv x hx ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := ih
    have hbi := (triangular (R:=R) height (k+1)).inv_mem hb
    have hai := (Strip (layer height k) (above height k) (layer_above_disjoint height k)).inv_mem ha
    have hconj : b⁻¹*a⁻¹*b∈Strip (layer height k) (above height k) (layer_above_disjoint height k) := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (deeper_normalizes_strip height k hbi) a⁻¹).mp hai
    exact ⟨b⁻¹*a⁻¹*b,hconj,b⁻¹,hbi,by simp [mul_assoc]⟩
lemma triangular_faithful_aux (height : Fin n→ℕ) (d k : ℕ)
    (hbound : ∀i,height i<k+d) {g : Steinberg n R}
    (hg : g∈triangular height k) (hmat : Elementary.representation g=1) : g=1 := by
  induction d generalizing k g with
  | zero =>
    have hbot : triangular (R:=R) height k≤⊥ := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨p,a,hk,hp,rfl⟩
      have hb := hbound p.row
      omega
    exact (Subgroup.mem_bot.mp (hbot hg))
  | succ d ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := triangular_split height k hg
    have he : a=1 := by
      apply strip_eq_one_of_rows _ _ (layer_above_disjoint height k) ha
      intro i hi
      have hbi := deeper_fixes_layer (R:=R) height k i hi ((triangular height (k+1)).inv_mem hb)
      have hab : Elementary.representation a=Elementary.representation b⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left (by simpa only [map_mul] using hmat)
      rw [hab]
      exact hbi
    rw [he,one_mul] at hmat ⊢
    apply ih (k+1) _ hb hmat
    intro i
    have h := hbound i
    omega

theorem triangular_faithful (height : Fin n→ℕ) (B : ℕ) (hbound : ∀i,height i<B)
    {g : Steinberg n R} (hg : g∈triangular height 0)
    (hmat : Elementary.representation g=1) : g=1 :=
  triangular_faithful_aux height B 0 (by simpa only [zero_add] using hbound) hg hmat
lemma level_conjugate_triangular_root (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R)
    (q : Root n) (hqk : k≤height q.row) (hq : height q.row<height q.col) (b : R) :
    Steinberg.x p a*Steinberg.x q b*(Steinberg.x p a)⁻¹∈triangular height k := by
  by_cases hc : p.col=q.row
  · have hjk : p.col≠q.col := hc ▸ q.ne
    have hik : p.row≠q.col := by
      intro he
      have heh := congrArg height he
      rw [hc] at hp
      omega
    have hqeq : q=⟨p.col,q.col,hjk⟩ := by cases q;cases hc;rfl
    rw [hqeq,Steinberg.conjugate_chain p.row p.col q.col p.ne hjk hik a b]
    apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      exact ⟨⟨p.row,q.col,hik⟩,a*b,by rw [hp,hc];exact hqk,by rw [hp,hc];exact hq,rfl⟩
    · exact Subgroup.subset_closure ⟨⟨p.col,q.col,hjk⟩,b,by simpa only [hc] using hqk,by simpa only [hc] using hq,rfl⟩
  · by_cases hr : p.row=q.col
    · have hij : q.row≠p.row := hr ▸ q.ne
      have hik : q.row≠p.col := by
        intro he
        have heh := congrArg height he
        rw [hr] at hp
        omega
      have hqeq : q=⟨q.row,p.row,hij⟩ := by cases q;cases hr;rfl
      rw [hqeq,Steinberg.conjugate_reverse q.row p.row p.col hij p.ne hik b a]
      apply Subgroup.mul_mem
      · apply Subgroup.subset_closure
        refine ⟨⟨q.row,p.col,hik⟩,-(b*a),hqk,?_,rfl⟩
        rw [←hp,hr]
        exact hq
      · exact Subgroup.subset_closure ⟨⟨q.row,p.row,hij⟩,b,hqk,by simpa only [hr] using hq,rfl⟩
    · rw [Steinberg.conjugate_commute p q hc hr]
      exact Subgroup.subset_closure ⟨q,b,hqk,hq,rfl⟩
lemma level_conjugate_triangular (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R)
    {g : Steinberg n R} (hg : g∈triangular height k) :
    Steinberg.x p a*g*(Steinberg.x p a)⁻¹∈triangular height k := by
  have H : triangular (R:=R) height k≤(triangular height k).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨q,b,hqk,hq,rfl⟩
    exact level_conjugate_triangular_root height k p hp a q hqk hq b
  exact H hg

theorem level_root_normalizes (height : Fin n→ℕ) (k : ℕ)
    (p : Root n) (hp : height p.row=height p.col) (a : R) :
    Steinberg.x p a∈Subgroup.normalizer (triangular (R:=R) height k : Set (Steinberg n R)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact level_conjugate_triangular height k p hp a
  · intro hx
    have hx' := level_conjugate_triangular height k p hp (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hx'
end
end SourceBurnside.Kernel

namespace SourceBurnside.Steinberg
variable {n : ℕ} {R G : Type*} [Ring R] [Group G]
lemma hom_images_commute (f g : Steinberg n R →* G)
    (h : ∀p q a b,Commute (f (x p a)) (g (x q b))) (u v : Steinberg n R) :
    Commute (f u) (g v) := by
  have hx (p : Root n) (a : R) : Commute (f (x p a)) (g v) := by
    have he : (MulAut.conj (f (x p a))).toMonoidHom.comp g=g := by
      apply hom_ext
      intro q b
      exact CommutatorCalculus.conj_of_commute (h p q a b)
    have hv := DFunLike.congr_fun he v
    change f (x p a)*g v*(f (x p a))⁻¹=g v at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  have he : (MulAut.conj (g v)).toMonoidHom.comp f=f := by
    apply hom_ext
    intro p a
    exact CommutatorCalculus.conj_of_commute (hx p a).symm
  have hu := DFunLike.congr_fun he u
  change g v*f u*(g v)⁻¹=f u at hu
  exact (show Commute (g v) (f u) from mul_inv_eq_iff_eq_mul.mp hu).symm
end SourceBurnside.Steinberg
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
lemma blockIndex_ne_inner (i j : Fin n) {s t : Fin N} (h : s≠t) : blockIndex i s≠blockIndex j t := by
  intro he
  exact h (congrArg Prod.snd (finProdFinEquiv.injective he))
def copyMap (s : Fin N) : Steinberg n R →* Steinberg (n*N) R :=
  Steinberg.coordinateMap (fun i=>blockIndex i s)
    (fun _row _col he=>congrArg Prod.fst (finProdFinEquiv.injective he))
@[simp] lemma copyMap_x (s : Fin N) (p : Root n) (a : R) :
    copyMap s (Steinberg.x p a)=Steinberg.x (blockPosition p (s,s)) a := rfl
lemma copy_commute {s t : Fin N} (h : s≠t) (u v : Steinberg n R) :
    Commute (copyMap s u) (copyMap t v) := by
  apply Steinberg.hom_images_commute
  intro p q a b
  rw [copyMap_x,copyMap_x]
  apply Steinberg.x_commute
  · exact blockIndex_ne_inner _ _ h
  · exact blockIndex_ne_inner _ _ h
def copyFamily : (Fin N→Steinberg n R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod copyMap (fun _ _ h u v=>copy_commute h u v)

def diagonalCopy : Steinberg n R →* Steinberg (n*N) R where
  toFun u := copyFamily (fun _=>u)
  map_one' := map_one copyFamily
  map_mul' u v := map_mul copyFamily (fun _=>u) (fun _=>v)
def diagonalBlockHom (p : Root n) : (Fin N→Multiplicative R) →* Steinberg (n*N) R where
  toFun v := blockRoot p (Matrix.diagonal (fun s=>(v s).toAdd))
  map_one' := by simpa using blockRoot_zero (R:=R) (N:=N) p
  map_mul' u v := by
    change blockRoot p (Matrix.diagonal (fun s=>(u s).toAdd+(v s).toAdd))=_
    rw [←Matrix.diagonal_add,blockRoot_add]
def copyRoots (p : Root n) : (Fin N→Multiplicative R) →* Steinberg (n*N) R :=
  MonoidHom.noncommPiCoprod (fun s=>(copyMap s).comp (rootHom p))
    (fun _ _ h a b=>copy_commute h (rootHom p a) (rootHom p b))
lemma diagonalBlockHom_eq (p : Root n) : diagonalBlockHom (N:=N) (R:=R) p=copyRoots p := by
  apply MonoidHom.pi_ext
  intro s a
  have he : (fun t : Fin N=>((Pi.mulSingle s a : Fin N→Multiplicative R) t).toAdd)=Pi.single s a.toAdd := by
    funext t
    by_cases ht : t=s <;> simp [ht]
  change blockRoot p (Matrix.diagonal (fun t=>((Pi.mulSingle s a : Fin N→Multiplicative R) t).toAdd))=copyRoots p (Pi.mulSingle s a)
  rw [he,Matrix.diagonal_single,blockRoot_single]
  exact (MonoidHom.noncommPiCoprod_mulSingle
    (fun s=>(copyMap (n:=n) (R:=R) s).comp (rootHom p)) s a).symm
lemma diagonalCopy_x (p : Root n) (a : R) :
    diagonalCopy (N:=N) (Steinberg.x p a)=blockRoot p (Matrix.diagonal (fun _=>a)) := by
  have he := DFunLike.congr_fun (diagonalBlockHom_eq (N:=N) (R:=R) p) (fun _=>Multiplicative.ofAdd a)
  exact he.symm
def innerHeight (x : Fin (n*N)) : ℕ := (finProdFinEquiv.symm x).2.val
@[simp] lemma innerHeight_blockIndex (i : Fin n) (s : Fin N) : innerHeight (blockIndex i s)=s.val := by
  simp [innerHeight,blockIndex]
def upper : Subgroup (Steinberg (n*N) R) := triangular innerHeight 0
lemma upper_faithful {g : Steinberg (n*N) R} (hg : g∈upper) (hmat : Elementary.representation g=1) : g=1 :=
  triangular_faithful innerHeight N (fun i=>(finProdFinEquiv.symm i).2.isLt) hg hmat
lemma strict_block_mem_upper (p : Root n) (A : Matrix (Fin N) (Fin N) R)
    (hA : ∀ s t, t ≤ s → A s t = 0) : blockRoot p A∈upper := by
  change Finset.noncommProd Finset.univ
    (fun st : Fin N×Fin N=>Steinberg.x (blockPosition p st) (A st.1 st.2))
    (fun st _ uv _ _=>block_factors_commute p st uv _ _)∈upper
  apply Subgroup.noncommProd_mem
  intro st _
  by_cases ht : st.1<st.2
  · apply Subgroup.subset_closure
    refine ⟨blockPosition p st,A st.1 st.2,by omega,?_,rfl⟩
    simpa only [blockPosition,innerHeight_blockIndex] using (show st.1.val < st.2.val from ht)
  · rw [hA _ _ (le_of_not_gt ht),Steinberg.x_zero]
    exact Subgroup.one_mem _
lemma diagonalCopy_normalizes (u : Steinberg n R) :
    diagonalCopy (N:=N) u∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R)) := by
  have he : (⊤ : Subgroup (Steinberg n R))≤
      (Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))).comap diagonalCopy := by
    rw [←Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨p,a⟩,rfl⟩
    change diagonalCopy (N:=N) (Steinberg.x p a)∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))
    change Finset.noncommProd Finset.univ
      (fun s : Fin N=>copyMap s (Steinberg.x p a))
      (fun s _ t _ h=>copy_commute h _ _)∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R))
    apply Subgroup.noncommProd_mem
    intro s _
    change Steinberg.x (blockPosition p (s,s)) a∈_
    apply level_root_normalizes innerHeight 0
    simp only [blockPosition,innerHeight_blockIndex]
  exact he (Subgroup.mem_top u)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def numericMatrix (T : Matrix (Fin N) (Fin N) (ZMod 2)) : Matrix (Fin N) (Fin N) R :=
  T.map (algebraMap (ZMod 2) R)
lemma numeric_scalar_commute (T : Matrix (Fin N) (Fin N) (ZMod 2)) (a : R) :
    Commute (Matrix.scalar (Fin N) a) (numericMatrix T) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.scalar_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  exact (Algebra.commutes (T i j) a).symm

def matrixEval (T : Matrix (Fin N) (Fin N) (ZMod 2)) : Polynomial R →+* Matrix (Fin N) (Fin N) R :=
  Polynomial.eval₂RingHom' (Matrix.scalar (Fin N)) (numericMatrix T) (numeric_scalar_commute T)
def scalarEval (c : ZMod 2) : Polynomial R →+* R :=
  Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap (ZMod 2) R c)
    (fun a=>(Algebra.commutes c a).symm)
def matrixEvalRingHom (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    @RingHom (Polynomial R) (Matrix (Fin N) (Fin N) R)
      (inferInstance : Ring (Polynomial R)).toNonAssocSemiring
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun := matrixEval T
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' := map_add _
  map_mul' := map_mul _
def matrixSteinbergEval (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    Steinberg n (Polynomial R) →* Steinberg (n*N) R := blockMap.comp (Steinberg.map (matrixEvalRingHom T))
lemma matrixSteinbergEval_kernel (T : Matrix (Fin N) (Fin N) (ZMod 2))
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    Elementary.representation (matrixSteinbergEval T u)=1 := by
  exact blockMap_kernel (n:=n) (N:=N) (R:=R) _
    (Elementary.map_kernel (n:=n) (R:=Polynomial R) (S:=Matrix (Fin N) (Fin N) R) (matrixEvalRingHom T) u hu)
lemma scalarEval_kernel (c : ZMod 2) (u : Steinberg n (Polynomial R))
    (hu : Elementary.representation u=1) : Elementary.representation (Steinberg.map (scalarEval c) u)=1 :=
  Elementary.map_kernel (scalarEval c) u hu
lemma numeric_upper {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular) :
    (numericMatrix (R:=R) T).IsUpperTriangular := by
  intro i j hji
  change algebraMap (ZMod 2) R (T i j)=0
  rw [hT hji,map_zero]
omit [Algebra (ZMod 2) R] in
lemma triangular_mul_diag {A B : Matrix (Fin N) (Fin N) R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (s : Fin N) :
    (A*B) s s=A s s*B s s := by
  rw [Matrix.mul_apply,Finset.sum_eq_single s]
  · intro t _ hts
    rcases lt_or_gt_of_ne hts with hts|hst
    · rw [hA hts,zero_mul]
    · rw [hB hst,mul_zero]
  · simp
omit [Algebra (ZMod 2) R] in
lemma triangular_pow_diag {A : Matrix (Fin N) (Fin N) R} (hA : A.IsUpperTriangular)
    (m : ℕ) (s : Fin N) : (A^m) s s=(A s s)^m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,triangular_mul_diag (hA.pow m) hA,ih,pow_succ]
lemma matrixEval_upper {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular)
    (a : Polynomial R) : (matrixEval T a).IsUpperTriangular := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add];exact ha.add hb
  | monomial m a =>
    change (Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix T) (Polynomial.monomial m a)).IsUpperTriangular
    rw [Polynomial.eval₂_monomial,Matrix.scalar_apply]
    exact (Matrix.blockTriangular_diagonal _).mul ((numeric_upper hT).pow m)
lemma matrixEval_diag {T : Matrix (Fin N) (Fin N) (ZMod 2)} (hT : T.IsUpperTriangular)
    (c : ZMod 2) (hd : ∀ s,T s s=c) (a : Polynomial R) (s : Fin N) :
    matrixEval T a s s=scalarEval c a := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add,Matrix.add_apply,ha,hb]
  | monomial m a =>
    change Polynomial.eval₂ (Matrix.scalar (Fin N)) (numericMatrix T) (Polynomial.monomial m a) s s=
      Polynomial.eval₂ (RingHom.id R) (algebraMap (ZMod 2) R c) (Polynomial.monomial m a)
    rw [Polynomial.eval₂_monomial,Polynomial.eval₂_monomial,Matrix.scalar_apply,Matrix.diagonal_mul,
      triangular_pow_diag (numeric_upper hT)]
    change a*(algebraMap (ZMod 2) R (T s s))^m=a*(algebraMap (ZMod 2) R c)^m
    rw [hd]
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def scalarRingHom : @RingHom R (Matrix (Fin N) (Fin N) R)
    (inferInstance : Ring R).toNonAssocSemiring
    (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun := Matrix.scalar (Fin N)
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' := map_add _
  map_mul' := map_mul _
lemma diagonalCopy_eq : diagonalCopy (n:=n) (N:=N) (R:=R)=
    blockMap.comp (Steinberg.map scalarRingHom) := by
  apply Steinberg.hom_ext
  intro p a
  rw [diagonalCopy_x,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
  rfl
lemma diagonalCopy_kernel (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (diagonalCopy (N:=N) u)=1 := by
  rw [diagonalCopy_eq]
  exact blockMap_kernel (n:=n) (N:=N) (R:=R) _
    (Elementary.map_kernel (n:=n) (R:=R) (S:=Matrix (Fin N) (Fin N) R) scalarRingHom u hu)
variable [Algebra (ZMod 2) R]
lemma triangular_entry_split {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (p : Root n) (a : Polynomial R) :
    ∃z∈upper (n:=n) (N:=N) (R:=R),
      matrixSteinbergEval T (Steinberg.x p a)=
        diagonalCopy (N:=N) (Steinberg.map (scalarEval c) (Steinberg.x p a))*z := by
  let D : Matrix (Fin N) (Fin N) R := Matrix.diagonal (fun _=>scalarEval c a)
  let B : Matrix (Fin N) (Fin N) R := matrixEval T a-D
  refine ⟨blockRoot p B,?_,?_⟩
  · apply strict_block_mem_upper
    intro s t hts
    rcases eq_or_lt_of_le hts with he|ht
    · subst t
      simp only [B,D,Matrix.sub_apply,Matrix.diagonal_apply_eq,matrixEval_diag hT c hd,sub_self]
    · have hne : s≠t := (ne_of_lt ht).symm
      simp only [B,D,Matrix.sub_apply,matrixEval_upper hT a ht,Matrix.diagonal_apply_ne _ hne,sub_self]
  · rw [Steinberg.map_x,diagonalCopy_x]
    rw [matrixSteinbergEval,MonoidHom.comp_apply,Steinberg.map_x,blockMap_x]
    change blockRoot p (matrixEval T a)=blockRoot p D*blockRoot p B
    rw [←blockRoot_add]
    congr 1
    dsimp [B]
    abel
lemma triangular_collect {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (u : Steinberg n (Polynomial R)) :
    ∃z∈upper (n:=n) (N:=N) (R:=R),matrixSteinbergEval T u=
      diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u)*z := by
  have hu : u∈Subgroup.closure (Set.range (fun pa : Root n×Polynomial R=>Steinberg.x pa.1 pa.2)) := by
    rw [Steinberg.closure_range_x]
    exact Subgroup.mem_top u
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨⟨p,a⟩,rfl⟩:=hu
    exact triangular_entry_split hT c hd p a
  | one => exact ⟨1,Subgroup.one_mem _,by simp⟩
  | mul u v hu hv ihu ihv =>
    obtain ⟨z,hz,hez⟩:=ihu
    obtain ⟨w,hw,hew⟩:=ihv
    let d := diagonalCopy (N:=N) (Steinberg.map (scalarEval c) v)
    have hn : d⁻¹∈Subgroup.normalizer (upper (n:=n) (N:=N) (R:=R) : Set (Steinberg (n*N) R)) :=
      Subgroup.inv_mem _ (diagonalCopy_normalizes _)
    have hc : d⁻¹*z*d∈upper := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn z).mp hz
    refine ⟨(d⁻¹*z*d)*w,Subgroup.mul_mem _ hc hw,?_⟩
    simp only [map_mul,hez,hew]
    dsimp [d]
    group
  | inv u hu ihu =>
    obtain ⟨z,hz,hez⟩:=ihu
    let d := diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u)
    have hc : d*z⁻¹*d⁻¹∈upper :=
      (Subgroup.mem_normalizer_iff.mp (diagonalCopy_normalizes _) z⁻¹).mp (Subgroup.inv_mem _ hz)
    refine ⟨d*z⁻¹*d⁻¹,hc,?_⟩
    simp only [map_inv,hez]
    dsimp [d]
    group

theorem triangular_evaluation {T : Matrix (Fin N) (Fin N) (ZMod 2)}
    (hT : T.IsUpperTriangular) (c : ZMod 2) (hd : ∀s,T s s=c)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    matrixSteinbergEval T u=diagonalCopy (N:=N) (Steinberg.map (scalarEval c) u) := by
  obtain ⟨z,hz,he⟩ := triangular_collect hT c hd u
  have hf := matrixSteinbergEval_kernel (R:=R) T u hu
  have hg := diagonalCopy_kernel (N:=N) _ (scalarEval_kernel c u hu)
  have hm := congrArg Elementary.representation he
  rw [map_mul,hg,one_mul,hf] at hm
  have hz1 := upper_faithful hz hm.symm
  simpa only [hz1,mul_one] using he
end
end SourceBurnside.Kernel

end

end OAI
