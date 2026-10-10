import OAI.Combinatorics.HadwigerCounterexample.AttackCutDecomposition

namespace OAI

/-! # Cover Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

noncomputable def prj (S : Space (Vec I)) : Mat I I :=
  (proj_exists S ⊥ disjoint_bot_right).choose

theorem prj_data (S : Space (Vec I)) : ProjData S ⊥ (prj S) :=
  (proj_exists S ⊥ disjoint_bot_right).choose_spec

variable [DecidableEq I] [DecidableEq J]
def chop (S : Space (Vec I)) := 1-prj S

theorem chop_ker (S : Space (Vec I)) (x : Vec I) :
    chop S *ᵥ x=0 ↔ x∈S := by
  rw [chop,Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero]
  constructor
  · intro h; exact h.symm ▸ (prj_data S).onto x
  exact fun h => ((prj_data S).fixes x h).symm

theorem chop_colT (S : Space (Vec I)) : colSp (chop S)ᵀ=annih S := by
  have hi : colSp (chop S)ᵀ ≤annih S := (colSp_kill ..).mpr (fun x hx => by
    rw [transpose_transpose]; exact (chop_ker S x).mpr hx)
  apply Submodule.eq_of_le_of_finrank_eq hi
  have h := (chop S).mulVecLin.finrank_range_add_finrank_ker
  rw [show ker (chop S).mulVecLin=S from (by ext x; exact chop_ker S x)] at h
  change (chop S).rank + dim S = dim (Vec I) at h
  have he := annih_dim S
  rw [dim_vec,← he, add_comm] at h
  exact (Matrix.rank_transpose _).trans (Nat.add_left_cancel h)

theorem vanish_chop {S : Space (Vec I)} {T : Space (Vec J)} (M : Mat I J) :
    vanish S T M ↔ liftM (chop S) (chop T) M=0 := by
  let A := (chop S)ᵀ
  let B := (chop T)ᵀ
  have h1 : liftM (chop S) (chop T) M=pullM A B M := by
    simp only [A,B,pullM,Matrix.transpose_transpose]
  have h2 : colSp A=annih S := chop_colT _
  have h3 : colSp B=annih T := chop_colT _
  rw [h1]
  unfold vanish
  rw [←h2,←h3]
  constructor
  · intro h
    refine evmat_ext fun x y => ?_
    rw [evmat_pull, h (A *ᵥ x) ⟨_,rfl⟩ (B *ᵥ y) ⟨_,rfl⟩]
    simp [evmat]
  rintro h x ⟨x,rfl⟩ y ⟨y,rfl⟩
  rw [mulVecLin_apply,mulVecLin_apply,←evmat_pull,h]
  simp [evmat]

def chopSpace (S T : Space (Vec I)) := T.map (chop S).mulVecLin

theorem chopSpace_join (S T : Space (Vec I)) :
    S ⊔ chopSpace S T=S⊔ T := by
  classical
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rintro t ⟨x,h,rfl⟩
    rw [mulVecLin_apply,chop,Matrix.sub_mulVec,Matrix.one_mulVec]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right h)
      (Submodule.mem_sup_left ((prj_data S).onto x))
  intro x hx
  have he : x=prj S *ᵥ x+chop S *ᵥ x := by
    rw [chop,Matrix.sub_mulVec,Matrix.one_mulVec,add_sub_cancel]
  exact he.symm ▸ Submodule.add_mem_sup ((prj_data S).onto x)
    (show chop S *ᵥ x∈chopSpace S T from ⟨x,hx,rfl⟩)

theorem chopSpace_disjoint (S T : Space (Vec I)) : Disjoint S (chopSpace S T) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,y,hy,rfl⟩
  rw [mulVecLin_apply,chop,Matrix.sub_mulVec,Matrix.one_mulVec] at hx ⊢
  have hi := (prj_data S).fixes _ hx
  rw [Matrix.mulVec_sub,(prj_data S).fixes _ ((prj_data S).onto y),sub_self] at hi
  rw [←hi]; exact Submodule.zero_mem _

theorem chopSpace_rank (S T : Space (Vec I)) :
    dim S+dim (chopSpace S T) = dim (S⊔T : Submodule _ _) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (chopSpace S T)
  rw [chopSpace_join,(chopSpace_disjoint S T).eq_bot,finrank_bot,add_zero] at h
  exact h.symm

abbrev Cov (p : Shape) (N : ℕ) := Place p → Space (Vec (Fin N))
def cdSign (p : Shape) {N} (S : Cov p N) (i : Bool) :=
  ∑ e : Comp p.g,dim (S (e,i))
def cdim (p : Shape) {N} (S : Cov p N) := ∑ i : Place p,dim (S i)
theorem cdim_sign (p : Shape) {N} (S : Cov p N) :
    cdim p S=cdSign p S true+cdSign p S false := by
  simp only [cdim,cdSign,Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]

def epoch (p : Shape) {N} (x : Ambient p N) := ∑ e : Comp p.g,(x e).rank

def matter (p : Shape) {N} (x : Ambient p N) : Cov p N :=
  fun z => colSp (if z.2 then x z.1 else (x z.1)ᵀ)

theorem matter_dim (x : Ambient p N) (b : Bool) : cdSign p (matter p x) b=epoch p x :=
  Finset.sum_congr rfl fun i _ => by cases b; exact Matrix.rank_transpose _; rfl

def erased (p : Shape) {N} (S : Cov p N) : Ambient p N →ₗ[F] Ambient p N :=
  LinearMap.pi (fun i => liftM (chop (S (i,true))) (chop (S (i,false))) ∘ₗ LinearMap.proj i)

def covered (p : Shape) {N} (S : Cov p N) (x : Ambient p N) :=
  erased p S x=0

theorem covered_iff (S : Cov p N) (x) : covered p S x ↔
    ∀ e,vanish (S (e,true)) (S (e,false)) (x e) := by
  constructor
  · intro h e
    apply (vanish_chop _).mpr
    exact congr_fun h e
  intro h
  exact funext fun e => (vanish_chop _).mp (h e)

theorem covered_part {S : Cov p N} {x : Ambient p N} (h : matter p x ≤ S) :
    covered p S x := by
  refine (covered_iff ..).mpr (fun e a ha b _ => ?_)
  change dotProduct a (x e *ᵥ b)=0
  apply (annih_mem ..).mp ha
  exact h (e,true) ⟨b,rfl⟩

/-- Cover as a tensor space; used to count tiny-cover span. -/
def coverX (p : Shape) {N} (S : Cov p N) := ker (erased p S)

private theorem vanish_sum {S : Space (Vec I)} {T : Space (Vec J)}
    (M : Mat I J) :
    vanish S T M ↔ M∈box S ⊤ ⊔ box ⊤ T := by
  classical
  constructor
  · intro h
    let A := prj S
    let B := prj T
    let D := A*M
    let E := (1-A)*M*Bᵀ
    have hh : colSp D≤S := by
      rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply,show D=_*_ from rfl,←mulVec_mulVec]
      exact (prj_data S).onto _
    have he : colSp Eᵀ ≤ T := by
      rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply,show E=_*_ from rfl,transpose_mul,transpose_transpose,←mulVec_mulVec]
      exact (prj_data T).onto _
    have hx : M=D+E := by
      have hg := (vanish_chop _).mp h
      change (1-A)*M*(1-B)ᵀ = 0 at hg
      rw [transpose_sub,transpose_one,Matrix.mul_sub,Matrix.mul_one] at hg
      unfold D E
      rw [← sub_eq_zero.mp hg,Matrix.sub_mul,Matrix.one_mul,add_sub_cancel]
    rw [hx]; exact Submodule.add_mem_sup ((box_mem ..).mpr ⟨hh,le_top⟩)
      ((box_mem ..).mpr ⟨le_top,he⟩)
  · intro h
    obtain ⟨A,hA,B,hB,rfl⟩ := Submodule.mem_sup.mp h
    intro x hx y hy
    have hi : colSp A≤ S := ((box_mem ..).mp hA).1
    have hj : colSp Bᵀ≤ T := ((box_mem ..).mp hB).2
    rw [evmat_addM,show evmat A x y=0 from
      (annih_mem ..).mp hx _ (hi ⟨_,rfl⟩),zero_add,← evmat_transpose B]
    exact (annih_mem ..).mp hy _ (hj ⟨_,rfl⟩)

theorem cover_mem (S : Cov p N) (x : Ambient p N) :
    x∈coverX p S ↔ ∀ e,x e∈box (S (e,true)) ⊤ ⊔ box ⊤ (S (e,false)) :=
  (covered_iff ..).trans (forall_congr' fun e => vanish_sum (x e))

private theorem cov_pi_bound {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (s : J→ Submodule F V) :
    dim (Submodule.pi Set.univ s) ≤ ∑ i, dim (s i) := by
  let T := Submodule.pi Set.univ s
  have h (i : J) (x : T) : x.val i∈ s i := x.property i (Set.mem_univ i)
  let f : T →ₗ[F] (∀ i,s i) := {
    toFun := fun x i => ⟨_,h i x⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl }
  have hf : Function.Injective f := fun x y e => Subtype.ext (funext (fun i =>
    show x.val i=y.val i from congrArg (fun t:s i => t.val) (congr_fun e i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
    (Module.finrank_pi_fintype _)

theorem cover_dim (p : Shape) {N} (S : Cov p N) :
    dim (coverX p S)≤ N*cdim p S := by
  let A (i : Comp p.g) : Space (Mat (Fin N) (Fin N)) :=
    box (S (i,true)) ⊤ ⊔ box ⊤ (S (i,false))
  have he : coverX p S≤ Submodule.pi Set.univ A := by
    intro x hx i _
    exact (cover_mem ..).mp hx i
  refine ((Submodule.finrank_mono he).trans (cov_pi_bound ..)).trans ?_
  unfold cdim
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  have ht : dim (⊤ : Space (Vec (Fin N)))=N := (finrank_top ..).trans
    ((dim_vec _).trans (Fintype.card_fin _))
  refine Finset.sum_le_sum fun i _ => ?_
  apply (Submodule.finrank_add_le_finrank_add_finrank ..).trans
  change dim (box (S (i,true)) _)+dim (box _ (S (i,false)))≤_
  rw [box_dim,box_dim,ht,Fintype.sum_bool,Nat.mul_add,Nat.mul_comm N _]
  rw [Nat.mul_comm N _]

end HadwigerCounterexample

end

end OAI
