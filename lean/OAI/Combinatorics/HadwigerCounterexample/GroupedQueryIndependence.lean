import OAI.Combinatorics.HadwigerCounterexample.RepeatedBatchLaws

namespace OAI

/-! # Grouped Query Independence -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N : ℕ}
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

instance knFin (g n : ℕ) : Fintype (Knobs g n) := inferInstanceAs (Fintype (Knobs g n))
def freePart (p : Shape) {n} (x : Knobs p.g n) := x Block.Z

def frozenZ (p : Shape) {n} (P : Knobs p.g n → Prop) :=
  ∀ x y, (P x ↔ P (x+Pi.single Block.Z y))

theorem spin_scan_free (p : Shape) (n) (l) (f : Flavor p.g) :
    ∀ (x : Knobs p.g n) y,scan p l f (x+Pi.single Block.Z y)=scan p l f x := by
  classical
  intro x y; funext i
  have hx : asBlock i ≠ Block.Z := by rcases i with (⟨i,j⟩|_) <;> simp [asBlock]
  simp only [scan,Pi.add_apply,Pi.single_eq_of_ne hx,add_zero]

theorem fresh_Z (p : Shape) (n) (P : Knobs p.g n→ Prop)
    (h : frozenZ p P) (hh : IsLaw (onW (spins p n) P)) :
    mapW (onW (spins p n) P) (freePart p) = unif := by
  classical
  let w := onW (spins p n) P
  have he (c : Vec (Fin n)) (x : Knobs p.g n) :
      w (x+Pi.single Block.Z c)=w x := by
    have hv (x : Knobs p.g n) : spins p n x=unif x := congr_fun
      (Eq.symm draws_unif) x
    simp only [w,onW_val,hv,unif_apply,← h x c]
  have hv (x y : Vec (Fin n)) :
      mapW w (freePart p) x=mapW w (freePart p) y := by
    let t : Knobs p.g n := Pi.single Block.Z (x-y)
    let e : Knobs p.g n ≃ Knobs p.g n :=
      { toFun := (·+t)
        invFun := (·-t)
        left_inv a := add_sub_cancel_right ..
        right_inv a := sub_add_cancel .. }
    have hh (b : Knobs p.g n) :
        freePart p (e b)=x ↔ freePart p b=y := by
      unfold freePart
      change b Block.Z+t Block.Z=x ↔ _
      rw [show t Block.Z=x-y from Pi.single_eq_same _ _]; constructor <;> intro h
      · apply add_right_cancel (b:=x-y)
        rw [h,add_sub_cancel]
      rw [h,add_sub_cancel]
    unfold mapW pr
    rw [← avg_bij e]
    have hf i : w (e i)=w i := he _ i
    simp_rw [hf,hh]
  rw [←unifOn_true (A:=Vec (Fin n))]
  exact uniform_support (mapW_law hh _) (by intro x h; exact (h trivial).elim) (fun i j _ _ => hv i j)

theorem scopedZ_bit (p : Shape) (n l f x) (h : IsLaw (scopedBit p n l f x)) :
    mapW (scopedBit p n l f x) (freePart p)=unif :=
  fresh_Z p n _ (fun v y => by
    simp only [dialed,spin_scan_free]) h

theorem scopedZ_scan (p : Shape) (n l f x) (h : IsLaw (scopedScan p n l f x)) :
    mapW (scopedScan p n l f x) (freePart p)=unif :=
  fresh_Z p n _ (fun v y => by simp only [spin_scan_free]) h

def freeNet (p : Shape) {n} (x : J→ Inputs p n I) :
    PlusRack (J × I) n :=
  Matrix.of (fun i j => freePart p (x j.1 j.2) i)

theorem law_probes (p : Shape) (n)
    (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,mapW (w i) (freePart p)=unif) :
    mapW (draws J (prodW w)) (freeNet p (n:=n) (I:=I))=unif := by
  classical
  let X (x : Inputs p n I) : I → Vec (Fin n) := fun i => freePart p (x i)
  have he := mapW_repeat w (f:=fun i => freePart p (n:=n))
  simp_rw [hw] at he
  have hh : mapW (prodW w) X=unif := he.trans (Eq.symm draws_unif)
  let E : (J→I→Vec (Fin n))≃PlusRack (J×I) n :=
    { toFun := fun x => Matrix.of (fun i j => x j.1 j.2 i)
      invFun := fun x j i k => x k (j,i)
      left_inv _ := rfl
      right_inv _ := rfl }
  let Y (x : J→ Inputs p n I) := fun i => X (x i)
  have h : mapW (draws J (prodW w)) Y=unif := by
    have hY := mapW_repeat (fun (_ : J) => prodW w) (fun _ => X)
    simp_rw [hh] at hY
    exact hY.trans (Eq.symm draws_unif)
  change mapW _ (E ∘ Y) = _
  rw [←mapW_nested,h,unif_equiv]

def bloom (p : Shape) {n} (x : J→Inputs p n I) :=
  Injective (freeNet p x).mulVec

theorem buds (p : Shape) (n)
    (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,mapW (w i) (freePart p)=unif) :
    pr (draws J (prodW w)) (fun x => ¬bloom p x) ≤ bp (num J*num I-n) := by
  classical
  unfold bloom
  rw [show pr _ _ = pr (mapW (draws J (prodW w)) (freeNet p)) (fun x : PlusRack (J×I) n =>
    ¬Injective x.mulVec) from (mapW_pr ..).symm,law_probes _ _ _ hw]
  simpa only [num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    using (@unif_fail (J×I) (Fin n) _ _ _ _)

omit [DecidableEq I] in
theorem inject_column_slice {f : I→J} (M : PlusRack J n)
    (h : Injective M.mulVec) (hf : Injective f) :
    Injective (M.submatrix _root_.id f).mulVec := by
  rw [← mul_embedMat]
  exact inj_comp_mat _ _ h (embedMat_inj hf)

variable {g : Route I G}

omit [Fintype G] [DecidableEq J] in
theorem ray_bloom {f : Route J G} {b : J → I}
    {A : NomQuery p n f} (e : G) (V : PlusRack I n)
    (h : Injective V.mulVec) (he : Injective (fun i : Port f e => b i.val))
    (hm : ∀ i : Port f e, ∀ j : Fin n,A e (emptySel,some (Block.Z,j)) i=V j (b i.val)) :
    Injective (A e).mulVec := by
  intro x y hx
  apply inject_column_slice V h he
  funext j
  have hh := congr_fun hx (emptySel,some (Block.Z,j))
  change ∑ i:Port f e,_=∑ i:Port f e,_ at *
  simp_rw [hm] at hh; exact hh

namespace Template

variable (v : Template p I)

def queryLaw (x : Inputs p n I)
    {g : Route (KeySlots p v.t) G} : NomQuery p n g :=
  fun _ => Matrix.of (fun j k => (v.draw x).rayAt k.val.1 j)

omit [Fintype G] in
/-- covers endpoint variants whenever a position only visits each port once -/
theorem queries_bloom (x : J→ Inputs p n I) (g : Route (KeySlots p v.t) G)
    (h : bloom p x) (he : ∀ e : G,Injective (fun i : Port g e => i.val.1))
    (i : G) :
    Injective (pooled (fun i => queryLaw v (x i) (g:=g)) i).mulVec := by
  classical
  let r : J × KeySlots p v.t → J×I := fun y => (y.1,y.2.1)
  have hr : Injective (fun a : Port (tied g J) i => r a.val) := by
    rintro ⟨⟨j,a⟩,ha⟩ ⟨⟨j',b⟩,hb⟩ heq
    have hA : j=j' := congrArg Prod.fst heq
    have hK : a=b := congrArg Subtype.val (he i (show (⟨a,ha⟩:Port g i).val.1=
      (⟨b,hb⟩:Port g i).val.1 from congrArg Prod.snd heq))
    exact Subtype.ext (Prod.ext hA hK)
  refine ray_bloom (b:=r) _ _ h hr ?_
  rintro a j
  let t := a.val.1
  let i := a.val.2.1
  change point p _ _ (emptySel,some (Block.Z,j))=freeNet p x j (t,i)
  rw [point_base_eval]; exact ite_eq_left (Flavor.keepZ _ _)
end Template

end HadwigerCounterexample

end

end OAI
