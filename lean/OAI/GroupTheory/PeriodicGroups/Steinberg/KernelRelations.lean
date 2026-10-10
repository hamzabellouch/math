import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.MonomialPresentation

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
open scoped BigOperators
noncomputable section
open Classical

variable {n : ℕ} {R : Type u} [Ring R]

def rootHom (p : Root n) : Multiplicative R →* Steinberg n R where
  toFun a := Steinberg.x p a.toAdd
  map_one' := Steinberg.x_zero p
  map_mul' a b := Steinberg.x_add p a.toAdd b.toAdd

abbrev RectIndex (H L : Finset (Fin n)) := {i // i ∈ H} × {j // j ∈ L}

variable (H L : Finset (Fin n)) (hHL : Disjoint H L)

def rectPosition (p : RectIndex H L) : Root n :=
  ⟨p.1.val, p.2.val, fun h => Finset.disjoint_left.mp hHL p.1.property (h ▸ p.2.property)⟩

lemma rect_commute (p q : RectIndex H L) (a b : R) :
    Commute (Steinberg.x (rectPosition H L hHL p) a)
      (Steinberg.x (rectPosition H L hHL q) b) := by
  apply Steinberg.x_commute
  · intro h
    change p.2.val = q.1.val at h
    exact Finset.disjoint_left.mp hHL q.1.property (h ▸ p.2.property)
  · intro h
    change p.1.val = q.2.val at h
    exact Finset.disjoint_left.mp hHL p.1.property (h ▸ q.2.property)

def rectRoot : (RectIndex H L → Multiplicative R) →* Steinberg n R :=
  MonoidHom.noncommPiCoprod (fun p => rootHom (rectPosition H L hHL p))
    (fun p q _ a b => rect_commute H L hHL p q a.toAdd b.toAdd)

@[simp] lemma rectRoot_single (p : RectIndex H L) (a : R) :
    rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Steinberg.x (rectPosition H L hHL p) a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def rectMatrix (A : RectIndex H L → Multiplicative R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if hi : i ∈ H then if hj : j ∈ L then (A (⟨i, hi⟩, ⟨j, hj⟩)).toAdd
    else 0 else 0

@[simp] lemma rectMatrix_entry (A : RectIndex H L → Multiplicative R)
    (p : RectIndex H L) : rectMatrix H L A p.1.val p.2.val = (A p).toAdd := by
  simp [rectMatrix, p.1.property, p.2.property]

@[simp] lemma rectMatrix_one : rectMatrix H L (1 : RectIndex H L → Multiplicative R) = 0 := by
  ext i j
  simp [rectMatrix]

@[simp] lemma rectMatrix_mul (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L (A * B) = rectMatrix H L A + rectMatrix H L B := by
  ext i j
  simp only [rectMatrix, Matrix.add_apply]
  split_ifs <;> simp_all

include hHL in
lemma rectMatrix_product (A B : RectIndex H L → Multiplicative R) :
    rectMatrix H L A * rectMatrix H L B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ H
  · have hk' : k ∉ L := fun hl => Finset.disjoint_left.mp hHL hk hl
    simp [rectMatrix, hk']
  · simp [rectMatrix, hk]

def rectUnits : (RectIndex H L → Multiplicative R) →*
    (Matrix (Fin n) (Fin n) R)ˣ where
  toFun A :=
    { val := 1 + rectMatrix H L A
      inv := 1 - rectMatrix H L A
      val_inv := by
        simp [add_mul, mul_sub, rectMatrix_product H L hHL]
      inv_val := by
        simp [sub_mul, mul_add, rectMatrix_product H L hHL] }
  map_one' := by apply Units.ext; simp
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul, rectMatrix_mul]
    simp [add_mul, mul_add, rectMatrix_product H L hHL, add_assoc]

@[simp] lemma coe_rectUnits (A : RectIndex H L → Multiplicative R) :
    (rectUnits H L hHL A).val = 1 + rectMatrix H L A := rfl

lemma rectMatrix_single (p : RectIndex H L) (a : R) :
    rectMatrix H L (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Matrix.single p.1.val p.2.val a := by
  ext i j
  by_cases hi : i ∈ H
  · by_cases hj : j ∈ L
    · simp only [rectMatrix, dite_eq_left hi, dite_eq_left hj, Matrix.single_apply]
      by_cases hp : p = (⟨i, hi⟩, ⟨j, hj⟩)
      · subst p
        simp
      · have hp' : ¬ (p.1.val = i ∧ p.2.val = j) := by
          rintro ⟨h₁, h₂⟩
          apply hp
          exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
        simp [hp, hp']
    · have hn : p.2.val ≠ j := by intro h; exact hj (h ▸ p.2.property)
      simp [rectMatrix, hi, hj, hn]
  · have hn : p.1.val ≠ i := by intro h; exact hi (h ▸ p.1.property)
    simp [rectMatrix, hi, hn]

@[simp] lemma rectUnits_single (p : RectIndex H L) (a : R) :
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a)) =
      Elementary.e (rectPosition H L hHL p) a := by
  apply Units.ext
  rw [coe_rectUnits, rectMatrix_single]
  rfl

lemma representation_rectRoot :
    Elementary.representation.comp (rectRoot H L hHL (R := R)) = rectUnits H L hHL := by
  apply MonoidHom.pi_ext
  intro p a
  change Elementary.representation (rectRoot H L hHL (Pi.mulSingle p a)) =
    rectUnits H L hHL (Pi.mulSingle p a)
  change Elementary.representation
    (rectRoot H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))) =
    rectUnits H L hHL (Pi.mulSingle p (Multiplicative.ofAdd a.toAdd))
  rw [rectRoot_single, rectUnits_single, Elementary.representation_x]

lemma rectUnits_injective : Function.Injective (rectUnits H L hHL (R := R)) := by
  intro A B h
  have hm := congrArg (fun x : (Matrix (Fin n) (Fin n) R)ˣ => x.val) h
  have he : rectMatrix H L A = rectMatrix H L B := add_left_cancel hm
  funext p
  apply Multiplicative.toAdd.injective
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) R => M p.1.val p.2.val) he

def Strip : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃ (p : RectIndex H L) (a : R),
    g = Steinberg.x (rectPosition H L hHL p) a}

lemma strip_le_range : Strip H L hHL ≤ (rectRoot H L hHL (R := R)).range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p, a, rfl⟩
  exact ⟨Pi.mulSingle p (Multiplicative.ofAdd a), rectRoot_single H L hHL p a⟩

theorem strip_faithful {g : Steinberg n R} (hg : g ∈ Strip H L hHL)
    (hmat : Elementary.representation g = 1) : g = 1 := by
  obtain ⟨A, rfl⟩ := strip_le_range H L hHL hg
  have hr : rectUnits H L hHL A = 1 := by
    rw [← MonoidHom.comp_apply, representation_rectRoot] at hmat
    exact hmat
  have ha : A = 1 := rectUnits_injective H L hHL (hr.trans (map_one _).symm)
  rw [ha, map_one]

end
end SourceBurnside.Kernel

namespace SourceBurnside
namespace Root

def map {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f) (p : Root n) : Root m :=
  ⟨f p.row, f p.col, fun h => p.ne (hf h)⟩
end Root

namespace Steinberg
variable {n m : ℕ} {R : Type u} [Ring R]

def coordinateMap (f : Fin n → Fin m) (hf : Function.Injective f) :
    Steinberg n R →* Steinberg m R :=
  lift (fun p a => x (p.map f hf) a)
    (fun _ _ _ => x_add _ _ _)
    (fun _p _q h₁ h₂ a b => x_commute _ _ (fun h => h₁ (hf h)) (fun h => h₂ (hf h)) a b)
    (fun i j k hij hjk hik a b =>
      x_mul (f i) (f j) (f k) (fun h => hij (hf h)) (fun h => hjk (hf h))
        (fun h => hik (hf h)) a b)

@[simp] theorem coordinateMap_x (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : Root n) (a : R) : coordinateMap f hf (x p a) = x (p.map f hf) a :=
  lift_x _ _ _ _ _ _

lemma conjugate_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨i,j,hij⟩ a * x ⟨j,k,hjk⟩ b * (x ⟨i,j,hij⟩ a)⁻¹ =
      x ⟨i,k,hik⟩ (a*b) * x ⟨j,k,hjk⟩ b := by
  calc
    _ = bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b) * x ⟨j,k,hjk⟩ b := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul]

lemma conjugate_reverse (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    x ⟨j,k,hjk⟩ b * x ⟨i,j,hij⟩ a * (x ⟨j,k,hjk⟩ b)⁻¹ =
      x ⟨i,k,hik⟩ (-(a*b)) * x ⟨i,j,hij⟩ a := by
  calc
    _ = (bracket (x ⟨i,j,hij⟩ a) (x ⟨j,k,hjk⟩ b))⁻¹ * x ⟨i,j,hij⟩ a := by
      simp [bracket, mul_assoc]
    _ = _ := by rw [x_mul, x_neg]

lemma conjugate_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : x p a * x q b * (x p a)⁻¹ = x q b := by
  rw [(x_commute p q h₁ h₂ a b).eq, mul_inv_cancel_right]

lemma outside (hn : 3 ≤ n) (p : Root n) : ∃ k : Fin n, k ≠ p.row ∧ k ≠ p.col := by
  have hc : ({p.row,p.col} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h := (Finset.card_le_two : ({p.row,p.col} : Finset (Fin n)).card ≤ 2)
    simpa using (lt_of_le_of_lt h (show 2 < n by omega))
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, by simpa using hk⟩

theorem commutator_eq_top (hn : 3 ≤ n) : commutator (Steinberg n R) = ⊤ := by
  apply top_unique
  rw [← closure_range_x]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨p,a⟩,rfl⟩
  obtain ⟨k,hki,hkj⟩ := outside hn p
  have hb := x_mul p.row k p.col hki.symm hkj p.ne a (1 : R)
  rw [mul_one] at hb
  change x p a ∈ commutator (Steinberg n R)
  change _ = x p a at hb
  rw [← hb, commutator_eq_closure]
  exact Subgroup.subset_closure ⟨x ⟨p.row,k,hki.symm⟩ a, x ⟨k,p.col,hkj⟩ 1, rfl⟩

theorem hom_to_commGroup_trivial (hn : 3 ≤ n) {A : Type v} [CommGroup A]
    (f : Steinberg n R →* A) : f = 1 := by
  apply hom_ext
  intro p a
  obtain ⟨k,hki,hkj⟩ := outside hn p
  have hb := x_mul p.row k p.col hki.symm hkj p.ne a (1 : R)
  rw [mul_one] at hb
  rw [← hb, map_bracket]
  simp [bracket, mul_comm]

end Steinberg
end SourceBurnside

namespace SourceBurnside.Kernel
noncomputable section

theorem rational_detection {A : Type u} [AddCommGroup A] (a : A)
    (ha : ∀ f : A →+ ℚ, f a = 0) : ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  let S := nonZeroDivisors ℤ
  let V := LocalizedModule S A
  let : Module ℚ V := LocalizedModule.moduleOfIsLocalization
  let f := LocalizedModule.mkLinearMap S A
  have hz : f a = 0 := by
    by_contra hn
    obtain ⟨g,hg⟩ := Module.Projective.exists_dual_ne_zero ℚ hn
    exact hg (ha (g.toAddMonoidHom.comp f.toAddMonoidHom))
  have hz' : LocalizedModule.mk a (1 : S) = LocalizedModule.mk (0 : A) (1 : S) := by
    simpa only [f, LocalizedModule.mkLinearMap_apply, LocalizedModule.zero_mk] using hz
  obtain ⟨n,hn⟩ := LocalizedModule.mk_eq.mp hz'
  simp only [one_smul, smul_zero] at hn
  exact ⟨(n.val : ℤ).natAbs, Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero n),
    natAbs_nsmul_eq_zero.mpr hn⟩

end
end SourceBurnside.Kernel

namespace SourceBurnside.Steinberg
variable {n : ℕ} {R : Type u} [Ring R]

theorem periodic_of_finite_central_image (hn : 3 ≤ n)
    {H : Type v} [Group H] [Finite H] (f : Steinberg n R →* H)
    (hc : f.ker ≤ Subgroup.center (Steinberg n R)) : Periodic (Steinberg n R) := by
  let : f.ker.FiniteIndex := Subgroup.finiteIndex_ker f
  let : (Subgroup.center (Steinberg n R)).FiniteIndex := Subgroup.finiteIndex_of_le hc
  let : CommGroup (Subgroup.center (Steinberg n R)) :=
    { (inferInstance : Group (Subgroup.center (Steinberg n R))) with
      mul_comm := fun a b => Subtype.ext (b.property.comm a).symm }
  have ht := hom_to_commGroup_trivial hn (MonoidHom.transferCenterPow (Steinberg n R))
  intro g
  refine ⟨(Subgroup.center (Steinberg n R)).index,
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  have he := congrArg Subtype.val (DFunLike.congr_fun ht g)
  simpa only [MonoidHom.transferCenterPow_apply, MonoidHom.one_apply, OneMemClass.coe_one] using he

end SourceBurnside.Steinberg

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def awayCoordinates (t : Fin n) : Finset (Fin n) := Finset.univ.erase t
lemma away_disjoint (t : Fin n) : Disjoint (awayCoordinates t) {t} := by
  simp [awayCoordinates]
def columnStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip (awayCoordinates t) {t} (away_disjoint t)
def rowStrip (t : Fin n) : Subgroup (Steinberg n R) := Strip {t} (awayCoordinates t) (away_disjoint t).symm
lemma column_root_mem (t i : Fin n) (hi : i≠t) (a : R) :
    Steinberg.x ⟨i,t,hi⟩ a∈columnStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨i,by simp [awayCoordinates,hi]⟩,⟨t,by simp⟩),a,rfl⟩
lemma row_root_mem (t i : Fin n) (hi : t≠i) (a : R) :
    Steinberg.x ⟨t,i,hi⟩ a∈rowStrip t := by
  apply Subgroup.subset_closure
  refine ⟨(⟨t,by simp⟩,⟨i,by simp [awayCoordinates,Ne.symm hi]⟩),a,rfl⟩
lemma conjugate_column_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : i≠t) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨i,t,hi⟩ b * (Steinberg.x p a)⁻¹∈columnStrip t := by
  by_cases hc : p.col=i
  · have he := Steinberg.conjugate_chain p.row i t (hc ▸ p.ne) hi hpt a b
    have hp : p=⟨p.row,i,hc ▸ p.ne⟩ := by cases p;cases hc;rfl
    rw [hp,he]
    exact (columnStrip t).mul_mem (column_root_mem t _ hpt _) (column_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨i,t,hi⟩ hc hpt]
    exact column_root_mem t i hi b
lemma conjugate_row_root_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) (i : Fin n) (hi : t≠i) (b : R) :
    Steinberg.x p a * Steinberg.x ⟨t,i,hi⟩ b * (Steinberg.x p a)⁻¹∈rowStrip t := by
  by_cases hr : p.row=i
  · have he := Steinberg.conjugate_reverse t i p.col hi (hr ▸ p.ne) hct.symm b a
    have hp : p=⟨i,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
    rw [hp,he]
    exact (rowStrip t).mul_mem (row_root_mem t _ hct.symm _) (row_root_mem t _ hi _)
  · rw [Steinberg.conjugate_commute p ⟨t,i,hi⟩ hct hr]
    exact row_root_mem t i hi b
lemma conjugate_column_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈columnStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈columnStrip t := by
  have H : columnStrip (R:=R) t ≤ (columnStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hj' : j=t := Finset.mem_singleton.mp hj
    subst j
    have hi' : i≠t := by simpa [awayCoordinates] using hi
    exact conjugate_column_root_mem t p hpt hct a i hi' b
  exact H hg
lemma conjugate_row_mem (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t)
    (a : R) {g : Steinberg n R} (hg : g∈rowStrip t) :
    Steinberg.x p a * g * (Steinberg.x p a)⁻¹∈rowStrip t := by
  have H : rowStrip (R:=R) t ≤ (rowStrip t).comap (MulAut.conj (Steinberg.x p a)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,b,rfl⟩
    have hi' : i=t := Finset.mem_singleton.mp hi
    subst i
    have hj' : j≠t := by simpa [awayCoordinates] using hj
    exact conjugate_row_root_mem t p hpt hct a j hj'.symm b
  exact H hg

def away (t : Fin n) : Subgroup (Steinberg n R) :=
  Subgroup.closure {g | ∃(p : Root n)(a : R),p.row≠t ∧ p.col≠t ∧ g=Steinberg.x p a}
lemma away_le_column_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (columnStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_column_mem t p hpt hct a
  · intro hx
    have H := conjugate_column_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
lemma away_le_row_normalizer (t : Fin n) :
    away (R:=R) t ≤ Subgroup.normalizer (rowStrip (R:=R) t : Set (Steinberg n R)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p,a,hpt,hct,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_row_mem t p hpt hct a
  · intro hx
    have H := conjugate_row_mem t p hpt hct (-a) hx
    simpa only [Steinberg.x_neg,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using H
lemma kernel_commutes_column (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : i≠t) (a : R) :
    Commute g (Steinberg.x ⟨i,t,hi⟩ a) := by
  let x := Steinberg.x ⟨i,t,hi⟩ a
  have hx : x∈columnStrip t := column_root_mem t i hi a
  have hc : g*x*g⁻¹∈columnStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_column_normalizer t hg) x).mp hx
  have H := strip_faithful (awayCoordinates t) {t} (away_disjoint t)
    ((columnStrip t).mul_mem hc ((columnStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)
lemma kernel_commutes_row (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) (i : Fin n) (hi : t≠i) (a : R) :
    Commute g (Steinberg.x ⟨t,i,hi⟩ a) := by
  let x := Steinberg.x ⟨t,i,hi⟩ a
  have hx : x∈rowStrip t := row_root_mem t i hi a
  have hc : g*x*g⁻¹∈rowStrip t := (Subgroup.mem_normalizer_iff.mp (away_le_row_normalizer t hg) x).mp hx
  have H := strip_faithful {t} (awayCoordinates t) (away_disjoint t).symm
    ((rowStrip t).mul_mem hc ((rowStrip t).inv_mem hx)) (by simp [map_mul,map_inv,hmat])
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp H)

theorem supported_kernel_central (t : Fin n) {g : Steinberg n R} (hg : g∈away t)
    (hmat : Elementary.representation g=1) : g∈Subgroup.center (Steinberg n R) := by
  have hc (p : Root n) (a : R) : Commute g (Steinberg.x p a) := by
    by_cases hr : p.row=t
    · have hp : p=⟨t,p.col,hr ▸ p.ne⟩ := by cases p;cases hr;rfl
      rw [hp]
      exact kernel_commutes_row t hg hmat p.col (hr ▸ p.ne) a
    · by_cases ht : p.col=t
      · have hp : p=⟨p.row,t,ht ▸ p.ne⟩ := by cases p;cases ht;rfl
        rw [hp]
        exact kernel_commutes_column t hg hmat p.row (ht ▸ p.ne) a
      · have he := Steinberg.x_mul p.row t p.col hr (Ne.symm ht) p.ne a (1:R)
        rw [mul_one] at he
        have HH := CommutatorCalculus.commute_bracket_right
          (kernel_commutes_column t hg hmat p.row hr a)
          (kernel_commutes_row t hg hmat p.col (Ne.symm ht) 1)
        exact he ▸ HH
  have hf : (MulAut.conj g).toMonoidHom=MonoidHom.id (Steinberg n R) := by
    apply Steinberg.hom_ext
    intro p a
    change g*Steinberg.x p a*g⁻¹=Steinberg.x p a
    rw [(hc p a).eq,mul_inv_cancel_right]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have H := DFunLike.congr_fun hf x
  change g*x*g⁻¹=x at H
  exact (mul_inv_eq_iff_eq_mul.mp H).symm
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def coordinateEquiv (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
def coordinateIndex (n : ℕ) (i : Fin n) : Fin (n+1) := coordinateEquiv n (Sum.inl i)
lemma coordinateIndex_injective (n : ℕ) : Function.Injective (coordinateIndex n) :=
  (coordinateEquiv n).injective.comp Sum.inl_injective
def spareCoordinate (n : ℕ) : Fin (n+1) := coordinateEquiv n (Sum.inr 0)
lemma coordinateIndex_ne_spare (i : Fin n) : coordinateIndex n i≠spareCoordinate n := by
  intro he
  have := (coordinateEquiv n).injective he
  contradiction

def blockUnits (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks u.val 0 0 1
  inv := Matrix.fromBlocks u.inv 0 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]
def blockUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  toFun := blockUnits
  map_one' := by apply Units.ext;simp [blockUnits]
  map_mul' u v := by apply Units.ext;simp [blockUnits,Matrix.fromBlocks_multiply]
def padUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ :=
  (Units.map (Matrix.reindexRingEquiv R (coordinateEquiv n)).toMonoidHom).comp blockUnitsHom
lemma padUnitsHom_e (p : Root n) (a : R) :
    padUnitsHom (Elementary.e p a)=Elementary.e (p.map (coordinateIndex n) (coordinateIndex_injective n)) a := by
  apply Units.ext
  change (Matrix.fromBlocks (1+Matrix.single p.row p.col a) 0 0 1).submatrix
    (coordinateEquiv n).symm (coordinateEquiv n).symm =
      1+Matrix.single (coordinateIndex n p.row) (coordinateIndex n p.col) a
  apply Matrix.ext
  intro i j
  obtain ⟨i,rfl⟩ := (coordinateEquiv n).surjective i
  obtain ⟨j,rfl⟩ := (coordinateEquiv n).surjective j
  cases i <;> cases j <;>
    simp [coordinateIndex,Matrix.submatrix_apply,Matrix.fromBlocks,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]

def padSteinberg : Steinberg n R →* Steinberg (n+1) R :=
  Steinberg.coordinateMap (coordinateIndex n) (coordinateIndex_injective n)
lemma pad_representation :
    Elementary.representation.comp (padSteinberg (n:=n) (R:=R))=
      padUnitsHom.comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,padSteinberg,Steinberg.coordinateMap_x,Elementary.representation_x,padUnitsHom_e]
lemma pad_mem_away (g : Steinberg n R) : padSteinberg g∈away (spareCoordinate n) := by
  have H : (⊤ : Subgroup (Steinberg n R)) ≤ (away (spareCoordinate n)).comap padSteinberg := by
    rw [←Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨p,a⟩,rfl⟩
    apply Subgroup.subset_closure
    exact ⟨p.map (coordinateIndex n) (coordinateIndex_injective n),a,
      coordinateIndex_ne_spare p.row,coordinateIndex_ne_spare p.col,by simp [padSteinberg]⟩
  exact H (Subgroup.mem_top g)

theorem stabilized_kernel_central (g : Steinberg n R) (hg : Elementary.representation g=1) :
    padSteinberg g∈Subgroup.center (Steinberg (n+1) R) := by
  apply supported_kernel_central (spareCoordinate n) (pad_mem_away g)
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end
end SourceBurnside.Kernel

namespace SourceBurnside.Steinberg
noncomputable section
variable {n : ℕ} {R G H : Type*} [Ring R] [Group G] [Group H]

lemma finite_central_image_periodic (hn : 3≤n) [Finite H]
    (f : Steinberg n R →* G) (ρ : G →* H)
    (hc : ∀g : Steinberg n R,ρ (f g)=1 → f g∈Subgroup.center G) :
    ∀g : Steinberg n R,∃ m : ℕ, 0 < m ∧ (f g)^m=1 := by
  let F := f.range
  let ψ : F →* H := ρ.comp F.subtype
  have hcen : ψ.ker ≤ Subgroup.center F := by
    rintro x hx
    obtain ⟨g,hg⟩ := x.property
    have hx' : ρ (f g)=1 := by
      change ρ x.val=1 at hx
      exact hg ▸ hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change y.val * x.val = x.val * y.val
    rw [← hg]
    exact Subgroup.mem_center_iff.mp (hc g hx') y.val
  let : ψ.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ
  let : (Subgroup.center F).FiniteIndex := Subgroup.finiteIndex_of_le hcen
  let : CommGroup (Subgroup.center F) :=
    { (inferInstance : Group (Subgroup.center F)) with
      mul_comm := fun a b=>Subtype.ext (b.property.comm a).symm }
  let θ : Steinberg n R →* Subgroup.center F := (MonoidHom.transferCenterPow F).comp f.rangeRestrict
  have hθ : θ=1 := hom_to_commGroup_trivial hn θ
  intro g
  refine ⟨(Subgroup.center F).index,Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,?_⟩
  have he := congrArg (fun z : Subgroup.center F=>z.val.val) (DFunLike.congr_fun hθ g)
  simp only [θ,MonoidHom.comp_apply,MonoidHom.transferCenterPow_apply,MonoidHom.one_apply,
    OneMemClass.coe_one,Subgroup.coe_pow] at he
  change (f g) ^ (Subgroup.center F).index = 1 at he
  exact he
end
end SourceBurnside.Steinberg
namespace SourceBurnside.Kernel
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]
lemma padUnitsHom_injective : Function.Injective (padUnitsHom (n:=n) (R:=R)) := by
  intro u v huv
  apply Units.ext
  have he := congrArg Units.val huv
  change (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks u.val 0 0 1)=
    (Matrix.reindexRingEquiv R (coordinateEquiv n)) (Matrix.fromBlocks v.val 0 0 1) at he
  have hb := (Matrix.reindexRingEquiv R (coordinateEquiv n)).injective he
  apply Matrix.ext
  intro i j
  exact congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R=>M (Sum.inl i) (Sum.inl j)) hb
lemma pad_kernel_iff (g : Steinberg n R) :
    Elementary.representation (padSteinberg g)=1 ↔ Elementary.representation g=1 := by
  have he := DFunLike.congr_fun (pad_representation (n:=n) (R:=R)) g
  change Elementary.representation (padSteinberg g)=padUnitsHom (Elementary.representation g) at he
  rw [he]
  exact (map_eq_one_iff _ padUnitsHom_injective)

theorem stabilized_field_periodic (hn : 3≤n) (g : Steinberg n (ZMod 2)) :
    ∃ m : ℕ, 0 < m ∧ (padSteinberg g)^m=1 := by
  apply Steinberg.finite_central_image_periodic hn padSteinberg Elementary.representation
  intro u hu
  exact stabilized_kernel_central u ((pad_kernel_iff u).mp hu)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Elementary
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]
lemma map_e (f : R →+* S) (p : Root n) (a : R) :
    Units.map f.mapMatrix.toMonoidHom (e p a)=e p (f a) := by
  apply Units.ext
  change f.mapMatrix (1+Matrix.single p.row p.col a)=1+Matrix.single p.row p.col (f a)
  rw [map_add,map_one]
  congr 1
  exact Matrix.map_single p.row p.col a f

lemma representation_map (f : R →+* S) :
    representation.comp (Steinberg.map (n:=n) f)=
      (Units.map f.mapMatrix.toMonoidHom).comp representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,Steinberg.map_x,representation_x,map_e]
lemma map_kernel (f : R →+* S) (g : Steinberg n R) (hg : representation g=1) :
    representation (Steinberg.map f g)=1 := by
  have he := DFunLike.congr_fun (representation_map (n:=n) f) g
  simpa only [MonoidHom.comp_apply,hg,map_one] using he
end SourceBurnside.Elementary
namespace SourceBurnside.Steinberg
variable {n : ℕ} {R S T : Type*} [Ring R] [Ring S] [Ring T]
lemma map_comp (g : S →+* T) (f : R →+* S) :
    (map (n:=n) g).comp (map f)=map (g.comp f) := by
  apply hom_ext
  intro p a
  simp [map_x]
lemma map_map (g : S →+* T) (f : R →+* S) (x : Steinberg n R) :
    map g (map f x)=map (g.comp f) x := DFunLike.congr_fun (map_comp g f) x
lemma map_identity : map (n:=n) (RingHom.id R)=MonoidHom.id _ := by
  apply hom_ext
  intro p a
  simp [map_x]
@[simp] lemma map_identity_apply (x : Steinberg n R) : map (RingHom.id R) x=x :=
  DFunLike.congr_fun map_identity x
end SourceBurnside.Steinberg

end

end OAI
