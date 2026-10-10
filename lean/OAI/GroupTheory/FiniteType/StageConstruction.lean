import Mathlib
import OAI.GroupTheory.FiniteType.PrefixPermutation
import OAI.GroupTheory.FiniteType.SteinbergSixThree

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]
abbrev Seven := Fin 6 ⊕ Unit
abbrev Q (R : Type*) [Ring R] := NoncommElementary.elementary (n:=Seven) (R:=R)
abbrev X (R : Type*) := Seven → R

def first : Seven := Sum.inr ()
def second : Seven := Sum.inl 0
lemma first_ne_second : first≠second := by decide

def action : Q R →* Equiv.Perm (X R) :=
  NoncommElementary.columnAction.comp NoncommElementary.elementary.subtype

@[simp] lemma action_apply (q : Q R) (x : X R) : action q x=q.val.val.mulVec x := rfl

def block : Steinberg.Group (Fin 6) R →* Q R :=
  Steinberg.pi.comp (Steinberg.reindex Function.Embedding.inl)

lemma block_matrix (g : Steinberg.Group (Fin 6) R) :
    (block g).val=Steinberg.matrixBlock (p:=Unit) (Steinberg.matrix g) :=
  Steinberg.matrix_reindex_inl g

lemma block_fixes (g : Steinberg.Group (Fin 6) R) (a : R) :
    action (block g) (Pi.single first a)=Pi.single first a := by
  rw [action_apply,block_matrix]
  ext i
  cases i <;> simp [Steinberg.matrixBlock,Matrix.mulVec,dotProduct,
    Matrix.fromBlocks,first,Pi.single_apply]

lemma block_position (v : Rˣ) :
    Steinberg.matrixBlock (p:=Unit) (NoncommElementary.position (0:Fin 6) v)=
      NoncommElementary.position second v := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;>
    simp [Steinberg.matrixBlock,NoncommElementary.position_val,second,
      Matrix.single,Matrix.fromBlocks,Matrix.one_apply]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

def transitionUnits : Rˣ →* Q R :=
  (NoncommElementary.compressed φ D first second first_ne_second).comp
    (NonunitalCompression.units φ)

lemma transitionUnits_val (v : Rˣ) :
    (transitionUnits φ D v).val=
      NoncommElementary.position first (NonunitalCompression.units (φ.comp φ) v) := by
  simp only [transitionUnits,MonoidHom.comp_apply,NoncommElementary.compressed_coe,
    Steinberg.units_comp]

lemma block_lift (v : Rˣ) :
    (block (Steinberg.unitLift φ D v)).val=
      NoncommElementary.position second (NonunitalCompression.units (φ.comp φ) v) := by
  rw [block_matrix,Steinberg.matrix_unitLift,block_position]

def exchange (d : R) : Q R :=
  ⟨NoncommElementary.exchange first second first_ne_second d,
    NoncommElementary.exchange_mem _ _ _ _⟩

lemma exchange_fixes (d a : R) (ha : d*a=0) :
    action (exchange d) (Pi.single first a)=Pi.single first a :=
  NoncommElementary.exchange_fixes _ _ _ _ _ ha

lemma exchange_lift (d : R) (hd : d*d=d) (v : Rˣ)
    (hl : d*(φ (φ (v.val-1)))=φ (φ (v.val-1)))
    (hr : φ (φ (v.val-1))*d=φ (φ (v.val-1))) :
    exchange d*transitionUnits φ D v*(exchange d)⁻¹=block (Steinberg.unitLift φ D v) := by
  apply Subtype.ext
  change NoncommElementary.exchange first second first_ne_second d *
    (transitionUnits φ D v).val * (NoncommElementary.exchange first second first_ne_second d)⁻¹=_
  rw [transitionUnits_val,block_lift]
  apply NoncommElementary.exchange_move _ _ _ _ hd
  · simpa only [NonunitalCompression.units_val,add_sub_cancel_left,
      NonUnitalRingHom.comp_apply] using hl
  · simpa only [NonunitalCompression.units_val,add_sub_cancel_left,
      NonUnitalRingHom.comp_apply] using hr

variable {ι : Type*}

def fixing (z : ι → X R) : Subgroup (Q R) where
  carrier := {q | ∀ i, action q (z i)=z i}
  one_mem' i := by rw [map_one]; rfl
  mul_mem' ha hb i := by rw [map_mul,Equiv.Perm.mul_apply,hb i,ha i]
  inv_mem' {q} h i := by
    apply (action q).injective
    rw [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply,h i]

def stabilizerBlock (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) :
    Steinberg.Group (Fin 6) R →* fixing (fun i => action a (Pi.single first (c i))) :=
  (((MulAut.conj (a*(exchange d)⁻¹)).toMonoidHom).comp block).codRestrict _ (by
    intro g i
    change action ((a*(exchange d)⁻¹)*block g*(a*(exchange d)⁻¹)⁻¹)
      (action a (Pi.single first (c i)))=action a (Pi.single first (c i))
    simp only [mul_inv_rev,inv_inv,map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def]
    rw [Equiv.symm_apply_apply,exchange_fixes d (c i) (hc i),block_fixes]
    have he := exchange_fixes d (c i) (hc i)
    have hei : (action (exchange d)).symm (Pi.single first (c i))=Pi.single first (c i) :=
      (Equiv.symm_apply_eq (action (exchange d))).mpr he.symm
    rw [hei])

lemma stabilizerBlock_val (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) (g : Steinberg.Group (Fin 6) R) :
    (stabilizerBlock c a d hc g).val=a*(exchange d)⁻¹*block g*exchange d*a⁻¹ := by
  change (a*(exchange d)⁻¹)*block g*(a*(exchange d)⁻¹)⁻¹=_
  group

lemma stabilizerBlock_lift (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) (hd : d*d=d) (v : Rˣ)
    (hl : d*(φ (φ (v.val-1)))=φ (φ (v.val-1)))
    (hr : φ (φ (v.val-1))*d=φ (φ (v.val-1))) :
    (stabilizerBlock c a d hc (Steinberg.unitLift φ D v)).val=
      a * transitionUnits φ D v * a⁻¹ := by
  rw [stabilizerBlock_val,← exchange_lift φ D d hd v hl hr]
  group

end StageConstruction

namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
lemma unitValue_mul_image (φ : R →ₙ+* S) (u x : R) :
    unitValue φ u*φ x=φ (u*x) := by
  have hp : φ 1*φ x=φ x := by rw [← map_mul,one_mul]
  simp only [unitValue,map_sub,map_mul]
  noncomm_ring [hp]
end NonunitalCompression

namespace StageConstruction
variable {R : Type*} [Ring R]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma transitionUnits_fixes (v : Rˣ) (a : R) (ha : v.val*a=a) :
    action (transitionUnits φ D v) (Pi.single first (φ (φ a)))=
      Pi.single first (φ (φ a)) := by
  rw [action_apply,transitionUnits_val,NoncommElementary.position_mulVec]
  congr 1
  exact (NonunitalCompression.unitValue_mul_image (φ.comp φ) v.val a).trans
    (congrArg (φ.comp φ) ha)

variable {ι : Type*} (c : ι → R) (a : Q R)
abbrev compressedFixing := fixing (fun i => action a (Pi.single first (φ (φ (c i)))))

def stabilizerEnd
    (v : compressedFixing φ c a →* Rˣ)
    (hv : ∀ u i, (v u).val*c i=c i) : compressedFixing φ c a →* compressedFixing φ c a :=
  ((((MulAut.conj a).toMonoidHom).comp (transitionUnits φ D)).comp v).codRestrict _ (by
    intro u i
    change action (a * transitionUnits φ D (v u) * a⁻¹)
      (action a (Pi.single first (φ (φ (c i)))))=
        action a (Pi.single first (φ (φ (c i))))
    simp only [map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def]
    rw [Equiv.symm_apply_apply,transitionUnits_fixes φ D (v u) (c i) (hv u i)])

@[simp] lemma stabilizerEnd_val
    (v : compressedFixing φ c a →* Rˣ)
    (hv : ∀ u i, (v u).val*c i=c i) (u : compressedFixing φ c a) :
    (stabilizerEnd φ D c a v hv u).val=a * transitionUnits φ D (v u) * a⁻¹ := rfl

variable {Y : Type*} [DecidableEq Y] [Fintype ι] [DecidableEq ι]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (x : ι → Y) (hx : Function.Injective x)

include hTS hSe hx in

theorem stabilizer_factor
    (v : compressedFixing φ (S ∘ x) a →* Rˣ)
    (hvS : ∀ u i, (v u).val*S (x i)=S (x i))
    (hvT : ∀ u i, T (x i)*(v u).val=T (x i)) :
    ∃ (α : compressedFixing φ (S ∘ x) a →* Steinberg.Group (Fin 6) R)
      (b : Steinberg.Group (Fin 6) R →* compressedFixing φ (S ∘ x) a),
      b.comp α=stabilizerEnd φ D (S ∘ x) a v hvS := by
  let d := PrefixPermutation.complement S T x (φ.comp φ)
  have hd : d*d=d := PrefixPermutation.complement_idempotent e S T hTS hSe x hx (φ.comp φ)
  have hc : ∀ i, d*φ (φ (S (x i)))=0 :=
    PrefixPermutation.complement_prefix e S T hTS hSe x hx (φ.comp φ)
  refine ⟨(Steinberg.unitLift φ D).comp v,
    stabilizerBlock (fun i => φ (φ (S (x i)))) a d hc, ?_⟩
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  simp only [MonoidHom.comp_apply,stabilizerEnd_val]
  have h := PrefixPermutation.complement_support S T x (φ.comp φ) ((v u).val-1)
    (fun i => by rw [sub_mul,one_mul,hvS u i,sub_self])
    (fun i => by rw [mul_sub,mul_one,hvT u i,sub_self])
  exact stabilizerBlock_lift φ D (fun i => φ (φ (S (x i)))) a d hc hd (v u) h.1 h.2

end StageConstruction

namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
lemma units_injective (φ : R →ₙ+* S) (hφ : Function.Injective φ) :
    Function.Injective (units φ) := by
  intro u v h
  apply Units.ext
  have he := congrArg Units.val h
  change 1+φ (u.val-1)=1+φ (v.val-1) at he
  exact sub_left_injective (hφ (add_left_cancel he))
end NonunitalCompression

namespace StageConstruction
variable {R : Type*} [Ring R]

lemma action_injective : Function.Injective (action (R:=R)) :=
  NoncommElementary.columnAction_injective.comp Subtype.val_injective

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma transitionUnits_injective (hφ : Function.Injective φ) :
    Function.Injective (transitionUnits φ D) := by
  intro u v h
  apply NonunitalCompression.units_injective (φ.comp φ) (hφ.comp hφ)
  apply Units.ext
  have he := congrArg (fun q : Q R => action q (Pi.single first 1) first) h
  simpa only [action_apply,transitionUnits_val,NoncommElementary.position_mulVec,
    mul_one,Pi.single_eq_same] using he

def beta {Y : Type*} (S : Y → R) (y : Y) : X R := Pi.single first (φ (φ (S y)))

lemma beta_injective {Y : Type*} (S : Y → R) (hS : Function.Injective S)
    (hφ : Function.Injective φ) : Function.Injective (beta φ S) := by
  intro y z h
  exact hS (hφ (hφ (by simpa only [beta,Pi.single_eq_same] using congrFun h first)))

lemma transitionUnits_beta {Y : Type*} (S : Y → R) (v : Rˣ) (y z : Y)
    (h : v.val*S y=S z) : action (transitionUnits φ D v) (beta φ S y)=beta φ S z := by
  rw [action_apply,transitionUnits_val,beta,NoncommElementary.position_mulVec]
  congr 1
  exact (NonunitalCompression.unitValue_mul_image (φ.comp φ) v.val (S y)).trans
    (congrArg (φ.comp φ) h)

lemma beta_not_surjective [Nontrivial R] {Y : Type*} (S : Y → R) :
    ¬Function.Surjective (beta φ S) := by
  intro h
  obtain ⟨y,hy⟩ := h (Pi.single second 1)
  have he := congrFun hy second
  have hne : second≠first := first_ne_second.symm
  simp [beta,hne] at he

variable {Y : Type*} [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

include D hTS hSe in

theorem beta_tuple_transitivity {ι : Type*} [Fintype ι]
    (x y : ι → Y) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : Q R, ∀ i, action q (beta φ S (x i))=beta φ S (y i) := by
  classical
  let F : Finset Y := Finset.univ.image x ∪ Finset.univ.image y
  let x' : ι → F := fun i => ⟨x i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  let y' : ι → F := fun i => ⟨y i,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
  have hx' : Function.Injective x' := fun i j h => hx (congrArg Subtype.val h)
  have hy' : Function.Injective y' := fun i j h => hy (congrArg Subtype.val h)
  obtain ⟨η,hη⟩ := Equiv.Perm.exists_extending_pair x' y' hx' hy'
  let v := PrefixPermutation.units e S T hTS hSe (Subtype.val : F → Y) Subtype.val_injective η
  refine ⟨transitionUnits φ D v,fun i => transitionUnits_beta φ D S v (x i) (y i) ?_⟩
  change PrefixPermutation.value S T (Subtype.val : F → Y) η*S (x i)=S (y i)
  have hv := PrefixPermutation.value_prefix e S T hTS hSe
    (Subtype.val : F → Y) Subtype.val_injective η (x' i)
  simpa only [hη] using hv

variable {W : Type*} [Group W] [MulAction W Y]
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (action q x))

def delta : Q R →* Q R := (transitionUnits φ D).comp (ρ.comp ι)
def sigma : X R → X R := beta φ S ∘ point

lemma delta_injective (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
    (hι : Function.Injective ι) : Function.Injective (delta φ D ρ ι) :=
  (transitionUnits_injective φ D hφ).comp (hρ.comp hι)

include hTS in
lemma sigma_injective (he : e≠0) (hφ : Function.Injective φ)
    (hpt : Function.Injective point) : Function.Injective (sigma φ S point) :=
  (beta_injective φ S (PrefixPermutation.prefix_injective e S T hTS he) hφ).comp hpt

omit [DecidableEq Y] in
lemma sigma_not_surjective [Nontrivial R] : ¬Function.Surjective (sigma φ S point) := by
  intro h
  apply beta_not_surjective φ S
  intro y
  obtain ⟨x,hx⟩ := h y
  exact ⟨point x,hx⟩

include hρS hpoint in
omit [DecidableEq Y] in
lemma transition_equivariant (q : Q R) (x : X R) :
    action (delta φ D ρ ι q) (sigma φ S point x)=sigma φ S point (action q x) := by
  change action (transitionUnits φ D (ρ (ι q))) (beta φ S (point x))=_
  rw [transitionUnits_beta φ D S (ρ (ι q)) (point x) (ι q • point x) (hρS _ _),hpoint]
  rfl

include D hTS hSe in
lemma sigma_tuple_transitivity (hpt : Function.Injective point) (n : ℕ)
    (x y : Fin n → X R) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ q : Q R, ∀ i, action q (sigma φ S point (x i))=sigma φ S point (y i) :=
  beta_tuple_transitivity φ D e S T hTS hSe (point ∘ x) (point ∘ y) (hpt.comp hx) (hpt.comp hy)

end StageConstruction

end

end OAI
