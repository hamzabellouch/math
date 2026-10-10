import Mathlib

namespace OAI

section
noncomputable section
open Set Function

namespace CriticalPercolation.NormalOrbit
universe u v
variable {A : Type u} {X : Type v} [Group A] [MulAction A X]
variable (H : Subgroup A) [H.Normal]

abbrev Blocks := MulAction.orbitRel.Quotient H X

def block (x : X) : Blocks (X := X) H := Quotient.mk'' x

lemma map_rel (g : A) {x y : X} (h : MulAction.orbitRel H X x y) :
    MulAction.orbitRel H X (g • x) (g • y) := by
  obtain ⟨h,rfl⟩ := h
  refine ⟨⟨g*h.val*g⁻¹,(inferInstance : H.Normal).conj_mem h.val h.property g⟩,?_⟩
  change (g*h.val*g⁻¹) • (g • y)=g • (h.val • y)
  simp only [mul_smul,inv_smul_smul]

def blockPerm (g : A) : Equiv.Perm (Blocks (X := X) H) where
  toFun := Quotient.map (g • ·) (fun _ _ => map_rel H g)
  invFun := Quotient.map (g⁻¹ • ·) (fun _ _ => map_rel H g⁻¹)
  left_inv := by
    intro b
    induction b using Quotient.inductionOn with
    | h x => change block H (g⁻¹ • (g • x))=block H x; rw [inv_smul_smul]
  right_inv := by
    intro b
    induction b using Quotient.inductionOn with
    | h x => change block H (g • (g⁻¹ • x))=block H x; rw [smul_inv_smul]

@[simp] lemma blockPerm_block (g : A) (x : X) :
    blockPerm H g (block H x)=block H (g • x) := rfl

def blockHom : A →* Equiv.Perm (Blocks (X := X) H) where
  toFun := blockPerm H
  map_one' := by
    ext b
    induction b using Quotient.inductionOn with
    | h x => change block H ((1 : A) • x)=block H x; rw [one_smul]
  map_mul' g h := by
    ext b
    induction b using Quotient.inductionOn with
    | h x => change block H ((g*h) • x)=block H (g • (h • x)); rw [mul_smul]

lemma le_ker_blockHom : H ≤ (blockHom (X := X) H).ker := by
  intro h hh
  apply Equiv.ext
  intro b
  induction b using Quotient.inductionOn with
  | h x =>
    change block H (h • x)=block H x
    exact Quotient.sound ⟨⟨h,hh⟩,rfl⟩

def quotientHom : A ⧸ H →* Equiv.Perm (Blocks (X := X) H) :=
  QuotientGroup.lift H (blockHom H) (le_ker_blockHom H)

instance quotientAction : MulAction (A ⧸ H) (Blocks (X := X) H) :=
  MulAction.compHom (Blocks (X := X) H) (quotientHom (X := X) H)

@[simp] lemma mk_smul_block (g : A) (x : X) :
    (QuotientGroup.mk' H g) • block H x=block H (g • x) := rfl

omit [H.Normal] in
lemma block_eq_iff (x y : X) : block H x=block H y ↔ x∈MulAction.orbit H y :=
  Quotient.eq

lemma quotient_stabilizer_contains_image (x : X) :
    (MulAction.stabilizer A x).map (QuotientGroup.mk' H) ≤
      MulAction.stabilizer (A ⧸ H) (block H x) := by
  rintro _ ⟨g,hg,rfl⟩
  change (QuotientGroup.mk' H g) • block H x=block H x
  rw [mk_smul_block,hg]

lemma finite_stabilizer_image (x : X)
    (h : (MulAction.stabilizer (A ⧸ H) (block H x) : Set (A ⧸ H)).Finite) :
    ((MulAction.stabilizer A x).map (QuotientGroup.mk' H) : Set (A ⧸ H)).Finite :=
  h.subset (quotient_stabilizer_contains_image H x)

end CriticalPercolation.NormalOrbit
end
end

end OAI
