import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CenteredGaussProgram

namespace OAI

/-! The emitted centered label list is exactly the finite cell-by-eight-node
grid used by the Coulomb quadrature theorems. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CenteredGaussLabels

def decode (i : GaussLatticeIndex) : TransformedGauss.Label :=
  ((i.1 0,(i.1 1,i.1 2)),(decide (i.2 0=1),(decide (i.2 1=1),decide (i.2 2=1))))

private theorem bit_value (v : Fin 2) : (if decide (v=1) then (1:Fin 2) else 0) = v := by
  fin_cases v <;> decide

@[simp] theorem index_decode (i : GaussLatticeIndex) :
    RationalGaussNodes.index (decode i).1 (decode i).2 = i := by
  apply Prod.ext
  · funext a
    fin_cases a <;> rfl
  · funext a
    fin_cases a <;> exact bit_value _

@[simp] theorem decode_index (l : TransformedGauss.Label) :
    decode (RationalGaussNodes.index l.1 l.2) = l := by
  apply TransformedGauss.index_injective
  exact index_decode _

def indexEquiv : TransformedGauss.Label ≃ GaussLatticeIndex where
  toFun l := RationalGaussNodes.index l.1 l.2
  invFun := decode
  left_inv := decode_index
  right_inv := index_decode

abbrev Grid (r : Radii) :=
  {k // k ∈ centeredGridIndices (radiiVector r)} × (Fin 3 → Fin 2)

def restrictedEquiv (r : Radii) : {l // l ∈ labels r} ≃ Grid r where
  toFun l := (⟨(indexEquiv l.val).1,(mem_labels r l.val).mp l.property⟩,(indexEquiv l.val).2)
  invFun kv := ⟨decode (kv.1.val,kv.2),(mem_labels r _).mpr (by
    rw [index_decode]
    exact kv.1.property)⟩
  left_inv l := Subtype.ext (decode_index l.val)
  right_inv kv := by
    have he := index_decode (kv.1.val,kv.2)
    have h1 : (indexEquiv (decode (kv.1.val,kv.2))).1 = kv.1.val :=
      congrArg (fun p : GaussLatticeIndex => p.1) he
    have h2 : (indexEquiv (decode (kv.1.val,kv.2))).2 = kv.2 :=
      congrArg (fun p : GaussLatticeIndex => p.2) he
    exact Prod.ext (Subtype.ext h1) h2

def enumerationEquiv (r : Radii) : Fin (labels r).length ≃ Grid r :=
  (List.Nodup.getEquiv (labels r) (labels_nodup r)).trans (restrictedEquiv r)

@[simp] theorem enumeration_first (r : Radii) (a : Fin (labels r).length) :
    (enumerationEquiv r a).1.val = (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2).1 := rfl

@[simp] theorem enumeration_second (r : Radii) (a : Fin (labels r).length) :
    (enumerationEquiv r a).2 = (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2).2 := rfl

theorem sum_enumeration {A : Type*} [AddCommMonoid A] (r : Radii) (f : GaussLatticeIndex → A) :
    (∑ a : Fin (labels r).length,
      f (RationalGaussNodes.index ((labels r).get a).1 ((labels r).get a).2)) =
    ∑ k : {k // k ∈ centeredGridIndices (radiiVector r)}, ∑ v : Fin 3 → Fin 2, f (k.val,v) := by
  have he := (enumerationEquiv r).sum_comp (fun kv : Grid r => f (kv.1.val,kv.2))
  simpa only [Fintype.sum_prod_type,enumeration_first,enumeration_second] using he

end ContinuumCoulomb.CenteredGaussLabels

end

end OAI
