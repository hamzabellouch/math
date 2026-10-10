import Mathlib
import OAI.Analysis.Commutator.CentralCorner
import OAI.Analysis.Commutator.ProjectionBlocks

namespace OAI

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CentralAtoms

open CentralCorner AtomicFactor ProjectionBlocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def Atom (M : VonNeumannAlgebra H) := {p : H →L[ℂ] H // IsMinimalProjection (CentralCorner.center M) p}

def projection (M : VonNeumannAlgebra H) (p : Atom M) : H →L[ℂ] H := p.val

lemma isProjection (M : VonNeumannAlgebra H) (p : Atom M) : IsStarProjection (projection M p) :=
  p.property.2.1

lemma orthogonal (M : VonNeumannAlgebra H) (p q : Atom M) (hpq : p≠q) :
    projection M p*projection M q=0 := by
  let a := projection M p
  let b := projection M q
  have ha : IsStarProjection a := isProjection M p
  have hb : IsStarProjection b := isProjection M q
  have hc : Commute a b := (((mem_center M _).mp p.property.1).2 b
    ((mem_center M _).mp q.property.1).1).symm
  have hab : IsStarProjection (a*b) := ha.mul hb hc
  have habM : a*b∈CentralCorner.center M := (CentralCorner.center M).mul_mem p.property.1 q.property.1
  have hpa : a*b≤a := (hab.le_iff_mul_eq_right ha).mpr (by rw [←mul_assoc,ha.isIdempotentElem.eq])
  have hqb : a*b≤b := (hab.le_iff_mul_eq_left hb).mpr (by rw [mul_assoc,hb.isIdempotentElem.eq])
  by_contra hn
  have heap : a*b=a := (p.property.2.2.2 _ habM hab hpa).resolve_left hn
  have heaq : a*b=b := (q.property.2.2.2 _ habM hab hqb).resolve_left hn
  exact hpq (Subtype.ext (heap.symm.trans heaq))

def part (M : VonNeumannAlgebra H) : H →L[ℂ] H := (space (projection M)).starProjection

lemma part_projection (M : VonNeumannAlgebra H) : IsStarProjection (part M) :=
  isStarProjection_starProjection

lemma part_mem_center (M : VonNeumannAlgebra H) : part M∈CentralCorner.center M := by
  apply (mem_center M _).mpr
  constructor
  · change part M∈(M : Set (H →L[ℂ] H))
    rw [←M.centralizer_centralizer]
    intro T hT
    exact (projection_commutes (projection M) (isProjection M) T (fun p =>
      (hT (projection M p) ((mem_center M _).mp p.property.1).1).symm)).symm
  · intro T hT
    exact (projection_commutes (projection M) (isProjection M) T (fun p =>
      ((mem_center M _).mp p.property.1).2 T hT)).symm

lemma part_mul (M : VonNeumannAlgebra H) (p : Atom M) : part M*projection M p=projection M p :=
  projection_left (projection M) p

theorem no_atom_below_complement (M : VonNeumannAlgebra H) (p : Atom M) :
    ¬projection M p≤1-part M := by
  intro hp
  have he := ((isProjection M p).le_iff_mul_eq_right (part_projection M).one_sub).mp hp
  rw [sub_mul,one_mul,part_mul,sub_self] at he
  exact p.property.2.2.1 he.symm

def IsAtomicCenter (M : VonNeumannAlgebra H) : Prop :=
  ∀ p∈CentralCorner.center M,IsStarProjection p → p≠0 → ∃ q : Atom M,projection M q≤p

lemma part_eq_one_of_atomic (M : VonNeumannAlgebra H) (h : IsAtomicCenter M) : part M=1 := by
  have hz : 1-part M=0 := by
    by_contra hn
    obtain ⟨q,hq⟩ := h (1-part M) ((CentralCorner.center M).sub_mem (CentralCorner.center M).one_mem (part_mem_center M))
      (part_projection M).one_sub hn
    exact no_atom_below_complement M q hq
  exact (sub_eq_zero.mp hz).symm

end Kadison.CentralAtoms
end
end

end OAI
