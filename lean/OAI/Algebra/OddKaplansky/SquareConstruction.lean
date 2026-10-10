import OAI.Algebra.OddKaplansky.SectorConstruction

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.Construction
noncomputable section
local instance squareConstructionDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators Matrix
open SourceGluing SourceGraph
local notation "M" => SourceGluing.modulus
local notation "p" => SourceGluing.p
variable {K : Type} [Field K] [Fintype K] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
@[instance_reducible]

def slotOrder : LinearOrder SourceFit.Slot := LinearOrder.lift' (fun s => s.val.sort) (by
  intro s t h
  apply Subtype.ext
  simpa using congrArg List.toFinset h)
@[instance_reducible]
def lexOrder (α : Type portUniverse2) (β : Type portUniverse3) [LinearOrder α] [LinearOrder β] : LinearOrder (α×β) :=
  LinearOrder.lift' (fun a : α×β => toLex a) (fun _ _ h => h)
def orderedIndex (α : Type portUniverse4) [LinearOrder α] [Fintype α] : α ≃ Fin (Fintype.card α) :=
  (Fintype.orderIsoFinOfCardEq α rfl).symm.toEquiv
def smallIndex : Small ≃ Fin (Fintype.card Small) := @orderedIndex Small (@lexOrder W SourceFit.Slot inferInstance slotOrder) inferInstance
def largeIndex (d : LocalDatum (K := K)) : Large d ≃ Fin (Fintype.card (Large d)) :=
  @orderedIndex (Large d) (@lexOrder Vertex (N d) inferInstance inferInstance) inferInstance
def inclusion (d : LocalDatum (K := K)) : Small → Large d := IndexCut.inclusion smallIndex (largeIndex d) (sizes d)
lemma inclusion_injective (d : LocalDatum (K := K)) : Function.Injective (inclusion d) := IndexCut.injective smallIndex (largeIndex d) (sizes d)
def extra (d : LocalDatum (K := K)) : Large d := IndexCut.extra (largeIndex d) (sizes d)
lemma inclusion_ne_extra (d : LocalDatum (K := K)) (i : Small) : inclusion d i≠extra d :=
  IndexCut.misses smallIndex (largeIndex d) (sizes d) i

def squareA (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small Small (R (K := K)) :=
  SquareCertificate.A (f hζ) (inclusion d) (D hζ d rect)
def squareB (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix Small Small (R (K := K)) :=
  SquareCertificate.B (f hζ) (inclusion d) (C hζ d rect)
lemma square_products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) :
    squareA hζ d rect*squareB hζ d rect=1 ∧ squareB hζ d rect*squareA hζ d rect≠1 := by
  constructor
  · convert SquareCertificate.products (f hζ) (f_idem hζ) (f_commute hζ) (inclusion d) (inclusion_injective d)
      (C hζ d rect) (D hζ d rect) (C_sector hζ d rect) (D_sector hζ d rect) (DC_classical hζ d rect) using 1 <;> congr ; exact Subsingleton.elim _ _
  · convert SquareCertificate.reverse_ne (f hζ) (f_idem hζ) (f_nonzero hζ) (f_commute hζ) (inclusion d)
      (C hζ d rect) (D hζ d rect) (C_sector hζ d rect) (DC_classical hζ d rect) (extra d) (inclusion_ne_extra d) using 1 <;> congr ; exact Subsingleton.elim _ _
lemma visible_certificate (d : LocalDatum (K := K)) (rect : Rectangular hζ d) :
    SquareCertificate.v (f hζ) (C hζ d rect) (extra d)≠0 ∧
    D hζ d rect *ᵥ SquareCertificate.v (f hζ) (C hζ d rect) (extra d)=SquareCertificate.u (f hζ) (extra d) ∧
    squareA hζ d rect *ᵥ SquareCertificate.v (f hζ) (C hζ d rect) (extra d)=0 ∧
    (squareB hζ d rect*squareA hζ d rect-1) *ᵥ SquareCertificate.v (f hζ) (C hζ d rect) (extra d)= -SquareCertificate.v (f hζ) (C hζ d rect) (extra d) := by
  obtain ⟨hv,hDv,hAv,hdef⟩ := SquareCertificate.certificate (f hζ) (f_idem hζ) (f_nonzero hζ) (f_commute hζ) (inclusion d)
    (C hζ d rect) (D hζ d rect) (C_sector hζ d rect) (DC_classical hζ d rect) (extra d) (inclusion_ne_extra d)
  refine ⟨hv,hDv,hAv,?_⟩
  simpa only [squareA,squareB,Matrix.sub_mulVec,Matrix.one_mulVec] using hdef

def A (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Fin (Fintype.card Small)) (Fin (Fintype.card Small)) (R (K := K)) :=
  Matrix.reindexAlgEquiv K (R (K := K)) smallIndex (squareA hζ d rect)
def B (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : Matrix (Fin (Fintype.card Small)) (Fin (Fintype.card Small)) (R (K := K)) :=
  Matrix.reindexAlgEquiv K (R (K := K)) smallIndex (squareB hζ d rect)
lemma products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : A hζ d rect*B hζ d rect=1 ∧ B hζ d rect*A hζ d rect≠1 := by
  let E := Matrix.reindexAlgEquiv K (R (K := K)) smallIndex
  have hone : E 1=1 := map_one E
  have hmul : ∀ X Y, E (X*Y)=E X*E Y := fun X Y => map_mul E X Y
  constructor
  · change E (squareA hζ d rect)*E (squareB hζ d rect)=1
    rw [← hmul,(square_products hζ d rect).1,hone]
  · intro he
    apply (square_products hζ d rect).2
    apply E.injective
    rw [hmul,hone]
    exact he
lemma modulus_ge_two : 2≤M := by have := SourceGluing.modulus_gt; omega
def q : ℕ := FixedField.leastQ M modulus_ge_two (Fintype.card Small)
abbrev Λ := Heisenberg.GroupData M q
abbrev G := G₁×Λ
instance : Group.FG G := inferInstance

def a (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : MonoidAlgebra K G :=
  FixedField.output M modulus_ge_two (Fintype.card Small) hζ (A hζ d rect)
def b (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : MonoidAlgebra K G :=
  FixedField.output M modulus_ge_two (Fintype.card Small) hζ (B hζ d rect)
lemma scalar_products (d : LocalDatum (K := K)) (rect : Rectangular hζ d) : a hζ d rect*b hζ d rect=1 ∧ b hζ d rect*a hζ d rect≠1 := by
  exact FixedField.output_products M modulus_ge_two (Fintype.card Small) hζ (modulus_cast (K := K))
    (A hζ d rect) (B hζ d rect) (products hζ d rect).1 (products hζ d rect).2
lemma torsion : ∃ g : G, g≠1 ∧ IsOfFinOrder g := by
  let c : Fourier.C M := Multiplicative.ofAdd (1 : ZMod M)
  have hc : c≠1 := by
    intro h
    have he : (1 : ZMod M)=0 := congrArg Multiplicative.toAdd h
    have hd : M∣1 := (ZMod.natCast_eq_zero_iff 1 M).mp (by simpa only [Nat.cast_one] using he)
    have := Nat.dvd_one.mp hd
    have := SourceGluing.modulus_gt
    omega
  let z : Λ := Heisenberg.central M q c
  have hz : z≠1 := by
    intro h
    apply hc
    apply Heisenberg.central_injective M q
    simpa only [map_one] using h
  refine ⟨(1,z),?_,?_⟩
  · intro he
    exact hz (congrArg Prod.snd he)
  · exact (MonoidHom.inr G₁ Λ).isOfFinOrder (isOfFinOrder_of_finite z)
end
end OddKaplansky.Construction

end

end OAI
