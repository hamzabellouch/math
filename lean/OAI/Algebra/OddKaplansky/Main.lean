import OAI.Algebra.OddKaplansky.SquareConstruction

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.Prescribed
noncomputable section
local instance prescribedDecidableEq (α : Type portUniverse1) : DecidableEq α := Classical.decEq α
open scoped Classical BigOperators
local notation "p" => SourceGluing.p
local notation "M" => SourceGluing.modulus
abbrev K := QuadraticTower.CoeffField p Construction.p_ne_two
instance : Fact (Irreducible (QuadraticTower.polynomial (QuadraticTower.xi p Construction.p_ne_two))) :=
  ⟨QuadraticTower.second_irreducible p Construction.p_ne_two Construction.minus_square⟩
instance : Field K := inferInstance
instance : Fintype K := inferInstance
instance : CharP K p :=
  charP_of_injective_ringHom ((algebraMap (QuadraticTower.FirstField p Construction.p_ne_two) K).comp
    (algebraMap (ZMod p) (QuadraticTower.FirstField p Construction.p_ne_two))).injective p
lemma card_field : Fintype.card K=p^4 := QuadraticTower.tower_card p Construction.p_ne_two

def zeta : K := @FiniteChoice.primitive K inferInstance inferInstance (QuadraticTower.fieldOrder p Construction.p_ne_two)
lemma zeta_primitive : IsPrimitiveRoot zeta M := by
  have h := @FiniteChoice.primitive_spec K inferInstance inferInstance (QuadraticTower.fieldOrder p Construction.p_ne_two)
  change IsPrimitiveRoot zeta (Fintype.card K-1) at h
  rw [card_field] at h
  simpa only [SourceGluing.modulus] using h
lemma zeta_le (z : K) (hz : IsPrimitiveRoot z M) :
    @LE.le K (QuadraticTower.fieldOrder p Construction.p_ne_two).toLE zeta z := by
  apply @FiniteChoice.primitive_le K inferInstance inferInstance (QuadraticTower.fieldOrder p Construction.p_ne_two) z
  rw [card_field]
  simpa only [SourceGluing.modulus] using hz

def localDatum : Construction.LocalDatum (K := K) := Construction.prescribedLocalDatum zeta_primitive card_field
def rectangles : Construction.Rectangular zeta_primitive localDatum := Construction.prescribedRectangles zeta_primitive localDatum
abbrev G := Construction.G
def a : MonoidAlgebra K G := Construction.a zeta_primitive localDatum rectangles
def b : MonoidAlgebra K G := Construction.b zeta_primitive localDatum rectangles
lemma products : a*b=1 ∧ b*a≠1 := Construction.scalar_products zeta_primitive localDatum rectangles
lemma torsion : ∃ g : G, g≠1 ∧ IsOfFinOrder g := Construction.torsion
lemma cellular_consequences :
    Cellular.IsCellular (Cellular.operator b) ∧ Function.Injective (Cellular.operator b) ∧
    ¬Function.Surjective (Cellular.operator b) ∧
    Set.range (Cellular.operator b)={y | Cellular.operator (b*a) y=y} ∧
    ∃ h : G, (b*a-1).coeff h ≠ 0 ∧ Pi.single h 1 ∉ Set.range (Cellular.operator b) := by
  obtain ⟨hcell,hinj,hnonsurj,hrange,h,hh,hm⟩ := Cellular.theorem_all_configurations a b products.1 products.2
  refine ⟨hcell,hinj,hnonsurj,hrange,h,hh,?_⟩
  have hdelta : @Pi.single G (fun _ => K) (fun _ => inferInstance) (Classical.decEq G) h 1 = (Pi.single h 1 : G → K) := by
    funext g
    by_cases hg : g=h <;> simp [hg]
  rw [← hdelta]
  exact hm
end
end OddKaplansky.Prescribed

namespace OddKaplansky
noncomputable section
local instance mainEndpointDecidableEq (α : Type portUniverse2) : DecidableEq α := Classical.decEq α
open scoped Classical

def cellular {K G : Type} [Field K] [Group G]
    (d : MonoidAlgebra K G) (x : G → K) (g : G) : K :=
  d.coeff.sum fun u c => c * x (g * u)
lemma cellular_eq_operator {K G : Type} [Field K] [Group G] (d : MonoidAlgebra K G) :
    cellular d=Cellular.operator d := by
  funext x g
  exact (Cellular.operator_formula d x g).symm

def MainClaim : Prop :=
  sourcePrime.Prime ∧ Odd sourcePrime ∧
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K sourcePrime),
    Fintype.card K = sourcePrime^4 ∧
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G,
        a * b = 1 ∧ b * a ≠ 1 ∧
        Function.Injective (cellular b) ∧ ¬ Function.Surjective (cellular b)

theorem main_theorem : MainClaim := by
  let : CharP Prescribed.K sourcePrime := by rw [← SourceGluing.p_def]; infer_instance
  refine ⟨sourcePrime_prime,sourcePrime_odd,Prescribed.K,inferInstance,inferInstance,inferInstance,?_,
    Prescribed.G,inferInstance,inferInstance,Prescribed.torsion,Prescribed.a,Prescribed.b,
    Prescribed.products.1,Prescribed.products.2,?_,?_⟩
  · rw [Prescribed.card_field,SourceGluing.p_def]
  · rw [cellular_eq_operator]
    exact Prescribed.cellular_consequences.2.1
  · rw [cellular_eq_operator]
    exact Prescribed.cellular_consequences.2.2.1

theorem fixed_field_transfer (K L : Type) [Field K] [Fintype K]
    [Group L] (hK : 3 ≤ Fintype.card K) (r : ℕ) (_hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) (MonoidAlgebra K L))
    (hAB : A * B = 1) (hBA : B * A ≠ 1) :
    ∃ (Λ : Type) (_ : Group Λ) (_ : Fintype Λ),
      ∃ a b : MonoidAlgebra K (L × Λ), a * b = 1 ∧ b * a ≠ 1 := by
  let M := Fintype.card K-1
  have hM : 2≤M := by dsimp [M]; omega
  let : NeZero M := ⟨by omega⟩
  obtain ⟨ζ,hζ,hc⟩ := FixedField.finite_field_data K hK
  refine ⟨Heisenberg.GroupData M (FixedField.leastQ M hM r),inferInstance,inferInstance,
    FixedField.output M hM r hζ A,FixedField.output M hM r hζ B,?_⟩
  exact FixedField.output_products M hM r hζ hc A B hAB hBA
end
end OddKaplansky

end

end OAI
