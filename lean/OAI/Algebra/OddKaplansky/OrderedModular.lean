import OAI.Algebra.OddKaplansky.ModularSource

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6

section
namespace OddKaplansky.SourceOrders
noncomputable section
open scoped Classical
@[instance_reducible]
def cyclic (M : ℕ) [NeZero M] : LinearOrder (Fourier.C M) :=
  @FiniteChoice.multiplicativeOrder (ZMod M) (FiniteChoice.residueOrder M)
@[instance_reducible]
def point (p : ℕ) [NeZero p] : LinearOrder (Multiplicative (Fin 3 → ZMod p)) :=
  @FiniteChoice.multiplicativeOrder (Fin 3 → ZMod p)
    (@FiniteChoice.functionOrder (Fin 3) (ZMod p) inferInstance inferInstance (FiniteChoice.residueOrder p))
@[instance_reducible]
def character (p M : ℕ) [NeZero p] [NeZero M] :
    LinearOrder (WreathFourier.Base (H := Multiplicative (Fin 3 → ZMod p)) M) :=
  @FiniteChoice.functionOrder _ _ inferInstance (point p) (cyclic M)
end
end OddKaplansky.SourceOrders

namespace OddKaplansky.OrbitSelection.Ordered
noncomputable section
open scoped Classical BigOperators
variable {H : Type portUniverse1} {A : Type portUniverse2} [Group H] [sectionInstance42 : Fintype H] [Fintype A] [MulAction H A]
variable (order : LinearOrder A) (good : A → Prop)
def representative (r : Rep (H := H) good) : A :=
  @FiniteChoice.first A inferInstance order
    (fun a : A => (Quotient.mk'' a : MulAction.orbitRel.Quotient H A)=r.val ∧ good a) r.property
lemma representative_spec
    {H : Type contextUniverse1}
    {A : Type contextUniverse2}
    [contextInstance2 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [Fintype.{contextUniverse2} A]
    [@MulAction.{contextUniverse1, contextUniverse2} H A (@DivInvMonoid.toMonoid.{contextUniverse1} H (@Group.toDivInvMonoid.{contextUniverse1} H contextInstance2))]
    (order : LinearOrder.{contextUniverse2} A)
    (good : A → Prop) (r : Rep (H := H) good) :
    (Quotient.mk'' (representative order good r) : MulAction.orbitRel.Quotient H A) = r.val ∧ good (representative order good r) := by
  exact @FiniteChoice.first_spec A inferInstance order
    (fun a : A => (Quotient.mk'' a : MulAction.orbitRel.Quotient H A)=r.val ∧ good a) r.property
lemma representative_le
    {H : Type contextUniverse1}
    {A : Type contextUniverse2}
    [contextInstance2 : Group.{contextUniverse1} H]
    [Fintype.{contextUniverse1} H]
    [Fintype.{contextUniverse2} A]
    [@MulAction.{contextUniverse1, contextUniverse2} H A (@DivInvMonoid.toMonoid.{contextUniverse1} H (@Group.toDivInvMonoid.{contextUniverse1} H contextInstance2))]
    (order : LinearOrder.{contextUniverse2} A)
    (good : A → Prop) (r : Rep (H := H) good) (a : A)
    (he : (Quotient.mk'' a : MulAction.orbitRel.Quotient H A)=r.val) (ha : good a) :
    @LE.le A order.toLE (representative order good r) a :=
  @FiniteChoice.first_le A inferInstance order _ r.property a ⟨he,ha⟩
lemma orbit_injective (hfree : ∀ a, good a → ∀ g : H, g • a = a → g = 1) :
    Function.Injective (fun r : Rep (H := H) good × H => r.2 • representative order good r.1) := by
  rintro ⟨r,g⟩ ⟨s,h⟩ he
  have hrs : r = s := by
    apply Subtype.ext
    have hh := congrArg (Quotient.mk'' : A → MulAction.orbitRel.Quotient H A) he
    simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq,(representative_spec order good r).1,(representative_spec order good s).1] using hh
  subst s
  have hh : h⁻¹*g = 1 := by
    apply hfree (representative order good r) (representative_spec order good r).2
    simpa only [mul_smul,inv_smul_smul] using congrArg (fun a : A => h⁻¹ • a) he
  have hgh : g = h := (inv_mul_eq_one.mp hh).symm
  subst g
  rfl
end
end OddKaplansky.OrbitSelection.Ordered

namespace OddKaplansky.WreathFourier
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse3} {H : Type portUniverse4} {I : Type portUniverse5} [Field K] [Fintype K] [Group H] [Fintype H] [Fintype I]
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (order : LinearOrder (Base (H := H) M)) (B : Matrix H I K)

def modularElement : MonoidAlgebra K (Wreath (H := H) M) := by
  letI : MulAction H (Base (H := H) M) := shiftAction M
  exact Blocks.element M hζ B (OrbitSelection.Ordered.representative (H := H) order (Admissible M hζ B))
lemma modularElement_properties (hM : Fintype.card Kˣ = M)
    (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0) (hB : LinearIndependent K B.col)
    (ell : ℕ) (hleft : ∀ s : H, (TranslationMatrix.matrix (K := K) s - 1)^ell * B = 0)
    (hright : ∀ s : H, B.transpose * (TranslationMatrix.matrix (K := K) s - 1)^ell = 0)
    (hI : 4 * Fintype.card I < M) (hH : 4 * (Fintype.card H - 1) < M)
    (hlarge : Fintype.card H < 48 * Fintype.card I) :
    modularElement M hζ order B*modularElement M hζ order B=modularElement M hζ order B ∧
      (∀ s : H, (topElt M s-1)^ell*modularElement M hζ order B=0 ∧
        modularElement M hζ order B*(baseElt M (lamp (H := H) M)*topElt M s*baseElt M (lamp (H := H) M)⁻¹-1)^ell=0) ∧
      Fintype.card (Wreath (H := H) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ (modularElement M hζ order B))) := by
  let : MulAction H (Base (H := H) M) := shiftAction M
  let R := OrbitSelection.Rep (H := H) (Admissible M hζ B)
  let lmb : R → Base (H := H) M := OrbitSelection.Ordered.representative (H := H) order (Admissible M hζ B)
  have hlmb (r : R) : Admissible M hζ B (lmb r) := (OrbitSelection.Ordered.representative_spec order (Admissible M hζ B) r).2
  have hinj : Function.Injective (fun a : R × H => shift M a.2 (lmb a.1)) := by
    apply OrbitSelection.Ordered.orbit_injective order (Admissible M hζ B)
    intro a ha g hga
    exact ha.1 g (congrFun hga)
  have hN (r : R) : (WeightedProjection.gram B (Blocks.weights M hζ lmb r)).det ≠ 0 := (hlmb r).2
  change Blocks.element M hζ B lmb*Blocks.element M hζ B lmb=Blocks.element M hζ B lmb ∧ _
  refine ⟨Blocks.idempotent M hζ B lmb hc hinj hN,Blocks.annihilate M hζ B lmb ell hleft hright,?_⟩
  have hd := Blocks.rank_bound M hζ B lmb hc hinj hN
  have ha := cardinality M hζ hM B hB hI hH
  have hb := OrbitSelection.card_good (H := H) (Admissible M hζ B)
  change Fintype.card {a // Admissible M hζ B a} ≤ Fintype.card R * Fintype.card H at hb
  have hbase : 0 < Fintype.card (Base (H := H) M) := Fintype.card_pos
  have hR : 0 < Fintype.card R := by nlinarith
  have hsmall : Fintype.card (Base (H := H) M) < 96 * Fintype.card R * Fintype.card I := by
    have hh := Nat.mul_lt_mul_of_pos_left hlarge hR
    nlinarith
  have hn : 0 < Fintype.card H := Fintype.card_pos
  have hw := Nat.mul_lt_mul_of_pos_right hsmall hn
  have hcard : Fintype.card (Wreath (H := H) M) = Fintype.card (Base (H := H) M) * Fintype.card H := by
    rw [← Fintype.card_prod]
    apply Fintype.card_congr
    exact { toFun := fun g => (g.left,g.right)
            invFun := fun z => ⟨z.1,z.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [hcard]
  change Fintype.card (Base (H := H) M)*Fintype.card H<96*Module.finrank K (LinearMap.range (Algebra.lmul K _ (Blocks.element M hζ B lmb)))
  nlinarith
end
end OddKaplansky.WreathFourier

namespace OddKaplansky.ModularSource
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse6} [Field K] [Fintype K]
variable (p M ell : ℕ) [Fact p.Prime] [NeZero M] [CharP K p]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ M)
def explicitElement : MonoidAlgebra K (WreathFourier.Wreath (H := P p) M) :=
  WreathFourier.modularElement M hζ (SourceOrders.character p M) (Augmentation.columns (K := K) (E := Fin 3) p ell)
lemma explicit_properties (hp : 5 ≤ p) (hpell : p=2*ell+1) (hM : M+1=p^4)
    (hK : Fintype.card Kˣ = M) :
    explicitElement p M ell hζ*explicitElement p M ell hζ=explicitElement p M ell hζ ∧
      (∀ s : P p, (WreathFourier.topElt M s-1)^ell*explicitElement p M ell hζ=0 ∧
        explicitElement p M ell hζ*(WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)*WreathFourier.topElt M s*WreathFourier.baseElt M (WreathFourier.lamp (H := P p) M)⁻¹-1)^ell=0) ∧
      Fintype.card (WreathFourier.Wreath (H := P p) M) < 96 * Module.finrank K (LinearMap.range (Algebra.lmul K _ (explicitElement p M ell hζ))) := by
  apply WreathFourier.modularElement_properties M hζ (SourceOrders.character p M)
    (Augmentation.columns (K := K) (E := Fin 3) p ell) hK
    (by simpa only [Fintype.card_eq_nat_card] using base_nonzero (K := K) p M hM)
    (Augmentation.columns_independent (K := K) (E := Fin 3) p ell) ell
    (by intro s; convert left_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by intro s; convert right_ann (K := K) p ell s using 1 ; congr <;> exact Subsingleton.elim _ _)
    (by simpa only [Fintype.card_eq_nat_card] using high_small p M ell hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using point_small p M hp hM)
    (by simpa only [Fintype.card_eq_nat_card] using high_large p ell hp hpell)
end
end OddKaplansky.ModularSource

end

end OAI
