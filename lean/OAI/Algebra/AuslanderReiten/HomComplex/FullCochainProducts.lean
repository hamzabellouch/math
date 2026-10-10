import OAI.Algebra.AuslanderReiten.HomComplex.FullCochainTail

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

private theorem tailPrefix_congr {r : ℤ} (x : Cochain K K r) (p q : ℤ)
    (a b : ℕ) (hab : a=b) (ha : -(a : ℤ)=p) (hb : -(b : ℤ)=p)
    (hxa : -(a : ℤ)+r=q) (hxb : -(b : ℤ)+r=q) :
    ((completeExtResolution hK).cochainComplexXIso p a ha).hom ≫
      (tailTermIso K a).hom ≫ x.v (-(a : ℤ)) q hxa =
    ((completeExtResolution hK).cochainComplexXIso p b hb).hom ≫
      (tailTermIso K b).hom ≫ x.v (-(b : ℤ)) q hxb := by
  subst b
  rfl

theorem restrictedCocycle_product {r s : ℕ}
    (x : Cocycle K K (r : ℤ)) (y : Cocycle K K (s : ℤ)) :
    restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex (r+s)
      (ResolutionProducts.natCocycleProduct x y) =
      ResolutionProducts.natCocycleProduct
        (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex r x)
        (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex s y) := by
  change ↥(cocycle K K (r : ℤ)) at x
  change ↥(cocycle K K (s : ℤ)) at y
  apply Subtype.ext
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hq
    change (ResolutionProducts.natComparisonCochain _ _ (r+s) _).v _ _ _ = _
    erw [ResolutionProducts.natComparisonCochain_v_of_eq]
    erw [Cochain.comp_v _ _ _ _ (-((s+n : ℕ) : ℤ)) _ (by omega) (by omega)]
    change _ =
      (ResolutionProducts.natComparisonCochain _ _ r _).v _ _ _ ≫
        (ResolutionProducts.natComparisonCochain _ _ s _).v _ _ _
    erw [ResolutionProducts.natComparisonCochain_v_of_eq,
      ResolutionProducts.natComparisonCochain_v_of_eq]
    simp only [cochainTailMap, ResolutionProducts.natCocycleProduct,
      Cocycle.mk]
    try simp only [Nat.add_assoc]
    erw [Cochain.comp_v _ _ _ _ (-((s+n : ℕ) : ℤ)) _ (by omega) (by omega)]
    all_goals try omega
    let P := completeExtResolution hK
    let a := P.cochainComplexXIso p (r+(s+n)) (by omega)
    let b : P.complex.X (r+(s+n)) ≅ K.X (-((r+(s+n) : ℕ) : ℤ)) := tailTermIso K (r+(s+n))
    let c : P.complex.X (s+n) ≅ K.X (-((s+n : ℕ) : ℤ)) := tailTermIso K (s+n)
    let d := P.cochainComplexXIso (-((s+n : ℕ) : ℤ)) (s+n) rfl
    let e : P.complex.X n ≅ K.X (-(n : ℤ)) := tailTermIso K n
    let f := P.cochainComplexXIso (-(n : ℤ)) n rfl
    let xv := x.val.v (-((r+(s+n) : ℕ) : ℤ)) (-((s+n : ℕ) : ℤ)) (by omega)
    let yv := y.val.v (-((s+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
    have hh : a.hom ≫ (b.hom ≫ xv ≫ yv ≫ e.inv) ≫ f.inv =
        a.hom ≫ ((b.hom ≫ xv ≫ c.inv) ≫ d.inv) ≫ d.hom ≫
          (c.hom ≫ yv ≫ e.inv) ≫ f.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    convert! hh using 1
    dsimp only [a, b, c, d, e, f, xv, yv, P]
    have he := tailPrefix_congr K hK x.val p (-((s+n : ℕ) : ℤ))
      (r+s+n) (r+(s+n)) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hh' := congrArg (fun z => (z ≫ yv ≫ e.inv) ≫ f.inv) he
    exact hh'

  · exact ((completeExtResolution hK).cochainComplex.isZero_of_isStrictlyLE 0 q
      (by omega)).eq_of_tgt _ _

end ArExplicit.CompleteComparison

end

end OAI
