import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleSingleton
import OAI.NumberTheory.CubicMoment.Angular.AngularTripleTransitionSmoothed

namespace OAI

/-! The transition estimate for the actual independently weighted
three-prime tuple, with one specified coordinate separated from the other
two. All analytic hypotheses are the cited published inputs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_large_tuple_triple_transition_smoothed {i j : ℕ} (hij : i+j = 3)
    (a : Fin i ⊕ Fin j) (hpnt : PrimaryPrimePNT)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (u : ℝ),
      let B := largeTupleNormScale z.1.2 a
      let A := largeTupleGroupLength (Finset.univ\{a}) z
      T₀ ≤ B → (2*B)^(1/2:ℝ) < B → B^(1-η/4) ≤ A → A ≤ B^2 →
      |u| ≤ (1+Real.log B)^U →
      (∀ b : {b : Fin i ⊕ Fin j // b ∉ ({a} : Finset _)}, B^c ≤ largeTupleNormScale z.1.2 b) →
      ‖largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 {a} u‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(3/2:ℝ) := by
  let L := fun z : largeTupleBoxIndex i j => largeTupleNormScale z.1.2 a
  let W := fun z : largeTupleBoxIndex i j => largeTupleCoordinateWeight ξ z.1.1 z.1.2 a
  have hW : UniformLogWeights W :=
    (largeTupleCoordinateWeights i j ξ).reindex (fun z : largeTupleBoxIndex i j => (z.1,a))
  obtain ⟨η,K,T₀,hη,hη1,hK,hbound⟩ := angular_two_prime_transition_smoothed ℓ
    (triple_other_card hij a) hpnt hSW hℓ hpub hHuxley hperiod hMV hC hc hGI hGQ
    L W (fun z => z.property a) hW
    (fun z _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x) U
  refine ⟨η,K,T₀,hη,hη1,hK,?_⟩
  intro z u
  dsimp only
  intro hT hrough hlo hhi hu hrest
  rw [largeTupleSmoothedPolynomial_singleton]
  exact hbound z (largeTupleGroupLength (Finset.univ\{a}) z) z.1.1 u
    (fun b => largeTupleCoordinateWeight ξ z.1.1 z.1.2 b)
    (fun b => largeTupleNormScale z.1.2 b)
    hT hrough hlo hhi z.1.1.property hu
    (largeTupleRestrictedLength_notMem {a} z) hrest
    (fun b _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 b hx)
    (fun b _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 b hx)
    (fun b x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 b x)

end CubicFirstMoment

end

end OAI
