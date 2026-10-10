import OAI.Probability.SwitchChain.IndependentCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.IndependentCell

variable {Ω α β : Type*} [Fintype Ω]

theorem projection_covariance_of_product_moments
    (X : Ω → α) (Y : Ω → β)
    (hindep : ∀ (u : α → ℝ) (v : β → ℝ),
      (∑ ω, u (X ω) * v (Y ω)) =
        (∑ ω, u (X ω)) * (∑ ω, v (Y ω)) / (Fintype.card Ω : ℝ))
    (f g : EuclideanSpace ℝ Ω) :
    ⟪PairFibers.expectation (Setoid.ker X) f,
      PairFibers.expectation (Setoid.ker Y) g⟫ =
      (∑ ω, f ω) * (∑ ω, g ω) / (Fintype.card Ω : ℝ) := by
  let p := PairFibers.expectation (Setoid.ker X) f
  let q := PairFibers.expectation (Setoid.ker Y) g
  have hp : Function.FactorsThrough (fun ω => p ω) X := by
    intro ω ν h
    exact PairFibers.expectation_constant (Setoid.ker X) f h
  have hq : Function.FactorsThrough (fun ω => q ω) Y := by
    intro ω ν h
    exact PairFibers.expectation_constant (Setoid.ker Y) g h
  obtain ⟨u, hu⟩ := (Function.factorsThrough_iff (fun ω => p ω)).mp hp
  obtain ⟨v, hv⟩ := (Function.factorsThrough_iff (fun ω => q ω)).mp hq
  have h := hindep u v
  have hup (ω : Ω) : u (X ω) = p ω := (congrFun hu ω).symm
  have hvq (ω : Ω) : v (Y ω) = q ω := (congrFun hv ω).symm
  simp_rw [hup, hvq] at h
  rw [inner_eq_sum]
  change (∑ ω, p ω * q ω) = _
  rw [h]
  change (∑ ω, PairFibers.expectation (Setoid.ker X) f ω) *
    (∑ ω, PairFibers.expectation (Setoid.ker Y) g ω) / _ = _
  rw [sum_expectation, sum_expectation]

theorem projection_covariance_of_average_products
    (X : Ω → α) (Y : Ω → β)
    (hindep : ∀ (u : α → ℝ) (v : β → ℝ),
      (∑ ω, u (X ω) * v (Y ω)) / (Fintype.card Ω : ℝ) =
        ((∑ ω, u (X ω)) / (Fintype.card Ω : ℝ)) *
          ((∑ ω, v (Y ω)) / (Fintype.card Ω : ℝ)))
    (f g : EuclideanSpace ℝ Ω) :
    ⟪PairFibers.expectation (Setoid.ker X) f,
      PairFibers.expectation (Setoid.ker Y) g⟫ =
      (∑ ω, f ω) * (∑ ω, g ω) / (Fintype.card Ω : ℝ) := by
  apply projection_covariance_of_product_moments X Y _ f g
  intro u v
  by_cases hN : (Fintype.card Ω : ℝ) = 0
  · have hc : Fintype.card Ω = 0 := by exact_mod_cast hN
    have : IsEmpty Ω := Fintype.card_eq_zero_iff.mp hc
    simp
  have h := hindep u v
  field_simp at h ⊢
  nlinarith

end Problem315.IndependentCell

end

end OAI
