import OAI.Combinatorics.MatchingPSD.TableCoordinates

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

noncomputable def predicateAverage (P : X → Prop) : (X → ℝ) →ₗ[ℝ] ℝ :=
  (Fintype.card {x // P x} : ℝ)⁻¹ •
    ∑ x, if P x then LinearMap.proj x else 0

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

lemma predicateAverage_comp (P : X → Prop) (e : X ≃ X)
    (he : ∀ x, P (e x) ↔ P x) (f : X → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage P f := by
  rw [predicateAverage_apply, predicateAverage_apply]
  congr 1
  calc
    _ = ∑ x, if P (e x) then f (e x) else 0 := by simp only [he, Function.comp_apply]
    _ = _ := by
      apply Fintype.sum_equiv e
      intro x
      rfl

lemma predicateAverage_of_constant (P : X → Prop) (c : ℝ) (hP : ∃ x, P x)
    (f : X → ℝ) (hf : ∀ x, P x → f x = c) : predicateAverage P f = c := by
  classical
  have : Nonempty {x // P x} := ⟨⟨hP.choose, hP.choose_spec⟩⟩
  rw [predicateAverage_apply]
  have hs : (∑ x, if P x then f x else 0) = Fintype.card {x // P x} * c := by
    calc
      _ = ∑ x ∈ Finset.univ.filter P, f x := (Finset.sum_filter _ _).symm
      _ = ∑ _x ∈ Finset.univ.filter P, c := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hf x (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Fintype.card_subtype]
  rw [hs]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

lemma predicateAverage_colorAverage (z : V → C) (P : Pairing V → Prop)
    (hP : ∀ (p : colorStabilizer z) M, P (Pairing.relabel p.1 M) ↔ P M)
    (f : Pairing V → ℝ) :
    predicateAverage P (colorAverage z f) = predicateAverage P f := by
  classical
  have hp (p : colorStabilizer z) :
      predicateAverage P (Pairing.act p.1 f) = predicateAverage P f := by
    exact predicateAverage_comp P (Pairing.relabelEquiv p.1⁻¹) (hP p⁻¹) f
  simp only [colorAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, map_smul, map_sum]
  simp_rw [hp]
  simp [nsmul_eq_mul, Fintype.card_ne_zero]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

lemma table_average_polynomial (z : H × Bool → Fin 3) (d : ℕ)
    (f : Pairing (H × Bool) → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ t : Fin 6 → ℕ, (∃ M : Pairing (H × Bool), M.table z = t) →
        predicateAverage (fun M => M.table z = t) f =
          P (fun i => (t (threeEdgeType (crossPair i)) : ℝ)) := by
  obtain ⟨P, hP, hp⟩ := colorAverage_polynomial z d f hf
  refine ⟨P, hP, ?_⟩
  intro t ht
  have hInv (p : colorStabilizer z) (M : Pairing (H × Bool)) :
      (Pairing.relabel p.1 M).table z = t ↔ M.table z = t := by
    rw [Pairing.table_relabel]
    have hz : z ∘ p.1 = z := funext p.property
    rw [hz]
  rw [← predicateAverage_colorAverage z _ hInv]
  apply predicateAverage_of_constant _ _ ht
  intro M hM
  rw [hp]
  congr 1
  funext i
  rw [crossCoordinate_eq_table, hM]

end TablePolynomial
end MatchingSmoothing

end OAI
