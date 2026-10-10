import OAI.AlgebraicGeometry.PlaneCurves.CoefficientTransforms

namespace OAI

/-!
# Necessary section data for normal polynomials; Polynomial multiplicity and compatibility at nine marked points; Nonzero loci of sections
-/

section

namespace Nagata.CoefficientSpaces
open Nagata.Workers.W28 Filter Topology

/-- The assembled actual polynomial has exactly the normal polynomial's ordinary
local analytic multiplicity after the genuine fibre change away from the divisor. -/
theorem transformed_polynomial_order_iff
    (F G : Polynomial (ℂ → ℂ)) (N m : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) (hG : ∀ j, N < j → G.coeff j = 0)
    (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (hfactor : ∀ j, ∀ z ∈ U, P z ^ m * G.coeff j z = P z ^ j * F.coeff j z)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun y : ℂ × ℂ => scalarExpression G y.1 y.2) x m ↔
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun y : ℂ × ℂ => scalarExpression F y.1 y.2)
      (x.1, P x.1 * x.2) m := by
  have he : (fun y : ℂ × ℂ => scalarExpression G y.1 y.2) =ᶠ[𝓝 x]
      (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹ * scalarExpression F y.1 (P y.1 * y.2)) := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hx] with y hy
    have hs := scalarExpression_transform F G N m hF hG P y.1 y.2
      (fun j => hfactor j y.1 hy)
    rw [← hs, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m (hne y.1 hy)), one_mul]
  have hc := Nagata.FiberCoordinateChange.order_preserved_by_fibre_substitution
    P U hU hP hne (fun y : ℂ × ℂ => scalarExpression F y.1 y.2) x hx m
  constructor
  · intro h
    exact hc.mp (h.congr he)
  · intro h
    exact (hc.mpr h).congr he.symm

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W28

/-- The actual necessary-W implication from the normal polynomial. It uses the
nine marked coefficient orders and the source multiplicities at all moving points.
The source normal-specialization theorem must supply precisely these inputs. -/
theorem necessary_W_of_normal_polynomial {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.automorphicSections τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i))
    (U : Set ℂ) (hU : IsOpen U) (hU0 : ∀ z ∈ U, z ≠ 0)
    (hUP : ∀ z ∈ U, (nineThetaSection hτ hτ0 a ha).val z ≠ 0)
    (p : ι → ℂ × ℂ) (hp : ∀ i, (p i).1 ∈ U)
    (hmoving : ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F y.1 y.2)
      ((p i).1, (nineThetaSection hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : polynomialSections τ L (∏ i, -a i) d (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  obtain ⟨G, hfactor, hne⟩ := exists_marked_transformed_polynomial hτ hτ0 hL a ha
    hdisjoint d m F hbound hsource hmarked
  refine ⟨G, hne hneF, ?_⟩
  intro i
  apply (transformed_polynomial_order_iff F G.val ((d / 3).toNat) m hbound G.property.1
    (nineThetaSection hτ hτ0 a ha).val U hU
    (fun z hz => Nagata.W08.automorphicSection_analyticAt _ (hU0 z hz)) hUP
    (fun j z hz => hfactor j z (hU0 z hz)) (p i) (hp i)).mpr
  exact hmoving i

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces

/-- The actual marked section in necessary-W and in the source basis is the
same function, including its prescribed value at the omitted origin. -/
theorem nineThetaSection_ray_eq {τ : ℝ} (hpos : 0 < τ) (hlt : τ < 1)
    (hτ : ‖(τ : ℂ)‖ < 1) (hτ0 : (τ : ℂ) ≠ 0) (ξ : Fin 9 → ℝ)
    (ha : ∀ i, ((τ ^ ξ i : ℝ) : ℂ) ≠ 0) :
    (nineThetaSection hτ hτ0 (fun i => ((τ ^ ξ i : ℝ) : ℂ)) ha).val =
      (Nagata.W22.rayMarkedSection hpos hlt ξ).val := rfl

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open Filter Topology

/-- The genuine nonvanishing locus of a section in the punctured covering plane. -/
def sectionNonzeroLocus {τ γ : ℂ} {n : ℤ}
    (P : Nagata.W08.automorphicSections τ n γ) : Set ℂ := {z | z ≠ 0 ∧ P.val z ≠ 0}

/-- Zero extension at the omitted origin does not obstruct the actual open
nonvanishing locus on the covering plane. -/
theorem isOpen_sectionNonzeroLocus {τ γ : ℂ} {n : ℤ}
    (P : Nagata.W08.automorphicSections τ n γ) : IsOpen (sectionNonzeroLocus P) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact (eventually_ne_nhds hz.1).and
    ((P.property.2.1 z hz.1).continuousAt.eventually_ne hz.2)

end Nagata.CoefficientSpaces

end

end OAI
