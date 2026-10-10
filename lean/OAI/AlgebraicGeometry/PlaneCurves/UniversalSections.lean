import OAI.AlgebraicGeometry.PlaneCurves.CoverNormal
import OAI.AlgebraicGeometry.PlaneCurves.NecessarySections

namespace OAI

/-!
# Nonzero necessary sections, marked Taylor orders, and local smooth constructions; Automorphic normal polynomials on curves and smooth curves
-/

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W28

/-- The actual necessary-W implication from the normal polynomial. It uses the
nine marked coefficient orders and the source multiplicities at all moving points.
The source normal-specialization theorem must supply precisely these inputs. -/
theorem necessary_W_at_nonzero_points {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.automorphicSections τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i))
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F y.1 y.2)
      ((p i).1, (nineThetaSection hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : polynomialSections τ L (∏ i, -a i) d (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  exact necessary_W_of_normal_polynomial hτ hτ0 hL a ha hdisjoint d m F hneF
    hbound hsource hmarked (sectionNonzeroLocus (nineThetaSection hτ hτ0 a ha))
    (isOpen_sectionNonzeroLocus _) (fun _ hz => hz.1) (fun _ hz => hz.2)
    p (fun i => ⟨hp0 i, hpP i⟩) hmoving

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W28

/-- The actual necessary-W implication from the normal polynomial. It uses the
nine marked coefficient orders and the source multiplicities at all moving points.
The source normal-specialization theorem must supply precisely these inputs. -/
theorem necessary_W_of_normal_Taylor_orders {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.automorphicSections τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hfixed : ∀ i : Fin 9, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F y.1 y.2) (a i, 0) m)
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F y.1 y.2)
      ((p i).1, (nineThetaSection hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : polynomialSections τ L (∏ i, -a i) d (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  exact necessary_W_at_nonzero_points hτ hτ0 hL a ha hdisjoint d m F hneF hbound
    hsource (fun j _ _ i => Nagata.W18.scalar_coefficient_order F (a i) m j (hfixed i))
    p hp0 hpP hmoving

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28

/-- The complete actual necessary-W transformation from an ambient polynomial
normal section restricted by genuine degree-three coordinate sections. The
nonzero restriction is a genuine polynomial inequality. -/
theorem necessary_W_of_nonzero_ambient_restriction {ι σ : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d m : ℕ) (X : σ → Nagata.W08.automorphicSections τ 3 L)
    (F : Polynomial (MvPolynomial σ ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - 3 * j))
    (hbound : ∀ j, d / 3 < j → F.coeff j = 0)
    (hneF : restrictedNormalPolynomial (fun i => (X i).val) F ≠ 0)
    (hfixed : ∀ i : Fin 9, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (ambientNormalScalar (fun i => (X i).val) F) (a i, 0) m)
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (ambientNormalScalar (fun i => (X i).val) F)
      ((p i).1, (nineThetaSection hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : polynomialSections τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  have hd : ((d : ℤ) / 3).toNat = d / 3 := by omega
  refine necessary_W_of_normal_Taylor_orders hτ hτ0 hL a ha hdisjoint (d : ℤ) m
    (restrictedNormalPolynomial (fun i => (X i).val) F)
    hneF ?_
    (restrictedNormalPolynomial_source_sections hτ0 X F d hhom hbound) ?_ p hp0 hpP ?_
  · rw [hd]
    exact restrictedNormalPolynomial_bound _ F _ hbound
  · intro i
    exact (restrictedNormalPolynomial_order_iff _ F (a i, 0) (ha i) m).mpr (hfixed i)
  · intro i
    exact (restrictedNormalPolynomial_order_iff _ F
      ((p i).1, (nineThetaSection hτ hτ0 a ha).val (p i).1 * (p i).2) (hp0 i) m).mpr (hmoving i)

end Nagata.CoefficientSpaces

end

section

namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.ProjectiveGeometry

theorem universalSupport_normal_polynomial_on_automorphic_curve
    {r d : ℕ} {m : Fin r → ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun a => (X a).val) =
      Ideal.span ({G} : Set _))
    (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, (X (chart b)).val (z b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun a => (X a).val) (chart b) (z b)))))
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) G))
      (normalizedCurvePoint (fun a => (X a).val) (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-3*n)) ∧
      (∀ n, d/3 < n → F.coeff n = 0) ∧
      restrictedNormalPolynomial (fun a => (X a).val) F ≠ 0 ∧
      ∀ b, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (Nagata.CoefficientSpaces.ambientNormalScalar (fun a => (X a).val) F)
        (z b,w b) (m b) := by
  have hmem : G ∈ Nagata.Workers.W25.polynomialRelationIdeal (fun a => (X a).val) := by
    rw [hrelations]
    exact Ideal.subset_span (by simp)
  have heq := (Nagata.Workers.W25.mem_polynomialRelationIdeal _ G).mp hmem
  obtain ⟨F,hhom,hweight,hne,horder⟩ :=
    universalSupport_covering_normal_polynomial hU G 3 hG (by decide)
      (fun a => (X a).val) chart z w hz hc
      (fun b a => Nagata.W08.automorphicSection_analyticAt (X a) (hz b)) heq hbase hpartial
  refine ⟨F,hhom,?_,restrictedNormalPolynomial_ne_zero_of_principal_relations
    (fun a => (X a).val) G hrelations F hne,horder⟩
  intro n hn
  by_contra hh
  have hw := hweight n hh
  omega

end Nagata.Workers.W17

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- The actual nine marked lifts followed by the moving base lifts. -/
def markedNormalBase {q : ℕ} (a : Fin 9 → ℂ) (p : Fin q → ℂ × ℂ) : Fin (9 + q) → ℂ :=
  Fin.addCases a (fun i => (p i).1)

/-- Zero normal displacements at the nine marks and Pi-scaled moving displacements. -/
def markedNormalFibre {q : ℕ} (P : ℂ → ℂ) (p : Fin q → ℂ × ℂ) : Fin (9 + q) → ℂ :=
  Fin.addCases (fun _ => 0) (fun i => P (p i).1 * (p i).2)

theorem universalSupport_necessary_W {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (p : Fin q → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val (p i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (markedNormalBase a p b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase a p b)))))
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) C))
      (normalizedCurvePoint (fun i => (X i).val) (chart b) (markedNormalBase a p b)) ≠ 0) :
    ∃ G : polynomialSections τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  have hz : ∀ b, markedNormalBase a p b ≠ 0 := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simpa only [markedNormalBase, Fin.addCases_left] using ha i
    · intro i
      simpa only [markedNormalBase, Fin.addCases_right] using hp0 i
  obtain ⟨F,hhom,hbound,hne,horders⟩ := universalSupport_normal_polynomial_on_automorphic_curve
    hU C hC X hrelations chart (markedNormalBase a p)
    (markedNormalFibre (nineThetaSection hτ hτ0 a ha).val p) hz hc hbase hpartial
  refine necessary_W_of_nonzero_ambient_restriction hτ hτ0 hL a ha hdisjoint d m X F
    hhom hbound hne ?_ p hp0 hpP ?_
  · intro i
    simpa only [markedNormalBase, markedNormalFibre, Fin.addCases_left] using
      horders (Fin.castAdd q i)
  · intro i
    simpa only [markedNormalBase, markedNormalFibre, Fin.addCases_right] using
      horders (Fin.natAdd 9 i)

end Nagata.CoefficientSpaces

end

section

namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.ProjectiveGeometry

theorem universalSupport_normal_polynomial_on_smooth_automorphic_curve
    {r d : ℕ} {m : Fin r → ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun a => (X a).val) =
      Ideal.span ({G} : Set _))
    (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, (X (chart b)).val (z b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun a => (X a).val) (chart b) (z b)))))
    (hdifferential : ∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) G)
      (normalizedCurvePoint (fun a => (X a).val) (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-3*n)) ∧
      (∀ n, d/3 < n → F.coeff n = 0) ∧
      restrictedNormalPolynomial (fun a => (X a).val) F ≠ 0 ∧
      ∀ b, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (Nagata.CoefficientSpaces.ambientNormalScalar (fun a => (X a).val) F)
        (z b,w b) (m b) := by
  have hmem : G ∈ Nagata.Workers.W25.polynomialRelationIdeal (fun a => (X a).val) := by
    rw [hrelations]
    exact Ideal.subset_span (by simp)
  have heq := (Nagata.Workers.W25.mem_polynomialRelationIdeal _ G).mp hmem
  obtain ⟨F,hhom,hweight,hne,horder⟩ :=
    universalSupport_smooth_covering_normal_polynomial hU G 3 hG (by decide)
      (fun a => (X a).val) chart z w hz hc
      (fun b a => Nagata.W08.automorphicSection_analyticAt (X a) (hz b)) heq hbase hdifferential
  refine ⟨F,hhom,?_,restrictedNormalPolynomial_ne_zero_of_principal_relations
    (fun a => (X a).val) G hrelations F hne,horder⟩
  intro n hn
  by_contra hh
  have hw := hweight n hh
  omega

end Nagata.Workers.W17

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- The genuine universal-support necessary-W conclusion in the actual local
logarithmic scalar coordinates used by the collision and jet maps. -/
theorem universalSupport_necessary_W_local {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (ξ : Fin q → ℂ)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val ((logarithmicPoints z₀ ξ) i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (markedNormalBase a (logarithmicPoints z₀ ξ) b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase a (logarithmicPoints z₀ ξ) b)))))
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) C))
      (normalizedCurvePoint (fun i => (X i).val) (chart b) (markedNormalBase a (logarithmicPoints z₀ ξ) b)) ≠ 0) :
    ∃ G : polynomialSections τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => Nagata.W20.localScalar G z₀ y.1 y.2) (ξ i, 0) m := by
  obtain ⟨G,hG,horder⟩ := universalSupport_necessary_W hU hτ hτ0 hL a ha hdisjoint
    (logarithmicPoints z₀ ξ) (fun i => mul_ne_zero hz₀ (Complex.exp_ne_zero (ξ i)))
    hpP C hC X hrelations chart hc hbase hpartial
  refine ⟨G,hG,fun i => ?_⟩
  exact localScalar_order_of_cover_order G z₀ (ξ i) (horder i)

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

theorem universalSupport_necessary_W_smooth {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (p : Fin q → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val (p i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (markedNormalBase a p b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase a p b)))))
    (hdifferential : ∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) C)
      (normalizedCurvePoint (fun i => (X i).val) (chart b) (markedNormalBase a p b)) ≠ 0) :
    ∃ G : polynomialSections τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => scalarExpression G.val y.1 y.2) (p i) m := by
  have hz : ∀ b, markedNormalBase a p b ≠ 0 := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simpa only [markedNormalBase, Fin.addCases_left] using ha i
    · intro i
      simpa only [markedNormalBase, Fin.addCases_right] using hp0 i
  obtain ⟨F,hhom,hbound,hne,horders⟩ := universalSupport_normal_polynomial_on_smooth_automorphic_curve
    hU C hC X hrelations chart (markedNormalBase a p)
    (markedNormalFibre (nineThetaSection hτ hτ0 a ha).val p) hz hc hbase hdifferential
  refine necessary_W_of_nonzero_ambient_restriction hτ hτ0 hL a ha hdisjoint d m X F
    hhom hbound hne ?_ p hp0 hpP ?_
  · intro i
    simpa only [markedNormalBase, markedNormalFibre, Fin.addCases_left] using
      horders (Fin.castAdd q i)
  · intro i
    simpa only [markedNormalBase, markedNormalFibre, Fin.addCases_right] using
      horders (Fin.natAdd 9 i)

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- The genuine universal-support necessary-W conclusion in the actual local
logarithmic scalar coordinates used by the collision and jet maps. -/
theorem universalSupport_necessary_W_smooth_local {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.UniversalSupport (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (ξ : Fin q → ℂ)
    (hpP : ∀ i, (nineThetaSection hτ hτ0 a ha).val ((logarithmicPoints z₀ ξ) i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.automorphicSections τ 3 L)
    (hrelations : Nagata.Workers.W25.polynomialRelationIdeal (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (markedNormalBase a (logarithmicPoints z₀ ξ) b) ≠ 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint (fun i => (X i).val) (chart b)
        (markedNormalBase a (logarithmicPoints z₀ ξ) b)))))
    (hdifferential : ∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) C)
      (normalizedCurvePoint (fun i => (X i).val) (chart b) (markedNormalBase a (logarithmicPoints z₀ ξ) b)) ≠ 0) :
    ∃ G : polynomialSections τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nineThetaSection hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun y : ℂ × ℂ => Nagata.W20.localScalar G z₀ y.1 y.2) (ξ i, 0) m := by
  obtain ⟨G,hG,horder⟩ := universalSupport_necessary_W_smooth hU hτ hτ0 hL a ha hdisjoint
    (logarithmicPoints z₀ ξ) (fun i => mul_ne_zero hz₀ (Complex.exp_ne_zero (ξ i)))
    hpP C hC X hrelations chart hc hbase hdifferential
  refine ⟨G,hG,fun i => ?_⟩
  exact localScalar_order_of_cover_order G z₀ (ξ i) (horder i)

end Nagata.CoefficientSpaces

end

end OAI
