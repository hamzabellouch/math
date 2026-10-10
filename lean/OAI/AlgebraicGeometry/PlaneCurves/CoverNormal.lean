import OAI.AlgebraicGeometry.PlaneCurves.HomogeneousFamilies
import OAI.AlgebraicGeometry.PlaneCurves.NormalSpecialization
import OAI.AlgebraicGeometry.PlaneCurves.SectionOrder
import OAI.AlgebraicGeometry.PlaneCurves.UniversalFamilies

namespace OAI

/-!
# Universal normal polynomials on line and smooth curve coverings
-/

section

/-! Genuine universal support produces one normalized homogeneous polynomial
family whose actual chart multiplicities hold at every parameter. -/

namespace Nagata.Workers.W17
open Nagata.W27 Nagata.Workers.W14 Nagata.ProjectiveGeometry

/-- A polynomial kernel family specializes to actual chart ideal powers. -/
theorem indexedPlaneFamily_chart_orders {r d : ℕ} (m : Fin r → ℕ)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (q : HomogeneousMonomial d → Polynomial ℂ)
    (hq : (parameterMatrix (chartPlaneJetMatrix c d m) p).mulVec q = 0)
    (s : ℂ) :
    ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => (p (i,j)).eval s) (m i)
      (directChartHom (c i) ((indexedPlaneFamily d q).eval (MvPolynomial.C s))) := by
  have hspec := Nagata.W18.specialize_polynomial_kernel
    (parameterMatrix (chartPlaneJetMatrix c d m) p) q hq s
  rw [parameterMatrix_mulVec] at hspec
  let F := (homogeneousCoordinates (R := ℂ) d).symm (fun ν => (q ν).eval s)
  have hcoord : homogeneousCoordinates d F = fun ν => (q ν).eval s :=
    (homogeneousCoordinates d).apply_symm_apply _
  have horders := (chart_orders_iff_kernel c d m (fun ij => (p ij).eval s) F).mpr
    (by rw [hcoord]; exact hspec)
  simpa only [eval_indexedPlaneFamily_eq_coordinates_symm, F] using horders

/-- The actual family is nonzero at parameter zero and homogeneous of degree d;
all moving-configuration ordinary orders hold without a genericity assumption
on the parameter after the polynomial kernel identity is established. -/
theorem universalSupport_polynomial_family {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ S : Polynomial (MvPolynomial (Fin 3) ℂ),
      S.coeff 0 ≠ 0 ∧ (∀ α, (S.coeff α).IsHomogeneous d) ∧
      ∀ s i, Nagata.AffineMultiplicity.orderAtLeast (fun j => (p (i,j)).eval s) (m i)
        (directChartHom (c i) (S.eval (MvPolynomial.C s))) := by
  obtain ⟨q, hzero, hq⟩ := universalSupport_normalized_parameter_family hU c p hbase
  exact ⟨indexedPlaneFamily d q, indexedPlaneFamily_constant_ne_zero d q hzero,
    indexedPlaneFamily_homogeneous d q, indexedPlaneFamily_chart_orders m c p q hq⟩

end Nagata.Workers.W17

end

section

namespace Nagata.Workers.W17
open scoped BigOperators
open Nagata.ProjectiveGeometry

/-- The complete algebraic input to normal specialization comes from actual
universal homogeneous equations along any distinct-based polynomial motion. -/
theorem universalSupport_degree_bounded_normal_data {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0)))
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k) :
    ∃ (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ),
      (∀ α ∈ I, ¬G ∣ T α) ∧
      (∀ α ∈ I, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ I, u ≤ α + j α) ∧ u ≤ d / k ∧
      (I.filter (fun α => α + j α = u)).Nonempty ∧
      ((liftedNormalPolynomial (I.filter (fun α => α + j α = u)) j T).map
        (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ))))) ≠ 0 ∧
      ∀ s i, Nagata.AffineMultiplicity.orderAtLeast (fun z => (p (i,z)).eval s) (m i)
        (Nagata.Workers.W28.factoredPlaneFamily I j
          (fun α => Nagata.W27.directChartHom (c i) (T α))
          (Nagata.W27.directChartHom (c i) G) s) := by
  classical
  obtain ⟨S, hzero, hcoeff, horders⟩ := universalSupport_polynomial_family hU c p hbase
  obtain ⟨j, T, u, hfactor, hnot, hdeg, hmin, hu, hsel, hinit⟩ :=
    exists_degree_bounded_plane_initial S G d k hcoeff hG hunit hk hzero
  refine ⟨S.support, j, T, u, hnot, hdeg, hmin, hu, hsel, ?_, ?_⟩
  · simpa only [map_liftedNormalPolynomial] using hinit
  · intro s i
    rw [← directChart_factored_family S G j T hfactor (c i) s]
    exact horders s i

end Nagata.Workers.W17

end

section

/-! Literal polynomial motions with prescribed homogeneous normal displacement.
The vectors are constructed from the actual partial derivative, never supplied
by a normal-bundle existence field. -/
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.ProjectiveGeometry

/-- Ordered affine coordinates of an actual complex-plane point. -/
def planeCoordinate (p : ComplexPlane) (a : Fin 2) : ℂ := if a = 0 then p.1 else p.2

/-- A literal polynomial affine motion, valid for every parameter. -/
def affineCoordinateMotion (p V : ComplexPlane) (a : Fin 2) : Polynomial ℂ :=
  Polynomial.C (planeCoordinate p a) + Polynomial.X * Polynomial.C (planeCoordinate V a)

@[simp] theorem affineCoordinateMotion_eval (p V : ComplexPlane) (a : Fin 2) (s : ℂ) :
    (affineCoordinateMotion p V a).eval s = planeCoordinate (p+s • V) a := by
  simp only [affineCoordinateMotion, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  dsimp only [planeCoordinate]
  split_ifs <;> simp

/-- Vertical velocity lifting a prescribed covering-frame normal coordinate. -/
def coveringNormalVelocity (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z w : ℂ) : ComplexPlane :=
  (0, (w/(X c z)^k) /
    planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z))

theorem coveringNormalVelocity_derivative (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z w : ℂ)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom c G))
      (normalizedCurvePoint X c z) ≠ 0) :
    polynomialGradient (Nagata.W27.directChartHom c G) (normalizedCurvePoint X c z)
      (coveringNormalVelocity G k X c z w) = w/(X c z)^k := by
  change _ * 0 + _ * ((w/(X c z)^k) / _) = _
  rw [mul_zero, zero_add]
  exact mul_div_cancel₀ _ hpartial

/-- The parameter-zero tuple of these motions is exactly the given genuine
projective tuple in its selected affine charts. -/
theorem coveringMotion_base_injective {r : ℕ}
    (c : Fin r → Fin 3) (p V : Fin r → ComplexPlane)
    (hbase : Function.Injective (fun b => chartPoint₂ (c b) (planeCoordinate (p b)))) :
    Function.Injective (configurationChartEmbedding c
      (fun ba => (affineCoordinateMotion (p ba.1) (V ba.1) ba.2).eval 0)) := by
  change Function.Injective (fun index => chartPoint₂ (c index)
    (fun coordinate => (affineCoordinateMotion (p index) (V index) coordinate).eval 0))
  simpa only [affineCoordinateMotion_eval, zero_smul, add_zero] using hbase

end Nagata.Workers.W17

end
end

section

/-! Simultaneous normal specialization on actual smooth marked line components.
The prescribed normal displacements are arbitrary; vertical velocities are
constructed by division by the actual nonzero normal partial derivative. -/
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.ProjectiveGeometry Nagata.Workers.W28

/-- Actual universal plane equations give selected homogeneous lifts with
ordinary surface orders at every prescribed normal displacement. -/
theorem universalSupport_selected_line_data {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (line ξ displacement : Fin r → ℂ)
    (hbase : Function.Injective (fun b : Fin r => (ξ b, (line b)^2 - line b * ξ b)))
    (hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b) G = 0)
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0) :
    ∃ (indices : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ),
      indices.Nonempty ∧ (∀ α ∈ indices, α + j α = u) ∧
      (∀ α ∈ indices, ¬G ∣ T α) ∧
      (∀ α ∈ indices, j α ≤ d / k) ∧
      (∀ α ∈ indices, (T α).IsHomogeneous (d - k * j α)) ∧
      ∀ b, (liftedNormalPolynomial indices j T).map
          (Nagata.W04.ReducibleSquare.lineRestriction (line b)) ∈
        (Nagata.W18.nestedPointIdeal (ξ b) (displacement b)) ^ (m b) := by
  classical
  let A := Nagata.W27.directChartHom (2 : Fin 3) G
  let point : Fin r → ComplexPlane := fun b => (ξ b, (line b)^2 - line b * ξ b)
  let normal : Fin r → ℂ := fun b => planePolynomialEval (MvPolynomial.pderiv 1 A) (point b)
  let V : Fin r → ComplexPlane := fun b => (0, displacement b / normal b)
  let coord : ComplexPlane → Fin 2 → ℂ := fun z a => if a = 0 then z.1 else z.2
  let motion : Fin r × Fin 2 → Polynomial ℂ := fun ba =>
    Polynomial.C (coord (point ba.1) ba.2) +
      Polynomial.X * Polynomial.C (coord (V ba.1) ba.2)
  have hmotion : ∀ b a s, (motion (b,a)).eval s = coord (point b + s • V b) a := by
    intro b a s
    simp only [motion, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    dsimp only [coord]
    split_ifs <;> simp
  have hbase' : Function.Injective
      (configurationChartEmbedding (fun _ : Fin r => (2 : Fin 3))
        (fun ba => (motion ba).eval 0)) := by
    intro b b' heq
    have heq' : coord (point b) = coord (point b') := by
      apply chartPoint₂_injective (2 : Fin 3)
      simpa only [configurationChartEmbedding, hmotion, zero_smul, add_zero] using heq
    apply hbase
    apply Prod.ext
    · have hh := congrFun heq' (0 : Fin 2)
      simpa only [coord, ite_eq_left rfl] using hh
    · have hh := congrFun heq' (1 : Fin 2)
      simpa only [coord, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)] using hh
  obtain ⟨I, j, T, u, hnot, hdeg, hmin, hu, hsel, hnonzero, horders⟩ :=
    universalSupport_degree_bounded_normal_data hU (fun _ => 2) motion hbase'
      G k hG (positive_homogeneous_not_isUnit hG hk) hk
  let selected := I.filter (fun α => α + j α = u)
  refine ⟨selected, j, T, u, hsel, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα
    exact (Finset.mem_filter.mp hα).2
  · intro α hα
    exact hnot α (Finset.mem_filter.mp hα).1
  · intro α hα
    exact (hdeg α (Finset.mem_filter.mp hα).1).1
  · intro α hα
    exact (hdeg α (Finset.mem_filter.mp hα).1).2
  · intro b
    have hv : polynomialGradient A (point b) (V b) = displacement b := by
      have hn : normal b ≠ 0 := hpartial b
      change planePolynomialEval (MvPolynomial.pderiv 0 A) (point b) * 0 +
        normal b * (displacement b / normal b) = displacement b
      rw [mul_zero, zero_add]
      exact mul_div_cancel₀ (displacement b) hn
    have ho : ∀ᶠ s : ℂ in 𝓝 0, s ∉ (∅ : Finset ℂ) →
        Nagata.AffineMultiplicity.orderAtLeast (coord (point b + s • V b)) (m b)
          (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom 2 (T α)) A s) := by
      exact Filter.Eventually.of_forall fun s _ => by
        simpa only [hmotion] using horders s b
    have h := line_normal_specialization I j T u hmin G (line b) (ξ b) (V b)
      (hline b) (hpartial b) ∅ (m b) ho
    change (liftedNormalPolynomial selected j T).map _ ∈
      (Nagata.W18.nestedPointIdeal (ξ b) (polynomialGradient A (point b) (V b))) ^ (m b) at h
    rwa [hv] at h

end Nagata.Workers.W17

end
end

section

/-! Simultaneous homogeneous normal specialization on an actual analytic
parametrized plane curve. All polynomial families, velocities, coefficient
factorizations, selected weights and local normal orders are constructed.
The geometric hypotheses describe only the genuine coordinate functions and
chosen smooth marked projective points. -/
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.Workers.W28 Nagata.ProjectiveGeometry

theorem universalSupport_covering_normal_polynomial {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (X : Fin 3 → ℂ → ℂ) (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, X (chart b) (z b) ≠ 0)
    (hX : ∀ b a, AnalyticAt ℂ (X a) (z b))
    (hzero : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (fun a => X a t) G = 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint X (chart b) (z b)))))
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (chart b) G))
      (normalizedCurvePoint X (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-k*n)) ∧
      (∀ n, F.coeff n ≠ 0 → k*n ≤ d) ∧
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0 ∧
      ∀ b, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (Nagata.CoefficientSpaces.ambientNormalScalar X F)
        (z b,w b) (m b) := by
  classical
  let point : Fin r → ComplexPlane := fun b => normalizedCurvePoint X (chart b) (z b)
  let V : Fin r → ComplexPlane := fun b => coveringNormalVelocity G k X (chart b) (z b) (w b)
  let motion : Fin r × Fin 2 → Polynomial ℂ := fun ba =>
    affineCoordinateMotion (point ba.1) (V ba.1) ba.2
  have hb := coveringMotion_base_injective chart point V hbase
  obtain ⟨I,j,T,u,hnot,hdeg,hmin,hu,hsel,hne,horders⟩ :=
    universalSupport_degree_bounded_normal_data hU chart motion hb G k hG
      (positive_homogeneous_not_isUnit hG hk) hk
  let selected := I.filter (fun α => α+j α=u)
  let F := liftedNormalPolynomial selected j T
  have hhom : ∀ α ∈ selected, (T α).IsHomogeneous (d-k*j α) :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).2
  have hbound : ∀ α ∈ selected, j α ≤ d/k :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).1
  refine ⟨F, homogeneous_coeff_liftedNormalPolynomial selected j T d k hhom, ?_, hne, ?_⟩
  · intro n hn
    have hb := nonzero_coeff_liftedNormalPolynomial_bound selected j T (d/k) n hbound hn
    have hh := (Nat.le_div_iff_mul_le hk).mp hb
    simpa only [Nat.mul_comm] using hh
  · intro b
    have hcurve : ∀ᶠ t in 𝓝 (z b), MvPolynomial.eval (fun a => X a t) G = 0 :=
      (eventually_ne_nhds (hz b)).mono fun t ht => hzero t ht
    have ho : ∀ᶠ s : ℂ in 𝓝 0, s ∉ (∅ : Finset ℂ) →
        Nagata.AffineMultiplicity.orderAtLeast (planeCoordinate (point b+s • V b)) (m b)
          (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom (chart b) (T α))
            (Nagata.W27.directChartHom (chart b) G) s) := by
      exact Filter.Eventually.of_forall fun s _ => by
        simpa only [motion, affineCoordinateMotion_eval] using horders s b
    have h := homogeneous_normal_specialization I j T u hmin d k
      (fun α hα => (hdeg α hα).2)
      (fun α hα => by
        have hh := (Nat.le_div_iff_mul_le hk).mp (hdeg α hα).1
        simpa only [Nat.mul_comm] using hh)
      G hG X (chart b) (z b) (w b) (hX b) (hc b) hcurve (hpartial b) (V b)
      (coveringNormalVelocity_derivative G k X (chart b) (z b) (w b) (hpartial b))
      ∅ (m b) ho
    apply h.congr
    exact Filter.Eventually.of_forall fun q => by
      simp [Nagata.CoefficientSpaces.ambientNormalScalar, F, liftedNormalPolynomial, selected,
        Polynomial.map_sum, Polynomial.eval_finsetSum, mul_comm]

end Nagata.Workers.W17

end
end

section

/-! The simultaneous normal polynomial in the original ambient homogeneous
coefficient ring, with coefficient degree, nonzero restriction and ordinary
surface multiplicity. -/
namespace Nagata.Workers.W17
open Nagata.Workers.W28

/-- Full literal normal-polynomial conclusion on finitely many smooth line
components, with all multiplicity and prescribed-displacement quantifiers. -/
theorem universalSupport_line_normal_polynomial {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (line ξ displacement : Fin r → ℂ)
    (hbase : Function.Injective (fun b : Fin r => (ξ b, (line b)^2 - line b * ξ b)))
    (hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b) G = 0)
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d - k*n)) ∧
      (∀ n, F.coeff n ≠ 0 → k*n ≤ d) ∧
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0 ∧
      ∀ b, F.map (Nagata.W04.ReducibleSquare.lineRestriction (line b)) ∈
        (Nagata.W18.nestedPointIdeal (ξ b) (displacement b)) ^ (m b) := by
  obtain ⟨I, j, T, u, hne, hweight, hnot, hbound, hhom, horder⟩ :=
    universalSupport_selected_line_data hU G k hG hk line ξ displacement hbase hline hpartial
  refine ⟨liftedNormalPolynomial I j T,
    homogeneous_coeff_liftedNormalPolynomial I j T d k hhom, ?_,
    quotient_liftedNormalPolynomial_ne_zero I j T G u hne hweight hnot, horder⟩
  intro n hn
  have hb := nonzero_coeff_liftedNormalPolynomial_bound I j T (d/k) n hbound hn
  have hh := (Nat.le_div_iff_mul_le hk).mp hb
  simpa only [Nat.mul_comm] using hh

end Nagata.Workers.W17

end

section

/-! Simultaneous homogeneous normal specialization on an actual analytic
parametrized plane curve. All polynomial families, velocities, coefficient
factorizations, selected weights and local normal orders are constructed.
The geometric hypotheses describe only the genuine coordinate functions and
chosen smooth marked projective points. -/
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.Workers.W28 Nagata.ProjectiveGeometry

theorem universalSupport_smooth_covering_normal_polynomial {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (X : Fin 3 → ℂ → ℂ) (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, X (chart b) (z b) ≠ 0)
    (hX : ∀ b a, AnalyticAt ℂ (X a) (z b))
    (hzero : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (fun a => X a t) G = 0)
    (hbase : Function.Injective (fun b => chartPoint₂ (chart b)
      (planeCoordinate (normalizedCurvePoint X (chart b) (z b)))))
    (hdifferential : ∀ b, polynomialGradient (Nagata.W27.directChartHom (chart b) G)
      (normalizedCurvePoint X (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-k*n)) ∧
      (∀ n, F.coeff n ≠ 0 → k*n ≤ d) ∧
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0 ∧
      ∀ b, HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (Nagata.CoefficientSpaces.ambientNormalScalar X F)
        (z b,w b) (m b) := by
  classical
  let point : Fin r → ComplexPlane := fun b => normalizedCurvePoint X (chart b) (z b)
  have hvelocity : ∀ b, ∃ V : ComplexPlane,
      polynomialGradient (Nagata.W27.directChartHom (chart b) G) (point b) V =
        w b / X (chart b) (z b) ^ k := by
    intro b
    exact Nagata.W29.affinePolynomialGradient_surjective _ _
      ((polynomialGradient_ne_zero_iff_partials _ _).mp (hdifferential b)) _
  choose V hV using hvelocity
  let motion : Fin r × Fin 2 → Polynomial ℂ := fun ba =>
    affineCoordinateMotion (point ba.1) (V ba.1) ba.2
  have hb := coveringMotion_base_injective chart point V hbase
  obtain ⟨I,j,T,u,hnot,hdeg,hmin,hu,hsel,hne,horders⟩ :=
    universalSupport_degree_bounded_normal_data hU chart motion hb G k hG
      (positive_homogeneous_not_isUnit hG hk) hk
  let selected := I.filter (fun α => α+j α=u)
  let F := liftedNormalPolynomial selected j T
  have hhom : ∀ α ∈ selected, (T α).IsHomogeneous (d-k*j α) :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).2
  have hbound : ∀ α ∈ selected, j α ≤ d/k :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).1
  refine ⟨F, homogeneous_coeff_liftedNormalPolynomial selected j T d k hhom, ?_, hne, ?_⟩
  · intro n hn
    have hb := nonzero_coeff_liftedNormalPolynomial_bound selected j T (d/k) n hbound hn
    have hh := (Nat.le_div_iff_mul_le hk).mp hb
    simpa only [Nat.mul_comm] using hh
  · intro b
    have hcurve : ∀ᶠ t in 𝓝 (z b), MvPolynomial.eval (fun a => X a t) G = 0 :=
      (eventually_ne_nhds (hz b)).mono fun t ht => hzero t ht
    have ho : ∀ᶠ s : ℂ in 𝓝 0, s ∉ (∅ : Finset ℂ) →
        Nagata.AffineMultiplicity.orderAtLeast (planeCoordinate (point b+s • V b)) (m b)
          (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom (chart b) (T α))
            (Nagata.W27.directChartHom (chart b) G) s) := by
      exact Filter.Eventually.of_forall fun s _ => by
        simpa only [motion, affineCoordinateMotion_eval] using horders s b
    have h := homogeneous_normal_specialization_of_nonzero_differential I j T u hmin d k
      (fun α hα => (hdeg α hα).2)
      (fun α hα => by
        have hh := (Nat.le_div_iff_mul_le hk).mp (hdeg α hα).1
        simpa only [Nat.mul_comm] using hh)
      G hG X (chart b) (z b) (w b) (hX b) (hc b) hcurve (hdifferential b) (V b) (hV b)
      ∅ (m b) ho
    apply h.congr
    exact Filter.Eventually.of_forall fun q => by
      simp [Nagata.CoefficientSpaces.ambientNormalScalar, F, liftedNormalPolynomial, selected,
        Polynomial.map_sum, Polynomial.eval_finsetSum, mul_comm]

end Nagata.Workers.W17

end
end

end OAI
