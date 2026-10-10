import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import OAI.AlgebraicGeometry.PlaneCurves.AssociatedBundles
import OAI.AlgebraicGeometry.PlaneCurves.CubicMap
import OAI.AlgebraicGeometry.PlaneCurves.CubicRelations
import OAI.AlgebraicGeometry.PlaneCurves.ProjectiveTopology

namespace OAI

/-!
# Cubic relations, closed embeddings, image containment, and gradients
-/

section

/-! Actual cubic monomials in degree-three sections belong to degree nine. -/
namespace Nagata.W21
open scoped BigOperators
open Nagata.W08

theorem cubicSectionProduct_mem {τ γ : ℂ}
    (b : Fin 3 → automorphicSections τ 3 γ) (e : Fin 3 → ℕ)
    (he : ∑ i, e i = 3) :
    (fun z ↦ ∏ i, (b i).val z ^ e i) ∈ automorphicSections τ 9 (γ ^ 3) := by
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [(b _).property.1]
    rw [Finset.prod_pow_eq_pow_sum, he]
    exact zero_pow (by decide)
  · intro z hz
    exact DifferentiableAt.fun_finsetProd fun i _ ↦ ((b i).property.2.1 z hz).pow (e i)
  · intro z hz
    change (∏ i, (b i).val (τ * z) ^ e i) =
      γ ^ 3 * z ^ (-9 : ℤ) * ∏ i, (b i).val z ^ e i
    simp_rw [(b _).property.2.2 z hz, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, he]
    have hp : (z ^ (-3 : ℤ)) ^ (3 : ℕ) = z ^ (-9 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul]
      rfl
    rw [hp]

end Nagata.W21

end

section

/-! A genuine cubic equation for the actual section evaluation map.
The degree-nine section dimension remains an explicitly listed input. -/
namespace Nagata.W21
open Nagata.W08

/-- The actual evaluation coordinates satisfy a nonzero homogeneous cubic,
conditional only here on the separately proved degree-nine section dimension. -/
theorem exists_cubicRelation_of_degreeNine_dimension {τ γ : ℂ}
    (b : Fin 3 → automorphicSections τ 3 γ)
    [Module.Finite ℂ (automorphicSections τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (automorphicSections τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      MvPolynomial.aeval (fun i ↦ (b i).val) P = 0 := by
  apply Nagata.W02.exists_nonzero_homogeneousCubic_relation
    (fun i ↦ (b i).val) (automorphicSections τ 9 (γ ^ 3)) hdim
  intro e
  rw [Nagata.W02.aeval_cubicMonomial_function]
  exact cubicSectionProduct_mem b e.val (Nagata.W02.cubicExponent_sum e)

/-- The cubic equation vanishes at every actual evaluation vector, including
all lifts used by the projective quotient map. -/
theorem exists_cubicEquation_of_degreeNine_dimension {τ γ : ℂ}
    (b : Fin 3 → automorphicSections τ 3 γ)
    [Module.Finite ℂ (automorphicSections τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (automorphicSections τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧ ∀ z : ℂ,
      MvPolynomial.aeval (fun i ↦ (b i).val z) P = 0 := by
  obtain ⟨P, hP, hhom, he⟩ := exists_cubicRelation_of_degreeNine_dimension b hdim
  refine ⟨P, hP, hhom, ?_⟩
  intro z
  have h := congrArg (Pi.evalAlgHom ℂ (fun _ : ℂ ↦ ℂ) z) he
  simpa only [MvPolynomial.comp_aeval_apply, map_zero, Pi.evalAlgHom_apply] using h

end Nagata.W21

end

section

/-! Continuity and compact image of the genuine cubic evaluation map. -/
namespace Nagata.W21
open Nagata.W07 Nagata.W08

 theorem continuous_cubicEvaluationVector {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) :
    Continuous (fun z : ℂˣ ↦ cubicEvaluationVector b (z : ℂ)) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((b i).property.2.1 (z : ℂ) z.ne_zero).continuousAt.comp
    Units.continuous_val.continuousAt

/-- Continuity into the canonical complex projective topology. -/
theorem continuous_cubicCoverMap {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Continuous (cubicCoverMap b hbase) := by
  have hc : Continuous (fun z : ℂˣ ↦
      (⟨cubicEvaluationVector b (z : ℂ),
        cubicEvaluationVector_ne_zero b (hbase z z.ne_zero)⟩ :
        {v : Fin 3 → ℂ // v ≠ 0})) :=
    (continuous_cubicEvaluationVector b).subtype_mk _
  exact (continuous_projectivization_mk' ℂ (Fin 3 → ℂ)).comp hc

/-- The descended actual torus map is continuous for both canonical quotient topologies. -/
theorem continuous_cubicTorusMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Continuous (cubicTorusMap τ b hbase) :=
  (continuous_cubicCoverMap b hbase).quotient_lift _

/-- The image is compact for every admissible period. -/
theorem isCompact_cubicTorusMap_range {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections
      (Nagata.Workers.W05.positivePeriod τ hτ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval (τ : ℂ) 3 γ z)) = 2) :
    IsCompact (Set.range (cubicTorusMap (Nagata.Workers.W05.positivePeriod τ hτ) b hbase)) := by
  let := Nagata.Workers.W05.compactSpace_torusPoint hτ hτ1
  exact isCompact_range (continuous_cubicTorusMap _ b hbase)

end Nagata.W21

end

section

namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16

/-- A homogeneous equation vanishing on the evaluation coordinates vanishes
on the canonical representative of every image point. -/
theorem cubicTorusMap_on_curve (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    {d : ℕ} (G : NonzeroHomogeneousForm d)
    (hG : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (cubicEvaluationVector b z) G.polynomial = 0)
    (q : TorusPoint τ) : MvPolynomial.eval (cubicTorusMap τ b hbase q).rep G.polynomial = 0 := by
  refine Quotient.inductionOn q ?_
  intro z
  change MvPolynomial.eval (Projectivization.mk ℂ (cubicEvaluationVector b z)
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))).rep G.polynomial = 0
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (cubicEvaluationVector b z)
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))
  rw [← hu]
  change MvPolynomial.eval (fun i ↦ (u : ℂ) * cubicEvaluationVector b z i) G.polynomial = 0
  rw [homogeneous_eval_scale G.homogeneous, hG z z.ne_zero, mul_zero]

/-- The actual projective curve-valued map, without a surjectivity claim. -/
noncomputable def cubicCurveMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    {d : ℕ} (G : NonzeroHomogeneousForm d)
    (hG : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (cubicEvaluationVector b z) G.polynomial = 0) :
    TorusPoint τ → AssociatedBundle.CurvePoint G :=
  fun q ↦ ⟨cubicTorusMap τ b hbase q, cubicTorusMap_on_curve τ b hbase G hG q⟩

theorem continuous_cubicCurveMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    {d : ℕ} (G : NonzeroHomogeneousForm d)
    (hG : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (cubicEvaluationVector b z) G.polynomial = 0) :
    Continuous (cubicCurveMap τ b hbase G hG) :=
  (continuous_cubicTorusMap τ b hbase).subtype_mk _

/-- The dimension argument supplies an actual nonzero homogeneous cubic with
the pointwise vanishing needed by the curve-valued map. -/
theorem exists_cubicForm_of_degreeNine_dimension {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    [Module.Finite ℂ (automorphicSections τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (automorphicSections τ 9 (γ ^ 3)) ≤ 9) :
    ∃ G : NonzeroHomogeneousForm 3, ∀ z : ℂ, z ≠ 0 →
      MvPolynomial.eval (cubicEvaluationVector b z) G.polynomial = 0 := by
  obtain ⟨P, hP, hhom, hv⟩ := exists_cubicEquation_of_degreeNine_dimension b hdim
  refine ⟨⟨P, hhom, hP⟩, ?_⟩
  intro z _
  exact hv z

end Nagata.W21

end

section

/-! Actual linear equations obtained from degree-three sections in a chosen basis. -/
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
open scoped BigOperators

/-- The literal projective linear equation corresponding to a section. -/
def sectionLinePolynomial {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (f : automorphicSections τ 3 γ) : MvPolynomial (Fin 3) ℂ :=
  ∑ i, MvPolynomial.C ((b.repr f) i) * MvPolynomial.X i

theorem sectionLinePolynomial_homogeneous {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (f : automorphicSections τ 3 γ) : (sectionLinePolynomial b f).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Evaluating the actual linear equation recovers the section itself. -/
theorem sectionLinePolynomial_eval {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (f : automorphicSections τ 3 γ) (z : ℂ) :
    MvPolynomial.eval (cubicEvaluationVector b z) (sectionLinePolynomial b f) = f.val z := by
  have he := congrArg (fun s : automorphicSections τ 3 γ ↦ s.val z) (b.sum_repr f)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at he
  simpa only [sectionLinePolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, cubicEvaluationVector] using he

/-- A nonzero actual section gives a nonzero projective line equation. -/
theorem sectionLinePolynomial_ne_zero {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    {f : automorphicSections τ 3 γ} (hf : f ≠ 0) : sectionLinePolynomial b f ≠ 0 := by
  intro hL
  apply hf
  apply Subtype.ext
  funext z
  have he := sectionLinePolynomial_eval b f z
  rw [hL, map_zero] at he
  exact he.symm

/-- A zero of the section maps to a point on the literal projective line. -/
theorem sectionLinePolynomial_vanishes_at_image (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (f : automorphicSections (τ : ℂ) 3 γ) (z : ℂˣ) (hz : f.val z = 0) :
    MvPolynomial.eval (cubicCoverMap b hbase z).rep (sectionLinePolynomial b f) = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (cubicEvaluationVector b z)
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))
  change MvPolynomial.eval (Projectivization.mk ℂ (cubicEvaluationVector b z)
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))).rep _ = 0
  rw [← hu]
  change MvPolynomial.eval (fun i ↦ (u : ℂ) * cubicEvaluationVector b z i) _ = 0
  rw [homogeneous_eval_scale (sectionLinePolynomial_homogeneous b f),
    sectionLinePolynomial_eval, hz, mul_zero]

end Nagata.W21

end
end

section

/-! The genuine cubic section map is a topological closed embedding once its
explicit section dimension inputs are supplied. -/
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.Workers.W05

/-- Compactness and actual projective Hausdorffness turn the proved injectivity
into a closed embedding, with both spaces carrying their canonical topologies. -/
theorem cubicTorusMap_isClosedEmbedding {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (positivePeriod τ hτ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval (τ : ℂ) 3 γ z)) = 2)
    (hsep : ∀ z w : ℂˣ, ¬ torusOrbitSetoid (positivePeriod τ hτ) z w →
      Module.finrank ℂ (LinearMap.ker (sectionTwoEval (τ : ℂ) 3 γ z w)) = 1) :
    Topology.IsClosedEmbedding (cubicTorusMap (positivePeriod τ hτ) b hbase) := by
  let := compactSpace_torusPoint hτ hτ1
  exact (continuous_cubicTorusMap _ b hbase).isClosedEmbedding
    (cubicTorusMap_injective _ b hbase hsep)

/-- The actual image is connected, independently of any Chow theorem. -/
theorem cubicTorusMap_range_isConnected (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    IsConnected (Set.range (cubicTorusMap τ b hbase)) := by
  let := torusPoint_connectedSpace τ
  exact isConnected_range (continuous_cubicTorusMap τ b hbase)

theorem positivePeriod_norm_lt {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    ‖(positivePeriod τ hτ : ℂ)‖ < 1 := by
  change ‖(τ : ℂ)‖ < 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτ1

/-- The closed embedding statement with all divisor-kernel hypotheses reduced
to the actual D1/D2/D3 section dimensions. These dimensions remain explicit. -/
theorem cubicMapFromDimensions_isClosedEmbedding {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (positivePeriod τ hτ : ℂ) 3 γ))
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections (τ : ℂ) 1 δ) = 1)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections (τ : ℂ) 2 δ) = 2) :
    Topology.IsClosedEmbedding
      (cubicMapFromDimensions (positivePeriod τ hτ) (positivePeriod_norm_lt hτ hτ1) hγ b h2) := by
  let := compactSpace_torusPoint hτ hτ1
  exact (continuous_cubicTorusMap _ b _).isClosedEmbedding
    (cubicMapFromDimensions_injective _ (positivePeriod_norm_lt hτ hτ1) hγ b h1 h2)

end Nagata.W21

end

section

/-! Unconditional topological embedding and actual cubic equation for the
manuscript's theta section map. Algebraic image equality and smoothness remain
separate statements. -/
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16

 theorem continuous_actualCubicMap {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Continuous (actualCubicMap hτ hτone hγ) :=
  continuous_cubicTorusMap _ _ _

/-- The actual theta map is a topological closed embedding; all section
dimension assumptions have been discharged by the genuine Laurent basis. -/
theorem actualCubicMap_isClosedEmbedding {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Topology.IsClosedEmbedding (actualCubicMap hτ hτone hγ) := by
  let : CompactSpace (TorusPoint (cubicPeriod hτ)) :=
    Nagata.Workers.W05.compactSpace_torusPoint hτ hτone
  exact (continuous_actualCubicMap hτ hτone hγ).isClosedEmbedding
    (actualCubicMap_injective hτ hτone hγ)

theorem actualCubicMap_range_isConnected {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : IsConnected (Set.range (actualCubicMap hτ hτone hγ)) := by
  let := torusPoint_connectedSpace (cubicPeriod hτ)
  exact isConnected_range (continuous_actualCubicMap hτ hτone hγ)

/-- An actual nonzero homogeneous cubic vanishes on every evaluation vector,
with no dimension, finiteness or basis assumption left. -/
theorem exists_actualCubicForm {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) :
    ∃ G : NonzeroHomogeneousForm 3, ∀ z : ℂ, z ≠ 0 →
      MvPolynomial.eval (cubicEvaluationVector (actualCubicBasis hτ hτone hγ) z)
        G.polynomial = 0 := by
  let : Module.Finite ℂ (automorphicSections (τ : ℂ) 9 (γ ^ 3)) :=
    Nagata.Workers.W10.positiveSection_finite hτ hτone
      (fun n δ ↦ Nagata.W01.laurentCoefficientMap_injective _ n δ)
      (show (0 : ℤ) < 9 by decide) (pow_ne_zero 3 hγ)
  apply exists_cubicForm_of_degreeNine_dimension (actualCubicBasis hτ hτone hγ)
  exact (actualPositiveSection_finrank hτ hτone (show (0 : ℤ) < 9 by decide)
    (pow_ne_zero 3 hγ)).le

/-- The closed embedded torus is contained in the actual cubic zero locus.
This is containment only, not equality or smoothness of that zero locus. -/
theorem exists_actualCubic_image_containment {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) :
    ∃ G : NonzeroHomogeneousForm 3, ∀ q : TorusPoint (cubicPeriod hτ),
      MvPolynomial.eval (actualCubicMap hτ hτone hγ q).rep G.polynomial = 0 := by
  obtain ⟨G, hG⟩ := exists_actualCubicForm hτ hτone hγ
  exact ⟨G, cubicTorusMap_on_curve _ _ _ G hG⟩

end Nagata.W21

end
end

section

/-! Source 02, cubic embedding and local normal frames: the cubic Jacobian
condition is independent of the actual homogeneous representative. -/
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16

 theorem cubic_gradient_scale_iff (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (u : ℂ) (hu : u ≠ 0) :
    (∃ i, MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  have he (i : Fin 3) :
      MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) =
        u ^ 2 * MvPolynomial.eval x (MvPolynomial.pderiv i G) := by
    exact homogeneous_eval_scale (show (MvPolynomial.pderiv i G).IsHomogeneous 2 from hG.pderiv) x u
  simp only [he, ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hu,
    false_or]

 theorem cubic_gradient_mk_rep_iff (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (hx : x ≠ 0) :
    (∃ i, MvPolynomial.eval (Projectivization.mk ℂ x hx).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  rw [← hu]
  exact cubic_gradient_scale_iff G hG x (u : ℂ) u.ne_zero

 theorem actualCubicMap_gradient_iff {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (z : ℂˣ) :
    (∃ i, MvPolynomial.eval
      (actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) z)).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval (cubicEvaluationVector (actualCubicBasis hτ hτone hγ) z)
        (MvPolynomial.pderiv i G) ≠ 0 :=
  cubic_gradient_mk_rep_iff G hG _ _

end Nagata.W21

end

section

/-! Actual lines meeting the embedded torus in three distinct marked points. -/
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.ProjectiveGeometry

/-- Through every image point there is an actual line with three distinct image
points. The line does not vanish identically on the torus. -/
theorem exists_threePointLine_through_image {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (q : TorusPoint (cubicPeriod hτ)) :
    ∃ (L : MvPolynomial (Fin 3) ℂ) (p : Fin 3 → PlanePoint),
      L ≠ 0 ∧ L.IsHomogeneous 1 ∧ Function.Injective p ∧
      p 0 = actualCubicMap hτ hτone hγ q ∧
      (∀ i, p i ∈ Set.range (actualCubicMap hτ hτone hγ)) ∧
      (∀ i, MvPolynomial.eval (p i).rep L = 0) ∧
      ∃ z : ℂ, z ≠ 0 ∧
        MvPolynomial.eval (cubicEvaluationVector (actualCubicBasis hτ hτone hγ) z) L ≠ 0 := by
  refine Quotient.inductionOn q ?_
  intro a
  obtain ⟨m, s, hm0, hm, hd, _, hs, _, hz, _⟩ :=
    exists_cubic_three_simple_zeros_pos_real hτ hτone hγ a.ne_zero
  let b := actualCubicBasis hτ hτone hγ
  let u : Fin 3 → ℂˣ := fun i ↦ Units.mk0 (m i) (hm i)
  let p : Fin 3 → PlanePoint := fun i ↦ actualCubicMap hτ hτone hγ
    (torusPointMk (cubicPeriod hτ) (u i))
  refine ⟨sectionLinePolynomial b s, p, sectionLinePolynomial_ne_zero b hs,
    sectionLinePolynomial_homogeneous b s, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have he := actualCubicMap_injective hτ hτone hγ hij
    obtain ⟨k, hk⟩ := (torusPointMk_eq_iff (cubicPeriod hτ) (u j) (u i)).mp he.symm
    have hc := congrArg (fun v : ℂˣ ↦ (v : ℂ)) hk
    apply hd hne k
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, cubicPeriod_val,
      u, Units.val_mk0, mul_comm] using hc.symm
  · change actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) (u 0)) =
      actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) a)
    congr 2
    apply Units.ext
    exact hm0
  · intro i
    exact ⟨torusPointMk (cubicPeriod hτ) (u i), rfl⟩
  · intro i
    apply sectionLinePolynomial_vanishes_at_image (cubicPeriod hτ) b
      (fun _ hw ↦ actualCubic_eval_kernel_dimension hτ hτone hγ hw) s (u i)
    exact (hz (m i) (hm i)).mpr ⟨i, 0, by simp⟩
  · by_contra h
    apply hs
    apply automorphicSections_ext
    intro z hzne
    change s.val z = 0
    rw [← sectionLinePolynomial_eval b s z]
    exact not_ne_iff.mp (fun hne ↦ h ⟨z, hzne, hne⟩)

end Nagata.W21

end
end

end OAI
