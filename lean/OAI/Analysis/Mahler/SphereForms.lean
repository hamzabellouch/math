import OAI.Analysis.Mahler.HomogeneousDeformation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def coordinateMap (n : ℕ) (j : Fin n) (z : ComplexEuclidean n) : ℂ := z j

lemma coordinateMap_differentiable (n : ℕ) : ∀ j, Differentiable ℂ (coordinateMap n j) :=
  fun j => (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable

lemma coordinateMap_homogeneous (n : ℕ) : ∀ j (z : ComplexEuclidean n) (c : ℂ),
    coordinateMap n j (c • z) = c^1 * coordinateMap n j z := by
  intros
  simp [coordinateMap]

lemma coordinateMap_tau_pos {n : ℕ} {z : ComplexEuclidean n} (hz : z ≠ 0) :
    0 < tau (coordinateMap n) z := by
  apply tau_pos_of_component_ne_zero
  by_contra h
  push Not at h
  apply hz
  ext i
  exact h i

/-- The tangent hyperplane of a Euclidean sphere, with its usual real metric. -/
noncomputable def sphereTangent {n : ℕ} (z : ComplexEuclidean n) : Submodule ℝ (ComplexEuclidean n) :=
  (ℝ ∙ z)ᗮ

lemma circle_mem_sphereTangent {n : ℕ} (z : ComplexEuclidean n) : I • z ∈ sphereTangent z := by
  rw [sphereTangent, Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact real_inner_I_smul_self ℂ (z i)

noncomputable def circleTangent {n : ℕ} (z : ComplexEuclidean n) : sphereTangent z :=
  ⟨I • z, circle_mem_sphereTangent z⟩

lemma circleTangent_ne_zero {n : ℕ} {z : ComplexEuclidean n} (hz : z ≠ 0) :
    circleTangent z ≠ 0 := by
  intro h
  have he : I • z = 0 := congrArg Subtype.val h
  exact (smul_eq_zero.mp he).elim I_ne_zero hz

lemma sphereTangent_finrank {n : ℕ} (hn : 1 ≤ n) {z : ComplexEuclidean n} (hz : z ≠ 0) :
    Module.finrank ℝ (sphereTangent z) = 2 * (n - 1) + 1 := by
  have hd : Module.finrank ℝ (ComplexEuclidean n) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexEuclidean n)]
    simp [ComplexEuclidean, Complex.finrank_real_complex]
  let : Fact (Module.finrank ℝ (ComplexEuclidean n) = (2 * (n - 1) + 1) + 1) :=
    ⟨by rw [hd]; omega⟩
  exact Submodule.finrank_orthogonal_span_singleton hz

lemma horizontal_twoForm {T : Type*} [AddCommGroup T] [Module ℝ T]
    {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T} (ha : ∀ w, a ![V, w] = 0) : Horizontal a V := by
  intro v i hi
  fin_cases i
  · have he : v = ![V, v 1] := by ext i; fin_cases i <;> simp_all
    rw [he, ha]
  · have he : v = ![v 0, V] := by ext i; fin_cases i <;> simp_all
    have hs := a.map_swap ![V, v 0] (i := 0) (j := 1) (by decide)
    have he' : ![V, v 0] ∘ Equiv.swap (0 : Fin 2) 1 = ![v 0, V] := by
      ext i; fin_cases i <;> simp
    rw [he', ha, neg_zero] at hs
    rw [he, hs]

noncomputable def tangentForm {n : ℕ} {ι : Type*} (z : ComplexEuclidean n)
    (a : ComplexEuclidean n [⋀^ι]→ₗ[ℝ] ℂ) : sphereTangent z [⋀^ι]→ₗ[ℝ] ℂ :=
  a.compLinearMap (sphereTangent z).subtype

lemma Horizontal.tangentForm {n : ℕ} {ι : Type*} {z : ComplexEuclidean n}
    {a : ComplexEuclidean n [⋀^ι]→ₗ[ℝ] ℂ} (ha : Horizontal a (I • z)) :
    Horizontal (tangentForm z a) (circleTangent z) := by
  intro v i hi
  apply ha (fun i => (v i : ComplexEuclidean n)) i
  exact congrArg Subtype.val hi

/-- The top-degree deformation term vanishes on every sphere tangent
space under the polynomial hypotheses. -/
theorem MassHypotheses.sphere_beta_wedge_power_zero {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) :
    wedge
      (tangentForm z (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap)
        (n - 1)) = 0 := by
  have hfG := polynomialMap_differentiable G
  have htG := tau_pos_of_component_ne_zero (f := polynomialMap G) (x := z) (h.leading_nonzero z hz)
  have hhG := polynomialMap_homogeneous h.homogeneous
  apply beta_wedge_power_eq_zero (n - 1) (sphereTangent_finrank h.dimension_pos hz)
    (circleTangent_ne_zero hz)
  · apply Horizontal.tangentForm
    intro v i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    change betaLinear (polynomialMap G) (coordinateMap n) m z (v 0) = 0
    rw [hi]
    exact betaLinear_circle (fun j => (hfG j).differentiableAt) htG (fun j c => hhG j z c)
      (fun j => (coordinateMap_differentiable n j).differentiableAt) (coordinateMap_tau_pos hz)
      (fun j c => coordinateMap_homogeneous n j z c)
  · apply Horizontal.tangentForm
    apply horizontal_twoForm
    intro v
    exact alphaPath_extDeriv_horizontal hfG htG hhG (coordinateMap_differentiable n)
      (coordinateMap_tau_pos hz) (coordinateMap_homogeneous n) t v

end Mahler

end OAI
