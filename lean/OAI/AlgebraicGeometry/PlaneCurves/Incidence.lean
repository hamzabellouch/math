import OAI.AlgebraicGeometry.PlaneCurves.ChartJets
import OAI.AlgebraicGeometry.PlaneCurves.ChartMultiplicityBridge
import OAI.AlgebraicGeometry.PlaneCurves.Homogenization
import OAI.AlgebraicGeometry.PlaneCurves.UniversalReduction

namespace OAI

/-!
# Projective incidence and closed multiplicity support loci; Geometric realization of universal multiplicity reduction
-/

section

/-! Logical gluing for guarded chart equations. The geometric construction of
the equations and verification of these explicit hypotheses are separate. -/
namespace Nagata.Workers.W25

/-- Equations attached to an open-chart cover glue when each equation vanishes
outside its own chart. No finiteness is needed for this logical step. -/
theorem guarded_chart_gluing {C X : Type*} {I : C → Type*}
    (U : C → X → Prop) (Z : (c : C) → I c → X → Prop) (S : X → Prop)
    (hcover : ∀ x, ∃ c, U c x)
    (houtside : ∀ c e x, ¬ U c x → Z c e x)
    (hlocal : ∀ c x, U c x → (S x ↔ ∀ e, Z c e x)) :
    ∀ x, S x ↔ ∀ c e, Z c e x := by
  intro x
  constructor
  · intro hS c e
    by_cases hU : U c x
    · exact (hlocal c x hU).mp hS e
    · exact houtside c e x hU
  · intro hZ
    obtain ⟨c, hc⟩ := hcover x
    exact (hlocal c x hc).mpr (hZ c)

end Nagata.Workers.W25

end

section

/-!
# Gluing polynomial equations on genuine configuration charts
-/

noncomputable section

namespace Nagata.ProjectiveGeometry

open scoped BigOperators

/-- An actual guarded multihomogeneous extension of an affine chart equation. -/
def guardedEquation {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) : MultihomogeneousEquation r where
  polynomial := W27.guardedHomogenize c f
  multidegree := fun i => W27.blockDegreeBound f i + 1
  homogeneous := W27.guardedHomogenize_homogeneous c f

theorem guardedEquation_vanishes_outside {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PlanePoint)
    (hp : ¬ InConfigurationChart c p) : equationVanishes (guardedEquation c f) p := by
  rw [equationVanishes_iff_eval_rep]
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hp
  exact W27.eval_guardedHomogenize_zero c f (fun ij => (p ij.1).rep ij.2) i
    (Classical.not_not.mp hi)

/-- Inside its own chart, the guarded homogeneous equation has exactly the
same zeros as the original affine polynomial. -/
theorem guardedEquation_vanishes_iff {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PlanePoint)
    (hp : InConfigurationChart c p) :
    equationVanishes (guardedEquation c f) p ↔
      MvPolynomial.eval (configurationChartCoordinates₂ c p) f = 0 := by
  rw [equationVanishes_iff_eval_rep]
  exact W27.eval_guardedHomogenize_eq_zero_iff c f
    (fun ij => (p ij.1).rep ij.2) hp

def productCommonZeroLocus {r : ℕ} {ι : Type*}
    (F : ι → MultihomogeneousEquation r) : Set (Fin r → PlanePoint) :=
  {p | ∀ i, equationVanishes (F i) p}

theorem isProductZariskiClosed_commonZeroLocus {r : ℕ} {ι : Type*}
    (F : ι → MultihomogeneousEquation r) :
    IsProductZariskiClosed (productCommonZeroLocus F) := by
  refine ⟨Set.range F, ?_⟩
  intro p
  constructor
  · intro hp G hG
    obtain ⟨i, rfl⟩ := hG
    exact hp i
  · intro hp i
    exact hp (F i) ⟨i, rfl⟩

/-- The ambient version of chartwise polynomial closedness, needed to identify
the multihomogeneous topology with the standard simultaneous affine charts. -/
theorem productClosed_of_chart_polynomial_equations {r : ℕ}
    {I : ConfigurationChart r → Type*}
    (f : (c : ConfigurationChart r) → I c → MvPolynomial (Fin r × Fin 2) ℂ)
    (S : Set (Fin r → PlanePoint))
    (hlocal : ∀ c p, InConfigurationChart c p →
      (p ∈ S ↔ ∀ e, MvPolynomial.eval (configurationChartCoordinates₂ c p) (f c e) = 0)) :
    IsProductZariskiClosed S := by
  let F : (Σ c, I c) → MultihomogeneousEquation r :=
    fun ce => guardedEquation ce.1 (f ce.1 ce.2)
  have hglue := Workers.W25.guarded_chart_gluing
    (fun c p => InConfigurationChart c p)
    (fun c e p => equationVanishes (guardedEquation c (f c e)) p)
    (fun p => p ∈ S) configurationChart_cover
    (fun c e p hp => guardedEquation_vanishes_outside c (f c e) p hp)
    (fun c p hp => (hlocal c p hp).trans
      (forall_congr' fun e => (guardedEquation_vanishes_iff c (f c e) p hp).symm))
  have heq : S = productCommonZeroLocus F := by
    ext p
    constructor
    · intro hp ce
      exact (hglue p).mp hp ce.1 ce.2
    · intro hp
      exact (hglue p).mpr (fun c e => hp ⟨c, e⟩)
  rw [heq]
  exact isProductZariskiClosed_commonZeroLocus F

/-- Guarded polynomial equations on all charts produce a relatively closed
subset of the actual ordered configuration space. Each hypothesis is a
concrete vanishing identity or chart membership statement. -/
theorem configurationClosed_of_guarded_equations {r : ℕ}
    {I : ConfigurationChart r → Type*}
    (G : (c : ConfigurationChart r) → I c → MultihomogeneousEquation r)
    (S : Set (OrderedDistinctPoints r))
    (houtside : ∀ c e (p : OrderedDistinctPoints r),
      ¬ InConfigurationChart c p.val → equationVanishes (G c e) p.val)
    (hlocal : ∀ c p, InConfigurationChart c p.val →
      (p ∈ S ↔ ∀ e, equationVanishes (G c e) p.val)) :
    IsConfigurationZariskiClosed S := by
  let F : (Σ c, I c) → MultihomogeneousEquation r := fun ce => G ce.1 ce.2
  refine ⟨productCommonZeroLocus F, isProductZariskiClosed_commonZeroLocus F, ?_⟩
  intro p
  have hglue := Workers.W25.guarded_chart_gluing
    (fun c (q : OrderedDistinctPoints r) => InConfigurationChart c q.val)
    (fun c e (q : OrderedDistinctPoints r) => equationVanishes (G c e) q.val)
    (fun q => q ∈ S)
    (fun q => configurationChart_cover q.val) houtside hlocal p
  constructor
  · intro hp ce
    exact hglue.mp hp ce.1 ce.2
  · intro hp
    exact hglue.mpr (fun c e => hp ⟨c, e⟩)

/-- Polynomial equations in every simultaneous affine chart glue to the
genuine multihomogeneous Zariski closedness definition. The guarding polynomials,
boundary vanishing, and normalization factors are all constructed above. -/
theorem configurationClosed_of_chart_polynomial_equations {r : ℕ}
    {I : ConfigurationChart r → Type*}
    (f : (c : ConfigurationChart r) → I c → MvPolynomial (Fin r × Fin 2) ℂ)
    (S : Set (OrderedDistinctPoints r))
    (hlocal : ∀ c p, InConfigurationChart c p.val →
      (p ∈ S ↔ ∀ e, MvPolynomial.eval (configurationChartCoordinates₂ c p.val) (f c e) = 0)) :
    IsConfigurationZariskiClosed S := by
  apply configurationClosed_of_guarded_equations (fun c e => guardedEquation c (f c e)) S
  · intro c e p hp
    exact guardedEquation_vanishes_outside c (f c e) p.val hp
  · intro c p hp
    exact (hlocal c p hp).trans
      (forall_congr' fun e => (guardedEquation_vanishes_iff c (f c e) p.val hp).symm)

end Nagata.ProjectiveGeometry

end
end

section

/-!
# Closedness of the actual projective support locus

The coefficient columns are a basis of the same global homogeneous form space
in every point chart. Ordinary ideal-power multiplicity is identified with the
actual Taylor jets, maximal minors detect a nonzero coefficient kernel, and the
resulting chart equations are guarded and homogenized before gluing.
-/

noncomputable section

open Classical

namespace Nagata.ProjectiveGeometry

theorem multiplicityAtLeast_iff_directChart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    multiplicityAtLeast F p m ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates₂ c p) m (W27.directChartHom c F) := by
  apply (multiplicityAtLeast_iff_chart hF p c hc m).trans
  simpa only [chartDehomogenize₂_eq_eval₂_insertNth, W27.directChartHom,
    MvPolynomial.coe_eval₂Hom] using
    (orderAtLeast_chartDehomogenize₂_iff c p F m).symm

/-- On any containing simultaneous chart the genuine projective support locus
is exactly the zero set of the actual global-form matrix minors. -/
theorem supportLocus_iff_chart_minors (r : ℕ) (index : Workers.W25.IncidenceIndex r)
    (c : ConfigurationChart r) (p : OrderedDistinctPoints r)
    (hp : InConfigurationChart c p.val) :
    p ∈ W13.supportLocus r index ↔
      ∀ s : W27.HomogeneousMonomial index.1.val → W27.PlaneJet r index.2,
        MvPolynomial.eval (configurationChartCoordinates₂ c p.val)
          (W27.minorPolynomial (W27.chartPlaneJetMatrix (R := ℂ) c index.1.val index.2) s) = 0 := by
  classical
  have hforms : p ∈ W13.supportLocus r index ↔
      ∃ F : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ index.1.val,
        F.val ≠ 0 ∧ ∀ i,
          AffineMultiplicity.orderAtLeast
            (fun j => configurationChartCoordinates₂ c p.val (i, j)) (index.2 i)
            (W27.directChartHom (c i) F.val) := by
    constructor
    · rintro ⟨F, hFne, hFhom, hForder⟩
      refine ⟨⟨F, hFhom⟩, hFne, ?_⟩
      intro i
      exact (multiplicityAtLeast_iff_directChart hFhom (p.val i) (c i) (hp i)
        (index.2 i)).mp (hForder i)
    · rintro ⟨F, hFne, hForder⟩
      refine ⟨F.val, hFne, F.property, ?_⟩
      intro i
      exact (multiplicityAtLeast_iff_directChart F.property (p.val i) (c i) (hp i)
        (index.2 i)).mpr (hForder i)
  exact hforms.trans (W27.exists_nonzero_form_iff_chart_minors c index.1.val index.2
    (configurationChartCoordinates₂ c p.val))

/-- Closedness required by manuscript §1, Lemma `lem:universal`, for every
positive degree and every unequal nonnegative multiplicity vector. -/
theorem supportLocus_isConfigurationZariskiClosed (r : ℕ)
    (index : Workers.W25.IncidenceIndex r) :
    IsConfigurationZariskiClosed (W13.supportLocus r index) := by
  classical
  apply configurationClosed_of_chart_polynomial_equations
    (fun c s => W27.minorPolynomial
      (W27.chartPlaneJetMatrix (R := ℂ) c index.1.val index.2) s)
    (W13.supportLocus r index)
  intro c p hp
  exact supportLocus_iff_chart_minors r index c p hp

end Nagata.ProjectiveGeometry

end
end

section

/-!
# Actual projective universal reduction

This composes the projective support-locus closedness theorem with the complete
countable-avoidance and permutation-product construction. There is no incidence
closedness hypothesis in `universal_reduction`. All imported proofs must still
pass kernel validation before this draft can be advertised as proved.

The subsequent `strict_bound_of_no_universal` explicitly retains the main
mathematical exclusion of universal systems. It is not a Nagata proof.
-/
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- The full source universal reduction for genuine projective configurations,
actual homogeneous forms, and ordinary chart ideal-power conditions. -/
theorem universal_reduction (r : ℕ) (hr : 10 ≤ r) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
          ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ (D : ℝ) / M ≤ Real.sqrt r ∧
            UniversalSupport r D (fun _ => M) :=
  source_universal_reduction_of_incidence_closed r hr
    (supportLocus_isConfigurationZariskiClosed r)

/-- Conditional consequence: actual projective closedness is supplied, but
excluding all positive equal-multiplicity universal systems remains an explicit
input, including the square-case equality boundary. -/
theorem strict_bound_of_no_universal (r : ℕ) (hr : 10 ≤ r)
    (hno : ∀ D M : ℕ, 0 < D → 0 < M →
      (D : ℝ) / M ≤ Real.sqrt r → ¬ UniversalSupport r D (fun _ => M)) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt r :=
  strict_bound_of_incidence_closed_and_no_universal r hr
    (supportLocus_isConfigurationZariskiClosed r) hno

end Nagata.W13

end
end

end OAI
