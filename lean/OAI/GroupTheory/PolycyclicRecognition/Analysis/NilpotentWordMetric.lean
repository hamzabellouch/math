import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarseFlowBounds

namespace OAI

/-! # Metric bounds for the actual unit-weight nilpotent charts -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A word of bounded length and bounded letters has the corresponding
metric bound in every group with a left invariant metric. -/
theorem dist_generatorGroupWord_le
    {I L G : Type*} [SMul ℝ L] [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (X : I → L) (Exp : L → G) (u : List (I × ℝ)) {B D : ℝ}
    (hu : ∀ z ∈ u, |z.2| ≤ B)
    (hstep : ∀ i t, |t| ≤ B → dist 1 (Exp (t • X i)) ≤ D) :
    dist 1 (generatorGroupWord X Exp u) ≤ (u.length : ℝ) * D := by
  induction u with
  | nil => simp [generatorGroupWord]
  | cons z u ih =>
    rw [generatorGroupWord_cons]
    have hz := hstep z.1 z.2 (hu z (by simp))
    have hr := ih (fun w hw => hu w (by simp [hw]))
    calc
      _ ≤ dist 1 (Exp (z.2 • X z.1)) +
          dist (Exp (z.2 • X z.1)) (Exp (z.2 • X z.1) * generatorGroupWord X Exp u) :=
        dist_triangle _ _ _
      _ = dist 1 (Exp (z.2 • X z.1)) + dist 1 (generatorGroupWord X Exp u) := by
        congr 1
        simpa only [mul_one] using
          dist_mul_left (Exp (z.2 • X z.1)) 1 (generatorGroupWord X Exp u)
      _ ≤ D + (u.length : ℝ) * D := add_le_add hz hr
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- Uniform generator-word bounds imply linear metric growth on every
fixed-radius unit-weight chart. Only continuity of the generating flows
is required from the metric; no geodesic or scaling estimate is assumed. -/
theorem exists_unit_weight_chart_metric_bound
    {I L G : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : I → L) {k c : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hcont : ∀ i, Continuous (fun t : ℝ => Exp (t • X i)))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent (fun _ : I => 1) w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent (fun _ : I => 1) (β.val i)) r).equivFun v‖ ≤ R →
      dist 1 (Exp v) ≤ C * Real.exp r := by
  classical
  obtain ⟨N, B, hB, hgen⟩ := exists_uniform_rescaled_generator_words X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch R
  choose D hD hflow using fun i => continuous_flow_coarse_bound
    (fun t : ℝ => Exp (t • X i)) (hcont i) (by simpa using hzero) (hadd (X i))
  let D₀ := ∑ i, D i
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg (fun i _ => hD i)
  have hDi (i : I) : D i ≤ D₀ :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
  refine ⟨(N : ℝ) * (D₀ * (1 + B)), by positivity, ?_⟩
  intro β hβ r hr v hv
  obtain ⟨u, hu, hub, hue⟩ := hgen (fun _ : I => 1) β hβ r hr v hv
  have her : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
  have hstep (i : I) (t : ℝ) (ht : |t| ≤ B) :
      dist 1 (Exp (t • (Real.exp (r * (1 : ℝ)) • X i))) ≤ D₀ * (1 + B) * Real.exp r := by
    rw [smul_smul, mul_one]
    calc
      _ ≤ D i * (1 + |t * Real.exp r|) := hflow i _
      _ ≤ D₀ * (1 + B * Real.exp r) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        gcongr
        exact hDi i
      _ ≤ D₀ * ((1 + B) * Real.exp r) := by
        apply mul_le_mul_of_nonneg_left _ hD₀
        nlinarith
      _ = _ := by ring
  rw [← hue]
  calc
    _ ≤ (u.length : ℝ) * (D₀ * (1 + B) * Real.exp r) :=
      dist_generatorGroupWord_le _ Exp u hub hstep
    _ ≤ (N : ℝ) * (D₀ * (1 + B) * Real.exp r) := by gcongr
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
