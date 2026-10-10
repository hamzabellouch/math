import OAI.Analysis.KadisonSimilarity.Representation.FactorAssembly
import OAI.Analysis.KadisonSimilarity.Representation.CentralSymmetrization
import OAI.Analysis.KadisonSimilarity.Representation.CountableFiberTests

namespace OAI

/-! # Central decomposition and the uniform separable estimate

The direct-integral input records only representatives of decomposable
operators, their almost-everywhere algebra operations, the scalar and matrix
norm formulas, and countably many dense contraction sections. These are the
specializations of Blackadar, III.1.6.1–4 and III.5.1.10–15 used here (with
Kaplansky density, I.9.1.3, for the contraction tests). Representatives need
satisfy algebraic identities only almost everywhere for each fixed pair.

The scalar fiber bounds, their common conull set, the factor estimates, and
the final perturbation estimate are proved below.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter ContinuousLinearMapWOT
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every element of the algebra commutes with its center. -/
theorem le_center_commutant (P : VonNeumannAlgebra H) :
    P.toStarSubalgebra ≤ (vonNeumannCenter P).commutant.toStarSubalgebra := by
  intro x hx
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro z hz
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) x hx).symm

/-- The original algebra as a subalgebra of the decomposable operators. -/
def centerCommutantInclusion (P : VonNeumannAlgebra H) :
    P.toStarSubalgebra →⋆ₐ[ℂ] (vonNeumannCenter P).commutant.toStarSubalgebra :=
  StarSubalgebra.inclusion (le_center_commutant P)

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type u) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- The exact direct-integral identities needed for one separable algebra.
No commutator estimate is a field of this structure. -/
structure CentralDecompositionData (P : VonNeumannAlgebra H) where
  algebra : ∀ a, VonNeumannAlgebra (K a)
  fiber : (vonNeumannCenter P).commutant.toStarSubalgebra → ∀ a, K a →L[ℂ] K a
  map_sub : ∀ x y, ∀ᵐ a ∂μ, fiber (x - y) a = fiber x a - fiber y a
  map_mul : ∀ x y, ∀ᵐ a ∂μ, fiber (x * y) a = fiber x a * fiber y a
  mem : ∀ x : P.toStarSubalgebra, ∀ᵐ a ∂μ,
    fiber (centerCommutantInclusion P x) a ∈ algebra a
  norm_le_iff : ∀ (x : (vonNeumannCenter P).commutant.toStarSubalgebra) (c : ℝ), 0 ≤ c →
    (‖(x : H →L[ℂ] H)‖ ≤ c ↔ ∀ᵐ a ∂μ, ‖fiber x a‖ ≤ c)
  matrix_norm_le_iff : ∀ (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (vonNeumannCenter P).commutant.toStarSubalgebra)
    (c : ℝ), 0 ≤ c →
    (‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ ≤ c ↔
      ∀ᵐ a ∂μ, ‖matrixOperator (fun i j => fiber (X i j) a)‖ ≤ c)
  test : ℕ → P.toStarSubalgebra
  test_norm : ∀ j, ‖(test j : H →L[ℂ] H)‖ ≤ 1
  test_dense : ∀ᵐ a ∂μ, ∀ T : K a →L[ℂ] K a,
    T ∈ algebra a → ‖T‖ ≤ 1 →
    ofCLM T ∈ closure (Set.range fun j =>
      ofCLM (fiber (centerCommutantInclusion P (test j)) a))

variable {μ K} {P : VonNeumannAlgebra H}

/-- Fiber representatives preserve each fixed commutator almost everywhere. -/
theorem CentralDecompositionData.map_commutator
    (D : CentralDecompositionData μ K P)
    (x y : (vonNeumannCenter P).commutant.toStarSubalgebra) :
    ∀ᵐ a ∂μ, D.fiber (commutator x y) a =
      commutator (D.fiber x a) (D.fiber y a) := by
  filter_upwards [D.map_sub (x * y) (y * x), D.map_mul x y, D.map_mul y x]
    with a hs hxy hyx
  simpa only [commutator, hxy, hyx] using hs

/-- The countable sections give one conull set with the full scalar bound. -/
theorem CentralDecompositionData.scalar_bound
    (D : CentralDecompositionData μ K P)
    (Y : (vonNeumannCenter P).commutant.toStarSubalgebra)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : scalarCommutatorNorm P (Y : H →L[ℂ] H) ≤ c) :
    ∀ᵐ a ∂μ, scalarCommutatorNorm (D.algebra a) (D.fiber Y a) ≤ c := by
  apply ae_scalarCommutatorNorm_le_of_countable_tests μ K D.algebra (D.fiber Y)
    (fun a j => D.fiber (centerCommutantInclusion P (D.test j)) a) D.test_dense hc
  intro j
  have hb : ‖commutator (Y : H →L[ℂ] H) (D.test j : H →L[ℂ] H)‖ ≤ c := by
    calc
      _ ≤ scalarCommutatorNorm P (Y : H →L[ℂ] H) *
          ‖(D.test j : H →L[ℂ] H)‖ :=
        norm_commutator_le_scalarCommutatorNorm P Y (D.test j) (D.test j).property
      _ ≤ c * 1 := mul_le_mul hbound (D.test_norm j) (norm_nonneg _) hc
      _ = c := mul_one _
  have hf := (D.norm_le_iff (commutator Y (centerCommutantInclusion P (D.test j))) c hc).mp hb
  filter_upwards [hf, D.map_commutator Y (centerCommutantInclusion P (D.test j))]
    with a ha he
  simpa only [he] using ha

variable [∀ a, TopologicalSpace.SeparableSpace (K a)]

/-- A decomposable operator on the separable direct-integral fibers inherits
the uniform factor bound. -/
theorem CentralDecompositionData.matrix_bound
    (D : CentralDecompositionData μ K P)
    (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
    (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a)))
    (Y : (vonNeumannCenter P).commutant.toStarSubalgebra)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : scalarCommutatorNorm P (Y : H →L[ℂ] H) ≤ c)
    (n : ℕ) (X : Matrix (Fin n) (Fin n) P.toStarSubalgebra) :
    ‖commutator (amplify (Y : H →L[ℂ] H) n)
      (matrixOperator (fun i j => (X i j : H →L[ℂ] H)))‖ ≤
      factorConstant * c * ‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ := by
  let Z := fun i j => centerCommutantInclusion P (X i j)
  let R := ‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖
  have hR : 0 ≤ R := norm_nonneg _
  have hnorm : ∀ᵐ a ∂μ, ‖matrixOperator (fun i j => D.fiber (Z i j) a)‖ ≤ R :=
    (D.matrix_norm_le_iff n Z R hR).mp le_rfl
  have hmem : ∀ᵐ a ∂μ, ∀ i j, D.fiber (Z i j) a ∈ D.algebra a := by
    exact eventually_countable_forall.mpr fun i =>
      eventually_countable_forall.mpr fun j => D.mem (X i j)
  have hcomm : ∀ᵐ a ∂μ, ∀ i j,
      D.fiber (commutator Y (Z i j)) a =
        commutator (D.fiber Y a) (D.fiber (Z i j) a) := by
    exact eventually_countable_forall.mpr fun i =>
      eventually_countable_forall.mpr fun j => D.map_commutator Y (Z i j)
  rw [commutator_amplify_matrixOperator (Y : H →L[ℂ] H)
    (X := fun i j => (X i j : H →L[ℂ] H))]
  apply (D.matrix_norm_le_iff n (fun i j => commutator Y (Z i j))
    (factorConstant * c * R)
    (mul_nonneg (mul_nonneg (le_of_lt factorConstant_pos) hc) hR)).mpr
  filter_upwards [cases, dickson, D.scalar_bound Y hc hbound, hnorm, hmem, hcomm]
    with a hcase hd hs hn hm he
  have h := factor_estimate_of_published_cases (D.algebra a) hcase hd
    (D.fiber Y a) n (fun i j => D.fiber (Z i j) a) hm
  have heq : (fun i j => D.fiber (commutator Y (Z i j)) a) =
      (fun i j => commutator (D.fiber Y a) (D.fiber (Z i j) a)) := by
    funext i j
    exact he i j
  rw [heq, ← commutator_amplify_matrixOperator (D.fiber Y a)
    (X := fun i j => D.fiber (Z i j) a)]
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hs (le_of_lt factorConstant_pos)) hn (norm_nonneg _)
    (mul_nonneg (le_of_lt factorConstant_pos) hc))

/-- Central averaging followed by the factor estimates proves the
manuscript's constant on this represented algebra. -/
theorem commutatorEstimate_of_centralDecomposition
    (D : CentralDecompositionData μ K P)
    (approximation : SpectralStepApproximation (vonNeumannCenter P))
    (cases : ∀ᵐ a ∂μ, PublishedFactorCasesInput (D.algebra a))
    (dickson : ∀ᵐ a ∂μ, DicksonTwoBound (A := D.algebra a) (RectangularSum (K a) (K a))) :
    CommutatorEstimate P universalConstant := by
  intro Y n X hX
  let δ := scalarCommutatorNorm P Y
  have hδ : 0 ≤ δ := scalarCommutatorNorm_nonneg P Y
  obtain ⟨Y₁, _, hclose, hscalar, hcenter⟩ :=
    exists_central_symmetrization P approximation Y hδ le_rfl
  have hY₁ : Y₁ ∈ (vonNeumannCenter P).commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (sub_eq_zero.mp (hcenter a ha)).symm
  have hbound := D.matrix_bound cases dickson ⟨Y₁, hY₁⟩
    (show 0 ≤ 3 * δ by positivity) hscalar n (fun i j => ⟨X i j, hX i j⟩)
  have hperturb : ‖amplify Y n - amplify Y₁ n‖ ≤ δ := by
    have he : amplify Y n - amplify Y₁ n = amplify (Y - Y₁) n := by
      ext ξ i
      simp [amplify_apply, _root_.sub_apply]
    rw [he]
    exact (norm_amplify_le _ _).trans (by simpa only [norm_sub_rev] using hclose)
  calc
    _ ≤ factorConstant * (3 * δ) * ‖matrixOperator X‖ +
        2 * δ * ‖matrixOperator X‖ :=
      norm_commutator_le_of_approx (amplify Y n) (amplify Y₁ n)
        (matrixOperator X) hbound hperturb
    _ = universalConstant * scalarCommutatorNorm P Y * ‖matrixOperator X‖ := by
      dsimp [universalConstant, δ]
      ring

end KadisonSimilarity

end

end OAI
