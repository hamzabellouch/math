import OAI.Analysis.KadisonSimilarity.Tracial.MatrixExpectationIdentification
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixStageGrowth
import OAI.Analysis.BoundedHochschild.RankOneQuantization

namespace OAI

/-! Relative finite matrix averaging in an irreducible inclusion. The matrix
systems stay in the prescribed source algebra throughout the refinement. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

theorem map_matrix_rankOne {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {n : ℕ} (E : MatrixUnitSystem (Fin n) A) (φ : A →⋆ₐ[ℂ] B)
    (g : Fin n → ZMod 3) :
    φ ((matrixSystemOfUnits E).rankOne g) =
      (matrixSystemOfUnits (E.map φ)).rankOne g := by
  simp only [HochschildMatrixSystems.MatrixSystem.rankOne,
    HochschildMatrixSystems.MatrixSystem.scalarMatrix, map_sum, map_smul]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]
  (υ : TracialRepresentation M) (hNM : N ≤ M)
  (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c = c * coordinateInclusion hNM a) →
    ∃ z : ℂ, c = z • 1)

local instance relativeMatrixAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

local instance relativeMatrixSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

theorem matrix_stage_size_le_of_algebra_le {E F : FiniteMatrixStage N}
    (h : E.units.algebra ≤ F.units.algebra) : E.size ≤ F.size := by
  apply concreteStage_size_le
  intro x hx
  let a : N.toStarSubalgebra := ⟨x, E.units.concreteAlgebra_le hx⟩
  exact (F.units.mem_concreteAlgebra a).mpr (h ((E.units.mem_concreteAlgebra a).mp hx))

include hfactor hdiff hirr in
theorem exists_relative_matrix_expectation_budget {I : Type*} [Fintype I]
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N, E.size ≤ F.size ∧
      (∑ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        ((matrixSystemOfUnits (F.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2) < ε := by
  obtain ⟨F, hEF, hF⟩ := FiniteMatrixStage.exists_finite_matrix_energy_budget
    υ hNM hfactor hdiff hirr Finset.univ x (fun i _ => hx i) E ε hε
  refine ⟨F, matrix_stage_size_le_of_algebra_le hEF, ?_⟩
  simpa only [matrix_stage_energy_eq] using hF

omit [Nontrivial N.toStarSubalgebra] in
/-- A small phase-energy budget gives a nonzero compression in the source
algebra, with its exact trace retained in the ambient representation. -/
theorem exists_source_rankOne_compression {I : Type*} [Fintype I]
    (E : FiniteMatrixStage N) (x : I → M.toStarSubalgebra) {δ : ℝ}
    (hbudget : (∑ i,
      (‖(vectorPositiveFunctional M υ.vector).toPreGNS
          ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2 +
        ‖(vectorPositiveFunctional M υ.vector).toPreGNS (x i)‖ ^ 2 / (E.size : ℝ))) < δ) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      υ.trace (coordinateInclusion hNM q) = (E.size : ℂ)⁻¹ ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  classical
  let S := matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))
  let ρ := vectorPositiveFunctional M υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := υ.trace_mul_comm
  have h1 : ρ 1 = 1 := υ.trace_one
  have hn := Nat.ne_of_gt E.positive
  obtain ⟨g, hg⟩ := S.exists_phase_energy_bound ρ htr hn x
  let q := (matrixSystemOfUnits E.units).rankOne g
  have hq : coordinateInclusion hNM q = S.rankOne g := map_matrix_rankOne E.units _ g
  have ht : υ.trace (coordinateInclusion hNM q) = (E.size : ℂ)⁻¹ := by
    rw [hq]
    exact S.trace_rankOne ρ htr h1 hn g
  refine ⟨q, (matrixSystemOfUnits E.units).rankOne_projection hn g, ?_, ht, ?_⟩
  · intro hz
    rw [hz, map_zero] at ht
    rw [show υ.trace 0 = 0 by simp [TracialRepresentation.trace]] at ht
    have hnC : (E.size : ℂ) ≠ 0 := by exact_mod_cast hn
    exact (inv_ne_zero hnC) ht.symm
  · intro i
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        sq_nonneg ‖ρ.toPreGNS (S.phaseCoefficient g (x j))‖) (Finset.mem_univ i)
    have hiδ : ‖ρ.toPreGNS (S.phaseCoefficient g (x i))‖ ^ 2 < δ :=
      hi.trans_lt (hg.trans_lt hbudget)
    rw [hq]
    change ‖ρ.toPreGNS (S.rankOne g * x i * S.rankOne g)‖ ^ 2 < δ * (ρ (S.rankOne g)).re
    rw [S.rankOne_compression_norm ρ htr hn, S.trace_rankOne ρ htr h1 hn]
    have he : (E.size : ℂ)⁻¹ = Complex.ofReal ((E.size : ℝ)⁻¹) := by simp
    rw [he, Complex.ofReal_re, mul_comm δ]
    exact mul_lt_mul_of_pos_left hiδ (inv_pos.mpr (by exact_mod_cast E.positive))

include hfactor hdiff hirr in
/-- Relative local quantization with a small projection in the prescribed
source, using its cofinal family of finite matrix stages. -/
theorem exists_source_small_projection {I : Type*} [Fintype I]
    (T : ℕ → FiniteMatrixStage N) (hT : ∀ m : ℕ, ∃ j, m < (T j).size)
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  let ρ := vectorPositiveFunctional M υ.vector
  let B : ℝ := ∑ i, ‖ρ.toPreGNS (x i)‖ ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (2 * B / δ) (1 / η))
  obtain ⟨j, hj⟩ := hT m
  obtain ⟨E, hTE, hE⟩ := exists_relative_matrix_expectation_budget υ hNM hfactor hdiff hirr
    x hx (T j) (δ / 2) (by positivity)
  have hmn : m < E.size := hj.trans_le hTE
  have hn : (0 : ℝ) < E.size := by exact_mod_cast E.positive
  have hBsmall : B / (E.size : ℝ) < δ / 2 := by
    have hlt : 2 * B / δ < (E.size : ℝ) :=
      (le_max_left _ _).trans_lt (hm.trans (by exact_mod_cast hmn))
    have hh := (div_lt_iff₀ hδ).mp hlt
    apply (div_lt_iff₀ hn).mpr
    nlinarith
  have hbudget : (∑ i,
      (‖ρ.toPreGNS
          ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2 +
        ‖ρ.toPreGNS (x i)‖ ^ 2 / (E.size : ℝ))) < δ := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    change _ + B / (E.size : ℝ) < δ
    linarith
  obtain ⟨q, hq, hq0, ht, hc⟩ := exists_source_rankOne_compression υ hNM E x hbudget
  refine ⟨q, hq, hq0, ?_, hc⟩
  rw [ht]
  have he : (E.size : ℂ)⁻¹ = Complex.ofReal ((E.size : ℝ)⁻¹) := by simp
  rw [he, Complex.ofReal_re]
  apply (inv_lt_comm₀ hn hη).mpr
  have hlt : 1 / η < (E.size : ℝ) :=
    (le_max_right _ _).trans_lt (hm.trans (by exact_mod_cast hmn))
  simpa only [one_div] using hlt

include υ hNM hfactor hdiff in
omit [Nontrivial N.toStarSubalgebra] in
/-- Every required finite size occurs in the diffuse source; no separable
matrix tower is needed for the local estimate. -/
theorem exists_source_matrix_stage (n : ℕ) (hn : 0 < n) :
    ∃ E : FiniteMatrixStage N, E.size = n := by
  obtain ⟨E, _⟩ := exists_commuting_matrix_extension (restrictedTrace υ hNM)
    (FiniteMatrixStage.scalarStage N).units ⟨0, Nat.zero_lt_one⟩ hfactor hdiff n hn
  exact ⟨⟨n, hn, E⟩, rfl⟩

include hfactor hdiff hirr in
/-- Relative local quantization without a chosen matrix tower. -/
theorem exists_source_small_projection_of_diffuse {I : Type*} [Fintype I]
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  choose T hT using fun n => exists_source_matrix_stage υ hNM hfactor hdiff
    (n + 1) (Nat.succ_pos n)
  exact exists_source_small_projection υ hNM hfactor hdiff hirr T
    (fun n => ⟨n, by rw [hT]; exact Nat.lt_succ_self n⟩) x hx hδ hη

end KadisonSimilarity

end

end OAI
