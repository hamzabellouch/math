import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinSummableProducts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialChartCoordinates

namespace OAI

/-! # Small products in the actual word-length chart

The bound keeps the sum of the rescaled increment sizes. Thus a word with
length small compared with the chart scale has small chart coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

theorem norm_word_chart_coordinates_le
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 1 ≤ cost j)
    {r : ℝ} (hr : 1 ≤ r) (x : L) :
    ‖(exponentialRescaleBasis b cost (Real.log r)).equivFun x‖ ≤
      ‖b.equivFun x‖ / r := by
  have hr0 : 0 < r := by linarith
  have hh := norm_change_exponentialRescaleBasis_le b cost (fun _ => 0)
    (Real.log_nonneg hr) (α := -1) (fun j => by linarith [hcost j]) x
  have hb : exponentialRescaleBasis b (fun _ => 0) (Real.log r) = b := by
    ext j
    simp only [exponentialRescaleBasis, Basis.unitsSMul_apply, mul_zero, Real.exp_zero,
      Units.smul_def, Units.val_mk0, one_smul]
  rw [hb, mul_neg_one, Real.exp_neg, Real.exp_log hr0] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Changing the physical scale by at most a factor of two expands
coordinates by at most the largest word degree. -/
theorem norm_word_chart_change_le
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (p : ℕ)
    (hcost : ∀ j, 0 ≤ cost j) (hp : ∀ j, cost j ≤ p)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ 2 * s) (x : L) :
    ‖(exponentialRescaleBasis b cost (Real.log s)).equivFun x‖ ≤
      2 ^ p * ‖(exponentialRescaleBasis b cost (Real.log r)).equivFun x‖ := by
  have hlog : Real.log r - Real.log s ≤ Real.log 2 := by
    rw [← Real.log_div hr.ne' hs.ne']
    apply Real.log_le_log (div_pos hr hs)
    exact (div_le_iff₀ hs).mpr (by linarith)
  have hgap j : Real.log r * cost j - Real.log s * cost j ≤ Real.log 2 * p := by
    calc
      _ = (Real.log r - Real.log s) * cost j := by ring
      _ ≤ Real.log 2 * cost j := mul_le_mul_of_nonneg_right hlog (hcost j)
      _ ≤ Real.log 2 * p := mul_le_mul_of_nonneg_left (hp j) (Real.log_nonneg (by norm_num))
  have hh := norm_change_exponentialRescaleBasis_le b
    (fun j => Real.log s * cost j) (fun j => Real.log r * cost j)
    zero_le_one hgap x
  have he : Real.exp (Real.log 2 * p) = (2 : ℝ) ^ p := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simpa only [exponentialRescaleBasis, one_mul, he] using hh

variable {L I E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The constant is independent of the scale and number of increments.
Only the published finite Dynkin identity is used. -/
theorem exists_word_chart_small_product_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : WordBasisSelections X (boundedBracketWords c))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (r : ℝ), 1 ≤ r → ∀ (n : ℕ) (v : Fin n → L)
      (R : ℝ), 0 ≤ R →
      (∀ i, ‖(WordBasisSelections.basis X (boundedBracketWords c) β).equivFun (v i)‖ ≤ R) →
      ∃ z : L, (List.ofFn (fun i => Exp (e (v i)))).prod = Exp (e z) ∧
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j))
          (Real.log r)).equivFun z‖ ≤
            A * ((n : ℝ) * R / r) * (1 + (n : ℝ) * R / r) ^ c := by
  obtain ⟨C, hC, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound X hc b₀
  let A := (c : ℝ) * 2 ^ c * (1 + (finrank ℝ L : ℝ) ^ 2 * C) ^ c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro r hr n v R hR hv
  let b := WordBasisSelections.basis X (boundedBracketWords c) β
  let br := exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  have hcost j : 1 ≤ bracketWordExponent (fun _ : I => 1) (β.val j) := by
    rw [bracketWordExponent_one, bracketWordLength_eq_nodes_add_one]
    exact_mod_cast Nat.le_add_left 1 (bracketWordNodes (β.val j : FreeMagma I))
  have hsmall i : ‖br.equivFun (v i)‖ ≤ R / r :=
    (norm_word_chart_coordinates_le b _ hcost hr (v i)).trans
      (div_le_div_of_nonneg_right (hv i) (by linarith))
  have hsum : (∑ i, ‖br.equivFun (v i)‖) ≤ (n : ℝ) * R / r := by
    calc
      _ ≤ ∑ _i : Fin n, R / r := Finset.sum_le_sum (fun i _ => hsmall i)
      _ = _ := by simp [mul_div_assoc]
  obtain ⟨a, ha, hp⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc n
  refine ⟨finiteDynkinPolynomial a v, hp v, ?_⟩
  have hb := norm_finiteDynkinPolynomial_le_sum br a ha v hC
    (hbracket (fun _ : I => 1) β hβ (Real.log r) (Real.log_nonneg hr))
  change ‖br.equivFun (finiteDynkinPolynomial a v)‖ ≤ _
  apply hb.trans
  simp only [Fintype.card_fin]
  change A * (∑ i, ‖br.equivFun (v i)‖) * (1 + ∑ i, ‖br.equivFun (v i)‖) ^ c ≤ _
  gcongr

end PolycyclicRecognition

end

end OAI
