import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrenceBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxMass
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Subexponential denominators for the actual translated recurrence boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold ENNReal Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

include hExp haar dynkin in
theorem exists_sequence_recurrence_enlargement
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let B := fun n => M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n)
    ∃ V : ℕ → ℝ, (∀ n, 1 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      HasSubexponentialUpperBoundSeq scale (fun n => V n ^ finrank ℝ (cartanRootIdeal H)) ∧
      ∀ n (k : N),
        μ ((fun y => y * k) '' B n 1) ≠ ∞ ∧
        0 < (μ ((fun y => y * k) '' B n 1)).toReal ∧
        μ ((fun y => y * k) '' B n (V n)) ≠ ∞ ∧
        0 < (μ ((fun y => y * k) '' B n (V n))).toReal ∧
        (μ ((fun y => y * k) '' B n (V n))).toReal =
          V n ^ finrank ℝ (cartanRootIdeal H) * (μ ((fun y => y * k) '' B n 1)).toReal ∧
        ∀ v : N, k * v * k⁻¹ ∈ B n (R n) →
          ∀ x ∈ (fun y => y * k) '' B n 1, x * v ∈ (fun y => y * k) '' B n (V n) := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
  let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let V := fun n => 1 + C * 3 ^ M.bound * (2 + R n) ^ M.bound
  have hV1 (n : ℕ) : 1 ≤ V n := by
    have := hR0 n
    dsimp [V]
    exact le_add_of_nonneg_right (by positivity)
  have hV : HasSubexponentialUpperBoundSeq scale V := by
    have hp := ((sequence_subexponential_upper_const hs 2).add hR hs).pow hs
      (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound
    exact (sequence_subexponential_upper_const hs 1).add
      ((sequence_subexponential_upper_const hs (C * 3 ^ M.bound)).mul hp
        (Eventually.of_forall (fun _ => by positivity))) hs
  dsimp only
  refine ⟨V, hV1, hV, hV.pow hs (Eventually.of_forall (fun n => (hV1 n).trans' zero_le_one)) _, ?_⟩
  intro n k
  have hunit := exponential_box_unit_mass eN Exp chart hchart b₀ (M.boxBasis T hunimod eW E β (scale n))
  have hmass : μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)) =
      ENNReal.ofReal (V n ^ finrank ℝ (cartanRootIdeal H)) *
        μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1) := by
    rw [measure_image_mul_right μ, measure_image_mul_right μ]
    exact exponential_box_radius_measure eN Exp chart hchart b₀
      (M.boxBasis T hunimod eW E β (scale n)) ((hV1 n).trans' zero_le_one)
  have hunit' : μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1) ≠ ∞ ∧
      0 < (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1)).toReal := by
    rw [measure_image_mul_right μ]
    exact hunit
  have hp : 0 < V n ^ finrank ℝ (cartanRootIdeal H) := pow_pos (zero_lt_one.trans_le (hV1 n)) _
  have hreal : (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n))).toReal =
      V n ^ finrank ℝ (cartanRootIdeal H) *
        (μ ((fun y => y * k) '' M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1)).toReal := by
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le]
  refine ⟨hunit'.1, hunit'.2, ?_, ?_, hreal, ?_⟩
  · rw [hmass]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit'.1
  · rw [hreal]
    exact mul_pos hp hunit'.2
  intro v hv x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (1 + R n) := by
    obtain ⟨w, hw, hb⟩ := hy
    exact ⟨w, hw, hb.trans (by linarith [hR0 n])⟩
  have hv' : k * v * k⁻¹ ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (1 + R n) := by
    obtain ⟨w, hw, hb⟩ := hv
    exact ⟨w, hw, hb.trans (by linarith)⟩
  have hb := hprod E β hβ (scale n) (hscale n) 2 (1 + R n) (by linarith [hR0 n])
    ![y, k * v * k⁻¹] (by intro i; fin_cases i; exact hy'; exact hv')
  have hb' : y * (k * v * k⁻¹) ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n) := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, mul_one] at hb
    obtain ⟨w, hw, hwbound⟩ := hb
    change (Exp ∘ eN) w = y * (k * v * k⁻¹) at hw
    refine ⟨w, hw, hwbound.trans ?_⟩
    dsimp [V]
    norm_num
    ring_nf
    linarith
  refine ⟨y * (k * v * k⁻¹), hb', ?_⟩
  group

end PolycyclicRecognition.CartanWordModel

end

end OAI
