import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedBoxMass

namespace OAI

/-! # A fixed denominator bound for the recurrence boxes -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

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
/-- Once the conjugated increment is in the unit normalized box, a single
fixed enlargement controls every recurrence denominator. Its volume ratio
is independent of the template, scale, suffix and increment law. -/
theorem exists_recurrence_box_enlargement
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val → ∀ r : ℝ, 0 ≤ r →
      let B := M.groupBox T hunimod eW (Exp ∘ eN) E β r
      let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
      (∀ k s : N, k * s * k⁻¹ ∈ B 1 →
        ∀ x ∈ (fun y => y * k) '' B 1, x * s ∈ (fun y => y * k) '' B R) ∧
      ∀ k : N, μ ((fun y => y * k) '' B R) =
        ENNReal.ofReal (R ^ finrank ℝ (cartanRootIdeal H)) * μ ((fun y => y * k) '' B 1) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let R := 1 + C * (3 : ℝ) ^ M.bound * (2 : ℝ) ^ M.bound
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_right (by positivity)
  refine ⟨R, hR, ?_⟩
  intro E β hβ r hr
  dsimp only
  let B := M.groupBox T hunimod eW (Exp ∘ eN) E β r
  have hbinary : ∀ x ∈ B 1, ∀ y ∈ B 1, x * y ∈ B R := by
    intro x hx y hy
    have hh := hprod E β hβ r hr 2 1 zero_le_one ![x, y] (by
      intro i
      fin_cases i
      · exact hx
      · exact hy)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, mul_one] at hh
    obtain ⟨z, hz, hb⟩ := hh
    refine ⟨z, hz, hb.trans ?_⟩
    dsimp [R]
    norm_num
  constructor
  · intro k s hs x hx
    exact translated_box_increment_mem hbinary k s hs hx
  · let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
    have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
      (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
    obtain ⟨⟨chart, hc⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
    intro k
    change μ ((fun y => y * k) '' B R) = _
    rw [measure_image_mul_right μ, measure_image_mul_right μ]
    exact exponential_box_radius_measure eN Exp chart hc b₀
      (M.boxBasis T hunimod eW E β r) (zero_le_one.trans hR)

end PolycyclicRecognition.CartanWordModel

end

end OAI
