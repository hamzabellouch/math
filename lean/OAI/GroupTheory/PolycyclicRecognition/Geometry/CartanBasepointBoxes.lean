import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConjugationHeightBound

namespace OAI

/-! # The two strict box margins in a change of basepoint -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

omit [FiniteDimensional ℝ W] in
include hExp dynkin in
/-- One fixed radius contains the three factors in the inverse-image
cover used by the changed-center Haar law. -/
theorem exists_basepoint_box_product_cover
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ x u a : N,
      x ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1 →
      u ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1 →
      a ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r 1 →
      x⁻¹ * u⁻¹ * a ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R := by
  obtain ⟨C, _, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  refine ⟨max 1 (C * 4 ^ M.bound * 2 ^ M.bound), le_max_left _ _, ?_⟩
  intro E β hβ r hr x u a hx hu ha
  have hp := hprod E β hβ r hr 3 1 zero_le_one ![x⁻¹, u⁻¹, a] (by
    intro i
    fin_cases i
    · exact M.groupBox_inv_mem T hunimod eW eN Exp hExp E β r 1 hx
    · exact M.groupBox_inv_mem T hunimod eW eN Exp hExp E β r 1 hu
    · exact ha)
  have hp' : x⁻¹ * u⁻¹ * a ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
      (C * 4 ^ M.bound * 2 ^ M.bound) := by
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, mul_one, mul_assoc,
      Nat.cast_ofNat, show (1 : ℝ) + 3 = 4 from by norm_num,
      show (1 : ℝ) + 1 = 2 from by norm_num] using hp
  obtain ⟨v, hv, hb⟩ := hp'
  exact ⟨v, hv, hb.trans (le_max_right _ _)⟩

/-- A fixed small height fraction preserves both strict scale margins.
The logarithmic bound and the larger radius may be any subexponential
sequences; the permitted height fraction is chosen before those sequences. -/
theorem exists_small_height_two_scale_inclusions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo α βscale : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    (hα : 0 < α) (hα1 : α < 1) (hβscale : 1 < βscale) :
    ∃ η : ℝ, 0 < η ∧ ∀ scale RH R : ℕ → ℝ,
      Tendsto scale atTop atTop → (∀ n, 0 ≤ RH n) → (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale RH → HasSubexponentialUpperBoundSeq scale R →
      ∀ᶠ n in atTop, ∀ h : H,
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ η * scale n →
        (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h ''
          M.groupBox T hunimod eW (Exp ∘ eN) E β (α * scale n) 1 ⊆
            M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1) ∧
        (M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin h ''
          M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) ⊆
            M.groupBox T hunimod eW (Exp ∘ eN) E β (βscale * scale n) 1) := by
  obtain ⟨K, hK, hincl⟩ := M.exists_eventual_adjoint_box_inclusion T hunimod eW
    eN Exp hExp hbij dynkin b₀ hE hne β hβ lo hcost
  let ε := min (1 - α) (βscale - 1) * lo / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεa : 2 * ε ≤ (1 - α) * lo := by
    have := mul_le_mul_of_nonneg_right (min_le_left (1 - α) (βscale - 1)) hlo.le
    dsimp [ε]
    linarith
  have hεb : 2 * ε ≤ (βscale - 1) * lo := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1 - α) (βscale - 1)) hlo.le
    dsimp [ε]
    linarith
  let η := ε / (K + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηeq : η * (K + 1) = ε := by dsimp [η]; field_simp
  have hKη : K * η ≤ ε := by nlinarith
  refine ⟨η, hη, ?_⟩
  intro scale RH R hs hRH0 hR0 hRH hR
  have hgap₁ : ∀ᶠ n in atTop, 0 < α * scale n ∧ α * scale n ≤ scale n ∧
      K * (η * scale n) - (scale n - α * scale n) * lo ≤ -ε * scale n := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    refine ⟨mul_pos hα hn, ?_, ?_⟩
    · nlinarith
    · have := mul_le_mul_of_nonneg_right (by linarith : K * η - (1 - α) * lo ≤ -ε) hn.le
      nlinarith
  have hgap₂ : ∀ᶠ n in atTop, 0 < scale n ∧ scale n ≤ βscale * scale n ∧
      K * (η * scale n) - (βscale * scale n - scale n) * lo ≤ -ε * scale n := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    refine ⟨hn, ?_, ?_⟩
    · nlinarith
    · have := mul_le_mul_of_nonneg_right (by linarith : K * η - (βscale - 1) * lo ≤ -ε) hn.le
      nlinarith
  have hi₁ := hincl scale (fun n => α * scale n) scale RH (fun _ => 1)
    (fun n => η * scale n) hs hRH0 (fun _ => zero_le_one) hRH
    (sequence_subexponential_upper_const hs 1) ε hε hgap₁
  have hi₂ := hincl scale scale (fun n => βscale * scale n) RH R
    (fun n => η * scale n) hs hRH0 hR0 hRH hR ε hε hgap₂
  filter_upwards [hi₁, hi₂] with n hn hm h hlog hheight
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    exact hn h hlog hheight g hg
  · rintro _ ⟨g, hg, rfl⟩
    exact hm h hlog hheight g hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
