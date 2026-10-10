import OAI.Geometry.SurfaceImmersion.Geometry.LongitudinalNormalChoice
import OAI.Geometry.SurfaceImmersion.Primitive.CompactTurnDichotomy

namespace OAI

/-! Uniform choice of an admissible preferred-normal path at a crossing.
The transverse threshold is fixed before the angular loop. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem compact_crossing_normal_choice (sLo sHi K d T : ℝ)
    (hsLo : 0 < sLo) (hsHi : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ C : Set X, IsCompact C →
      ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
      (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
      ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
      ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → |N-N₀ x| < η → |z*L-A x| < η →
      let P := frameVector n m (slopePure S D N L k t)
      let Q := frameVector n m (slopePure S D N L k u)
      (0 < inner ℝ P n ∧ 0 < inner ℝ Q n) ∨
        (0 < inner ℝ P Q ∧ ∃ w : E,
          inner ℝ n w = 0 ∧ 0 < inner ℝ P w ∧ 0 < inner ℝ Q w) := by
  obtain ⟨H,hH,htransverse⟩ := uniform_crossing_threshold (E := E)
    sLo sHi K d T 0 hsLo hsHi hK hd hT le_rfl
  refine ⟨H,hH,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B+1
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hbound : ∀ x ∈ C, |N₀ x| ≤ max 0 B := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  obtain ⟨J,hJ,hlong⟩ := longitudinal_normal_choice (E := E)
    sHi d B₀ T hsHi.le hd hB₀ hT
  obtain ⟨η₀,hη₀,halt⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min zero_lt_one hη₀,?_⟩
  intro z hz hzη x hx n m hn hm hmn S D N L k t u hS hShi hk hD ht hu hN hL
  dsimp only
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀ := by
    have hh := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at hh
    dsimp [B₀]
    linarith [hbound x hx]
  rcases halt z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
      (hL.trans_le (min_le_right _ _)) with hlargeN | hlargeL
  · left
    rw [frameVector_inner_first hn hmn,frameVector_inner_first hn hmn]
    exact ⟨(htransverse n m hn hm hmn S D N L k t u hS hShi hk hD ht hu hlargeN).1,
      (htransverse n m hn hm hmn S D N L k u t hS hShi hk hD hu ht hlargeN).1⟩
  · right
    exact hlong n m hn hm hmn S D N L k t u (hsLo.trans_le hS) hShi hD hNbound ht hu hlargeL

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
