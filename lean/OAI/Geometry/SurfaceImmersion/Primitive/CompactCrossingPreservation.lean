import OAI.Geometry.SurfaceImmersion.Primitive.TwoMechanismCrossing

namespace OAI

/-! Uniform positivity at the later crossings from the actual two second-form
limits.  Only the limiting angular speed and mixed component enter compactness. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem compact_crossing_preservation (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ (C : Set X), IsCompact C →
    ∀ A N₀ : X → ℝ, Continuous A → Continuous N₀ →
    (∀ x ∈ C, A x = 0 → H+2 < |N₀ x|) →
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η → ∀ x ∈ C,
    ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → |N-N₀ x| < η → |z*L-A x| < η →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  obtain ⟨H,hH,hthreshold⟩ := two_mechanism_crossing_threshold (E := E)
    sLo sHi K d T hmin hmax hK hd hT
  refine ⟨H,hH,?_⟩
  intro C hC A N₀ hA hN₀ hturn
  obtain ⟨B,hB⟩ := (hC.image hN₀.abs).bddAbove
  let B₀ := max 0 B
  have hB₀ : 0 ≤ B₀ := le_max_left _ _
  have hbound : ∀ x ∈ C, |N₀ x| ≤ B₀ := fun x hx =>
    (hB (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  obtain ⟨J,hJ,hcross⟩ := hthreshold (B₀+1) (by positivity)
  obtain ⟨η₀,hη₀,hdichotomy⟩ := small_scale_turn_or_longitudinal hC hA hN₀ H J hJ.le hturn
  refine ⟨min 1 η₀,lt_min (by norm_num) hη₀,?_⟩
  intro z hz hzη x hx n m hn hm hmn S D N L k t u hSmin hSmax hk hD ht hu hN hL
  have hNsmall : |N-N₀ x| < 1 := hN.trans_le (min_le_left _ _)
  have hNbound : |N| ≤ B₀+1 := by
    have ha := abs_sub_le N (N₀ x) 0
    simp only [sub_zero] at ha
    linarith [hbound x hx]
  apply hcross n m hn hm hmn S D N L k t u hSmin hSmax hk hD hNbound ht hu
  exact hdichotomy z hz (hzη.trans_le (min_le_right _ _)) x hx N L hNsmall
    (hL.trans_le (min_le_right _ _))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
