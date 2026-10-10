import OAI.Geometry.SurfaceImmersion.Primitive.CompactTurnDichotomy

namespace OAI

/-! The turn threshold is fixed before any bound on the loop's transverse
coefficient.  The longitudinal threshold is allowed to depend on that bound. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem longitudinal_ordered_crossing_threshold (sHi K d B T : ℝ)
    (hsHi : 0 ≤ sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ J : ℝ, 0 < J ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → -K ≤ k → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → J < |L| →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  let R := Real.sqrt (K*(2*T)^2)+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨J,hJ,hproj⟩ := longitudinal_projection_threshold
    (E := E) sHi d B T R hsHi hd hB hT hR
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hS hSmax hk hD hN ht hu hL
  exact ⟨crossing_positive_of_projection hK hk ht hu
      (hproj n m hn hm hmn S D N L k t u hS hSmax hD hN ht hu hL),
    crossing_positive_of_projection hK hk hu ht
      (hproj n m hn hm hmn S D N L k u t hS hSmax hD hN hu ht hL)⟩

theorem two_mechanism_crossing_threshold (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ B : ℝ, 0 ≤ B → ∃ J : ℝ, 0 < J ∧
    ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → (H < |N| ∨ J < |L|) →
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  obtain ⟨H,hH,hturn⟩ := ordered_crossing_threshold (E := E) sLo sHi K d T
    hmin hmax hK hd hT
  refine ⟨H,hH,?_⟩
  intro B hB
  obtain ⟨J,hJ,hlong⟩ := longitudinal_ordered_crossing_threshold (E := E)
    sHi K d B T hmax.le hK hd hB hT
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hD hN ht hu halt
  rcases halt with hlargeN | hlargeL
  · exact (hturn n m hn hm hmn S D N L k t u hSmin hSmax hk hD ht hu hlargeN).2.2
  · exact hlong n m hn hm hmn S D N L k t u (hmin.trans_le hSmin)
      hSmax hk hD hN ht hu hlargeL

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
