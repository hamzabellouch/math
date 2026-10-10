import OAI.Geometry.SurfaceImmersion.Primitive.CrossingThreshold

namespace OAI

/-! The same finite threshold gives both ordered crossing inequalities. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma crossing_positive_of_projection {K T k t u p : ℝ}
    (hK : 0 ≤ K) (hk : -K ≤ k) (ht : |t| ≤ T) (hu : |u| ≤ T)
    (hp : Real.sqrt (K*(2*T)^2)+1 < p) : 0 < p^2+k*(t-u)^2 := by
  have hab : |t-u| ≤ 2*T := by
    have hh := (abs_sub t u).trans (add_le_add ht hu)
    linarith
  have hsq : (t-u)^2 ≤ (2*T)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t-u)) hab 2
  have hcurv : -K*(2*T)^2 ≤ k*(t-u)^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hsq hK
    have h₂ := mul_le_mul_of_nonneg_right hk (sq_nonneg (t-u))
    nlinarith
  have hs := Real.sq_sqrt (mul_nonneg hK (sq_nonneg (2*T)))
  have hs0 := Real.sqrt_nonneg (K*(2*T)^2)
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def modelOrderedCrossing (n m : E) (S D N L k t u : ℝ) : ℝ :=
  (inner ℝ (frameVector n m (slopeMixed S D N L k t u))
    (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
      frameVector n m (slopePure S D N L k t)))^2+k*(t-u)^2

theorem ordered_crossing_threshold (sLo sHi K d T : ℝ)
    (hmin : 0 < sLo) (hmax : 0 < sHi) (hK : 0 ≤ K) (hd : 0 ≤ d) (hT : 0 ≤ T) :
    ∃ H : ℝ, 0 < H ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, sLo ≤ S → S ≤ sHi → -K ≤ k → |D| ≤ d →
      |t| ≤ T → |u| ≤ T → H < |N| →
      0 < (slopePure S D N L k t).1 ∧ 0 < (slopePure S D N L k u).1 ∧
      0 < modelOrderedCrossing n m S D N L k t u ∧
      0 < modelOrderedCrossing n m S D N L k u t := by
  let R := Real.sqrt (K*(2*T)^2)+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨H,hH,hh⟩ := uniform_crossing_threshold (E := E) sLo sHi K d T R hmin hmax hK hd hT hR
  refine ⟨H,hH,?_⟩
  intro n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  obtain ⟨hpt,hqt⟩ := hh n m hn hm hmn S D N L k t u hSmin hSmax hk hDb htb hub hN
  obtain ⟨hpu,hqu⟩ := hh n m hn hm hmn S D N L k u t hSmin hSmax hk hDb hub htb hN
  exact ⟨hpt,hpu,crossing_positive_of_projection hK hk htb hub hqt,
    crossing_positive_of_projection hK hk hub htb hqu⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
