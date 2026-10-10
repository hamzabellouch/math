import OAI.Geometry.SurfaceImmersion.Primitive.CrossingProjectionBounds

namespace OAI

/-! Uniform crossing estimates with no dependence on the longitudinal
second-form coefficient. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma crossing_first_lower {S D N L k t sLo sHi K : ℝ}
    (hmin : 0 < sLo) (hSmin : sLo ≤ S) (hSmax : S ≤ sHi) (hK : 0 ≤ K) (hk : -K ≤ k) :
    N^2/sHi-K/sLo ≤ (slopePure S D N L k t).1 := by
  have hS : 0 < S := hmin.trans_le hSmin
  have hN := div_le_div_of_nonneg_left (sq_nonneg N) hS hSmax
  have hK' := div_le_div_of_nonneg_left hK hmin hSmin
  have hk' := div_le_div_of_nonneg_right hk hS.le
  have hsquare := div_nonneg (sq_nonneg (D+S*t)) hS.le
  change _ ≤ (N^2+k+(D+S*t)^2)/S
  rw [add_div,add_div]
  rw [neg_div] at hk'
  linarith

lemma crossing_slope_bound {S D N t u sHi d T : ℝ}
    (hS : 0 ≤ S) (hSmax : S ≤ sHi) (hd : |D| ≤ d)
    (ht : |t| ≤ T) (hu : |u| ≤ T) :
    |u-t| * (|D+S*t|+|N|) ≤ 2*T*(d+sHi*T+|N|) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hsHi : 0 ≤ sHi := hS.trans hSmax
  have hdiff : |u-t| ≤ 2*T := by
    have hh := (abs_sub u t).trans (add_le_add hu ht)
    linarith
  have hlinear : |D+S*t| ≤ d+sHi*T := by
    calc
      |D+S*t| ≤ |D|+|S*t| := abs_add_le _ _
      _ = |D|+S*|t| := by rw [abs_mul,abs_of_nonneg hS]
      _ ≤ d+sHi*T := add_le_add hd (mul_le_mul hSmax ht (abs_nonneg _) hsHi)
  exact mul_le_mul hdiff (add_le_add hlinear le_rfl) (by positivity) (by positivity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_crossing_projection_lower {n m : E}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hmn : inner ℝ m n = 0)
    {S D N L k t u sLo sHi K d T : ℝ}
    (hmin : 0 < sLo) (hSmin : sLo ≤ S) (hSmax : S ≤ sHi)
    (hK : 0 ≤ K) (hk : -K ≤ k) (hd : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T)
    (hlarge : K/sLo < N^2/sHi) :
    0 < (slopePure S D N L k t).1 ∧
    N^2/sHi-K/sLo-2*T*(d+sHi*T+|N|) ≤
      inner ℝ (frameVector n m (slopeMixed S D N L k t u))
        (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
          frameVector n m (slopePure S D N L k t)) := by
  have hfirst := crossing_first_lower (N := N) (D := D) (L := L) (t := t) hmin hSmin hSmax hK hk
  have hpos : 0 < (slopePure S D N L k t).1 := by linarith
  refine ⟨hpos,?_⟩
  have hbound := crossing_slope_bound (N := N) (hmin.le.trans hSmin) hSmax hd ht hu
  exact (sub_le_sub hfirst hbound).trans
    (crossing_projection_lower hn hm hmn (hmin.trans_le hSmin).ne' hpos)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
