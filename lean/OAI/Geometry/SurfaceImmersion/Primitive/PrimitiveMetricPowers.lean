import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSlowErrorProfiles

namespace OAI

/-! The fast remainder stays arbitrarily small at a prescribed unweighted
order when the slow exponent is chosen after its fixed loss. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma primitive_tail_power_bound {z b : ℝ} {N R loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b) (hbl : b < 1/(1+(loss : ℝ))) :
    z^(N+R+1)/(z^b)^loss/z^R ≤ z^N := by
  have hl : 0 ≤ (loss : ℝ) := Nat.cast_nonneg _
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have he : (N : ℝ) ≤ (N+R+1 : ℕ)-b*(loss : ℝ)-(R : ℝ) := by
    push_cast
    nlinarith
  have hid : z^(N+R+1)/(z^b)^loss/z^R =
      z^((N+R+1 : ℕ)-b*(loss : ℝ)-(R : ℝ)) := by
    rw [← Real.rpow_natCast z (N+R+1),← Real.rpow_mul_natCast hz.le,
      ← Real.rpow_natCast z R,← Real.rpow_sub hz,← Real.rpow_sub hz]
  rw [hid]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hz hz1 he

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
