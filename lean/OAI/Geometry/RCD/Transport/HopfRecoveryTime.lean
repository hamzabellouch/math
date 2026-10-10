import OAI.Geometry.RCD.Transport.PointedHopfErrorLimit

namespace OAI

/-! # A positive smoothing time slower than the metric approximation error -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def hopfRecoveryTime (ε : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (ε k)+1/((k:ℝ)+1)

theorem hopfRecoveryTime_pos (ε : ℕ → ℝ) (k : ℕ) : 0<hopfRecoveryTime ε k := by
  unfold hopfRecoveryTime
  positivity

theorem hopfRecoveryTime_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (hopfRecoveryTime ε) atTop (𝓝 0) := by
  change Tendsto (fun k => Real.sqrt (ε k)+1/((k:ℝ)+1)) atTop (𝓝 0)
  simpa only [Real.sqrt_zero,zero_add] using
    hε.sqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))

theorem error_div_hopfRecoveryTime_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ k, 0≤ε k) :
    Tendsto (fun k => ε k/hopfRecoveryTime ε k) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => div_nonneg (hε0 k) (hopfRecoveryTime_pos ε k).le)
    (fun k => ?_) (by simpa only [Real.sqrt_zero] using hε.sqrt)
  apply (div_le_iff₀ (hopfRecoveryTime_pos ε k)).mpr
  have hs := Real.sq_sqrt (hε0 k)
  have hp : 0≤1/((k:ℝ)+1) := by positivity
  dsimp only [hopfRecoveryTime]
  nlinarith [Real.sqrt_nonneg (ε k)]

theorem pointedHopfSlopeError_eq {t M ε e : ℝ} (ht : 0<t) :
    (Real.sqrt (2*t*pointedHopfError t M ε e)+ε)/t =
      Real.sqrt (4*(e/t)+14*M*(ε/t)+5*(ε/t)^2)+ε/t := by
  have heq : 4*(e/t)+14*M*(ε/t)+5*(ε/t)^2 =
      (2*t*pointedHopfError t M ε e)/t^2 := by
    unfold pointedHopfError
    field_simp
    ring
  rw [heq,Real.sqrt_div' _ (sq_nonneg t),Real.sqrt_sq ht.le,add_div]

theorem pointedHopfSlopeError_diagonal_tendsto {t ε e : ℕ → ℝ} {M : ℝ}
    (ht : ∀ k, 0<t k)
    (hε : Tendsto (fun k => ε k/t k) atTop (𝓝 0))
    (he : Tendsto (fun k => e k/t k) atTop (𝓝 0)) :
    Tendsto (fun k => (Real.sqrt (2*t k*pointedHopfError (t k) M (ε k) (e k))+ε k)/t k)
      atTop (𝓝 0) := by
  have h := (((he.const_mul 4).add (hε.const_mul (14*M))).add
    ((hε.pow 2).const_mul 5)).sqrt.add hε
  simp only [mul_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add,Real.sqrt_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun k => (pointedHopfSlopeError_eq (ht k)).symm

end RegularPointCoordinates

end

end OAI
