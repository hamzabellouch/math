import OAI.Geometry.RCD.Sobolev.EventualDiagonalLevel
import OAI.Geometry.RCD.Coordinates.NormalizedL2ProductError

namespace OAI

/-! # Shrinking endpoint balls while their normalized error cost vanishes -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem exists_vanishing_radius_cost (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k)
    (he0 : Tendsto e atTop (𝓝 0)) (n : ℕ) :
    ∃ δ : ℕ → ℝ, (∀ k, 0 < δ k ∧ δ k ≤ 1/2) ∧
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun k => e k/(δ k)^n) atTop (𝓝 0) := by
  let P (m k : ℕ) := e k*((m:ℝ)+2)^n ≤ ((m:ℝ)+2)⁻¹
  have hP (m : ℕ) : ∀ᶠ k in atTop, P m k := by
    have hh : Tendsto (fun k => e k*((m:ℝ)+2)^n) atTop (𝓝 0) := by
      simpa only [zero_mul] using he0.mul_const (((m:ℝ)+2)^n)
    exact (hh.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<((m:ℝ)+2)⁻¹))).mono
      (fun _ hk => hk.le)
  obtain ⟨d,hd,hbound⟩ := exists_eventual_diagonal_level P hP
  let δ (k : ℕ) := ((d k:ℝ)+2)⁻¹
  have hδ (k : ℕ) : 0 < δ k ∧ δ k ≤ 1/2 := by
    dsimp only [δ]
    constructor
    · positivity
    · rw [one_div]
      exact inv_anti₀ (by norm_num) (by have hh : (0:ℝ) ≤ d k := Nat.cast_nonneg _; linarith)
  have htop : Tendsto (fun k => (d k:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hd)
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htop
  refine ⟨δ,hδ,hδ0,?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg (he k) (pow_nonneg (hδ k).1.le n)))
    ?_ hδ0
  filter_upwards [hbound] with k hk
  change e k*((d k:ℝ)+2)^n ≤ ((d k:ℝ)+2)⁻¹ at hk
  simpa only [δ,inv_pow,div_inv_eq_mul] using hk

end RegularPointCoordinates

end

end OAI
