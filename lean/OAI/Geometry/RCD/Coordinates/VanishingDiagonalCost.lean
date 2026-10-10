import OAI.Geometry.RCD.Coordinates.VanishingRadiusCost

namespace OAI

/-! # A slowly varying level retaining vanishing nonnegative costs -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem exists_vanishing_diagonal_cost (e : ℕ → ℕ → ℝ)
    (he : ∀ m k, 0 ≤ e m k)
    (hlim : ∀ m, Tendsto (e m) atTop (𝓝 0)) :
    ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧
      Tendsto (fun k => e (d k) k) atTop (𝓝 0) := by
  let P (m k : ℕ) := e m k ≤ ((m:ℝ)+2)⁻¹
  have hP (m : ℕ) : ∀ᶠ k in atTop, P m k :=
    ((hlim m).eventually (Iio_mem_nhds (by positivity : (0:ℝ)<((m:ℝ)+2)⁻¹))).mono
      (fun _ hk => hk.le)
  obtain ⟨d,hd,hbound⟩ := exists_eventual_diagonal_level P hP
  refine ⟨d,hd,?_⟩
  have htop : Tendsto (fun k => (d k:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hd)
  exact squeeze_zero' (Eventually.of_forall (fun k => he (d k) k)) hbound
    (tendsto_inv_atTop_zero.comp htop)

end RegularPointCoordinates

end

end OAI
