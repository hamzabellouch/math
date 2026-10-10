import OAI.Probability.InvariantIsing.Haar.HaarPolynomialEntropyBound

namespace OAI

/-! The one-variable entropy-to-exponential-moment argument. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

theorem log_moment_le_of_entropy (M M' : ℝ → ℝ) (A : ℝ)
    (hM : ∀ t, 0 < M t) (h0 : M 0 = 1) (hD : ∀ t, HasDerivAt M (M' t) t)
    (hE : ∀ t, 0 < t → t*M' t-M t*Real.log (M t) ≤ A*t^2*M t)
    {t : ℝ} (ht : 0 < t) : Real.log (M t) ≤ M' 0*t+A*t^2 := by
  let K (s : ℝ) := Real.log (M s)/s-A*s
  let K' (s : ℝ) := (M' s/M s*s-Real.log (M s))/s^2-A
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt K (K' s) s := by
    convert (((hD s).log (hM s).ne').div (hasDerivAt_id s) hs.ne').sub
      ((hasDerivAt_id s).const_mul A) using 1
    all_goals first | rfl | simp only [K',id_eq,mul_one]
  have hn (s : ℝ) (hs : 0 < s) : K' s ≤ 0 := by
    have heq : M' s/M s*s-Real.log (M s) =
        (s*M' s-M s*Real.log (M s))/M s := by
      field_simp [(hM s).ne']
    have hb : (M' s/M s*s-Real.log (M s))/s^2 ≤ A := by
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      rw [heq]
      apply (div_le_iff₀ (hM s)).mpr
      exact hE s hs
    exact sub_nonpos.mpr hb
  have hanti : AntitoneOn K (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ioi,mem_Ioi] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ioi,mem_Ioi] using hs
      rw [(hd s hs').deriv]
      exact hn s hs'
  have hlog := ((hD 0).log (hM 0).ne').tendsto_slope_zero_right
  have hl : Tendsto (fun s : ℝ => Real.log (M s)/s) (𝓝[>] (0:ℝ)) (𝓝 (M' 0)) := by
    simpa only [zero_add,h0,Real.log_one,sub_zero,div_one,smul_eq_mul,div_eq_mul_inv,mul_comm,
      inv_one,mul_one] using hlog
  have hK : Tendsto K (𝓝[>] (0:ℝ)) (𝓝 (M' 0)) := by
    have hz : Tendsto (fun s : ℝ => A*s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using hid.const_mul A
    simpa only [sub_zero] using hl.sub hz
  have hb : K t ≤ M' 0 := ge_of_tendsto hK (by
    have hu : ∀ᶠ s : ℝ in 𝓝[>] (0:ℝ), s < t :=
      (show ∀ᶠ s : ℝ in 𝓝 (0:ℝ), s < t from Iio_mem_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hu] with s hs hst
    exact hanti hs ht hst.le)
  have hh : Real.log (M t)/t ≤ M' 0+A*t := by
    change Real.log (M t)/t-A*t ≤ M' 0 at hb
    linarith
  have hf := (div_le_iff₀ ht).mp hh
  nlinarith

end InvariantIsing

end

end OAI
