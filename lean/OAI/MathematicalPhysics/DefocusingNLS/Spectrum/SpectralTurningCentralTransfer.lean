import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarIntervalBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningWeightLimit

namespace OAI

/-! Uniform two-way transfer across the fixed central turning interval.
All Cauchy states are solutions of the actual rescaled Liouville equation. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_central_transfer
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G : ℝ) (hM : 0 < M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc (r₀ n-d n*M) (r₀ n+d n*M)) →
      (∀ t ∈ Icc (r₀ n-d n*M) (r₀ n+d n*M), HasDerivAt q
        (spectralScalarField ((homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (q t)) t) →
      let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n) t‖
      spectralShellNorm (k (r₀ n+d n*M)) (q (r₀ n+d n*M)) ≤
        C*spectralShellNorm (k (r₀ n-d n*M)) (q (r₀ n-d n*M)) ∧
      spectralShellNorm (k (r₀ n-d n*M)) (q (r₀ n-d n*M)) ≤
        C*spectralShellNorm (k (r₀ n+d n*M)) (q (r₀ n+d n*M)) := by
  let k₀ := Real.sqrt (Real.sqrt M)
  let low := k₀/2
  let up := 2*k₀
  let C := (up+low⁻¹)*max low⁻¹ up*Real.exp ((1+(M+1))*(M-(-M)))
  have hk₀ : 0 < k₀ := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hM)
  have hl : 0 < low := by dsimp only [low]; positivity
  have hup : 0 ≤ up := by dsimp only [up]; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  have hcoeff := spectralTurningCoefficient_uniform_limit h b eta omega gamma r₀ d M G hM.le hr₀ hdata
  have hplus := spectralTurning_weight_tendsto_at h b eta omega gamma r₀ d M G hr₀ hdata
  have hminus := spectralTurning_weight_tendsto_at h b eta omega gamma r₀ d (-M) G hr₀ hdata
  simp only [abs_neg,abs_of_pos hM] at hplus hminus
  have hkl : low < k₀ := by dsimp only [low]; linarith
  have hku : k₀ < up := by dsimp only [up]; linarith
  filter_upwards [hdata, (Metric.tendstoUniformlyOn_iff.mp hcoeff) 1 (by norm_num),
    hplus.eventually (lt_mem_nhds hkl),hplus.eventually (gt_mem_nhds hku),
    hminus.eventually (lt_mem_nhds hkl),hminus.eventually (gt_mem_nhds hku)]
    with n hn hc hpl hpu hml hmu
  intro q hq hqD
  let s := Real.sqrt (d n)
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hh := hn.2.2.2.2.2
    rw [← he] at hh
    norm_num at hh
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hs2 : s^2 = d n := Real.sq_sqrt hd.le
  let Q := spectralTurningState (r₀ n) (d n) s q
  let V := spectralTurningCoefficient h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n)
  let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n) t‖
  have hmem (t : ℝ) (ht : t ∈ Icc (-M) M) : r₀ n+d n*t ∈ Icc (r₀ n-d n*M) (r₀ n+d n*M) := by
    constructor <;> nlinarith [ht.1,ht.2]
  have hQc : ContinuousOn Q (Icc (-M) M) :=
    ((hq.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hmem).fst.div_const _).prodMk
      (continuousOn_const.mul (hq.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hmem).snd)
  have hQD (t : ℝ) (ht : t ∈ Icc (-M) M) : HasDerivAt Q (spectralScalarField (V t) (Q t)) t := by
    simpa only [Q,V,spectralTurningCoefficient,Complex.ofReal_pow] using
      spectralTurningState_hasDerivAt (r₀ n) (d n) s t hs.ne' hs2 q _ (hqD _ (hmem t ht))
  have hV (t : ℝ) (ht : t ∈ Icc (-M) M) : ‖V t‖ ≤ M+1 := by
    have he : ‖V t-(t : ℂ)‖ ≤ 1 := by
      simpa only [V,dist_eq_norm,norm_sub_rev] using (hc t ht).le
    have htM : |t| ≤ M := abs_le.mpr ht
    have htN : ‖(t : ℂ)‖ ≤ M := by simpa only [Complex.norm_real,Real.norm_eq_abs] using htM
    have hb := norm_add_le (V t-(t : ℂ)) (t : ℂ)
    rw [sub_add_cancel] at hb
    linarith
  have hkL : 0 < k (r₀ n-d n*M) := by
    change low < s*k (r₀ n+d n*(-M)) at hml
    have he : r₀ n+d n*(-M) = r₀ n-d n*M := by ring
    rw [he] at hml
    nlinarith
  have hkU : 0 < k (r₀ n+d n*M) := by
    change low < s*k (r₀ n+d n*M) at hpl
    nlinarith
  have hminus_eq : r₀ n+d n*(-M) = r₀ n-d n*M := by ring
  have hlt : low ≤ s*k (r₀ n-d n*M) := by simpa only [hminus_eq] using hml.le
  have hut : s*k (r₀ n-d n*M) ≤ up := by simpa only [hminus_eq] using hmu.le
  have ht := spectralScalar_interval_shell_bound (-M) M (M+1) low up
    (s*k (r₀ n-d n*M)) (s*k (r₀ n+d n*M)) (by linarith) (by positivity) hl
    hlt hut hpl.le hpu.le V Q hQc hQD hV
  have hQL : spectralShellNorm (s*k (r₀ n-d n*M)) (Q (-M)) =
      spectralShellNorm (k (r₀ n-d n*M)) (q (r₀ n-d n*M)) := by
    simpa only [hminus_eq,Q] using spectralTurningState_shell_norm (r₀ n) (d n) s (-M)
      (k (r₀ n+d n*(-M))) hs (by simpa only [hminus_eq] using hkL) q
  have hQU : spectralShellNorm (s*k (r₀ n+d n*M)) (Q M) =
      spectralShellNorm (k (r₀ n+d n*M)) (q (r₀ n+d n*M)) :=
    spectralTurningState_shell_norm (r₀ n) (d n) s M _ hs hkU q
  simpa only [hQL,hQU] using ht

end DefocusingNLS

end OAI
