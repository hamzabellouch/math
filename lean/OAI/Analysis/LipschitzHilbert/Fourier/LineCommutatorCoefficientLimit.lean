import OAI.Analysis.LipschitzHilbert.Fourier.LineDyadicTelescoping
import OAI.Analysis.LipschitzHilbert.Fourier.LineBoundedCommutatorL2

namespace OAI

/-! Uniform Lipschitz approximation of the coefficient identifies the
limit of the actual smoothed commutators in L2. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem scale_neg_nat_tendsto :
    Tendsto (fun N : ℕ => scale (-(N:ℤ))) atTop (𝓝 (0:ℝ)) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  simpa only [scale,zpow_neg,zpow_natCast,one_div,inv_pow] using hh

theorem lineCommutator_lowpass_tendsto (m b f : SchwartzMap ℝ ℂ) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    Tendsto (fun N : ℕ => (lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f).toLp 2 volume)
      atTop (𝓝 ((lineSchwartzCommutator m b f).toLp 2 volume)) := by
  let A := SchwartzMap.seminorm ℝ 0 0 m
  let M := ∫ t, |t| *‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖
  let delta := fun N : ℕ => L*scale (-(N:ℤ))*M
  let F := fun N : ℕ => lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f
  let G := lineSchwartzCommutator m b f
  have hd : Tendsto delta atTop (𝓝 0) := by
    have hh := (scale_neg_nat_tendsto.const_mul L).mul_const M
    simpa only [mul_zero,zero_mul] using hh
  have hb (N : ℕ) (x : ℝ) : ‖(lineLowpass b (-(N:ℤ))-b) x‖≤delta N := by
    simp only [lineLowpass,sub_apply,lineSchwartzProjection_eq_convolution]
    exact lowpassProjection_lipschitz_approximation (scale (-(N:ℤ))) (scale_pos _)
      b b.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 b) (fun y => b.norm_le_seminorm ℝ y) L hLip x
  have hn (N : ℕ) : ‖(F N).toLp 2 volume-G.toLp 2 volume‖^2≤
      4*A^2*(delta N)^2*(∫ x, ‖f x‖^2) := by
    have hc := lineSchwartzCommutator_bounded_energy m (lineLowpass b (-(N:ℤ))-b) f A (delta N)
      (fun eta => m.norm_le_seminorm ℝ eta) (hb N)
    have he : (F N).toLp 2 volume-G.toLp 2 volume=
        (lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))-b) f).toLp 2 volume := by
      rw [lineSchwartzCommutator_sub_left]
      exact (map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (F N) G).symm
    rw [he]
    have hs := memLp_toL2_norm_sq volume _
      ((lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))-b) f).memLp 2 volume)
    exact hs.trans_le hc
  have hupper : Tendsto (fun N : ℕ => 4*A^2*(delta N)^2*(∫ x, ‖f x‖^2)) atTop (𝓝 0) := by
    have hh := ((hd.pow 2).const_mul (4*A^2)).mul_const (∫ x, ‖f x‖^2)
    simpa only [zero_pow (by decide : 2≠0),mul_zero,zero_mul] using hh
  have hsquare := squeeze_zero (fun N => sq_nonneg ‖(F N).toLp 2 volume-G.toLp 2 volume‖) hn hupper
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,Function.comp_def] at hnorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end LipschitzHilbert.PacketRepresentation

end

end OAI
