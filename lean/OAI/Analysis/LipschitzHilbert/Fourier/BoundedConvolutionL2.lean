import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionContinuity

namespace OAI

/-! Transfer of a Schwartz L2 convolution bound to bounded measurable
L2 inputs, using density and the actual convolution difference. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation
local instance instTwoAtLeastOne : Fact (1≤(2:ℝ≥0∞)) := ⟨by norm_num⟩

theorem toL2_norm_le_of_integral (f g : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (C : ℝ) (hC : 0≤C)
    (h : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    ‖hg.toLp g‖≤C*‖hf.toLp f‖ := by
  rw [←memLp_toL2_norm_sq volume g hg,←memLp_toL2_norm_sq volume f hf] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg (hg.toLp g)) (mul_nonneg hC (norm_nonneg (hf.toLp f)))
    (by decide : (2:ℕ)≠0)).mp (by simpa only [mul_pow] using h)

theorem lineConvolution_L2_norm_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 2 volume) :
    ‖(lineConvolution_energy_bound K hK hKm f hfm hf).1.toLp (lineConvolution K f)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f‖ :=
  toL2_norm_le_of_integral f _ hf _ _ (integral_nonneg fun _ => norm_nonneg _)
    (lineConvolution_energy_bound K hK hKm f hfm hf).2

theorem boundedConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have hn := toL2_norm_le_of_integral (f-g) (lineConvolution K f-lineConvolution K g)
    (hf.sub hg) (hcf.sub hcg) _ (integral_nonneg fun _ => norm_nonneg _) he
  rwa [hf.toLp_sub hg,hcf.toLp_sub hcg] at hn

theorem boundedConvolution_L2_of_schwartz (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (C : ℝ) (hC : 0≤C)
    (hsch : ∀ g : SchwartzMap ℝ ℂ,
      (∫ x, ‖lineConvolution K g x‖^2)≤C^2*(∫ x, ‖g x‖^2))
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    (∫ x, ‖lineConvolution K f x‖^2)≤C^2*(∫ x, ‖f x‖^2) := by
  let L := ∫ t, ‖K t‖
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  let hcf := (lineConvolution_energy_bound K hK hKm f hfm hf).1
  let xf := hf.toLp f
  let yf := hcf.toLp (lineConvolution K f)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  have hnorm : ‖yf‖≤C*‖xf‖ := by
    by_contra hn
    have hgap : 0<‖yf‖-C*‖xf‖ := by linarith
    let eps := (‖yf‖-C*‖xf‖)/(2*(C+L+1))
    have heps : 0<eps := div_pos hgap (by positivity)
    obtain ⟨g,hg⟩ := hd.exists_dist_lt xf heps
    let hcg := (lineConvolution_energy_bound K hK hKm g g.continuous.measurable (g.memLp 2 volume)).1
    let yg := hcg.toLp (lineConvolution K g)
    have hgBound : ‖yg‖≤C*‖g.toLp 2 volume‖ :=
      toL2_norm_le_of_integral g _ (g.memLp 2 volume) hcg C hC (hsch g)
    have hdiff : ‖yf-yg‖≤L*‖xf-g.toLp 2 volume‖ :=
      boundedConvolution_L2_difference K f g hK hKm hfm g.continuous.measurable
        hf (g.memLp 2 volume) hcf hcg B (SchwartzMap.seminorm ℝ 0 0 g)
        hfb (fun x => SchwartzMap.norm_le_seminorm ℝ g x)
    have htri : ‖yf‖≤‖yf-yg‖+‖yg‖ := by
      simpa only [sub_add_cancel] using norm_add_le (yf-yg) yg
    have hgin : ‖g.toLp 2 volume‖≤‖xf‖+‖xf-g.toLp 2 volume‖ := by
      have hh := norm_add_le (g.toLp 2 volume-xf) xf
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    have htot : ‖yf‖≤C*‖xf‖+(C+L)*‖xf-g.toLp 2 volume‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hgin hC]
    have hdist : ‖xf-g.toLp 2 volume‖<eps := by simpa only [dist_eq_norm] using hg
    have hsmall : (C+L)*‖xf-g.toLp 2 volume‖<(C+L+1)*eps := by
      calc
        _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hdist.le (add_nonneg hC hL)
        _ < _ := by nlinarith
    have heq : (C+L+1)*eps=(‖yf‖-C*‖xf‖)/2 := by
      dsimp [eps]
      field_simp [show C+L+1≠0 by positivity]
    rw [heq] at hsmall
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow,memLp_toL2_norm_sq volume f hf,memLp_toL2_norm_sq volume _ hcf] at hp
  exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
