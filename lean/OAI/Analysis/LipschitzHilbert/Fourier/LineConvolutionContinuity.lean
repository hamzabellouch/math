import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionKernel

namespace OAI

/-! Actual convolution on bounded L2 functions agrees with the continuous
extension of the corresponding Schwartz Fourier multiplier. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have ho := memLp_toL2_norm_sq volume _ (hcf.sub hcg)
  have hi := memLp_toL2_norm_sq volume _ (hf.sub hg)
  rw [hcf.toLp_sub hcg] at ho
  rw [hf.toLp_sub hg] at hi
  rw [←ho,←hi] at he
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))).1
    (by simpa only [mul_pow] using he)

theorem lineL2Projection_on_bounded (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) :
    lineL2Projection q W hW (hf.toLp f)=
      (lineConvolution_energy_bound (lineProjectionKernel q W hW)
        (lineProjectionKernel q W hW).integrable (lineProjectionKernel q W hW).continuous.measurable
        f hfm hf).1.toLp (lineConvolution (lineProjectionKernel q W hW) f) := by
  let K := lineProjectionKernel q W hW
  let C := SchwartzMap.seminorm ℝ 0 0 q
  let L := ∫ t, ‖K t‖
  let T := lineL2Projection q W hW
  let y := (lineConvolution_energy_bound K K.integrable K.continuous.measurable f hfm hf).1.toLp
    (lineConvolution K f)
  change T (hf.toLp f)=y
  have hC : 0≤C := apply_nonneg _ _
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  have hT : ‖T‖≤C := lineL2Projection_bound q W hW C hC (fun x => SchwartzMap.norm_le_seminorm ℝ q x)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hdpos : 0<‖T (hf.toLp f)-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let eps := ‖T (hf.toLp f)-y‖/(2*(C+L+1))
  have heps : 0<eps := div_pos hdpos (by positivity)
  obtain ⟨g,hg⟩ := hd.exists_dist_lt (hf.toLp f) heps
  let yg := (lineConvolution_energy_bound K K.integrable K.continuous.measurable
    g g.continuous.measurable (g.memLp 2 volume)).1.toLp (lineConvolution K g)
  have hTg : T (g.toLp 2 volume)=yg := by
    change lineL2Projection q W hW (g.toLp 2 volume)=_
    rw [lineL2Projection_onSchwartz]
    apply Lp.ext
    filter_upwards [(lineSchwartzProjection q W hW g).coeFn_toLp 2 volume,
      (lineConvolution_energy_bound K K.integrable K.continuous.measurable
        g g.continuous.measurable (g.memLp 2 volume)).1.coeFn_toLp] with x hx hy
    dsimp only [yg]
    rw [hx,hy]
    exact lineSchwartzProjection_eq_convolution q W hW g x
  have hc : ‖yg-y‖≤L*‖g.toLp 2 volume-hf.toLp f‖ :=
    lineConvolution_L2_difference K g f K.integrable K.continuous.measurable
      g.continuous.measurable hfm (g.memLp 2 volume) hf _ _
      (SchwartzMap.seminorm ℝ 0 0 g) B (fun x => SchwartzMap.norm_le_seminorm ℝ g x) hB
  have ht : ‖T (hf.toLp f)-T (g.toLp 2 volume)‖≤C*‖hf.toLp f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have htri := norm_add_le (T (hf.toLp f)-T (g.toLp 2 volume)) (T (g.toLp 2 volume)-y)
  rw [sub_add_sub_cancel,hTg] at htri
  rw [norm_sub_rev (g.toLp 2 volume) (hf.toLp f)] at hc
  simp only [dist_eq_norm] at hg
  have hmul : (C+L+1)*eps=‖T (hf.toLp f)-y‖/2 := by
    unfold eps
    field_simp [show C+L+1≠0 by positivity]
  rw [hTg] at ht
  have hs : ‖T (hf.toLp f)-y‖≤(C+L)*‖hf.toLp f-g.toLp 2 volume‖ := by
    nlinarith only [htri,ht,hc]
  have hsmall : (C+L)*‖hf.toLp f-g.toLp 2 volume‖<(C+L+1)*eps := by
    calc
      _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hg.le (add_nonneg hC hL)
      _ < _ := by nlinarith only [heps]
  rw [hmul] at hsmall
  linarith only [hs,hsmall,hdpos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
