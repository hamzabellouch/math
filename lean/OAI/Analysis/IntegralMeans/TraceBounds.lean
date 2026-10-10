import OAI.Analysis.IntegralMeans.NegativeArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma rectangle_trace_periodic {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R,ε) (R,Y), ContDiffAt ℝ 2 g p)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R,y) (1,0) = fderiv ℝ g (R,y) (1,0)) :
    (∫ p in Icc (-R,ε) (R,Y), (p.2-ε)*pairLaplacian g p) =
      (∫ x in -R..R, traceFluxY g ε (x,Y)) + ∫ x in -R..R, g (x,ε) := by
  have hf : ContinuousOn (traceFluxX g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).1.continuousAt).continuousWithinAt
  have hh : ContinuousOn (traceFluxY g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).2.continuousAt).continuousWithinAt
  have hint : IntegrableOn (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p)
      (Icc (-R,ε) (R,Y)) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (continuousAt_pairLaplacian (hg p hp))
    exact hc.continuousWithinAt
  have heq (p : ℝ × ℝ) (hp : p ∈ Icc (-R,ε) (R,Y)) := divergence_traceFlux (hg p hp) ε
  have hi : IntegrableOn (fun p => fderiv ℝ (traceFluxX g ε) p (1,0)+
      fderiv ℝ (traceFluxY g ε) p (0,1)) (Icc (-R,ε) (R,Y)) volume :=
    hint.congr (ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => (heq p hp).symm))
  have hb := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (traceFluxX g ε) (traceFluxY g ε) (fderiv ℝ (traceFluxX g ε))
    (fderiv ℝ (traceFluxY g ε)) (-R,ε) (R,Y) ⟨by linarith,hεY⟩ hf hh
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).1.differentiableAt (by norm_num)).hasFDerivAt)
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).2.differentiableAt (by norm_num)).hasFDerivAt) hi
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hb
  have hsideint : (∫ y in ε..Y, traceFluxX g ε (R,y)) =
      ∫ y in ε..Y, traceFluxX g ε (-R,y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [traceFluxX]
    rw [hside y (by simpa only [uIcc_of_le hεY] using hy)]
  change _ = ((∫ x in -R..R, traceFluxY g ε (x,Y)) - ∫ x in -R..R, traceFluxY g ε (x,ε)) +
    (∫ y in ε..Y, traceFluxX g ε (R,y)) - ∫ y in ε..Y, traceFluxX g ε (-R,y) at hb
  rw [hsideint] at hb
  simpa only [traceFluxY,sub_self,zero_mul,zero_sub,
    intervalIntegral.integral_neg,sub_neg_eq_add, zero_add,add_zero,sub_zero,add_sub_cancel_right] using hb

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma rectangle_restrict_open (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Icc (a,c) (b,d)) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) := by
  rw [Icc_prod_eq]
  change (volume.prod volume).restrict (Icc a b ×ˢ Icc c d) =
    (volume.prod volume).restrict (Ioo a b ×ˢ Ioo c d)
  rw [← Measure.prod_restrict,← Measure.prod_restrict,
    restrict_Ioo_eq_restrict_Icc,restrict_Ioo_eq_restrict_Icc]

lemma rectangle_conformal_lintegral_le {F : ℂ → ℂ} {R ε Y : ℝ} (hε : 0 < ε)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    (hi : InjOn F {z : ℂ | -R < z.re ∧ z.re < R ∧ 0 < z.im}) (b : ℂ → ℝ≥0∞) :
    (∫⁻ p in Icc (-R,ε) (R,Y),
      ENNReal.ofReal (‖deriv F (Complex.equivRealProdCLM.symm p)‖^2)*
        b (F (Complex.equivRealProdCLM.symm p))) ≤ ∫⁻ w, b w := by
  rw [rectangle_restrict_open]
  let s : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo ε Y
  let E := Complex.equivRealProdCLM
  have hs : MeasurableSet (E ⁻¹' s) :=
    (measurableSet_Ioo.prod measurableSet_Ioo).preimage E.continuous.measurable
  have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) s
  have hh : (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) =
      ∫⁻ z in E ⁻¹' s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
    rw [← he]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (‖deriv F (E.symm (E z))‖^2)*b (F (E.symm (E z))) = _
    rw [E.symm_apply_apply]
  change (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) ≤ _
  rw [hh]
  apply conformal_lintegral_le hs
  · intro z hz
    exact hF z (hε.trans hz.2.1)
  · apply hi.mono
    intro z hz
    exact ⟨hz.1.1,hz.1.2,hε.trans hz.2.1⟩

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma periodic_conformal_trace_bounded {F : ℂ → ℂ} {ψ b : ℂ → ℝ} {K : ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi ∧ 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hb : Integrable b) (hbn : ∀ w, 0 ≤ b w) (hK : 0 ≤ K)
    (hside : ∀ y : ℝ, 0 < y →
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (-Real.pi,y) (1,0) =
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (Real.pi,y) (1,0))
    (hlap : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 ≤ Laplacian.laplacian (ψ ∘ F) z ∧
      z.im * Laplacian.laplacian (ψ ∘ F) z ≤ K*‖deriv F z‖^2*b (F z)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ x in -Real.pi..Real.pi, ψ (F (x+ε*Complex.I))) ≤ C := by
  let E := Complex.equivRealProdCLM.symm
  let g := (ψ ∘ F) ∘ E
  have hg (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p :=
    (hψ.contDiffAt.comp _ ((hF (E p) hp).contDiffAt.restrict_scalars ℝ)).comp _ E.contDiff.contDiffAt
  have hc (x : ℝ) : ContinuousAt (fun x : ℝ => g (x,1)) x := by
    exact (hg (x,1) zero_lt_one).continuousAt.comp (f := fun v : ℝ => (v,(1:ℝ))) (show ContinuousAt (fun v : ℝ => (v,(1:ℝ))) x from (continuous_id.prodMk continuous_const).continuousAt)
  have hd (x : ℝ) : ContinuousAt (fun x : ℝ => fderiv ℝ g (x,1) (0,1)) x := by
    have hh := ((hg (x,1) zero_lt_one).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hl : ContinuousAt (fun x : ℝ => fderiv ℝ g (x,1)) x :=
      hh.comp (f := fun v : ℝ => (v,(1:ℝ))) (show ContinuousAt (fun v : ℝ => (v,(1:ℝ))) x from (continuous_id.prodMk continuous_const).continuousAt)
    exact hl.clm_apply continuousAt_const
  let A : ℝ := ∫ x in -Real.pi..Real.pi, |g (x,1)|+|fderiv ℝ g (x,1) (0,1)|
  have hAint : IntervalIntegrable (fun x : ℝ => |g (x,1)|+|fderiv ℝ g (x,1) (0,1)|)
      volume (-Real.pi) Real.pi :=
    ((continuous_iff_continuousAt.mpr hc).abs.add (continuous_iff_continuousAt.mpr hd).abs).intervalIntegrable _ _
  have hIb : 0 ≤ ∫ w, b w := integral_nonneg hbn
  refine ⟨K*(∫ w, b w)+A,fun ε hε hε1 => ?_⟩
  let S := Icc (-Real.pi,ε) (Real.pi,(1:ℝ))
  let U : ℝ × ℝ → ℝ := fun p => (p.2-ε)*pairLaplacian g p
  have hbox (p : ℝ × ℝ) (hp : p ∈ S) : ContDiffAt ℝ 2 g p := hg p (hε.trans_le hp.1.2)
  have hUi : IntegrableOn U S := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    apply ContinuousAt.continuousWithinAt
    exact (continuous_snd.continuousAt.sub_const ε).mul
      (continuousAt_pairLaplacian (hbox p hp))
  have hUn (p : ℝ × ℝ) (hp : p ∈ S) : 0 ≤ U p := by
    dsimp [U,g,E]
    rw [pairLaplacian_complex]
    exact mul_nonneg (by linarith [hp.1.2]) (hlap _ (hε.trans_le hp.1.2) hp.2.2).1
  have hUp (p : ℝ × ℝ) (hp : p ∈ S) :
      U p ≤ K*‖deriv F (E p)‖^2*b (F (E p)) := by
    have hx := hlap (E p) (hε.trans_le hp.1.2) hp.2.2
    dsimp only [U,g]
    rw [pairLaplacian_complex]
    calc
      _ ≤ p.2*Laplacian.laplacian (ψ ∘ F) (E p) := mul_le_mul_of_nonneg_right (by linarith) hx.1
      _ ≤ _ := hx.2
  have hIle : (∫ p in S, U p) ≤ K*(∫ w, b w) := by
    have he := ofReal_integral_eq_lintegral_ofReal hUi
      (ae_restrict_of_forall_mem measurableSet_Icc hUn)
    have hb' := ofReal_integral_eq_lintegral_ofReal hb (Eventually.of_forall hbn)
    have hL : (∫⁻ p in S, ENNReal.ofReal (U p)) ≤ ENNReal.ofReal (K*(∫ w, b w)) := by
      calc
        _ ≤ ∫⁻ p in S, ENNReal.ofReal K *
            (ENNReal.ofReal (‖deriv F (E p)‖^2)*ENNReal.ofReal (b (F (E p)))) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro p hp
          rw [← ENNReal.ofReal_mul (sq_nonneg _),← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          simpa only [mul_assoc] using hUp p hp
        _ = ENNReal.ofReal K * ∫⁻ p in S,
            ENNReal.ofReal (‖deriv F (E p)‖^2)*ENNReal.ofReal (b (F (E p))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal K * ∫⁻ w, ENNReal.ofReal (b w) :=
          mul_le_mul le_rfl (rectangle_conformal_lintegral_le hε
            (fun z hz => (hF z hz).differentiableAt) hi
            (fun w => ENNReal.ofReal (b w))) zero_le zero_le
        _ = ENNReal.ofReal (K*(∫ w, b w)) := by rw [← hb',ENNReal.ofReal_mul hK]
    rw [← he] at hL
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hIb)).mp hL
  have ht := rectangle_trace_periodic Real.pi_pos.le hε1 hbox
    (fun y hy => hside y (hε.trans_le hy.1))
  have htop : -(∫ x in -Real.pi..Real.pi, traceFluxY g ε (x,1)) ≤ A := by
    rw [← intervalIntegral.integral_neg]
    have htopc : Continuous (fun x : ℝ => -traceFluxY g ε (x,1)) := by
      simp only [traceFluxY]
      exact ((continuous_const.mul (continuous_iff_continuousAt.mpr hd)).sub
        (continuous_iff_continuousAt.mpr hc)).neg
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (htopc.intervalIntegrable _ _) hAint
    intro x _hx
    dsimp [traceFluxY]
    have hgabs := le_abs_self (g (x,1))
    have hdabs := neg_le_abs (fderiv ℝ g (x,1) (0,1))
    have hmul : -(1-ε)*fderiv ℝ g (x,1) (0,1) ≤ |fderiv ℝ g (x,1) (0,1)| := by
      calc
        _ = (1-ε)*(-fderiv ℝ g (x,1) (0,1)) := by ring
        _ ≤ (1-ε)*|fderiv ℝ g (x,1) (0,1)| := mul_le_mul_of_nonneg_left hdabs (by linarith)
        _ ≤ |fderiv ℝ g (x,1) (0,1)| := mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    linarith
  have hid : (∫ x in -Real.pi..Real.pi, ψ (F (x+ε*Complex.I))) =
      ∫ x in -Real.pi..Real.pi, g (x,ε) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [g,E,Function.comp_apply,Complex.equivRealProdCLM_symm_apply]
  rw [hid]
  change (∫ p in S, U p) = _ at ht
  linarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma radial_growth_upper {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖f ((r:ℂ)*ζ)‖ ≤ r/(1-r)^2 := by
  let B : ℝ → ℝ := fun t => (1+t)/(1-t)^3
  let G : ℝ → ℝ := fun t => t/(1-t)^2
  have hn (t : ℝ) (ht : t ∈ Icc 0 r) : ‖(t:ℂ)*ζ‖ = t := by
    simp [hζ,abs_of_nonneg ht.1]
  have hm (t : ℝ) (ht : t ∈ Icc 0 r) : (t:ℂ)*ζ ∈ disk := by
    simp only [disk,Metric.mem_ball,dist_zero_right,hn t ht]
    exact ht.2.trans_lt hr1
  have hd (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun t : ℝ => f ((t:ℂ)*ζ)) (deriv f ((t:ℂ)*ζ)*ζ) t := by
    have hdf := ((hf.1.1 _ (hm t ht)).differentiableAt (Metric.isOpen_ball.mem_nhds (hm t ht))).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ => (t:ℂ)*ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t : ℝ => Complex.ofRealCLM t*ζ) ((Complex.ofRealCLM (1:ℝ))*ζ) t)
    convert HasDerivAt.comp (𝕜 := ℝ) t hdf hl using 1
    rfl
  have hB : ContinuousOn B (Icc 0 r) := by
    unfold B
    exact (continuous_const.add continuous_id).continuousOn.div ((continuous_const.sub continuous_id).pow 3).continuousOn
      (fun t ht => pow_ne_zero 3 (by linarith [ht.2]))
  have hG (t : ℝ) (ht : t ∈ Icc 0 r) : HasDerivAt G (B t) t := by
    have hnz : 1-t ≠ 0 := by linarith [ht.2]
    have hd := (hasDerivAt_id t).div (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2) (pow_ne_zero 2 hnz)
    convert hd using 1 <;> try rfl
    dsimp [G,B]
    field_simp [hnz]
    ring
  have hb := norm_sub_le_integral_of_norm_deriv_le_of_le hr
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1.le,ht.2.le⟩).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall (fun t ht => show ‖deriv (fun t : ℝ => f ((t:ℂ)*ζ)) t‖ ≤ B t from by
      rw [(hd t ⟨ht.1.le,ht.2.le⟩).deriv,norm_mul,hζ,mul_one]
      simpa only [B,hn t ⟨ht.1.le,ht.2.le⟩] using (schlicht_deriv_bounds hf (hm t ⟨ht.1.le,ht.2.le⟩)).2))
    (hB.intervalIntegrable_of_Icc hr)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hG t (by simpa [uIcc_of_le hr] using ht))
    (hB.intervalIntegrable_of_Icc hr)
  rw [hi] at hb
  simpa [G,hf.2.1] using hb

lemma schlicht_growth_upper {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    ‖f z‖ ≤ ‖z‖/(1-‖z‖)^2 := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.1]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z/(‖z‖:ℂ)‖ = 1 := by
    simp [div_self hn.ne']
  have he : (‖z‖:ℂ)*(z/(‖z‖:ℂ)) = z := by
    field_simp [show (‖z‖:ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hn.ne']
  simpa [he] using radial_growth_upper hf hn.le (by simpa [disk] using hz) hζ

end Brennan

end

end OAI
