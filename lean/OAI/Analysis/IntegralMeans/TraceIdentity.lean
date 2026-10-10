import OAI.Analysis.IntegralMeans.BoundaryTail

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def pairLaplacian (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ g) p (1,0) (1,0) + fderiv ℝ (fderiv ℝ g) p (0,1) (0,1)

def traceFluxX (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2-ε)*fderiv ℝ g p (1,0)

def traceFluxY (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2-ε)*fderiv ℝ g p (0,1)-g p

lemma traceFlux_contDiffAt {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    ContDiffAt ℝ 1 (traceFluxX g ε) p ∧ ContDiffAt ℝ 1 (traceFluxY g ε) p := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ g) p := hg.fderiv_right (by norm_num)
  have htr : ContDiffAt ℝ 1 g p := hg.of_le (by norm_num)
  constructor
  · unfold traceFluxX; fun_prop
  · unfold traceFluxY; fun_prop

lemma divergence_traceFlux {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    fderiv ℝ (traceFluxX g ε) p (1,0)+fderiv ℝ (traceFluxY g ε) p (0,1) =
      (p.2-ε)*pairLaplacian g p := by
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) p)
  have hy := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) p)
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2-ε) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub_const ε
  unfold traceFluxX traceFluxY
  have hfx := (hs.mul hx).fderiv
  have hfy := ((hs.mul hy).sub hdg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (1,0)) p = _ at hfx
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (0,1)-g p) p = _ at hfy
  rw [hfx,hfy]
  simp [pairLaplacian,ContinuousLinearMap.flip_apply,mul_add]

lemma continuousAt_pairLaplacian {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) : ContinuousAt (pairLaplacian g) p := by
  have hh : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ g)) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuousAt
  unfold pairLaplacian
  fun_prop

lemma rectangle_trace_identity {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R,ε) (R,Y), ContDiffAt ℝ 2 g p)
    (htop : ∀ x ∈ Icc (-R) R, g (x,Y) = 0 ∧ fderiv ℝ g (x,Y) (0,1) = 0)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0) :
    (∫ p in Icc (-R,ε) (R,Y), (p.2-ε)*pairLaplacian g p) =
      ∫ x in -R..R, g (x,ε) := by
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
  have ht : (∫ x in -R..R, traceFluxY g ε (x,Y)) = 0 := by
    calc
      _ = ∫ _ in -R..R, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-R) R := by simpa only [uIcc_of_le (by linarith : -R ≤ R)] using hx
    simp [traceFluxY,(htop x hx').1,(htop x hx').2]
  have hl : (∫ y in ε..Y, traceFluxX g ε (-R,y)) = 0 := by
    calc
      _ = ∫ _ in ε..Y, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [traceFluxX,(hside y (by simpa only [uIcc_of_le hεY] using hy)).1]
  have hr : (∫ y in ε..Y, traceFluxX g ε (R,y)) = 0 := by
    calc
      _ = ∫ _ in ε..Y, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [traceFluxX,(hside y (by simpa only [uIcc_of_le hεY] using hy)).2]
  change _ = ((∫ x in -R..R, traceFluxY g ε (x,Y)) - ∫ x in -R..R, traceFluxY g ε (x,ε)) +
    (∫ y in ε..Y, traceFluxX g ε (R,y)) - ∫ y in ε..Y, traceFluxX g ε (-R,y) at hb
  rw [ht,hl,hr] at hb
  simpa only [traceFluxY,sub_self,zero_mul,zero_sub,
    intervalIntegral.integral_neg,sub_neg_eq_add,zero_add,add_zero,sub_zero] using hb

lemma half_trace_rectangle {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ε ≤ R ∧ Integrable (fun x : ℝ => g (x,ε)) ∧
      (∫ x : ℝ, g (x,ε)) =
        ∫ p in Icc (-R,ε) (R,R), (p.2-ε)*pairLaplacian g p := by
  obtain ⟨M,hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let R := max M ε+1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_right M ε]
  have hεR : ε ≤ R := by dsimp only [R]; linarith [le_max_right M ε]
  have hMR : M < R := by dsimp only [R]; linarith [le_max_left M ε]
  have hz (p : ℝ × ℝ) (hy : ε/2 ≤ p.2) (hn : M < ‖p‖) : g p = 0 := by
    by_contra hg
    have hh : ‖p‖ ≤ M := by simpa using hM (hs p hy hg)
    exact (not_lt_of_ge hh) hn
  have hznhd (p : ℝ × ℝ) (hy : ε/2 < p.2) (hn : M < ‖p‖) :
      g =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) := by
    have hy' : {q : ℝ × ℝ | ε/2 < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hy
    have hn' : {q : ℝ × ℝ | M < ‖q‖} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    filter_upwards [hy',hn'] with q hq₁ hq₂
    exact hz q hq₁.le hq₂
  have hd (p : ℝ × ℝ) (hy : ε/2 < p.2) (hn : M < ‖p‖) : fderiv ℝ g p = 0 := by
    rw [(hznhd p hy hn).fderiv_eq,fderiv_zero]
    rfl
  have htop (x : ℝ) (_hx : x ∈ Icc (-R) R) :
      g (x,R) = 0 ∧ fderiv ℝ g (x,R) (0,1) = 0 := by
    have hn : M < ‖(x,R)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_snd_le (x,R))
    exact ⟨hz (x,R) (by linarith) hn,by rw [hd (x,R) (by linarith) hn]; rfl⟩
  have hside (y : ℝ) (hy : y ∈ Icc ε R) :
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0 := by
    have h₁ : M < ‖(-R,y)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_neg,abs_of_pos hR] using norm_fst_le (-R,y))
    have h₂ : M < ‖(R,y)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_fst_le (R,y))
    rw [hd (-R,y) (by linarith [hy.1]) h₁,hd (R,y) (by linarith [hy.1]) h₂]
    simp
  have hbox (p : ℝ × ℝ) (hp : p ∈ Icc (-R,ε) (R,R)) : ContDiffAt ℝ 2 g p :=
    hc p (hε.trans_le hp.1.2)
  have hb := rectangle_trace_identity hR.le hεR hbox htop hside
  have hzero (x : ℝ) (hx : x ∉ Icc (-R) R) : g (x,ε) = 0 := by
    apply hz (x,ε) (by linarith)
    have hh : R < |x| := by
      have hh : x < -R ∨ R < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
      rcases hh with hh | hh
      · exact (lt_neg_of_lt_neg hh).trans_le (neg_le_abs x)
      · exact hh.trans_le (le_abs_self x)
    exact hMR.trans (hh.trans_le (norm_fst_le (x,ε)))
  have hcont : Continuous (fun x : ℝ => g (x,ε)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hc (x,ε) hε).continuousAt.comp (f := fun x : ℝ => (x,ε))
      (continuous_id.prodMk continuous_const).continuousAt
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc (a := -R) (b := R))
  have hline : (∫ x in -R..R, g (x,ε)) = ∫ x : ℝ, g (x,ε) := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      setIntegral_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  exact ⟨R,hR,hεR,hint.integrable_of_forall_notMem_eq_zero hzero,(hline.symm.trans hb.symm)⟩

lemma ofReal_integral_le_lintegral_abs.{u_1} {α : Type u_1} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (Eventually.of_forall (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_le_ofReal (integral_mono hf hf.abs (fun x => le_abs_self _))

lemma half_trace_lintegral_le {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    (hn : ∀ p : ℝ × ℝ, 0 ≤ g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    (∫⁻ x : ℝ, ENNReal.ofReal (g (x,ε))) ≤
      ∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|) := by
  obtain ⟨R,_,_,hi,he⟩ := half_trace_rectangle hε hc hK hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => hn (x,ε))),he]
  have hi₂ : IntegrableOn (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p)
      (Icc (-R,ε) (R,R)) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hp' : 0 < p.2 := hε.trans_le hp.1.2
    have hh : ContinuousAt (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (continuousAt_pairLaplacian (hc p hp'))
    exact hh.continuousWithinAt
  refine (ofReal_integral_le_lintegral_abs hi₂).trans ?_
  calc
    (∫⁻ p in Icc (-R,ε) (R,R), ENNReal.ofReal |(p.2-ε)*pairLaplacian g p|) =
        ∫⁻ p in Icc (-R,ε) (R,R), ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro p hp
      simp only [abs_mul,abs_of_nonneg (sub_nonneg.mpr hp.1.2)]
    _ ≤ _ := lintegral_mono_set (fun p hp => hp.1.2)

def secondReal (f : ℂ → ℝ) (z u v : ℂ) : ℝ := fderiv ℝ (fderiv ℝ f) z u v

def complexSecondReal (f : ℂ → ℂ) (z u v : ℂ) : ℂ := fderiv ℝ (fderiv ℝ f) z u v

lemma secondReal_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : ContDiffAt ℝ 2 F z) (u v : ℂ) :
    secondReal (ψ ∘ F) z u v =
      fderiv ℝ ψ (F z) (complexSecondReal F z u v) +
      secondReal ψ (F z) (fderiv ℝ F z u) (fderiv ℝ F z v) := by
  have hdψ := hψ.differentiableAt (by norm_num)
  have hdF := hF.differentiableAt (by norm_num)
  have hddψ := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hddF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (ψ ∘ F) =ᶠ[𝓝 z] fun w =>
      (fderiv ℝ ψ (F w)).comp (fderiv ℝ F w) := by
    filter_upwards [hF.eventually (by simp),hdF.continuousAt.eventually (hψ.eventually (by simp))] with w hFw hψw
    exact fderiv_comp w (hψw.differentiableAt (by norm_num)) (hFw.differentiableAt (by norm_num))
  have hh := ((hddψ.hasFDerivAt.comp z hdF.hasFDerivAt).clm_comp hddF.hasFDerivAt).congr_of_eventuallyEq he
  rw [secondReal,hh.fderiv]
  simp [secondReal,complexSecondReal,ContinuousLinearMap.compL_apply]

lemma bilinear_complex_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c*Complex.I) (c*Complex.I) = ‖c‖^2*(B 1 1+B Complex.I Complex.I) := by
  have hc : c = c.re • (1 : ℂ)+c.im • Complex.I := by simp
  have hci : c*Complex.I = (-c.im) • (1 : ℂ)+c.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hn : ‖c‖^2 = c.re^2+c.im^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  rw [hci,hc]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [← hc,hn]
  ring

lemma laplacian_eq_secondReal (f : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian f z = secondReal f z 1 1+secondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,secondReal]

lemma laplacian_eq_complexSecondReal (f : ℂ → ℂ) (z : ℂ) :
    Laplacian.laplacian f z = complexSecondReal f z 1 1+complexSecondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,complexSecondReal]

lemma fderiv_real_complex_apply {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) : fderiv ℝ F z v = deriv F z*v := by
  rw [(hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [smul_eq_mul,mul_comm]

lemma laplacian_holomorphic_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : AnalyticAt ℂ F z) :
    Laplacian.laplacian (ψ ∘ F) z = ‖deriv F z‖^2*Laplacian.laplacian ψ (F z) := by
  rw [laplacian_eq_secondReal,secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ),
    secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ)]
  have hz := hF.harmonicAt.2.eq_of_nhds
  rw [laplacian_eq_complexSecondReal] at hz
  change complexSecondReal F z 1 1+complexSecondReal F z Complex.I Complex.I = 0 at hz
  have he : fderiv ℝ ψ (F z) (complexSecondReal F z 1 1)+
      fderiv ℝ ψ (F z) (complexSecondReal F z Complex.I Complex.I) = 0 := by
    rw [← map_add,hz,map_zero]
  simp only [fderiv_real_complex_apply hF.differentiableAt,mul_one]
  have hb := bilinear_complex_rotation (fderiv ℝ (fderiv ℝ ψ) (F z)) (deriv F z)
  rw [laplacian_eq_secondReal]
  dsimp only [secondReal] at *
  linarith

lemma pairLaplacian_complex (f : ℂ → ℝ) (p : ℝ × ℝ) :
    pairLaplacian (f ∘ Complex.equivRealProdCLM.symm) p =
      Laplacian.laplacian f (Complex.equivRealProdCLM.symm p) := by
  have he := Complex.equivRealProdCLM.symm.iteratedFDerivWithin_comp_right
    f (s := univ) uniqueDiffOn_univ (mem_univ (Complex.equivRealProdCLM.symm p)) 2
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  have h₁ := congrArg (fun B => B ![((1,0) : ℝ × ℝ),(1,0)]) he
  have h₂ := congrArg (fun B => B ![((0,1) : ℝ × ℝ),(0,1)]) he
  simp only [iteratedFDeriv_two_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearEquiv.coe_coe] at h₁ h₂
  have hc₁ : Complex.equivRealProdCLM.symm (1,0) = 1 := by simp [Complex.equivRealProdCLM_symm_apply]
  have hc₂ : Complex.equivRealProdCLM.symm (0,1) = Complex.I := by simp [Complex.equivRealProdCLM_symm_apply]
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  rw [pairLaplacian,h₁,h₂,laplacian_eq_secondReal]
  rfl

lemma laplacian_eq_zero_outside_tsupport {ψ : ℂ → ℝ} {z : ℂ}
    (hz : z ∉ tsupport ψ) : Laplacian.laplacian ψ z = 0 := by
  have he := notMem_tsupport_iff_eventuallyEq.mp hz
  have hh := laplacian_congr_nhds he
  exact hh.eq_of_nhds.trans (by
    change Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) z = 0
    rw [laplacian_const]
    rfl)

lemma continuous_laplacian {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  have hh : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuous
  have he : Laplacian.laplacian ψ = fun z => secondReal ψ z 1 1+secondReal ψ z Complex.I Complex.I :=
    funext (laplacian_eq_secondReal ψ)
  rw [he]
  unfold secondReal
  fun_prop

lemma compactSupport_laplacian {ψ : ℂ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (Laplacian.laplacian ψ) := by
  apply hψ.mono'
  intro z hz
  by_contra hn
  exact hz (laplacian_eq_zero_outside_tsupport hn)

lemma conformal_lintegral_le {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) ≤ ∫⁻ w, b w := by
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b
  have hh : (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) = ∫⁻ w in F '' s, b w := by
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
    have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
    dsimp only
    rw [hf]
    have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
    rw [hd',abs_of_nonneg (sq_nonneg _)]
  rw [hh]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma conformal_cutoff_trace_bound {F : ℂ → ℂ} {ψ : ℂ → ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hn : ∀ w, 0 ≤ ψ w) (_hψK : HasCompactSupport ψ)
    (hproper : ∀ η : ℝ, 0 < η → IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' tsupport ψ))
    {H : ℝ} (hH : 0 ≤ H)
    (hheight : ∀ z : ℂ, 0 < z.im → F z ∈ tsupport ψ → z.im ≤ H) :
    ∀ ε : ℝ, 0 < ε → (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ENNReal.ofReal H * ∫⁻ w : ℂ, ENNReal.ofReal |Laplacian.laplacian ψ w| := by
  intro ε hε
  let C := Complex.equivRealProdCLM.symm
  let g : ℝ × ℝ → ℝ := (ψ ∘ F) ∘ C
  have hc (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p := by
    have hz : 0 < (C p).im := hp
    exact (hψ.contDiffAt.comp _ ((hF (C p) hz).contDiffAt.restrict_scalars ℝ)).comp _ C.contDiff.contDiffAt
  have hK := (hproper (ε/2) (by linarith)).image Complex.equivRealProdCLM.continuous
  have hs (p : ℝ × ℝ) (hp : ε/2 ≤ p.2) (hg : g p ≠ 0) :
      p ∈ Complex.equivRealProdCLM '' ({z : ℂ | ε/2 ≤ z.im} ∩ F ⁻¹' tsupport ψ) := by
    refine ⟨C p,⟨hp,subset_closure hg⟩,?_⟩
    exact Complex.equivRealProdCLM.apply_symm_apply p
  have ht := half_trace_lintegral_le hε hc (fun p => hn _) hK hs
  have ht' : (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|) := by
    have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|)) {p : ℝ × ℝ | ε ≤ p.2}
    have hh : (∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|)) =
        ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|) := by
      rw [← he]
      apply lintegral_congr
      intro z
      dsimp only [g,C]
      rw [pairLaplacian_complex]
      rfl
    rw [hh] at ht
    simpa only [g,C,Function.comp_apply,Complex.equivRealProdCLM_symm_apply] using ht
  refine ht'.trans ?_
  have hmeas : MeasurableSet {z : ℂ | ε ≤ z.im} := isClosed_le continuous_const Complex.continuous_im |>.measurableSet
  calc
    (∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|)) ≤
        ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal H *
          (ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)|) := by
      apply setLIntegral_mono' hmeas
      intro z hz
      rw [laplacian_holomorphic_comp hψ.contDiffAt (hF z (hε.trans_le hz)),
        abs_mul,abs_of_nonneg (sq_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul hH]
      apply ENNReal.ofReal_le_ofReal
      by_cases hd : Laplacian.laplacian ψ (F z) = 0
      · simp [hd]
      have hm : F z ∈ tsupport ψ := by
        by_contra hh
        exact hd (laplacian_eq_zero_outside_tsupport hh)
      nlinarith [sq_nonneg ‖deriv F z‖,abs_nonneg (Laplacian.laplacian ψ (F z)),
        hheight z (hε.trans_le hz) hm,
        mul_nonneg (sq_nonneg ‖deriv F z‖) (abs_nonneg (Laplacian.laplacian ψ (F z)))]
    _ = ENNReal.ofReal H * ∫⁻ z in {z : ℂ | ε ≤ z.im},
        ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      exact mul_le_mul le_rfl (conformal_lintegral_le hmeas
        (fun z hz => (hF z (hε.trans_le hz)).differentiableAt)
        (hi.mono (fun z hz => hε.trans_le hz))
        (fun w => ENNReal.ofReal |Laplacian.laplacian ψ w|)) zero_le zero_le

lemma exists_trace_smooth_cutoff (K : Set ℂ) (hK : IsCompact K) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ (∀ w, 0 ≤ ψ w) ∧ HasCompactSupport ψ ∧
      ∀ w ∈ K, ψ w = 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) := ⟨max R 0+1,max R 0+2,by positivity,by linarith⟩
  refine ⟨b,b.contDiff,b.nonneg',b.hasCompactSupport,fun w hw => ?_⟩
  apply b.one_of_mem_closedBall
  exact Metric.closedBall_subset_closedBall (by dsimp [b]; linarith [le_max_left R 0]) (hR hw)

lemma conformal_trace_bound {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hproper : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∀ K : Set ℂ, IsCompact K → ∃ H : ℝ, 0 < H ∧
      ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C := by
  obtain ⟨ψ,hψ,hn,hψK,hψone⟩ := exists_trace_smooth_cutoff K hK
  obtain ⟨H,hH,hHb⟩ := hheight (tsupport ψ) hψK
  let C := ENNReal.ofReal H * ∫⁻ w : ℂ, ENNReal.ofReal |Laplacian.laplacian ψ w|
  have hfin : C < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    have hi := (continuous_laplacian hψ).integrable_of_hasCompactSupport (μ := volume) (compactSupport_laplacian hψK)
    simpa only [HasFiniteIntegral,← ofReal_norm,Real.norm_eq_abs] using hi.hasFiniteIntegral
  refine ⟨C,hfin,fun ε hε => ?_⟩
  have hb := conformal_cutoff_trace_bound hF hi hψ hn hψK
    (hproper (tsupport ψ) hψK) hH.le hHb ε hε
  refine le_trans ?_ hb
  have hcont : Continuous (fun x : ℝ => F (x+ε*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz : 0 < (x+ε*Complex.I : ℂ).im := by simpa using hε
    exact (hF _ hz).continuousAt.comp (f := fun x : ℝ => (x+ε*Complex.I : ℂ))
      (by fun_prop)
  have hm : MeasurableSet {x : ℝ | F (x+ε*Complex.I) ∈ K} :=
    hK.isClosed.measurableSet.preimage hcont.measurable
  rw [← lintegral_indicator_one hm]
  apply lintegral_mono
  intro x
  by_cases hx : F (x+ε*Complex.I) ∈ K
  · simp [hx,hψone _ hx]
  · simp [hx]

lemma class_trace_bound (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | classFun g (x+ε*Complex.I) ∈ K} ≤ C := by
  apply conformal_trace_bound
    (fun z hz => (classFun_schlicht g).1.1.analyticAt (isOpen_halfPlane.mem_nhds hz))
    (classFun_schlicht g).1.2
    (fun _ hK η hη => class_proper_preimage g hβ hfin hK hη)
    (fun _ hK => class_preimage_height_bound g hβ hfin hK) hK

lemma uniform_relative_class_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : DiskClass) (w : ℂ), |w.re| ≤ 1 →
      (1/2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖classFun g w‖ ≤ M := by
  let B : Set (ℝ × ℝ) := Icc (-1,1/2) (1,1)
  let K : Set ℂ := Complex.equivRealProdCLM.symm '' B
  have hK : IsCompact K := isCompact_Icc.image Complex.equivRealProdCLM.symm.continuous
  have hKsub : K ⊆ Set.range (fun w : halfPlane => (w : ℂ)) := by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨⟨Complex.equivRealProdCLM.symm p,?_⟩,rfl⟩
    change 0 < p.2
    linarith [hp.1.2]
  have hKs : IsCompact ((fun w : halfPlane => (w : ℂ)) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKsub
  have hprod := (isCompact_univ (X := DiskClass)).prod hKs
  obtain ⟨M,hM⟩ := hprod.exists_bound_of_continuousOn continuous_classFun_eval.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun g w hx hy hyy => ?_⟩
  have hw : w ∈ halfPlane := by change 0 < w.im; linarith
  have hmem : (g,⟨w,hw⟩) ∈ (univ : Set DiskClass) ×ˢ ((fun w : halfPlane => (w : ℂ)) ⁻¹' K) := by
    refine ⟨mem_univ _,⟨(w.re,w.im),?_,?_⟩⟩
    · exact ⟨⟨(abs_le.mp hx).1,hy⟩,⟨(abs_le.mp hx).2,hyy⟩⟩
    · exact Complex.equivRealProdCLM.symm_apply_apply w
  exact (hM _ hmem).trans (le_max_left _ _)

end Brennan

end

end OAI
