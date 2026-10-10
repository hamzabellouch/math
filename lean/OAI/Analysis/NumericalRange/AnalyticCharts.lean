import OAI.Analysis.NumericalRange.ConvexBarrier

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate

section
lemma real_clm_complex_apply (D : ℂ →L[ℝ] ℝ) (z : ℂ) :
    D z = z.re * D 1 + z.im * D I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  conv_lhs => rw [hz]
  simp only [map_add,map_smul,smul_eq_mul]

def barrierComplexification {ι : Type u_13} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (w : ℂ × ℂ) : ℂ :=
  c*(w.1^2+w.2^2)+∑ i, Complex.exp ((l i 1 : ℂ)*w.1+(l i I : ℂ)*w.2-a i)

lemma barrierComplexification_analytic {ι : Type u_14} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (w : ℂ × ℂ) :
    AnalyticAt ℂ (barrierComplexification c l a) w := by
  have h1 := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt w
  have h2 := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt w
  unfold barrierComplexification
  exact (analyticAt_const.fun_mul ((h1.fun_pow 2).fun_add (h2.fun_pow 2))).fun_add
    (Finset.analyticAt_fun_sum _ (fun i _ =>
      ((analyticAt_const.fun_mul h1).fun_add (analyticAt_const.fun_mul h2) |>.fun_sub analyticAt_const).cexp))

lemma barrierComplexification_real {ι : Type u_15} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (z : ℂ) :
    barrierComplexification c l a ((z.re : ℂ),(z.im : ℂ)) = convexBarrier c l a z := by
  simp only [barrierComplexification,convexBarrier,Complex.normSq_apply,ofReal_add,
    ofReal_mul,ofReal_sum,ofReal_sub,ofReal_exp,pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [real_clm_complex_apply (l i) z]
  push_cast
  ring

lemma barrierComplexification_conj {ι : Type u_16} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (w : ℂ × ℂ) :
    barrierComplexification c l a (conj w.1,conj w.2) =
      conj (barrierComplexification c l a w) := by
  simp only [barrierComplexification,map_add,map_mul,map_pow,map_sum,map_sub,conj_ofReal,
    ← Complex.exp_conj]

def barrierChartComplexification {ι : Type u_17} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (p u v : ℂ) (w : ℂ × ℂ) : ℂ :=
  barrierComplexification c l a
    ((p.re : ℂ)+(u.re : ℂ)*w.1+(v.re : ℂ)*w.2,
      (p.im : ℂ)+(u.im : ℂ)*w.1+(v.im : ℂ)*w.2)-1

lemma barrierChartComplexification_analytic {ι : Type u_18} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (p u v : ℂ) :
    AnalyticAt ℂ (barrierChartComplexification c l a p u v) 0 := by
  have h1 := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt 0
  have h2 := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt 0
  have hr : AnalyticAt ℂ (fun w : ℂ × ℂ => (p.re : ℂ)+(u.re : ℂ)*w.1+(v.re : ℂ)*w.2) 0 :=
    (analyticAt_const.fun_add (analyticAt_const.fun_mul h1)).fun_add (analyticAt_const.fun_mul h2)
  have hi : AnalyticAt ℂ (fun w : ℂ × ℂ => (p.im : ℂ)+(u.im : ℂ)*w.1+(v.im : ℂ)*w.2) 0 :=
    (analyticAt_const.fun_add (analyticAt_const.fun_mul h1)).fun_add (analyticAt_const.fun_mul h2)
  exact ((barrierComplexification_analytic c l a _).comp (hr.prod hi)).fun_sub analyticAt_const

lemma barrierChartComplexification_real {ι : Type u_19} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (p u v : ℂ) (t s : ℝ) :
    barrierChartComplexification c l a p u v ((t : ℂ),(s : ℂ)) =
      (convexBarrier c l a (p+t • u+s • v)-1 : ℝ) := by
  unfold barrierChartComplexification
  rw [ofReal_sub,ofReal_one]
  congr 1
  rw [← barrierComplexification_real]
  congr 1
  apply Prod.ext <;> simp [Complex.real_smul] <;> ring

lemma barrierChartComplexification_conj {ι : Type u_20} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (p u v : ℂ) (w : ℂ × ℂ) :
    barrierChartComplexification c l a p u v (conj w.1,conj w.2) =
      conj (barrierChartComplexification c l a p u v w) := by
  unfold barrierChartComplexification
  rw [map_sub,map_one,← barrierComplexification_conj]
  congr 2 ; simp

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
section

lemma complex_prod_clm_apply (D : (ℂ × ℂ) →L[ℂ] ℂ) (z : ℂ × ℂ) :
    D z = z.1 * D (1,0) + z.2 * D (0,1) := by
  have hz : z = z.1 • ((1 : ℂ),0) + z.2 • ((0 : ℂ),1) := by ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add,map_smul,smul_eq_mul]

lemma analytic_real_complexification_deriv {q : ℂ → ℝ} {p u v : ℂ}
    {H : ℂ × ℂ → ℂ} {d : ℝ}
    (hq : DifferentiableAt ℝ q p) (hH : AnalyticAt ℂ H 0)
    (hr : ∀ t s : ℝ, H ((t : ℂ),(s : ℂ)) = (q (p+t • u+s • v)-1 : ℝ))
    (hu : fderiv ℝ q p u = 0) (hv : fderiv ℝ q p v = d) :
    HasFDerivAt H ((d : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
  let L := fderiv ℂ H 0
  have hLD : HasFDerivAt H L 0 := hH.differentiableAt.hasFDerivAt
  have h1 : L (1,0) = 0 := by
    have hc : HasDerivAt (fun t : ℂ => H (t,0)) (L (1,0)) 0 := by
      have hp : HasDerivAt (fun t : ℂ => (t,(0 : ℂ))) (1,0) 0 :=
        (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ))
      exact hLD.comp_hasDerivAt (f := fun t : ℂ => (t,0)) 0 hp
    have hline : HasDerivAt (fun t : ℝ => p+t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    have hreal : HasDerivAt (fun t : ℝ => (q (p+t • u)-1 : ℝ)) 0 0 := by
      have hh : HasFDerivAt q (fderiv ℝ q p) (p+(0 : ℝ) • u) := by simpa using hq.hasFDerivAt
      simpa only [Function.comp_def,hu,sub_zero] using
        (hh.comp_hasDerivAt (f := fun t : ℝ => p+t • u) (0 : ℝ) hline).sub_const 1
    have he : (fun t : ℝ => H ((t : ℂ),0)) = (fun t : ℝ => ((q (p+t • u)-1 : ℝ) : ℂ)) := by
      funext t
      simpa only [ofReal_zero,zero_smul,add_zero] using hr t 0
    have hh := hc.comp_ofReal (z := (0 : ℝ))
    rw [he] at hh
    simpa using hh.unique hreal.ofReal_comp
  have h2 : L (0,1) = d := by
    have hc : HasDerivAt (fun t : ℂ => H (0,t)) (L (0,1)) 0 := by
      have hp : HasDerivAt (fun t : ℂ => ((0 : ℂ),t)) (0,1) 0 :=
        (hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id (0 : ℂ))
      exact hLD.comp_hasDerivAt (f := fun t : ℂ => (0,t)) 0 hp
    have hline : HasDerivAt (fun t : ℝ => p+t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    have hreal : HasDerivAt (fun t : ℝ => (q (p+t • v)-1 : ℝ)) d 0 := by
      have hh : HasFDerivAt q (fderiv ℝ q p) (p+(0 : ℝ) • v) := by simpa using hq.hasFDerivAt
      simpa only [Function.comp_def,hv,sub_zero] using
        (hh.comp_hasDerivAt (f := fun t : ℝ => p+t • v) (0 : ℝ) hline).sub_const 1
    have he : (fun t : ℝ => H (0,(t : ℂ))) = (fun t : ℝ => ((q (p+t • v)-1 : ℝ) : ℂ)) := by
      funext t
      simpa only [ofReal_zero,zero_smul,add_zero] using hr 0 t
    have hh := hc.comp_ofReal (z := (0 : ℝ))
    rw [he] at hh
    exact hh.unique hreal.ofReal_comp
  have he : L = (d : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    rw [complex_prod_clm_apply,h1,h2]
    simp [mul_comm]
  rwa [← he]

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
section

lemma analytic_inverse_at {E : Type u_21} {F : Type u_22} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : OpenPartialHomeomorph E F) {p : E} (hp : p ∈ e.source)
    (ha : AnalyticAt ℂ e p) (L : E ≃L[ℂ] F) (hd : HasFDerivAt e (L : E →L[ℂ] F) p) :
    AnalyticAt ℂ e.symm (e p) := by
  obtain ⟨P,hP⟩ := ha
  refine ⟨P.leftInv L p,e.hasFPowerSeriesAt_symm hp hP ?_⟩
  apply (continuousMultilinearCurryFin1 ℂ E F).injective
  simpa using hP.hasFDerivAt.unique hd

def normalScaleEquiv (d : ℂ) (hd : d ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) where
  toFun p := (p.1,d*p.2)
  invFun p := (p.1,d⁻¹*p.2)
  left_inv p := by ext <;> simp [hd]
  right_inv p := by ext <;> simp [hd]
  map_add' p q := by ext <;> simp [mul_add]
  map_smul' a p := by ext <;> simp [smul_eq_mul]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma analytic_implicit_real_graph {H : ℂ × ℂ → ℂ} {d : ℝ}
    (hd : d ≠ 0) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hHD : HasFDerivAt H ((d : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0)
    (hreal : ∀ p, H (conj p.1,conj p.2) = conj (H p)) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ HasDerivAt φ 0 0 ∧
      (∀ᶠ z in 𝓝 0, H (z,φ z) = 0) ∧
      (∀ᶠ z in 𝓝 0, z.im = 0 → (φ z).im = 0) := by
  let F : ℂ × ℂ → ℂ × ℂ := fun p => (p.1,H p)
  let L := normalScaleEquiv (d : ℂ) (by exact_mod_cast hd)
  have hFa : AnalyticAt ℂ F 0 := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt 0 |>.prod hH
  have hFd : HasFDerivAt F (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := by
    convert! (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.prodMk hHD using 1
  have hFs : HasStrictFDerivAt F (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := by
    rw [← hFd.fderiv]
    exact hFa.hasStrictFDerivAt
  let e := hFs.toOpenPartialHomeomorph F
  have h0 : (0 : ℂ × ℂ) ∈ e.source := hFs.mem_toOpenPartialHomeomorph_source
  have hF0 : F 0 = 0 := by simp [F,hH0]
  have he0 : e 0 = 0 := hF0
  have het0 : (0 : ℂ × ℂ) ∈ e.target := he0 ▸ e.map_source h0
  have hes0 : e.symm 0 = 0 := by simpa only [he0] using e.left_inv h0
  have hes00 : e.symm ((0 : ℂ),0) = 0 := hes0
  have hea : AnalyticAt ℂ e.symm 0 := by
    simpa only [he0] using analytic_inverse_at e h0 hFa L hFd
  let φ : ℂ → ℂ := fun z => (e.symm (z,0)).2
  have hpair : AnalyticAt ℂ (fun z : ℂ => (z,(0 : ℂ))) 0 := analyticAt_id.prod analyticAt_const
  have hgea : AnalyticAt ℂ (fun z : ℂ => e.symm (z,0)) 0 := hea.comp_of_eq hpair rfl
  have hφa : AnalyticAt ℂ φ 0 :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (e.symm (0,0)) |>.comp_of_eq hgea rfl
  have hφ0 : φ 0 = 0 := by simp only [φ,hes00,Prod.snd_zero]
  have hin : ∀ᶠ z : ℂ in 𝓝 0, (z,(0 : ℂ)) ∈ e.target :=
    hpair.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds het0)
  have hge : ∀ᶠ z : ℂ in 𝓝 0, F (e.symm (z,0)) = (z,0) := by
    filter_upwards [hin] with z hz
    exact e.right_inv hz
  have hgfst : ∀ᶠ z : ℂ in 𝓝 0, (e.symm (z,0)).1 = z := by
    filter_upwards [hge] with z hz
    exact congrArg Prod.fst hz
  have hφH : ∀ᶠ z : ℂ in 𝓝 0, H (z,φ z) = 0 := by
    filter_upwards [hge,hgfst] with z hz hf
    have he := congrArg Prod.snd hz
    change H (e.symm (z,0)) = 0 at he
    have hpairEq : (z,φ z) = e.symm (z,0) := Prod.ext hf.symm rfl
    rw [hpairEq]
    exact he
  have hφD : HasDerivAt φ 0 0 := by
    have hgD := hFs.to_localInverse
    change HasStrictFDerivAt e.symm (L.symm : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (F 0) at hgD
    rw [hF0] at hgD
    have hdP : HasDerivAt (fun z : ℂ => (z,(0 : ℂ))) (1,0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    have hh := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt 0
      (hgD.hasFDerivAt.comp_hasDerivAt (f := fun z : ℂ => (z,0)) 0 hdP)
    convert! hh using 1
    change 0 = (d : ℂ)⁻¹ * 0
    simp
  have hcont : ContinuousAt (fun z : ℂ => e.symm (z,(0 : ℂ))) 0 := hgea.continuousAt
  have hconj : ContinuousAt (fun z : ℂ => (conj (e.symm (z,0)).1,conj (e.symm (z,0)).2)) 0 := by
    fun_prop
  have hins : ∀ᶠ z : ℂ in 𝓝 0, e.symm (z,0) ∈ e.source :=
    hcont.preimage_mem_nhds (by simpa only [hes00] using e.open_source.mem_nhds h0)
  have hinc : ∀ᶠ z : ℂ in 𝓝 0,
      (conj (e.symm (z,0)).1,conj (e.symm (z,0)).2) ∈ e.source :=
    hconj.preimage_mem_nhds (by simpa only [hes00,hes0,Prod.fst_zero,Prod.snd_zero,map_zero,Prod.mk_zero_zero] using e.open_source.mem_nhds h0)
  refine ⟨φ,hφa,hφ0,hφD,hφH,?_⟩
  filter_upwards [hins,hinc,hge] with z hs hc he
  intro hz
  have heq : (conj (e.symm (z,0)).1,conj (e.symm (z,0)).2) = e.symm (z,0) := by
    apply e.injOn hc hs
    change F _ = F _
    rw [he]
    have hf := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    change (e.symm (z,0)).1 = z at hf
    change H (e.symm (z,0)) = 0 at hh
    ext
    · simp only [F,hf,Complex.conj_eq_iff_im.mpr hz]
    · simp only [F,hreal,hh,map_zero]
  have hsnd := congrArg Prod.snd heq
  exact Complex.conj_eq_iff_im.mp hsnd

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
section

lemma local_normal_side {q : ℂ → ℝ} {d : ℝ} (hd : d < 0)
    (hD : HasStrictFDerivAt q (d • Complex.imCLM) 0)
    (haxis : ∀ᶠ z : ℂ in 𝓝 0, q (z.re : ℂ) = 1) :
    ∀ᶠ z : ℂ in 𝓝 0, (q z < 1 ↔ 0 < z.im) ∧ (z.im = 0 → q z = 1) := by
  have hc : ContinuousAt (fun z : ℂ => (z,(z.re : ℂ))) 0 := by fun_prop
  have he := hD.isLittleO.def (show 0 < -d/2 by linarith)
  have hep : ∀ᶠ z : ℂ in 𝓝 0,
      ‖q z-q (z.re : ℂ)-(d • Complex.imCLM) (z-(z.re : ℂ))‖ ≤
        (-d/2)*‖z-(z.re : ℂ)‖ := hc.tendsto.eventually he
  filter_upwards [haxis,hep] with z ha he
  have hn : ‖z-(z.re : ℂ)‖ = |z.im| := by
    have h : z-(z.re : ℂ) = z.im * I := by apply Complex.ext <;> simp
    rw [h,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [ha,hn] at he
  simp only [smul_apply,smul_eq_mul,map_sub,Complex.imCLM_apply,ofReal_im, Real.norm_eq_abs] at he
  have hl := (abs_le.mp he).1
  have hu := (abs_le.mp he).2
  constructor
  · constructor
    · intro hq
      by_contra hn
      have hz : z.im ≤ 0 := le_of_not_gt hn
      rw [abs_of_nonpos hz] at hl
      have hdz : 0 ≤ d*z.im := mul_nonneg_of_nonpos_of_nonpos hd.le hz
      nlinarith
    · intro hz
      rw [abs_of_pos hz] at hu
      have hdz : d*z.im < 0 := mul_neg_of_neg_of_pos hd hz
      nlinarith
  · intro hz
    have hzr : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz]
    rwa [hzr] at ha

lemma local_normal_le_side {q : ℂ → ℝ} {d : ℝ} (hd : d < 0)
    (hD : HasStrictFDerivAt q (d • Complex.imCLM) 0)
    (haxis : ∀ᶠ z : ℂ in 𝓝 0, q (z.re : ℂ) = 1) :
    ∀ᶠ z : ℂ in 𝓝 0, q z ≤ 1 ↔ 0 ≤ z.im := by
  have hc : ContinuousAt (fun z : ℂ => (z,(z.re : ℂ))) 0 := by fun_prop
  have he := hD.isLittleO.def (show 0 < -d/2 by linarith)
  have hep : ∀ᶠ z : ℂ in 𝓝 0,
      ‖q z-q (z.re : ℂ)-(d • Complex.imCLM) (z-(z.re : ℂ))‖ ≤
        (-d/2)*‖z-(z.re : ℂ)‖ := hc.tendsto.eventually he
  filter_upwards [haxis,hep] with z ha he
  have hn : ‖z-(z.re : ℂ)‖ = |z.im| := by
    have h : z-(z.re : ℂ) = z.im * I := by apply Complex.ext <;> simp
    rw [h,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [ha,hn] at he
  simp only [smul_apply,smul_eq_mul,map_sub,Complex.imCLM_apply,ofReal_im, Real.norm_eq_abs] at he
  have hl := (abs_le.mp he).1
  have hu := (abs_le.mp he).2
  constructor
  · intro hq
    by_contra hn
    have hz : z.im < 0 := lt_of_not_ge hn
    rw [abs_of_neg hz] at hl
    have hdz : 0 < d*z.im := mul_pos_of_neg_of_neg hd hz
    nlinarith
  · intro hz
    rw [abs_of_nonneg hz] at hu
    have hdz : d*z.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd.le hz
    nlinarith

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma analytic_chart_rescale {U : Set ℂ} {χ : ℂ → ℂ}
    (ha : AnalyticAt ℂ χ 0) (hd : deriv χ 0 ≠ 0)
    (hs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im)
    (hb : ∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U) :
    ∃ ψ : ℂ → ℂ, ψ 0 = χ 0 ∧ AnalyticOnNhd ℂ ψ (ball 0 2) ∧
      InjOn ψ (ball 0 2) ∧ (∀ z ∈ ball 0 2, deriv ψ z ≠ 0) ∧
      (∀ z ∈ ball 0 2, ψ z ∈ U ↔ 0 < z.im) ∧
      (∀ z ∈ ball 0 2, z.im = 0 → ψ z ∈ frontier U) := by
  have hi := ha.hasStrictDerivAt.eventually_left_inverse hd
  have hd' := ha.deriv.continuousAt.eventually_ne hd
  have hall := ha.eventually_analyticAt.and (hi.and (hd'.and (hs.and hb)))
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp hall
  let a : ℝ := r/3
  have ha0 : 0 < a := by dsimp [a]; positivity
  have han : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  let ψ : ℂ → ℂ := fun z => χ ((a : ℂ)*z)
  have hmul : ∀ z ∈ ball (0 : ℂ) 2, (a : ℂ)*z ∈ ball 0 r := by
    intro z hz
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    dsimp [a]
    nlinarith
  refine ⟨ψ,by simp [ψ],?_,?_,?_,?_,?_⟩
  · intro z hz
    exact (hrall (hmul z hz)).1.comp (analyticAt_const.fun_mul analyticAt_id)
  · intro z hz w hw he
    have hzi := (hrall (hmul z hz)).2.1
    have hwi := (hrall (hmul w hw)).2.1
    apply mul_left_cancel₀ han
    rw [← hzi,← hwi]
    exact congrArg _ he
  · intro z hz
    have hdχ := (hrall (hmul z hz)).1.differentiableAt.hasDerivAt
    have hdd := hdχ.comp z ((hasDerivAt_id z).const_mul (a : ℂ))
    have he : deriv ψ z = deriv χ ((a : ℂ)*z)*((a : ℂ)*1) := hdd.deriv
    rw [he]
    exact mul_ne_zero (hrall (hmul z hz)).2.2.1 (mul_ne_zero han one_ne_zero)
  · intro z hz
    change χ ((a : ℂ)*z) ∈ U ↔ 0 < z.im
    rw [(hrall (hmul z hz)).2.2.2.1]
    simpa using mul_pos_iff_of_pos_left ha0
  · intro z hz him
    apply (hrall (hmul z hz)).2.2.2.2
    simp [him]


end CompleteCrouzeix

end

end OAI
