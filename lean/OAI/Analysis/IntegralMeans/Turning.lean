import OAI.Analysis.IntegralMeans.LevelCurve

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

def secantTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

lemma convex_secantTriangle : Convex ℝ secantTriangle := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a*p.1+b*q.1 ∧ a*p.1+b*q.1 ≤ a*p.2+b*q.2 ∧ a*p.2+b*q.2 ≤ 1
  rcases hp with ⟨hp0,hpst,hp1⟩
  rcases hq with ⟨hq0,hqst,hq1⟩
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0),
    add_le_add (mul_le_mul_of_nonneg_left hpst ha)
      (mul_le_mul_of_nonneg_left hqst hb), ?_⟩
  calc
    _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hp1 ha)
      (mul_le_mul_of_nonneg_left hq1 hb)
    _ = 1 := by simpa using hab

lemma nonempty_secantTriangle : secantTriangle.Nonempty := ⟨(0,0), by simp [secantTriangle]⟩

def averagedDerivative (γ : ℝ → ℂ) (s t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv γ (s+u*(t-s))

lemma continuous_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun p : ℝ × ℝ => averagedDerivative γ p.1 p.2) := by
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hi : Continuous (fun p : ℝ × ℝ => ∫ u in Icc (0 : ℝ) 1, deriv γ (p.1+u*(p.2-p.1))) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa [averagedDerivative, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi

lemma sub_smul_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (s t : ℝ) :
    (t-s) • averagedDerivative γ s t = γ t-γ s := by
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hD (u : ℝ) : HasDerivAt (fun v : ℝ => γ (s+v*(t-s)))
      ((t-s) • deriv γ (s+u*(t-s))) u := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_mul] using ((hγ.differentiable (by norm_num) (s+u*(t-s))).hasDerivAt.scomp u
      ((hasDerivAt_const u s).add ((hasDerivAt_id u).mul_const (t-s))))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hD u)
    (((hd.comp (show Continuous (fun u : ℝ => s+u*(t-s)) by fun_prop)).const_smul (t-s)).intervalIntegrable 0 1)
  simpa [averagedDerivative, intervalIntegral.integral_smul, sub_eq_add_neg] using hFTC

@[simp] lemma averagedDerivative_diag (γ : ℝ → ℂ) (s : ℝ) :
    averagedDerivative γ s s = deriv γ s := by simp [averagedDerivative]

def extendedSecant (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1-(p.2-p.1)) • averagedDerivative γ p.1 p.2 -
    (p.2-p.1) • averagedDerivative γ p.1 (p.2-1)

lemma continuous_extendedSecant {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (extendedSecant γ) := by
  have hc := continuous_averagedDerivative hγ
  exact ((continuous_const.sub (continuous_snd.sub continuous_fst)).smul hc).sub
    ((continuous_snd.sub continuous_fst).smul (hc.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2-1)) by fun_prop)))

@[simp] lemma extendedSecant_diag (γ : ℝ → ℂ) (s : ℝ) :
    extendedSecant γ (s,s) = deriv γ s := by simp [extendedSecant]

@[simp] lemma extendedSecant_corner (γ : ℝ → ℂ) :
    extendedSecant γ (0,1) = -deriv γ 0 := by simp [extendedSecant]

lemma extendedSecant_scale {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (s t : ℝ) :
    ((t-s)*(1-(t-s))) • extendedSecant γ (s,t) =
      ((1-(t-s))^2+(t-s)^2) • (γ t-γ s) := by
  have h₁ := sub_smul_averagedDerivative hγ s t
  have h₂ := sub_smul_averagedDerivative hγ s (t-1)
  rw [hp.sub_eq] at h₂
  change ((t-s)*(1-(t-s))) • ((1-(t-s)) • averagedDerivative γ s t -
    (t-s) • averagedDerivative γ s (t-1)) = _
  calc
    _ = (1-(t-s))^2 • ((t-s) • averagedDerivative γ s t) +
      (t-s)^2 • ((t-1-s) • averagedDerivative γ s (t-1)) := by
        simp only [smul_sub, smul_smul]
        module
    _ = _ := by rw [h₁, h₂, ← add_smul]

lemma extendedSecant_ne_zero {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) {p : ℝ × ℝ}
    (hpt : p ∈ secantTriangle) : extendedSecant γ p ≠ 0 := by
  rcases p with ⟨s,t⟩
  rcases hpt with ⟨hs, hst, ht⟩
  by_cases heq : s = t
  · subst t
    simpa using hd s ⟨hs, ht⟩
  by_cases hc : s = 0 ∧ t = 1
  · rcases hc with ⟨rfl,rfl⟩
    simpa using hd 0 (by simp)
  have hst' : s < t := lt_of_le_of_ne hst heq
  have hneq : γ t ≠ γ s := by
    by_cases ht1 : t = 1
    · subst t
      rw [hp.eq]
      have hs0 : s ≠ 0 := fun h => hc ⟨h,rfl⟩
      exact fun h => hs0 ((hinj ⟨by norm_num, by norm_num⟩ ⟨hs,hst'⟩ h).symm)
    · exact fun h => (ne_of_gt hst') (hinj ⟨hs.trans hst, lt_of_le_of_ne ht ht1⟩
        ⟨hs, hst'.trans_le ht⟩ h)
  have hpos : 0 < (1-(t-s))^2+(t-s)^2 := by nlinarith [sq_nonneg (1-(t-s))]
  intro he
  have hscale := extendedSecant_scale hγ hp s t
  rw [he, smul_zero] at hscale
  exact hneq (sub_eq_zero.mp ((smul_eq_zero.mp hscale.symm).resolve_left hpos.ne'))

lemma periodic_deriv {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) :
    Function.Periodic (deriv γ) 1 := by
  intro t
  rw [← deriv_comp_add_const γ 1 t]
  congr 1
  exact funext hp

lemma extendedSecant_edges {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extendedSecant γ (t,1) = -extendedSecant γ (0,t) := by
  by_cases h0 : t = 0
  · subst t
    simp
  by_cases h1 : t = 1
  · subst t
    simpa using (periodic_deriv hp).eq
  have hd : t*(1-t) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  apply (smul_right_injective ℂ hd)
  have ha := extendedSecant_scale hγ hp 0 t
  have hb := extendedSecant_scale hγ hp t 1
  simp only [sub_zero] at ha
  rw [hp.eq] at hb
  have he : (1-t)*(1-(1-t)) = t*(1-t) := by ring
  have he' : (1-(1-t))^2+(1-t)^2 = (1-t)^2+t^2 := by ring
  rw [he, he'] at hb
  change (t*(1-t)) • extendedSecant γ (t,1) = (t*(1-t)) • (-extendedSecant γ (0,t))
  rw [smul_neg, ha, hb, ← smul_neg]
  congr 1
  module

lemma extendedSecant_left_re_nonneg {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hd : (deriv γ 0).re = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (extendedSecant γ (0,t)).re := by
  by_cases h0 : t = 0
  · subst t
    simp [hd]
  by_cases h1 : t = 1
  · subst t
    simp [hd]
  have hpos : 0 < t*(1-t) := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h0))
    (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))
  have hs := congrArg Complex.re (extendedSecant_scale hγ hp 0 t)
  simp only [sub_zero, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re] at hs
  have hnonneg : 0 ≤ ((1-t)^2+t^2)*((γ t).re-(γ 0).re) :=
    mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.mpr (hm t ht))
  nlinarith

def triangleOrigin : secantTriangle := ⟨(0,0), by simp [secantTriangle]⟩

def triangleCorner : secantTriangle := ⟨(0,1), by simp [secantTriangle]⟩

def triangleEnd : secantTriangle := ⟨(1,1), by simp [secantTriangle]⟩

lemma exists_secant_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ A : C(secantTriangle, ℂ), A triangleOrigin = Complex.log (deriv γ 0) ∧
      ∀ p, Complex.exp (A p) = extendedSecant γ p := by
  let := convex_secantTriangle.contractibleSpace nonempty_secantTriangle
  let := convex_secantTriangle.locallyPathConnectedSpace
  let S : C(secantTriangle, ℂ) :=
    ⟨fun p => extendedSecant γ p, (continuous_extendedSecant hγ).comp continuous_subtype_val⟩
  have he : Complex.exp (Complex.log (deriv γ 0)) = S triangleOrigin := by
    simpa [S, triangleOrigin] using Complex.exp_log (hd 0 (by simp))
  obtain ⟨A, ⟨hA0,hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts S he
    (fun p => extendedSecant_ne_zero hγ hp hinj hd p.property)
  exact ⟨A, hA0, fun p => congrFun hA p⟩

lemma continuous_log_unique.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) {x : X} (hx : A x = B x) : A = B := by
  exact Complex.isCoveringMap_exp.eq_of_comp_eq hA hB
    (by funext y; exact Subtype.ext (h y)) x hx

def triangleLeft (t : unitInterval) : secantTriangle :=
  ⟨(0,t), by exact ⟨le_rfl, t.property.1, t.property.2⟩⟩

def triangleTop (t : unitInterval) : secantTriangle :=
  ⟨(t,1), by exact ⟨t.property.1, t.property.2, le_rfl⟩⟩

def triangleDiag (t : unitInterval) : secantTriangle :=
  ⟨(t,t), by exact ⟨t.property.1, le_rfl, t.property.2⟩⟩

lemma continuous_triangleLeft : Continuous triangleLeft := by
  unfold triangleLeft
  fun_prop

lemma continuous_triangleTop : Continuous triangleTop := by
  unfold triangleTop
  fun_prop

lemma continuous_triangleDiag : Continuous triangleDiag := by
  unfold triangleDiag
  fun_prop

lemma mem_slitPlane_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ Complex.slitPlane := by
  by_cases hi : z.im = 0
  · left
    exact lt_of_le_of_ne hr (fun he => hz (Complex.ext he.symm hi))
  · exact Or.inr hi

lemma log_neg_of_downward {z : ℂ} (hr : z.re = 0) (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · have ha := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hr,hi⟩
    have hb : Complex.arg (-z) = Real.pi/2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simpa using hr, by simpa using hi⟩
    simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, ha, hb]
    ring

lemma tangent_turning_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0) :
    ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = deriv γ t) ∧
      T 1 = T 0 + (2*Real.pi : ℝ)*Complex.I := by
  obtain ⟨A,hA0,hA⟩ := exists_secant_log hγ hp hinj hd
  have hleftc : Continuous (fun t : unitInterval =>
      Complex.log (extendedSecant γ (triangleLeft t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_clog (mem_slitPlane_of_re_nonneg
      (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)
      (extendedSecant_left_re_nonneg hγ hp hm hr t.property))).comp (f := fun u : unitInterval => extendedSecant γ (triangleLeft u))
      ((continuous_extendedSecant hγ).comp
        (continuous_subtype_val.comp continuous_triangleLeft)).continuousAt
  have hleft : (fun t : unitInterval => A (triangleLeft t)) =
      (fun t : unitInterval => Complex.log (extendedSecant γ (triangleLeft t))) := by
    apply continuous_log_unique (x := (0 : unitInterval)) (A.continuous.comp continuous_triangleLeft) hleftc
    · intro t
      dsimp only [Function.comp_def]
      rw [hA, Complex.exp_log
        (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)]
    · simpa [Function.comp_def, triangleLeft, triangleOrigin] using hA0
  have hcorner : A triangleCorner = A triangleOrigin + (Real.pi : ℂ)*Complex.I := by
    have hcl := congrFun hleft 1
    have hcl' : A triangleCorner = Complex.log (-deriv γ 0) := by
      simpa [triangleLeft, triangleCorner] using hcl
    rw [hcl', hA0, log_neg_of_downward hr hi]
  have htop : (fun t : unitInterval => A (triangleTop t)) =
      (fun t : unitInterval => A (triangleLeft t) + (Real.pi : ℂ)*Complex.I) := by
    apply continuous_log_unique (x := (0 : unitInterval)) (A.continuous.comp continuous_triangleTop)
      ((A.continuous.comp continuous_triangleLeft).add continuous_const)
    · intro t
      dsimp only [Function.comp_def, Pi.add_apply]
      rw [Complex.exp_add, hA, hA, Complex.exp_pi_mul_I, mul_neg_one]
      exact extendedSecant_edges hγ hp t.property
    · exact hcorner
  refine ⟨⟨fun t => A (triangleDiag t), A.continuous.comp continuous_triangleDiag⟩,
    fun t => ?_, ?_⟩
  · exact (hA (triangleDiag t)).trans (extendedSecant_diag γ t)
  · have hpt := congrFun htop 1
    change A triangleEnd = A triangleCorner + (Real.pi : ℂ)*Complex.I at hpt
    change A triangleEnd = A triangleOrigin + (↑(2*Real.pi) : ℂ)*Complex.I
    rw [hpt, hcorner]
    push_cast
    ring

lemma regular_level_sublevel_nhds {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0)
    {W : Set ℂ} (hW : W ∈ 𝓝 z) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      IsPreconnected (U ∩ {w | f w < f z}) ∧
      (U ∩ {w | f w < f z}).Nonempty := by
  obtain ⟨e,hz,her,_⟩ := exists_regular_level_chart hf hp
  have het : e z ∈ e.target := e.map_source hz
  have hn : e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e z) :=
    inter_mem (e.open_target.mem_nhds het) (by
      have ht := (e.continuousAt_symm het).preimage_mem_nhds
        (show W ∈ 𝓝 (e.symm (e z)) by rwa [e.left_inv hz])
      exact ht)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hn
  let B := Metric.ball (e z) r
  let U := e.source ∩ e ⁻¹' B
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBU : ∀ b ∈ B, b ∈ e.target ∧ e.symm b ∈ U := by
    intro b hb
    have hbt := (hball hb).1
    exact ⟨hbt,e.map_target hbt,by simpa only [mem_preimage,e.right_inv hbt] using hb⟩
  have hUo : IsOpen U := e.isOpen_inter_preimage hBo
  have hzU : z ∈ U := ⟨hz,by simpa [B] using hr⟩
  have hUW : U ⊆ W := by
    intro w hw
    have h := (hball hw.2).2
    simpa only [mem_preimage,e.left_inv hw.1] using h
  have he : U ∩ {w | f w < f z} = e.symm '' (B ∩ {b | b.re < f z}) := by
    ext w
    constructor
    · rintro ⟨hw,hfw⟩
      exact ⟨e w,⟨hw.2,by simpa only [mem_ofPred,her] using hfw⟩,e.left_inv hw.1⟩
    · rintro ⟨b,⟨hb,hbr⟩,rfl⟩
      refine ⟨(hBU b hb).2,?_⟩
      have hh := her (e.symm b)
      rw [e.right_inv (hBU b hb).1] at hh
      change f (e.symm b) < f z
      rw [← hh]
      exact hbr
  have hconv : Convex ℝ (B ∩ {b : ℂ | b.re < f z}) :=
    (convex_ball (e z) r).inter ((convex_Iio (f z)).linear_preimage Complex.reCLM.toLinearMap)
  have hpc : IsPreconnected (U ∩ {w | f w < f z}) := by
    rw [he]
    exact hconv.isPreconnected.image e.symm (e.continuousOn_symm.mono (by
      intro b hb; exact (hBU b hb.1).1))
  refine ⟨U,hUo,hzU,hUW,hpc,?_⟩
  rw [he]
  apply Nonempty.image
  refine ⟨e z - (r/2 : ℝ),?_,?_⟩
  · change dist (e z-(r/2 : ℝ)) (e z) < r
    rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < r/2)]
    linarith
  · change (e z - (r/2 : ℝ)).re < f z
    rw [Complex.sub_re,Complex.ofReal_re,her]
    linarith

lemma regular_level_frequently_below {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ᶠ w in 𝓝 z, f w < f z := by
  rw [frequently_iff]
  intro P hP
  obtain ⟨U,_,_,hUP,_,w,hwU,hwf⟩ := regular_level_sublevel_nhds hf hp hP
  exact ⟨w,hUP hwU,hwf⟩

lemma regular_level_local_integer {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    (hj : ContinuousOn j {w | f w ≠ c}) (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0 := by
  obtain ⟨U,hUo,hzU,_,hpc,w₀,hw₀,hfw₀⟩ := regular_level_sublevel_nhds hf hp
    (show (univ : Set ℂ) ∈ 𝓝 z from univ_mem)
  refine ⟨j w₀,?_⟩
  filter_upwards [hUo.mem_nhds hzU] with w hw hne
  by_cases hlt : f w < c
  · rw [ite_eq_left hlt]
    have hdisc := (hpc.image j (hj.mono (by
      intro v hv
      have hh : f v < f z := hv.2
      exact ne_of_lt (by simpa only [hz] using hh)))).subsingleton
    exact hdisc ⟨w,⟨hw,by change f w < f z; simpa only [hz] using hlt⟩,rfl⟩ ⟨w₀,⟨hw₀,hfw₀⟩,rfl⟩
  · rw [ite_eq_right hlt]
    exact hj0 w (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)

lemma regular_level_local_integer_unique {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    {m n : ℤ}
    (hm : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then m else 0)
    (hn : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0) : m = n := by
  obtain ⟨w,hw,hmw,hnw⟩ := ((regular_level_frequently_below hf hp).and_eventually
    (hm.and hn)).exists
  have hlt : f w < c := by simpa only [hz] using hw
  have hm' := hmw hlt.ne
  have hn' := hnw hlt.ne
  simpa only [ite_eq_left hlt] using hm'.symm.trans hn'

lemma regular_level_integer_constant_along {f : ℂ → ℝ} {j : ℂ → ℤ}
    {c : ℝ} {γ : ℝ → ℂ} (hc : Continuous γ)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t)) (hp : ∀ t, fderiv ℝ f (γ t) ≠ 0)
    (hz : ∀ t, f (γ t) = c) (hj : ContinuousOn j {w | f w ≠ c})
    (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ t, ∀ᶠ w in 𝓝 (γ t),
      f w ≠ c → j w = if f w < c then n else 0 := by
  choose n hn using fun t => regular_level_local_integer (hf t) (hp t) (hz t) hj hj0
  have hnc : Continuous n := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have he : ∀ᶠ s in 𝓝 t, n s = n t := by
      filter_upwards [(hc.tendsto t).eventually (hn t).eventually_nhds] with s hs
      exact (regular_level_local_integer_unique (hf s) (hp s) (hz s) hs (hn s)).symm
    exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  refine ⟨n 0,fun t => ?_⟩
  have he : n t = n 0 := TotallyDisconnectedSpace.eq_of_continuous n hnc t 0
  simpa only [he] using hn t

lemma regular_level_loop_local_index {f : ℂ → ℝ} {c : ℝ} {γ : ℝ → ℂ}
    (hc : Continuous γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {d : ℂ}
    (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t))
    (hreg : ∀ t, fderiv ℝ f (γ t) ≠ 0) (hz : ∀ t, f (γ t) = c)
    (hbelow : ∀ w, w ∉ range γ → loopIndex (periodicLoop hc 0) w ≠ 0 → f w < c) :
    ∀ t, ∀ᶠ w in 𝓝 (γ t), f w ≠ c →
      loopIndex (periodicLoop hc 0) w = if f w < c then 1 else 0 := by
  have hj : ContinuousOn (loopIndex (periodicLoop hc 0)) {w | f w ≠ c} :=
    (continuousOn_loopIndex _ (periodicLoop_closed hc hp 0)).mono (by
      intro w hw
      rintro ⟨t,rfl⟩
      exact hw (hz ((t:ℝ)+0)))
  have hj0 : ∀ w, c < f w → loopIndex (periodicLoop hc 0) w = 0 := by
    intro w hw
    by_contra hn
    have hwr : w ∉ range γ := by rintro ⟨t,rfl⟩; linarith [hz t]
    exact (hbelow w hwr hn).not_gt hw
  obtain ⟨n,hn⟩ := regular_level_integer_constant_along hc hf hreg hz hj hj0
  obtain ⟨δ,hδ,hjump⟩ := winding_leftmost_normal hc hp hinj hd hdi hmin
  have ht : Tendsto (fun r : ℝ => γ 0+r • (Complex.I*d)) (𝓝 0) (𝓝 (γ 0)) := by
    have h : Continuous (fun r : ℝ => γ 0+r • (Complex.I*d)) := by fun_prop
    simpa only [zero_smul,add_zero] using h.tendsto 0
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (ht.eventually (hn 0))
  let r := min δ ε /2
  have hr : 0 < r := by dsimp [r]; exact half_pos (lt_min hδ hε)
  have hrd : r ≤ δ := by dsimp [r]; linarith [min_le_left δ ε]
  have hre : r < ε := by dsimp [r]; linarith [min_le_right δ ε]
  obtain ⟨hoff,hi⟩ := hjump r hr hrd
  have hlt := hbelow _ hoff (by rw [hi]; norm_num)
  have hh := he (show r ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr] using hre) hlt.ne
  have hne : n = 1 := by simpa only [ite_eq_left hlt,hi] using hh.symm
  simpa only [hne] using hn

end Brennan

end

end OAI
