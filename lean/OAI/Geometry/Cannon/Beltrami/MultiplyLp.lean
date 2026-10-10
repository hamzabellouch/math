import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma memLp_multiply (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    MemLp (fun x => m x*f x) 2 ν := by
  apply (Lp.memLp f).of_le_mul (c:=k) (hm.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖m x*f x‖ ≤ k*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def multiplyLp (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) : Lp ℂ 2 ν :=
  (memLp_multiply m hm hb f).toLp

lemma multiplyLp_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplyLp m hm hb f =ᵐ[ν] fun x => m x*f x :=
  MemLp.coeFn_toLp _

lemma multiplyLp_add (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f g : Lp ℂ 2 ν) :
    multiplyLp m hm hb (f+g)=multiplyLp m hm hb f+multiplyLp m hm hb g := by
  apply Lp.ext
  filter_upwards [multiplyLp_ae m hm hb (f+g),multiplyLp_ae m hm hb f,
    multiplyLp_ae m hm hb g,Lp.coeFn_add f g,
    Lp.coeFn_add (multiplyLp m hm hb f) (multiplyLp m hm hb g)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1,h5,h2,h3,h4,mul_add]

lemma multiplyLp_smul (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (c : ℂ) (f : Lp ℂ 2 ν) :
    multiplyLp m hm hb (c • f)=c • multiplyLp m hm hb f := by
  apply Lp.ext
  filter_upwards [multiplyLp_ae m hm hb (c • f),multiplyLp_ae m hm hb f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (multiplyLp m hm hb f)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply,smul_eq_mul] at h3 h4
  rw [h1,h4,h2,h3]
  exact mul_left_comm _ _ _

lemma norm_multiplyLp_le (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (_hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    ‖multiplyLp m hm hb f‖ ≤ k*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyLp_ae m hm hb f,hb] with x hx hx'
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hx' (norm_nonneg _)

def multiplier (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    { toFun := multiplyLp m hm hb
      map_add' := multiplyLp_add m hm hb
      map_smul' := multiplyLp_smul m hm hb }
    k (norm_multiplyLp_le m hm hk hb)

lemma multiplier_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplier m hm hk hb f =ᵐ[ν] fun x => m x*f x := multiplyLp_ae m hm hb f

lemma norm_multiplier_le (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) :
    ‖multiplier m hm hk hb‖ ≤ k := LinearMap.mkContinuous_norm_le _ hk _

lemma norm_multiplier_eq (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    (hunit : ∀ᵐ x ∂ν, ‖m x‖=1) (f : Lp ℂ 2 ν) :
    ‖multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f‖=‖f‖ := by
  let g := multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f
  have he : ∀ᵐ x ∂ν, ‖g x‖=‖f x‖ := by
    filter_upwards [multiplier_ae m hm zero_le_one (hunit.mono (fun _ h => h.le)) f,hunit] with x hx hx'
    dsimp [g]
    rw [hx,norm_mul,hx',one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

abbrev PlaneL2 := Lp (α:=ℂ) ℂ 2 volume

def beurlingSymbol (z : ℂ) : ℂ := if z=0 then 1 else star z/z

lemma measurable_beurlingSymbol : Measurable beurlingSymbol := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (continuous_star.measurable.div measurable_id)

lemma norm_beurlingSymbol (z : ℂ) : ‖beurlingSymbol z‖=1 := by
  by_cases hz : z=0
  · simp [beurlingSymbol,hz]
  · simp [beurlingSymbol,hz,norm_ne_zero_iff.mpr hz]

def symbolMultiplier : PlaneL2 →L[ℂ] PlaneL2 :=
  multiplier beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable zero_le_one
    (.of_forall (fun z => (norm_beurlingSymbol z).le))

def planeFourier : PlaneL2 ≃ₗᵢ[ℂ] PlaneL2 := Lp.fourierTransformₗᵢ ℂ ℂ

def beurling : PlaneL2 →L[ℂ] PlaneL2 :=
  planeFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (symbolMultiplier.comp planeFourier.toContinuousLinearEquiv.toContinuousLinearMap)

lemma norm_symbolMultiplier (f : PlaneL2) : ‖symbolMultiplier f‖=‖f‖ :=
  norm_multiplier_eq beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable
    (.of_forall norm_beurlingSymbol) f

lemma norm_beurling (f : PlaneL2) : ‖beurling f‖=‖f‖ := by
  change ‖planeFourier.symm (symbolMultiplier (planeFourier f))‖=‖f‖
  rw [planeFourier.symm.norm_map,norm_symbolMultiplier,planeFourier.norm_map]

lemma fourier_beurling_ae (f : PlaneL2) :
    planeFourier (beurling f) =ᵐ[volume] fun z => beurlingSymbol z*planeFourier f z := by
  have he : planeFourier (beurling f)=symbolMultiplier (planeFourier f) :=
    planeFourier.apply_symm_apply _
  rw [he]
  exact multiplier_ae _ _ _ _ _

theorem solve_beltrami_l2 (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k)
    (b : PlaneL2) :
    ∃ h : PlaneL2, h-multiplier μ hm hk hb (beurling h)=b ∧
      ‖h‖ ≤ ‖b‖/(1-k) ∧
      ∀ h' : PlaneL2, h'-multiplier μ hm hk hb (beurling h')=b → h'=h := by
  let T : PlaneL2 →L[ℂ] PlaneL2 := (multiplier μ hm hk hb).comp beurling
  have hT (h : PlaneL2) : ‖T h‖ ≤ k*‖h‖ := by
    change ‖multiplyLp μ hm hb (beurling h)‖ ≤ k*‖h‖
    exact (norm_multiplyLp_le μ hm hk hb (beurling h)).trans_eq (by rw [norm_beurling])
  let f : PlaneL2 → PlaneL2 := fun h => T h+b
  have hf : ContractingWith ⟨k,hk⟩ f := by
    refine ⟨hk1, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x+b) (T y+b) ≤ k*dist x y
    rw [dist_add_right,dist_eq_norm,← map_sub,dist_eq_norm]
    exact hT (x-y)
  let h := hf.fixedPoint f
  have hfix : f h=h := hf.fixedPoint_isFixedPt
  have heq : h-T h=b := by dsimp [f] at hfix; exact sub_eq_iff_eq_add.mpr (hfix.symm.trans (add_comm _ _))
  refine ⟨h,heq,?_,?_⟩
  · apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    have hn : ‖h‖ ≤ k*‖h‖+‖b‖ := by
      calc
        ‖h‖ = ‖T h+b‖ := congrArg norm hfix.symm
        _ ≤ ‖T h‖+‖b‖ := norm_add_le _ _
        _ ≤ k*‖h‖+‖b‖ := add_le_add (hT h) le_rfl
    nlinarith
  · intro h' hh'
    apply hf.fixedPoint_unique
    change T h'+b=h'
    change h'-T h'=b at hh'
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hh').symm

open FourierTransform

def translateL2 (a : ℂ) : PlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℂ => z+a) (measurePreserving_add_right volume a)

lemma translateL2_ae (a : ℂ) (f : PlaneL2) :
    translateL2 a f =ᵐ[volume] fun z => f (z+a) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma translate_schwartz (a : ℂ) (f : SchwartzMap ℂ ℂ) :
    translateL2 a (f.toLp 2)=(f.compSubConstCLM ℂ (-a)).toLp 2 := by
  change Lp.compMeasurePreserving _ _ ((f.memLp 2 volume).toLp f)=_
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp ((f.memLp 2 volume).comp_measurePreserving
    (measurePreserving_add_right volume a)),(f.compSubConstCLM ℂ (-a)).coeFn_toLp 2 volume] with z h1 h2
  rw [h1,h2]
  simp

def translationPhase (a z : ℂ) : ℂ := Real.fourierChar (inner ℝ a z)

lemma continuous_translationPhase (a : ℂ) : Continuous (translationPhase a) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

lemma norm_translationPhase (a z : ℂ) : ‖translationPhase a z‖=1 := Circle.norm_coe _

def phaseMultiplier (a : ℂ) : PlaneL2 →L[ℂ] PlaneL2 :=
  multiplier (translationPhase a) (continuous_translationPhase a).aestronglyMeasurable
    zero_le_one (.of_forall fun z => (norm_translationPhase a z).le)

lemma fourier_translate_schwartz (a : ℂ) (f : SchwartzMap ℂ ℂ) :
    planeFourier (translateL2 a (f.toLp 2))=phaseMultiplier a (planeFourier (f.toLp 2)) := by
  rw [translate_schwartz]
  change 𝓕 ((f.compSubConstCLM ℂ (-a)).toLp 2)=phaseMultiplier a (𝓕 (f.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ (-a))).coeFn_toLp 2 volume,
    multiplier_ae (translationPhase a) (continuous_translationPhase a).aestronglyMeasurable
      zero_le_one (.of_forall fun z => (norm_translationPhase a z).le) ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2 volume] with z h1 h2 h3
  dsimp only [phaseMultiplier]
  rw [h1,h2,h3]
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℂ) (f : ℂ → ℂ) a) z
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ)
    (fun z => f (z- -a)) z = translationPhase a z*
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℂ) (f : ℂ → ℂ) z
  simpa only [Function.comp_def,translationPhase,innerₗ_apply_apply,
    sub_neg_eq_add,Circle.smul_def,smul_eq_mul] using he

lemma fourier_translateL2 (a : ℂ) (f : PlaneL2) :
    planeFourier (translateL2 a f)=phaseMultiplier a (planeFourier f) := by
  have he := (SchwartzMap.denseRange_toLpCLM (E:=ℂ) (F:=ℂ) (μ:=volume)
    (p:=2) (by norm_num)).equalizer
      (planeFourier.continuous.comp (translateL2 a).continuous)
      ((phaseMultiplier a).continuous.comp planeFourier.continuous)
      (funext (fun s => fourier_translate_schwartz a s))
  exact congrFun he f

lemma multipliers_commute (m n : ℂ → ℂ)
    (hm : AEStronglyMeasurable m volume) (hn : AEStronglyMeasurable n volume)
    {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hb : ∀ᵐ z ∂volume, ‖m z‖ ≤ k) (hc : ∀ᵐ z ∂volume, ‖n z‖ ≤ l) (f : PlaneL2) :
    multiplier m hm hk hb (multiplier n hn hl hc f)=
      multiplier n hn hl hc (multiplier m hm hk hb f) := by
  apply Lp.ext
  filter_upwards [multiplier_ae m hm hk hb (multiplier n hn hl hc f),
    multiplier_ae n hn hl hc (multiplier m hm hk hb f),
    multiplier_ae m hm hk hb f,multiplier_ae n hn hl hc f] with z h1 h2 h3 h4
  rw [h1,h2,h3,h4,mul_left_comm]

lemma translate_beurling (a : ℂ) (f : PlaneL2) :
    translateL2 a (beurling f)=beurling (translateL2 a f) := by
  apply planeFourier.injective
  have hf (g : PlaneL2) : planeFourier (beurling g)=symbolMultiplier (planeFourier g) :=
    planeFourier.apply_symm_apply _
  rw [fourier_translateL2,hf,hf,fourier_translateL2]
  exact multipliers_commute _ _ _ _ _ _ _ _ _

def directionSymbol (v z : ℂ) : ℂ := 2*Real.pi*Complex.I*(inner ℝ v z : ℝ)

lemma continuous_directionSymbol (v : ℂ) : Continuous (directionSymbol v) := by
  unfold directionSymbol
  fun_prop

lemma translationPhase_derivative (v z : ℂ) :
    HasDerivAt (fun t : ℝ => translationPhase (t • v) z) (directionSymbol v z) 0 := by
  have h := (Real.hasDerivAt_fourierChar (0*(inner ℝ v z))).scomp 0
    ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ v z))
  simpa [translationPhase,directionSymbol,inner_smul_left,Complex.real_smul,
    Function.comp_def,mul_comm,mul_left_comm,mul_assoc,mul_add] using h

lemma translationPhase_slope (v z : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (translationPhase (t • v) z-1))
      (𝓝[≠] 0) (𝓝 (directionSymbol v z)) := by
  simpa [translationPhase] using (translationPhase_derivative v z).tendsto_slope_zero

theorem memLp_directionSymbol_of_translation_bound (f : PlaneL2)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : ℂ, ‖translateL2 a f-f‖ ≤ C*‖a‖) (v : ℂ) :
    MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume ∧
      eLpNorm (fun z => directionSymbol v z*planeFourier f z) 2 volume ≤
        ENNReal.ofReal (C*‖v‖) := by
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f)
  let F (t : ℝ) (z : ℂ) := (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z
  have hnorm (t : ℝ) : ‖q t‖ ≤ C*‖v‖ := by
    by_cases ht : t=0
    · simp [q,ht,mul_nonneg hC (norm_nonneg v)]
    · calc
        ‖q t‖ = |t|⁻¹*‖translateL2 (t • v) f-f‖ := by
          simp only [q,norm_smul,Real.norm_eq_abs,abs_inv,← map_sub,planeFourier.norm_map]
        _ ≤ |t|⁻¹*(C*‖t • v‖) :=
          mul_le_mul_of_nonneg_left (hb (t • v)) (inv_nonneg.mpr (abs_nonneg _))
        _ = C*‖v‖ := by
          rw [norm_smul,Real.norm_eq_abs]
          field_simp
  have hae (t : ℝ) : q t =ᵐ[volume] F t := by
    have ht := fourier_translateL2 (t • v) f
    filter_upwards [Lp.coeFn_smul (t⁻¹) (planeFourier (translateL2 (t • v) f)-planeFourier f),
      Lp.coeFn_sub (planeFourier (translateL2 (t • v) f)) (planeFourier f),
      multiplier_ae (translationPhase (t • v)) _ zero_le_one
        (.of_forall fun z => (norm_translationPhase (t • v) z).le) (planeFourier f)] with z h1 h2 h3
    dsimp only [q,F]
    simp only [Pi.smul_apply,Pi.sub_apply] at h1 h2
    rw [h1,h2,ht]
    change t⁻¹ • (phaseMultiplier (t • v) (planeFourier f) z-planeFourier f z)=_
    dsimp only [phaseMultiplier]
    rw [h3]
    simp only [smul_mul_assoc,sub_mul,one_mul]
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) volume :=
    ((Lp.memLp (q t)).aestronglyMeasurable.congr (hae t))
  have hbound : ∀ t, eLpNorm (F t) 2 volume ≤ ENNReal.ofReal (C*‖v‖) := by
    intro t
    rw [← eLpNorm_congr_ae (hae t),← Lp.enorm_def,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hnorm t)
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => F t z) (𝓝[≠] 0)
      (𝓝 (directionSymbol v z*planeFourier f z)) := by
    exact .of_forall fun z => (translationPhase_slope v z).mul_const (planeFourier f z)
  have hmeas := (continuous_directionSymbol v).aestronglyMeasurable.mul
    (Lp.memLp (planeFourier f)).aestronglyMeasurable
  have he := Lp.eLpNorm_le_of_ae_tendsto (.of_forall hbound) hFm hmeas hlim
  exact ⟨he.trans_lt ENNReal.ofReal_lt_top,he⟩

open scoped ENNReal

lemma dominated_toLp_zero_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → ℂ} (hf : ∀ n, MemLp (f n) 2 ν)
    {g : X → ℂ} (hg : MemLp g 2 ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 0) := by
  have hb' : ∀ n, (fun x => ‖f n x‖ₑ ^ (2:ℝ)) ≤ᵐ[ν] (fun x => ‖g x‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hb n] with x hx
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr hx) (by norm_num)
  have hfin : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂ν) ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num) hg).ne
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x‖ₑ ^ (2:ℝ)) l (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hl] with x hx
    have hc : Continuous (fun t : ℝ≥0∞ => t^(2:ℝ)) := ENNReal.continuous_rpow_const
    simpa only [Function.comp_def,enorm, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2)] using
      hc.continuousAt.tendsto.comp (ENNReal.tendsto_coe.mpr hx.nnnorm)
  have hi := tendsto_lintegral_filter_of_dominated_convergence' _
    (.of_forall fun n => (hf n).aestronglyMeasurable.enorm.pow_const (2:ℝ))
    (.of_forall hb') hfin hlim
  have heLp : Tendsto (fun n => eLpNorm (f n) 2 ν) l (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (hf _).aestronglyMeasurable]
    have hc : Continuous (fun t : ℝ≥0∞ => t^(1/2:ℝ)) := ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hi
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (0 : X → ℂ) (MemLp.zero : MemLp (0 : X → ℂ) 2 ν)).mpr
    (by simpa using heLp)
  simpa using h

lemma phase_slope_norm_le (v z : ℂ) (t : ℝ) :
    ‖t⁻¹ • (translationPhase (t • v) z-1)‖ ≤ ‖directionSymbol v z‖ := by
  by_cases ht : t=0
  · simp [ht]
  have he : translationPhase (t • v) z=
      Complex.exp (Complex.I*((2*Real.pi*(t*(inner ℝ v z)):ℝ):ℂ)) := by
    simp [translationPhase,Real.fourierChar_apply,
      mul_comm,mul_left_comm,mul_assoc,mul_add,add_mul]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*(t*(inner ℝ v z)))
  rw [← he] at hh
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    |t|⁻¹*‖translationPhase (t • v) z-1‖ ≤
        |t|⁻¹*‖2*Real.pi*(t*(inner ℝ v z))‖ :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = ‖directionSymbol v z‖ := by
      simp only [directionSymbol,norm_mul,Complex.norm_I,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2),mul_one]
      norm_num
      field_simp

lemma fourier_difference_quotient_ae (f : PlaneL2) (v : ℂ) (t : ℝ) :
    (t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f) : PlaneL2) =ᵐ[volume]
      fun z => (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z := by
  have ht := fourier_translateL2 (t • v) f
  filter_upwards [Lp.coeFn_smul (t⁻¹) (planeFourier (translateL2 (t • v) f)-planeFourier f),
    Lp.coeFn_sub (planeFourier (translateL2 (t • v) f)) (planeFourier f),
    multiplier_ae (translationPhase (t • v)) _ zero_le_one
      (.of_forall fun z => (norm_translationPhase (t • v) z).le) (planeFourier f)] with z h1 h2 h3
  simp only [Pi.smul_apply,Pi.sub_apply] at h1 h2
  rw [h1,h2,ht]
  dsimp only [phaseMultiplier]
  rw [h3]
  simp only [smul_mul_assoc,sub_mul,one_mul]

lemma translateL2_zero (f : PlaneL2) : translateL2 0 f=f := by
  apply Lp.ext
  simpa using translateL2_ae 0 f

theorem hasDerivAt_translateL2 (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume) :
    HasDerivAt (fun t : ℝ => translateL2 (t • v) f)
      (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z))) 0 := by
  let g (z : ℂ) := directionSymbol v z*planeFourier f z
  let F (t : ℝ) (z : ℂ) := (t⁻¹ • (translationPhase (t • v) z-1))*planeFourier f z
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (planeFourier (translateL2 (t • v) f)-planeFourier f)
  have hae (t : ℝ) : q t =ᵐ[volume] F t := fourier_difference_quotient_ae f v t
  have hF (t : ℝ) : MemLp (F t) 2 volume := MemLp.ae_eq (hae t) (Lp.memLp (q t))
  have hE (t : ℝ) : (hF t).toLp (F t)=q t := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hF t)).trans (hae t).symm
  have hdom (t : ℝ) : ∀ᵐ z ∂volume, ‖(F t-g) z‖ ≤ ‖(2:ℂ)*g z‖ := by
    apply Filter.Eventually.of_forall
    intro z
    change ‖F t z-g z‖ ≤ ‖(2:ℂ)*g z‖
    calc
      ‖F t z-g z‖ ≤ ‖F t z‖+‖g z‖ := norm_sub_le _ _
      _ ≤ ‖directionSymbol v z‖*‖planeFourier f z‖+‖g z‖ := by
        gcongr
        exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right
          (phase_slope_norm_le v z t) (norm_nonneg _))
      _ = ‖(2:ℂ)*g z‖ := by simp [g]; ring
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun t : ℝ => (F t-g) z) (𝓝[≠] 0) (𝓝 0) := by
    exact .of_forall fun z => by
      simpa only [F,g,Pi.sub_apply,sub_self] using
        ((translationPhase_slope v z).mul_const (planeFourier f z)).sub_const (g z)
  have hzero := dominated_toLp_zero_filter (fun t => (hF t).sub hd)
    (hd.const_mul (2:ℂ)) hdom hlim
  change Tendsto (fun t => (hF t).toLp (F t)-hd.toLp g) (𝓝[≠] 0) (𝓝 0) at hzero
  simp only [hE] at hzero
  have ht : Tendsto q (𝓝[≠] 0) (𝓝 (hd.toLp g)) := by
    simpa using hzero.add_const (hd.toLp g)
  have hi := planeFourier.symm.continuous.continuousAt.tendsto.comp ht
  have hsmul (t : ℝ) (x : PlaneL2) : planeFourier.symm (t • x)=t • planeFourier.symm x :=
    planeFourier.symm.toLinearEquiv.toLinearMap.map_smul_of_tower t x
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [Function.comp_def,q,zero_add,zero_smul,translateL2_zero,
    hsmul,map_sub,planeFourier.symm_apply_apply] using hi

lemma translate_toLp_ae {F : ℂ → ℂ} (hF : MemLp F 2 volume) (w : ℂ) :
    translateL2 w (hF.toLp F) =ᵐ[volume] fun x => F (x+w) := by
  exact (translateL2_ae w (hF.toLp F)).trans
    ((measurePreserving_add_right volume w).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hF))

theorem translation_bound_of_increment_bound {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => F (x+w)-F x) 2 volume ≤ ENNReal.ofReal (C*‖w‖)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, ‖translateL2 w (hF.toLp F)-hF.toLp F‖ ≤ D*‖w‖ := by
  let f := hF.toLp F
  refine ⟨max C (2*‖f‖),hC.trans (le_max_left _ _),fun w => ?_⟩
  by_cases hw : ‖w‖ ≤ 1
  · have hae : translateL2 w f-f =ᵐ[volume] fun x => F (x+w)-F x :=
      (Lp.coeFn_sub _ _).trans ((translate_toLp_ae hF w).sub (MemLp.coeFn_toLp hF))
    have he : eLpNorm (fun x => (translateL2 w f-f) x) 2 volume ≤ ENNReal.ofReal (C*‖w‖) := by
      rw [eLpNorm_congr_ae hae]
      exact hb w hw
    have hn : ‖translateL2 w f-f‖ ≤ C*‖w‖ := by
      rw [Lp.norm_def]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _)))
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · calc
      _ ≤ ‖translateL2 w f‖+‖f‖ := norm_sub_le _ _
      _ = 2*‖f‖ := by rw [(translateL2 w).norm_map]; ring
      _ ≤ (2*‖f‖)*‖w‖ := le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem translation_derivative_eq_ae {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x) (v : ℂ) (g : PlaneL2)
    (hg : HasDerivAt (fun t : ℝ => translateL2 (t • v) (hF.toLp F)) g 0) :
    g =ᵐ[volume] fun x => fderiv ℝ F x v := by
  let q (t : ℝ) : PlaneL2 := t⁻¹ • (translateL2 (t • v) (hF.toLp F)-hF.toLp F)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 g) := by
    simpa only [q,zero_add,zero_smul,translateL2_zero] using hg.tendsto_slope_zero
  obtain ⟨t,ht,ha⟩ := (tendstoInMeasure_of_tendsto_Lp hq).exists_seq_tendsto_ae'
  have he (n : ℕ) : q (t n) =ᵐ[volume] fun x => (t n)⁻¹ • (F (x+(t n) • v)-F x) := by
    filter_upwards [Lp.coeFn_smul ((t n)⁻¹) (translateL2 ((t n) • v) (hF.toLp F)-hF.toLp F),
      Lp.coeFn_sub (translateL2 ((t n) • v) (hF.toLp F)) (hF.toLp F),
      translate_toLp_ae hF ((t n) • v),MemLp.coeFn_toLp hF] with x h1 h2 h3 h4
    dsimp only [q]
    rw [h1]
    dsimp only [Pi.smul_apply]
    rw [h2]
    dsimp only [Pi.sub_apply]
    rw [h3,h4]
  filter_upwards [hFd,ha,ae_all_iff.mpr he] with x hdx hax hex
  have hv : HasDerivAt (fun s : ℝ => x+s • v) v 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun s : ℝ => F (x+s • v)) (fderiv ℝ F x v) 0 := by
    have hx' : HasFDerivAt F (fderiv ℝ F x) (x+(0:ℝ) • v) := by simpa using hdx.hasFDerivAt
    exact hx'.comp_hasDerivAt 0 hv
  have hp : Tendsto (fun s : ℝ => s⁻¹ • (F (x+s • v)-F x)) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ F x v)) := by
    simpa only [zero_add,zero_smul,add_zero] using hd.tendsto_slope_zero
  apply tendsto_nhds_unique hax
  exact (hp.comp ht).congr (fun n => (hex n).symm)

theorem memLp_fderiv_of_increment_bound {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => F (x+w)-F x) 2 volume ≤ ENNReal.ofReal (C*‖w‖)) (v : ℂ) :
    MemLp (fun x => fderiv ℝ F x v) 2 volume ∧
    ∃ g : PlaneL2, g =ᵐ[volume] (fun x => fderiv ℝ F x v) ∧
      HasDerivAt (fun t : ℝ => translateL2 (t • v) (hF.toLp F)) g 0 := by
  obtain ⟨D,hD,hd⟩ := translation_bound_of_increment_bound hF hC hb
  have hm := (memLp_directionSymbol_of_translation_bound (hF.toLp F) hD hd v).1
  let g : PlaneL2 := planeFourier.symm (hm.toLp _)
  have hg := hasDerivAt_translateL2 (hF.toLp F) v hm
  have he : g =ᵐ[volume] fun x => fderiv ℝ F x v := translation_derivative_eq_ae hF hFd v g hg
  exact ⟨(Lp.memLp g).ae_eq he, g,he,hg⟩
end CannonBeltrami

namespace CannonBeltrami
open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap

lemma fourier_derivative_distribution (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume) :
    ∂_{v} (f : 𝓢'(ℂ,ℂ)) =
      (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z)) : PlaneL2) := by
  apply (fourierCLE ℂ 𝓢'(ℂ,ℂ)).injective
  simp only [fourierCLE_apply]
  rw [TemperedDistribution.fourier_lineDerivOp_eq,Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq]
  have he : 𝓕 (planeFourier.symm (hd.toLp (fun z => directionSymbol v z*planeFourier f z)))=
      hd.toLp (fun z => directionSymbol v z*planeFourier f z) := planeFourier.apply_symm_apply _
  rw [he]
  ext φ
  have ht : (fun z : ℂ => ((inner ℝ z v):ℂ)).HasTemperateGrowth := by fun_prop
  simp only [smul_apply,TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hd] with z hz
  rw [hz]
  dsimp only [directionSymbol]
  simp only [SchwartzMap.smulLeftCLM_apply ht,smul_eq_mul]
  rw [real_inner_comm v z]
  change (2*Real.pi*Complex.I)*((inner ℝ v z:ℝ)*φ z*planeFourier f z)=
    φ z*(2*Real.pi*Complex.I*(inner ℝ v z:ℝ)*planeFourier f z)
  ring

lemma fourier_derivative_weak (f : PlaneL2) (v : ℂ)
    (hd : MemLp (fun z => directionSymbol v z*planeFourier f z) 2 volume)
    (φ : SchwartzMap ℂ ℂ) :
    (∫ z, φ z*(planeFourier.symm (hd.toLp _) : PlaneL2) z)=
      -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*f z) := by
  have h := congrArg (fun T : 𝓢'(ℂ,ℂ) => T φ) (fourier_derivative_distribution f v hd)
  simpa only [TemperedDistribution.lineDerivOp_apply_apply,Lp.toTemperedDistribution_apply,
    neg_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,smul_eq_mul,neg_mul,integral_neg] using h.symm

theorem weak_fderiv_of_increment_bound {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hFd : ∀ᵐ x ∂volume, DifferentiableAt ℝ F x)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w : ℂ, ‖w‖ ≤ 1 →
      eLpNorm (fun x => F (x+w)-F x) 2 volume ≤ ENNReal.ofReal (C*‖w‖)) (v : ℂ) :
    MemLp (fun x => fderiv ℝ F x v) 2 volume ∧
      ∀ φ : SchwartzMap ℂ ℂ, (∫ z, φ z*fderiv ℝ F z v)=
        -(∫ z, (fderiv ℝ (φ : ℂ → ℂ) z v)*F z) := by
  obtain ⟨D,hD,hd⟩ := translation_bound_of_increment_bound hF hC hb
  have hm := (memLp_directionSymbol_of_translation_bound (hF.toLp F) hD hd v).1
  let g : PlaneL2 := planeFourier.symm (hm.toLp _)
  have hg := hasDerivAt_translateL2 (hF.toLp F) v hm
  have he : g =ᵐ[volume] fun x => fderiv ℝ F x v := translation_derivative_eq_ae hF hFd v g hg
  refine ⟨(Lp.memLp g).ae_eq he,fun φ => ?_⟩
  have hh := fourier_derivative_weak (hF.toLp F) v hm φ
  calc
    _ = ∫ z, φ z*g z := integral_congr_ae (he.symm.mono (fun z hz => by simpa only using congrArg (fun u => φ z*u) hz))
    _ = -(∫ z, fderiv ℝ (φ : ℂ → ℂ) z v*(hF.toLp F) z) := hh
    _ = _ := by
      congr 1
      exact integral_congr_ae ((MemLp.coeFn_toLp hF).mono (fun z hz => by simpa only using congrArg (fun u => fderiv ℝ (φ : ℂ → ℂ) z v*u) hz))
end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
