import OAI.NumberTheory.DirichletL.Eisenstein.CutoffApproximation
import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

def cubicEisensteinResidue : KernelQuotientL2 :=
  kernelEisensteinResidueVector 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_nonzero_character :
    cubicEisensteinResidue≠0 ∧
      ∀M : CubicKubota.levelThree,kernelLevelPullback M cubicEisensteinResidue=
        CubicKubota.complexCharacter M • cubicEisensteinResidue := by
  apply kernelEisensteinResidueVector_nonzero_character_of_initial_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinResidue_ne_zero : cubicEisensteinResidue≠0 :=
  cubicEisensteinResidue_nonzero_character.1

lemma cubicEisensteinResidue_character (M : CubicKubota.levelThree) :
    kernelLevelPullback M cubicEisensteinResidue=
      CubicKubota.complexCharacter M • cubicEisensteinResidue :=
  cubicEisensteinResidue_nonzero_character.2 M

lemma cubicEisensteinResidue_eigenvector :
    (cubicEisensteinResidue,(8/9:ℂ) • cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinResidueVector_graph 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_limit :
    Tendsto (fun s : ℂ => (s-4/3) • kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cubicEisensteinResidue) :=
  kernelEisensteinResidueVector_limit 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_cusp_average :
    kernelCuspStripAverage cubicEisensteinResidue=cuspConstantAverageResidue := by
  apply kernelEisensteinResidueVector_average_of_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinCorrection_not_continuousAt :
    ¬ContinuousAt (kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact cubicEisensteinResidue_ne_zero (tendsto_nhds_unique cubicEisensteinResidue_limit hh)

lemma cubicEisensteinResidue_local_limit (S : Set KernelQuotient) (hS : IsCompact S) :
    Tendsto (fun s : ℂ => (s-4/3) •
      kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet cubicEisensteinResidue)) :=
  kernelLocalCorrectedSeed_residue_limit S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_initial_ae (S : Set KernelQuotient) (hS : IsCompact S)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s : KernelQuotient→ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        S.indicator (kernelQuotientEisenstein s (by linarith)) := by
  have hlocal := kernelLocalCorrectedSeed_ae_eq S hS 2 3 (by norm_num) (by norm_num) s
  have hoverlap := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  filter_upwards [hlocal,hoverlap] with q hq hc
  rw [hq]
  by_cases hmem : q∈S
  · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem]
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hc]
    ring
  · rw [Set.indicator_of_notMem hmem,Set.indicator_of_notMem hmem]

lemma cubicEisensteinLocalFamily_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) :=
  kernelLocalCorrectedSeed_meromorphicAt S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_not_continuousAt :
    ¬ContinuousAt (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  have hnonzero : kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet cubicEisensteinResidue≠0 := by
    intro hz
    have hh := congrArg kernelCuspStripAverage hz
    rw [kernelCuspStripAverage_restrict,map_zero,cubicEisensteinResidue_cusp_average] at hh
    exact cuspConstantAverageResidue_ne_zero hh
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact hnonzero (tendsto_nhds_unique
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact) hh)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def whittakerHeight (v : ℝ) : ℝ := max 5 v
def whittakerBase (p : ℝ × ℂ) : ℝ := whittakerHeight p.1*(1+‖p.2‖^2)
def whittakerIntegrand (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  (whittakerHeight p.1:ℂ)⁻¹*(whittakerBase p:ℂ)^(-s)*
    ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)
def whittakerIntegrandDeriv (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  -(Real.log (whittakerBase p):ℂ)*whittakerIntegrand freq s p
def whittakerProductVolume : Measure (ℝ × ℂ) :=
  (volume.restrict (Set.Icc (5:ℝ) 6)).prod volume

lemma whittakerHeight_ge_one (v : ℝ) : 1≤whittakerHeight v := by
  exact (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)

lemma whittakerBase_ge (p : ℝ × ℂ) : 1+‖p.2‖^2≤whittakerBase p := by
  exact le_mul_of_one_le_left (by positivity) (whittakerHeight_ge_one p.1)

lemma whittakerBase_ge_one (p : ℝ × ℂ) : 1≤whittakerBase p :=
  (by nlinarith [sq_nonneg ‖p.2‖] : 1≤1+‖p.2‖^2).trans (whittakerBase_ge p)

lemma whittakerBase_pos (p : ℝ × ℂ) : 0<whittakerBase p :=
  zero_lt_one.trans_le (whittakerBase_ge_one p)

lemma whittakerIntegrand_continuous (freq s : ℂ) : Continuous (whittakerIntegrand freq s) := by
  have hv : Continuous (fun p : ℝ × ℂ => whittakerHeight p.1) := by
    unfold whittakerHeight
    fun_prop
  have hb : Continuous whittakerBase := by unfold whittakerBase; fun_prop
  have hp : Continuous (fun p : ℝ × ℂ => (whittakerBase p:ℂ)^(-s)) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun p => Complex.ofReal_mem_slitPlane.mpr (whittakerBase_pos p))
  have hi : Continuous (fun p : ℝ × ℂ => (whittakerHeight p.1:ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hv).inv₀ (fun p => by
      change (whittakerHeight p.1:ℂ)≠0
      exact_mod_cast (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).ne')
  have hc : Continuous (fun p : ℝ × ℂ =>
      ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)) := by
    change Continuous (fun p : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-(freq*whittakerHeight p.1)*p.2)+starRingEnd ℂ (-(freq*whittakerHeight p.1)*p.2))))
    fun_prop
  exact (hi.mul hp).mul hc

lemma whittakerIntegrandDeriv_continuous (freq s : ℂ) : Continuous (whittakerIntegrandDeriv freq s) := by
  have hb : Continuous whittakerBase := by unfold whittakerBase whittakerHeight; fun_prop
  have hl : Continuous (fun p => Real.log (whittakerBase p)) :=
    hb.log (fun p => (whittakerBase_pos p).ne')
  exact (Complex.continuous_ofReal.comp hl).neg.mul (whittakerIntegrand_continuous freq s)

lemma whittakerIntegrand_hasDerivAt (freq s : ℂ) (p : ℝ × ℂ) :
    HasDerivAt (fun w => whittakerIntegrand freq w p) (whittakerIntegrandDeriv freq s p) s := by
  have hn : (whittakerBase p:ℂ)≠0 := by exact_mod_cast (whittakerBase_pos p).ne'
  have hh := (((hasDerivAt_id s).neg.const_cpow (Or.inl hn)).const_mul
    ((whittakerHeight p.1:ℂ)⁻¹)).mul_const
      (ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2))
  convert hh using 1
  · rfl
  · rw [←Complex.ofReal_log (whittakerBase_pos p).le]
    unfold whittakerIntegrandDeriv whittakerIntegrand
    simp only [Pi.neg_apply,id_eq]
    ring

lemma whittakerIntegrand_norm (freq s : ℂ) (p : ℝ × ℂ) :
    ‖whittakerIntegrand freq s p‖=(whittakerHeight p.1)⁻¹*(whittakerBase p)^(-s.re) := by
  unfold whittakerIntegrand
  rw [norm_mul,norm_mul,breveE_norm,mul_one,norm_inv,
    Complex.norm_of_nonneg (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (whittakerBase_pos p)]
  rfl

lemma whittakerIntegrand_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)

lemma whittakerIntegrandDeriv_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b ε : ℝ) (hb : 0≤b) (hε : 0<ε) (hs : b+ε≤s.re) :
    ‖whittakerIntegrandDeriv freq s p‖≤ε⁻¹*(1+‖p.2‖^2)^(-b) := by
  have hlog := Real.log_nonneg (whittakerBase_ge_one p)
  unfold whittakerIntegrandDeriv
  rw [norm_mul,norm_neg,Complex.norm_of_nonneg hlog,whittakerIntegrand_norm]
  calc
    _ ≤ Real.log (whittakerBase p)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
          (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))) hlog
    _ ≤ ((whittakerBase p)^ε/ε)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (Real.log_le_rpow_div (whittakerBase_pos p).le hε)
        (Real.rpow_nonneg (whittakerBase_pos p).le _)
    _ = ε⁻¹*(whittakerBase p)^(ε-s.re) := by
      rw [Real.rpow_sub (whittakerBase_pos p),Real.rpow_neg (whittakerBase_pos p).le]
      ring
    _ ≤ ε⁻¹*(whittakerBase p)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)) (by positivity)
    _ ≤ ε⁻¹*(1+‖p.2‖^2)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)) (by positivity)

lemma whittaker_bound_integrable (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) whittakerProductVolume := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Icc (5:ℝ) 6)) := integrable_const _
  unfold whittakerProductVolume
  simpa only [one_mul] using hv.mul_prod hk

lemma whittakerIntegrand_integrable (freq s : ℂ) (hs : 1<s.re) :
    Integrable (whittakerIntegrand freq s) whittakerProductVolume := by
  exact (whittaker_bound_integrable s.re hs).mono'
    (whittakerIntegrand_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p => whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl))

lemma whittakerProduct_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume) (F := whittakerIntegrand freq)
    (F' := whittakerIntegrandDeriv freq)
    (bound := fun p => ε⁻¹*(1+‖p.2‖^2)^(-b)) hU
    (Eventually.of_forall (fun w => (whittakerIntegrand_continuous freq w).aestronglyMeasurable))
    (whittakerIntegrand_integrable freq s hs)
    (whittakerIntegrandDeriv_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le))
    ((whittaker_bound_integrable b hb).const_mul ε⁻¹)
    (Eventually.of_forall (fun p w _ => whittakerIntegrand_hasDerivAt freq w p))
  exact h.2.differentiableAt

lemma whittakerIntegrand_eq (freq s : ℂ) (v : ℝ) (hv : 5≤v) (z : ℂ) :
    whittakerIntegrand freq s (v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hvp : 0<v := by linarith
  have hvn : (v:ℂ)≠0 := by exact_mod_cast hvp.ne'
  have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(-s)*(v:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hvn,Complex.cpow_one,div_eq_mul_inv]
  unfold whittakerIntegrand whittakerBase whittakerHeight hyperbolicKernel
  simp only [max_eq_right hv,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hvp.le (by positivity),hp]
  ring

lemma whittakerProduct_eq_average (freq s : ℂ) (hs : 1<s.re) :
    (∫p,whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := whittakerIntegrand_integrable freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => whittakerIntegrand_eq freq s v hv.1 z)
    _ = _ := integral_const_mul _ _

theorem cuspWhittakerAverage_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (whittakerProduct_eq_average freq w hw).symm
  exact (whittakerProduct_differentiableAt freq s hs).congr_of_eventuallyEq he

end

section
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT

lemma arithmeticDirichletTerm_differentiable (h : ActualEisensteinCubic.O) (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,ite_eq_right hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma arithmeticDirichletTerm_norm_mono (h : ActualEisensteinCubic.O)
    (a : ℝ) (s : ℂ) (ha : a≤s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,ite_eq_right hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

theorem scatteringCoefficient_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd (h : ActualEisensteinCubic.O) :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

local notation "O" => ActualEisensteinCubic.O

lemma cuspPeriodStrip_measure_ne_top : hyperbolicVolume (cuspPeriodStrip 5 6)≠(⊤:ℝ≥0∞) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := hm.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hh
  rw [hh]
  exact measure_ne_top _ _

instance cuspStripFiniteVolume : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) :=
  isFiniteMeasure_restrict.mpr cuspPeriodStrip_measure_ne_top

abbrev CuspStripL2 := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip 5 6))

def kernelCuspPullback : KernelQuotientL2→L[ℂ]CuspStripL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num))).toContinuousLinearMap.comp
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet)

lemma kernelCuspPullback_ae_eq (F : KernelQuotientL2) :
    kernelCuspPullback F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip 5 6)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hr := LpToLpRestrictCLM_coeFn ℂ kernelCuspStripSet F
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hr
  have hp := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet F) hm
  filter_upwards [hp,hc] with w hw hc
  exact hw.trans hc

def cuspFourierPhase (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ShortDraftTrace.breveE (-cuspFrequency h*hyperbolicHorizontal w)

lemma cuspFourierPhase_continuous (h : ActualEisensteinCubic.O) : Continuous (cuspFourierPhase h) := by
  have hc : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
    fun_prop
  exact hc.comp hyperbolicHorizontal_continuous

lemma cuspFourierPhase_norm (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ‖cuspFourierPhase h w‖=1 :=
  breveE_norm _

lemma cuspFourierTest_memLp (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspFourierPhase h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspFourierPhase_continuous h).star.aestronglyMeasurable 1
  exact Eventually.of_forall (fun w => by rw [norm_star,cuspFourierPhase_norm])

def cuspFourierTestL2 (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspFourierTest_memLp h).toLp (fun w => star (cuspFourierPhase h w))

def kernelCuspFourier (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspFourierTestL2 h)).comp kernelCuspPullback

lemma kernelCuspFourier_integral (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspFourierPhase h w∂hyperbolicVolume := by
  change inner ℂ (cuspFourierTestL2 h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspFourierTest_memLp h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspFourier_restrict (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspFourier h F := by
  rw [kernelCuspFourier_integral,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspFourierFamily (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspFourier h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspFourierFamily_meromorphicAt (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspFourierFamily h a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspFourier h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspFourierFamily_residue_limit (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspFourierFamily h a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := (kernelCuspFourier h).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspFourier_restrict,kernelCuspFourierFamily] using hh

lemma kernelCuspFourierFamily_actual_integral (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)*
        cuspFourierPhase h w∂hyperbolicVolume := by
  rw [kernelCuspFourierFamily,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

lemma kernelCuspFourierFamily_of_initial_overlap (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hcorrected (s := kernelCuspStripSet))
  rw [kernelCuspFourierFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (kernelQuotientEisenstein_mk s hs w))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "O" => ActualEisensteinCubic.O

lemma hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspFourierPhase h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
      cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    rw [eisensteinFourierCoefficient]
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  dsimp only
  rw [hh,eisensteinFourierCoefficient_formula v hpos s hs h]

def cuspWhittakerHeightFactor (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)

lemma hyperbolicEisenstein_cusp_fourier_nonzero (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [hyperbolicEisenstein_cusp_fourier_average s hs h]
  simp only [ite_eq_right hh,zero_add]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
        ((9*Real.sqrt 3/2:ℝ):ℂ)/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma cuspWhittakerHeightFactor_bessel (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWhittakerHeightFactor s h=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*
        ((2*Real.pi:ℂ)/Complex.Gamma s*
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖)) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_bessel s _ hs
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hpos.ne'))]

def kernelResidualFourierDatum (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) : ℂ :=
  kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab)

lemma kernelCuspFourierFamily_nonzero_of_initial_overlap (h : ActualEisensteinCubic.O) (hh : h≠0)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [kernelCuspFourierFamily_of_initial_overlap h a b ha hab s hs hoverlap,
    hyperbolicEisenstein_cusp_fourier_nonzero s hs h hh]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceFourierKernel_continuous_freq (s : ℂ) (hs : 1<s.re) :
    Continuous (sourceFourierKernel s) := by
  change Continuous (fun freq : ℂ => ∫z : ℂ,hyperbolicKernel s z*ShortDraftTrace.breveE (-freq*z))
  apply continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖)
  · exact fun freq => (sourceFourierKernel_integrable s freq hs).aestronglyMeasurable
  · exact fun freq => Eventually.of_forall (fun z => by rw [norm_mul,breveE_norm,mul_one])
  · exact (hyperbolicKernel_integrable s hs).norm
  · filter_upwards with z
    change Continuous (fun freq : ℂ => hyperbolicKernel s z*
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop

lemma schlafliIntegrand_real (nu x t : ℝ) (ht : 0<t) :
    (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))=
      ((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) := by
  have hp := Complex.ofReal_cpow ht.le (nu-1)
  simp only [Complex.ofReal_sub,Complex.ofReal_one] at hp
  rw [Complex.ofReal_mul,hp,Complex.ofReal_exp]
  congr 2
  push_cast
  rfl

lemma schlafliIntegral_real_re_pos (nu x : ℝ) (hnu : 0<nu) :
    0<(schlafliIntegral (nu:ℂ) x).re := by
  let f : ℝ→ℂ := fun t => (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))
  have hi : IntegrableOn f (Set.Ioi (0:ℝ)) volume := schlafliIntegral_integrable (nu:ℂ) x hnu
  have hp (t : ℝ) (ht : 0<t) : 0<(f t).re := by
    rw [show f t=((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) from schlafliIntegrand_real nu x t ht,
      Complex.ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  change 0<RCLike.re (∫t in Set.Ioi (0:ℝ),f t)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun t => RCLike.re (f t))=ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp t ht).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le

lemma sourceFourierKernel_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (freq : ℂ) :
    0<(sourceFourierKernel (sigma:ℂ) freq).re := by
  have hh := sourceFourierKernel_gamma_schlafli (sigma:ℂ) freq hsigma
  have hre := congrArg Complex.re hh
  have hsch : 0<(schlafliIntegral ((sigma:ℂ)-1) (4*Real.pi*‖freq‖)).re := by
    convert schlafliIntegral_real_re_pos (sigma-1) (4*Real.pi*‖freq‖) (by linarith) using 1 ; push_cast ; rfl
  rw [Complex.Gamma_ofReal] at hre
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at hre
  have hg := Real.Gamma_pos_of_pos (show 0<sigma by linarith)
  have hp := mul_pos Real.pi_pos hsch
  nlinarith

lemma cuspWhittakerHeightFactor_integrable (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))
      (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  exact ((Complex.continuousAt_ofReal_cpow_const v (-s-1) (Or.inr hpos.ne')).mul
    ((sourceFourierKernel_continuous_freq s hs).continuousAt.comp
      ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt

lemma cuspWhittakerHeightFactor_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (h : ActualEisensteinCubic.O) :
    0<(cuspWhittakerHeightFactor (sigma:ℂ) h).re := by
  let f : ℝ→ℂ := fun v => (v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)
  have hi : IntegrableOn f (Set.Icc (5:ℝ) 6) volume :=
    cuspWhittakerHeightFactor_integrable (sigma:ℂ) hsigma h
  have hp (v : ℝ) (hv : v∈Set.Icc (5:ℝ) 6) : 0<(f v).re := by
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have he := Complex.ofReal_cpow hpos.le (-sigma-1)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one] at he
    change 0<((v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)).re
    rw [←he,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hpos _) (sourceFourierKernel_real_re_pos sigma hsigma _)
  change 0<RCLike.re (∫v in Set.Icc (5:ℝ) 6,f v)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun v => RCLike.re (f v))=ᵐ[volume.restrict (Set.Icc (5:ℝ) 6)] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp v hv).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hp v hv).le

lemma cuspWhittakerHeightFactor_center_ne_zero (h : ActualEisensteinCubic.O) :
    cuspWhittakerHeightFactor (4/3:ℂ) h≠0 := by
  intro he
  have hh := cuspWhittakerHeightFactor_real_re_pos (4/3:ℝ) (by norm_num) h
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [he,Complex.zero_re] at hh
  exact lt_irrefl 0 hh

end CubicEisenstein

end

end OAI
