import OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def cuspTransition (a b v : ℝ) : ℝ := Real.smoothTransition ((v-a)/(b-a))

lemma cuspTransition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cuspTransition a b) := by
  unfold cuspTransition
  fun_prop

lemma cuspTransition_zero (a b v : ℝ) (hab : a<b) (hv : v≤a) : cuspTransition a b v=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (sub_pos.mpr hab).le)
lemma cuspTransition_one (a b v : ℝ) (hab : a<b) (hv : b≤v) : cuspTransition a b v=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma cuspTransition_derivatives (a b v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    deriv (cuspTransition a b) v=0 ∧ deriv (deriv (cuspTransition a b)) v=0 := by
  rcases hv with hv | hv
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspTransition_zero a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      exact cuspTransition_one a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩

def positiveHeightPower (s : ℂ) (v : ℝ) : ℂ := logRatioPower s v 1
lemma positiveHeightPower_eq_cpow (s : ℂ) (v : ℝ) (hv : 0<v) :
    positiveHeightPower s v=(v:ℂ)^s := by
  simpa only [positiveHeightPower,div_one] using logRatioPower_eq_cpow s hv (by norm_num : (0:ℝ)<1)

lemma positiveHeightPower_hasDerivAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (positiveHeightPower s) (positiveHeightPower s v*s/(v:ℂ)) v := by
  convert hasDerivAt_logRatioPower s (hasDerivAt_id v) (hasDerivAt_const v (1:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp [positiveHeightPower,div_eq_mul_inv]

lemma positiveHeightPower_hasDerivAt_deriv (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (positiveHeightPower s))
      (positiveHeightPower s v*s*(s-1)/(v:ℂ)^2) v := by
  convert hasDerivAt_deriv_logRatioPower s id (fun _ => 1) (fun _ => 1) (fun _ => 0) v 0 0
    (fun x => hasDerivAt_id x) (fun x => hasDerivAt_const x (1:ℝ))
    (hasDerivAt_const v (1:ℝ)) (hasDerivAt_const v (0:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp only [id_eq,zero_mul,mul_one,sub_self,sub_zero,one_pow,div_one,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,
      Complex.ofReal_zero,positiveHeightPower]
    field_simp [Complex.ofReal_ne_zero.mpr hv]
    ; ring

def cuspSeedProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (cuspTransition a b v:ℂ)*positiveHeightPower s v

lemma cuspSeedProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v≤a) :
    cuspSeedProfile a b s v=0 := by simp [cuspSeedProfile,cuspTransition_zero a b v hab hv]
lemma cuspSeedProfile_incoming (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : b≤v) (hpos : 0<v) : cuspSeedProfile a b s v=(v:ℂ)^s := by
  simp [cuspSeedProfile,cuspTransition_one a b v hab hv,positiveHeightPower_eq_cpow s v hpos]

lemma cuspSeedProfile_hasDerivAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (cuspSeedProfile a b s)
      (((deriv (cuspTransition a b) v:ℝ):ℂ)*positiveHeightPower s v+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s/(v:ℂ))) v := by
  exact (((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp).mul
    (positiveHeightPower_hasDerivAt s v hv)

lemma cuspSeedProfile_hasDerivAt_deriv (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (cuspSeedProfile a b s))
      (((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)*positiveHeightPower s v+
        2*((deriv (cuspTransition a b) v:ℝ):ℂ)*(positiveHeightPower s v*s/(v:ℂ))+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s*(s-1)/(v:ℂ)^2)) v := by
  have hχ := ((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp
  have hdχ := (((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2).differentiable
    (by simp) v).hasDerivAt.ofReal_comp
  have hH := positiveHeightPower_hasDerivAt s v hv
  have hdH := positiveHeightPower_hasDerivAt_deriv s v hv
  have heq : deriv (cuspSeedProfile a b s) =ᶠ[𝓝 v]
      (fun x => ((deriv (cuspTransition a b) x:ℝ):ℂ)*positiveHeightPower s x+
        (cuspTransition a b x:ℂ)*deriv (positiveHeightPower s) x) := by
    filter_upwards [eventually_ne_nhds hv] with x hx
    rw [(cuspSeedProfile_hasDerivAt a b s x hx).deriv,(positiveHeightPower_hasDerivAt s x hx).deriv]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hdχ.mul hH).add (hχ.mul hdH) using 1
  · rw [hH.deriv]
    ring

def cuspSeedDefectProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v*((v:ℂ)^2*((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)+
    (2*s-1)*(v:ℂ)*((deriv (cuspTransition a b) v:ℝ):ℂ))

lemma cuspSeedProfile_laplace_defect (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    (v:ℂ)^2*deriv (deriv (cuspSeedProfile a b s)) v-
      (v:ℂ)*deriv (cuspSeedProfile a b s) v-s*(s-2)*cuspSeedProfile a b s v=
        cuspSeedDefectProfile a b s v := by
  rw [(cuspSeedProfile_hasDerivAt a b s v hv).deriv,(cuspSeedProfile_hasDerivAt_deriv a b s v hv).deriv]
  unfold cuspSeedDefectProfile cuspSeedProfile
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ; ring

lemma cuspSeedDefectProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    cuspSeedDefectProfile a b s v=0 := by
  obtain ⟨h₁,h₂⟩ := cuspTransition_derivatives a b v hab hv
  simp [cuspSeedDefectProfile,h₁,h₂]

lemma cuspSeedDefectProfile_hasCompactSupport (a b : ℝ) (s : ℂ) (hab : a<b) :
    HasCompactSupport (cuspSeedDefectProfile a b s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra hn
  have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  exact hv (cuspSeedDefectProfile_zero a b s v hab hout)

def rowHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  p 2 / quadraticHeightDenominator (Complex.normSq (u 0)) (u 0*star (u 1)).re
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

lemma rowHeight_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<rowHeight u p := div_pos hp (row_denominator_pos u hu p hp)
lemma rowHeight_eq_transformedHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) :
    rowHeight u p=transformedHeight ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) u := by
  rw [transformedHeight,heightDenominator_eq_quadratic]
  rfl
lemma cosetHeight_upperPoint_rowHeight (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    cosetHeight r (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=rowHeight (embeddedRow r) p := by
  change (rowEnergy (rowOperator (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) (embeddedRow r)))⁻¹=_
  rw [rowEnergy_upperSection,inv_div,heightDenominator_eq_quadratic]
  rfl

lemma rowHeight_contDiffAt (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (rowHeight u) p := by
  have hq : ContDiffAt ℝ ∞
      (fun q : SpatialCoordinates => quadraticHeightDenominator (Complex.normSq (u 0))
        (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (q 0) (q 1) (q 2)) p := by
    unfold quadraticHeightDenominator
    fun_prop
  exact (show ContDiffAt ℝ ∞ (fun q : SpatialCoordinates => q 2) p by fun_prop).div hq
    (row_denominator_pos u hu p hp).ne'

lemma rowSmoothPower_eq_height (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) : rowSmoothPower s u p=(rowHeight u p:ℂ)^s :=
  logRatioPower_eq_cpow s hp (row_denominator_pos u hu p hp)

lemma norm_smoothSummand_three (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    ‖smoothSummand 3 r p‖=(rowHeight (embeddedRow r) p)^3 := by
  rw [smoothSummand,rowSmoothPower_eq_height 3 _ (embeddedRow_ne_zero r) p hp,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul]
  rw [show (3:ℂ)=(3:ℕ) by norm_num,Complex.cpow_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)]

lemma locally_finite_high_rows (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧ ∃S : Finset CuspCosets,
      ∀q∈U, 0<q 2 ∧ ∀r∉S,rowHeight (embeddedRow r) q<1 := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ :=
    spatial_summable_derivative_bounds 3 (by norm_num) p hp
  have hevent : ∀ᶠr in Filter.cofinite,M₀ r<1 :=
    hM₀.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hfinite : Set.Finite {r | ¬M₀ r<1} := Filter.eventually_cofinite.mp hevent
  refine ⟨U,hU,hpU,hfinite.toFinset,?_⟩
  intro q hq
  refine ⟨(hbound q hq).1,?_⟩
  intro r hr
  have hrM : M₀ r<1 := by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] using hr
  have hnorm := ((hbound q hq).2 r).1
  rw [norm_smoothSummand_three r q (hbound q hq).1] at hnorm
  have hpos := (rowHeight_pos _ (embeddedRow_ne_zero r) q (hbound q hq).1).le
  nlinarith [sq_nonneg (rowHeight (embeddedRow r) q-1)]

def heightPoincareField (F : ℝ → ℂ) (p : SpatialCoordinates) : ℂ :=
  ∑'r : CuspCosets,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma heightPoincareField_locally_finite (F : ℝ → ℂ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃S : Finset CuspCosets, heightPoincareField F =ᶠ[𝓝 p]
      (fun q => ∑r∈S,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) q)) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  refine ⟨S,?_⟩
  filter_upwards [hU.mem_nhds hpU] with q hq
  apply tsum_eq_sum
  intro r hr
  rw [hF _ ((hrows q hq).2 r hr).le,mul_zero]

lemma heightPoincareField_contDiffAt (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField F) p := by
  obtain ⟨S,hS⟩ := heightPoincareField_locally_finite F hzero p hp
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  apply ContDiffAt.sum
  intro r hr
  exact contDiffAt_const.mul ((hF _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)).comp p
    (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp))

lemma heightPoincareField_eq_cuspCorrection (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    heightPoincareField F p=cuspCutoffCorrection 1 F
      (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) := by
  unfold heightPoincareField cuspCutoffCorrection
  apply tsum_congr
  intro r
  rw [cuspCutoffTerm,cosetHeight_upperPoint_rowHeight]
  split_ifs with h
  · rfl
  · rw [hzero _ (le_of_not_gt h),mul_zero]

open CubicKubota

lemma positiveHeightPower_contDiffAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    ContDiffAt ℝ ∞ (positiveHeightPower s) v := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x:ℂ)) v :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv)
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => s*(Real.log x:ℂ)) v := contDiffAt_const.mul hlog
  unfold positiveHeightPower logRatioPower
  simpa only [Real.log_one,sub_zero] using hs.cexp

lemma cuspSeedProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedProfile a b s) v :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspTransition_contDiff a b).contDiffAt).mul
    (positiveHeightPower_contDiffAt s v hv.ne')

lemma cuspSeedDefectProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedDefectProfile a b s) v := by
  have hχ₁ : ContDiff ℝ ∞ (deriv (cuspTransition a b)) :=
    (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv (cuspTransition a b))) :=
    (contDiff_infty_iff_deriv.mp hχ₁).2
  have hd₁ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₁.contDiffAt
  have hd₂ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₂.contDiffAt
  have hid : ContDiffAt ℝ ∞ (fun x : ℝ => (x:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  exact (positiveHeightPower_contDiffAt s v hv.ne').mul
    (((hid.pow 2).mul hd₂).add ((contDiffAt_const.mul hid).mul hd₁))

lemma cuspSeedDefectProfile_continuous (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Continuous (cuspSeedDefectProfile a b s) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v<a
  · have heq : cuspSeedDefectProfile a b s =ᶠ[𝓝 v] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspSeedDefectProfile_zero a b s x hab (Or.inl hx)
    exact continuousAt_const.congr heq.symm
  · exact (cuspSeedDefectProfile_contDiffAt a b s v (lt_of_lt_of_le ha (le_of_not_gt hv))).continuousAt

lemma cuspSeedDefectProfile_integrable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Integrable (cuspSeedDefectProfile a b s) volume :=
  (cuspSeedDefectProfile_continuous a b s ha hab).integrable_of_hasCompactSupport
    (cuspSeedDefectProfile_hasCompactSupport a b s hab)

def smoothCuspSeed (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedProfile a b s)

def smoothCuspSeedDefect (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s)

lemma smoothCuspSeed_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeed a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w
lemma smoothCuspSeedDefect_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeedDefect a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w

lemma smoothCuspSeed_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeed a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le)) p hp).symm
lemma smoothCuspSeedDefect_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefect a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedDefectProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha))) p hp).symm

lemma smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedProfile a b s)) p :=
  heightPoincareField_contDiffAt _ (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp
lemma smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedDefectProfile a b s)) p :=
  heightPoincareField_contDiffAt _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha)))
    (cuspSeedDefectProfile_contDiffAt a b s) p hp

lemma cuspCutoffCorrection_upperPoint (F : ℝ → ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) (h1v : 1<v) :
    cuspCutoffCorrection 1 F (upperPoint z v hv)=F v := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspCutoffCorrection_eq 1 le_rfl _ _ (cosetOf 1) (hh.symm ▸ h1v),hh,
    cosetCharacter_cosetOf,map_one,inv_one,one_mul]

lemma smoothCuspSeed_incoming (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b≤v) :
    smoothCuspSeed a b s (upperPoint z v hv)=(v:ℂ)^s := by
  rw [smoothCuspSeed,cuspCutoffCorrection_upperPoint _ z v hv (lt_of_lt_of_le (ha.trans hab) hbv)]
  exact cuspSeedProfile_incoming a b s v hab hbv hv

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def rowLogHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  Real.log (p 2)-Real.log (quadraticHeightDenominator (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2))

lemma exp_rowLogHeight (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    Real.exp (rowLogHeight u p)=rowHeight u p := by
  rw [rowLogHeight,Real.exp_sub,Real.exp_log hp,Real.exp_log (row_denominator_pos u hu p hp)]
  rfl

lemma hasDerivAt_deriv_log_ratio (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t,HasDerivAt f (df t) t) (hg : ∀t,HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x≠0) (hg0 : g x≠0) :
    HasDerivAt (deriv (fun t => Real.log (f t)-Real.log (g t)))
      ((ddf*f x-df x*df x)/(f x)^2-(ddg*g x-dg x*dg x)/(g x)^2) x := by
  have heq : deriv (fun t => Real.log (f t)-Real.log (g t)) =ᶠ[𝓝 x]
      (fun t => df t/f t-dg t/g t) := by
    filter_upwards [((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)] with t ht
    exact (((hf t).log ht.1).sub ((hg t).log ht.2)).deriv
  exact ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).congr_of_eventuallyEq heq

lemma rowLogHeight_hasDerivAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (fun t => rowLogHeight u (Function.update p j t)) (rowLogD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := ((hasDerivAt_const (p 0) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_const (p 1) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_id (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDv,Function.update,A,B,C,D,Pi.sub_def] using! h

lemma rowLogHeight_hasDerivAt_deriv (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (fun t => rowLogHeight u (Function.update p j t))) (rowLogDD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDxx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDyy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio id
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDvv,Function.update,A,B,C,D,div_eq_mul_inv] using h

lemma complex_profile_second_chain (F : ℝ → ℂ) (g : ℝ → ℝ) (x dg ddg : ℝ) (dF ddF : ℂ)
    (hg : HasDerivAt g dg x) (hdg : HasDerivAt (deriv g) ddg x)
    (hF : HasDerivAt F dF (g x)) (hdF : HasDerivAt (deriv F) ddF (g x))
    (hlocal : ∀ᶠy in 𝓝 x,DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ F (g y)) :
    HasDerivAt (deriv (fun y => F (g y))) (ddF*(dg:ℂ)^2+dF*(ddg:ℂ)) x := by
  have heq : deriv (fun y => F (g y)) =ᶠ[𝓝 x]
      (fun y => (deriv g y:ℝ) • deriv F (g y)) := by
    filter_upwards [hlocal] with y hy
    exact (hy.2.hasDerivAt.scomp y hy.1.hasDerivAt).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert hdg.smul (hdF.scomp x hg) using 1
  · rfl
  · simp only [Function.comp_apply,hg.deriv,hF.deriv,Complex.real_smul]
    ring

lemma positiveProfile_differentiable (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (v : ℝ) (hv : 0<v) :
    DifferentiableAt ℝ F v ∧ DifferentiableAt ℝ (deriv F) v :=
  ⟨(hF v hv).differentiableAt (by simp),
    ((hF v hv).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma positiveProfile_exp_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (t : ℝ) :
    HasDerivAt (fun y => F (Real.exp y))
      (deriv F (Real.exp t)*(Real.exp t:ℂ)) t ∧
    HasDerivAt (deriv (fun y => F (Real.exp y)))
      (deriv (deriv F) (Real.exp t)*(Real.exp t:ℂ)^2+
        deriv F (Real.exp t)*(Real.exp t:ℂ)) t := by
  have hdf := positiveProfile_differentiable F hF (Real.exp t) (Real.exp_pos t)
  constructor
  · simpa only [Complex.real_smul,mul_comm,Function.comp_def] using! hdf.1.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  · apply complex_profile_second_chain F Real.exp t (Real.exp t) (Real.exp t)
      (deriv F (Real.exp t)) (deriv (deriv F) (Real.exp t)) (Real.hasDerivAt_exp t)
      (by simpa only [Real.deriv_exp] using Real.hasDerivAt_exp t) hdf.1.hasDerivAt hdf.2.hasDerivAt
    exact Filter.Eventually.of_forall (fun y =>
      ⟨Real.differentiable_exp y,(positiveProfile_differentiable F hF _ (Real.exp_pos y)).1⟩)

lemma rowProfile_axis_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => F (rowHeight u q)) p j)
      (deriv F (rowHeight u p)*(rowHeight u p:ℂ)*(rowLogD u p j:ℂ)) (p j) ∧
    HasDerivAt (deriv (axisSlice (fun q => F (rowHeight u q)) p j))
      (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2*(rowLogD u p j:ℂ)^2+
       deriv F (rowHeight u p)*(rowHeight u p:ℂ)*
        ((rowLogD u p j:ℂ)^2+(rowLogDD u p j:ℂ))) (p j) := by
  let g : ℝ → ℝ := fun t => rowLogHeight u (Function.update p j t)
  let G : ℝ → ℂ := fun t => F (Real.exp t)
  have hg : HasDerivAt g (rowLogD u p j) (p j) := rowLogHeight_hasDerivAt u hu p hp j
  have hdg : HasDerivAt (deriv g) (rowLogDD u p j) (p j) := rowLogHeight_hasDerivAt_deriv u hu p hp j
  have hgval : g (p j)=rowLogHeight u p := by simp [g,Function.update_eq_self]
  have hexp : Real.exp (g (p j))=rowHeight u p := by rw [hgval,exp_rowLogHeight u hu p hp]
  have hG := positiveProfile_exp_derivatives F hF (g (p j))
  have hnear : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 :=
    ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
      (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
  have heq : axisSlice (fun q => F (rowHeight u q)) p j =ᶠ[𝓝 (p j)] (fun t => G (g t)) := by
    filter_upwards [hnear] with t ht
    change F (rowHeight u (Function.update p j t))=F (Real.exp (rowLogHeight u (Function.update p j t)))
    rw [exp_rowLogHeight u hu _ ht]
  constructor
  · have hh := hG.1.scomp (p j) hg
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert hh using 1
    · rfl
    · simp only [Complex.real_smul,hexp]
      ring
  · have hlocal : ∀ᶠy in 𝓝 (p j),DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ G (g y) := by
      filter_upwards [hnear] with y hy
      constructor
      · have h := rowLogHeight_hasDerivAt u hu (Function.update p j y) hy j
        simpa only [Function.update_idem,Function.update_self] using h.differentiableAt
      · exact (positiveProfile_exp_derivatives F hF (g y)).1.differentiableAt
    have hh := complex_profile_second_chain G g (p j) (rowLogD u p j) (rowLogDD u p j)
      _ _ hg hdg hG.1 hG.2 hlocal
    apply HasDerivAt.congr_of_eventuallyEq _ heq.deriv
    convert hh using 1
    · rw [hexp]
      ring

lemma rowLog_eikonal (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*((rowLogD u p 0)^2+(rowLogD u p 1)^2+(rowLogD u p 2)^2)=1 := by
  exact heightLog_eikonal _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'
lemma rowLog_laplacian (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*(rowLogDD u p 0+rowLogDD u p 1+rowLogDD u p 2)-(p 2)*rowLogD u p 2= -2 := by
  exact heightLog_laplacian _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'

theorem rowProfile_laplacian (F : ℝ → ℂ) (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => F (rowHeight u q)) p=
      (rowHeight u p:ℂ)^2*deriv (deriv F) (rowHeight u p)-(rowHeight u p:ℂ)*deriv F (rowHeight u p) := by
  have hp0 := rowProfile_axis_derivatives F hF u hu p hp 0
  have hp1 := rowProfile_axis_derivatives F hF u hu p hp 1
  have hp2 := rowProfile_axis_derivatives F hF u hu p hp 2
  unfold axisLaplacian
  rw [Fin.sum_univ_three,hp0.2.deriv,hp1.2.deriv,hp2.2.deriv,hp2.1.deriv]
  have hE := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_eikonal u hu p hp)
  have hD := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_laplacian u hu p hp)
  push_cast at hE hD
  linear_combination
    (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2+
      deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hE+
    (deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hD

open Filter
open scoped BigOperators Classical Topology ContDiff

lemma axisLaplacian_congr_eventuallyEq (f g : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (heq : f =ᶠ[𝓝 p] g) : axisLaplacian f p=axisLaplacian g p := by
  have haxis (j : Fin 3) : axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
    have ht : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 p) := by
      have h : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 (Function.update p j (p j))) :=
        (continuous_axis_update p j).continuousAt
      simpa only [Function.update_eq_self] using h
    exact heq.comp_tendsto ht
  unfold axisLaplacian
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => (haxis j).deriv.deriv_eq)
  · rw [(haxis 2).deriv_eq]

lemma axisLaplacian_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c*f q) p=c*axisLaplacian f p := by
  unfold axisLaplacian
  simp only [Fin.sum_univ_three]
  unfold axisSlice
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma axisLaplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → SpatialCoordinates → ℂ)
    (hreg : ∀i∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f i) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f i) q j)) (q j))
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => ∑i∈S,f i q) p=∑i∈S,axisLaplacian (f i) p := by
  have hpair (j : Fin 3) :
      deriv (axisSlice (fun q => ∑i∈S,f i q) p j) (p j)=∑i∈S,deriv (axisSlice (f i) p j) (p j) ∧
      deriv (deriv (axisSlice (fun q => ∑i∈S,f i q) p j)) (p j)=
        ∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j) := by
    have hfirst (x : ℝ) (hx : 0<(Function.update p j x) 2) :
        HasDerivAt (axisSlice (fun q => ∑i∈S,f i q) p j)
          (∑i∈S,deriv (axisSlice (f i) p j) x) x := by
      have hi (i : ι) (hiS : i∈S) : DifferentiableAt ℝ (axisSlice (f i) p j) x := by
        simpa only [axisSlice_update,Function.update_self] using (hreg i hiS (Function.update p j x) hx j).1
      convert HasDerivAt.sum (fun i hiS => (hi i hiS).hasDerivAt) using 1
      ext y
      simp only [axisSlice,Finset.sum_apply]
    have hnear : ∀ᶠx in 𝓝 (p j),0<(Function.update p j x) 2 :=
      ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
        (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
    have heq : deriv (axisSlice (fun q => ∑i∈S,f i q) p j) =ᶠ[𝓝 (p j)]
        (fun x => ∑i∈S,deriv (axisSlice (f i) p j) x) := by
      filter_upwards [hnear] with x hx
      exact (hfirst x hx).deriv
    have hsecond : HasDerivAt (deriv (axisSlice (fun q => ∑i∈S,f i q) p j))
        (∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j)) (p j) := by
      apply (HasDerivAt.sum (fun i hiS => (hreg i hiS p hp j).2.hasDerivAt)).congr_of_eventuallyEq
      filter_upwards [heq] with x hx
      simpa only [Finset.sum_apply] using hx
    exact ⟨(hfirst (p j) (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)).deriv,hsecond.deriv⟩
  unfold axisLaplacian
  simp_rw [(hpair _).1,(hpair _).2]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]

end CubicEisenstein

end

end OAI
