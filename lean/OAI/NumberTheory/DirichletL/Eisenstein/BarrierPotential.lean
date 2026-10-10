import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
import OAI.NumberTheory.DirichletL.Eisenstein.CuspHeight

namespace OAI

noncomputable section

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma axisLaplacian_const_add (c : ℂ) (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c+f q) p=axisLaplacian f p := by
  unfold axisLaplacian axisSlice
  simp only [deriv_const_add,deriv_const_add']

lemma fullCuspProfileField_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    Summable (fun x => F (rowHeight (fullCuspRow x) p)) := by
  simpa only [fullCuspRow_height _ p hp] using
    fullCuspProfileSum_summable F hF (upperPoint (spatialHorizontal p) (p 2) hp)

lemma fullCuspProfileField_add (F G : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hG : ∀v≤1,G v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField (fun v => F v+G v) p=fullCuspProfileField F p+fullCuspProfileField G p :=
  (fullCuspProfileField_summable F hF p hp).tsum_add
    (fullCuspProfileField_summable G hG p hp)

lemma cuspBarrierProfile_laplacian_zero (a b v : ℝ) (ha : 1<a) (hab : a<b) (hv : v≤1) :
    positiveHeightLaplacian (cuspBarrierProfile a b) v=0 := by
  have hh := cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  rw [cuspBarrierDefectProfile,cuspBarrierProfile_zero a b hab v (hv.trans ha.le),sub_zero] at hh
  exact hh

def cuspBarrierField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  1+fullCuspProfileField (cuspBarrierProfile a b) p

def cuspBarrierDefectField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  -1+fullCuspProfileField (cuspBarrierDefectProfile a b) p

lemma cuspBarrierField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierField a b p=cuspBarrier a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierField,cuspBarrier,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierDefectField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierDefectField a b p=cuspBarrierDefect a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierDefectField,cuspBarrierDefect,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierField_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (cuspBarrierField a b q:ℂ)) p-(cuspBarrierField a b p:ℂ)=
      (cuspBarrierDefectField a b p:ℂ) := by
  have hF : ∀v≤1,cuspBarrierProfile a b v=0 :=
    fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha.le)
  have hD : ∀v≤1,cuspBarrierDefectProfile a b v=0 :=
    fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  have hid : positiveHeightLaplacian (cuspBarrierProfile a b)=
      fun v => cuspBarrierDefectProfile a b v+cuspBarrierProfile a b v := by
    funext v
    rw [cuspBarrierDefectProfile,sub_add_cancel]
  have hh := fullCuspProfileField_laplacian _ (cuspBarrierProfile_smooth a b) hF
    (fun v hv => cuspBarrierProfile_laplacian_zero a b v ha hab hv) p hp
  simp only [cuspBarrierField,Complex.ofReal_add,Complex.ofReal_one,axisLaplacian_const_add]
  rw [hh,hid,fullCuspProfileField_add _ _ hD hF p hp]
  simp only [cuspBarrierDefectField,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_one]
  ring

def kernelBarrierPotential (a b : ℝ) (q : KernelQuotient) : ℝ :=
  1+kernelQuotientBarrierDefect a b q/kernelQuotientBarrier a b q

lemma kernelBarrierPotential_lower (a b : ℝ) (ha : 1<a) (hab : a<b) :
    ∃K : Set KernelQuotient,IsCompact K ∧ ∃C : ℝ,0≤C ∧
      ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤kernelBarrierPotential a b q := by
  let D := kernelQuotientBarrierDefect a b
  let K := tsupport D
  have hK : IsCompact K := kernelQuotientBarrierDefect_hasCompactSupport a b ha hab
  obtain ⟨C,hC⟩ := (kernelQuotientBarrierDefect_hasCompactSupport a b ha hab).exists_bound_of_continuous
    (kernelQuotientBarrierDefect_continuous a b ha hab)
  refine ⟨K,hK,max C 0,le_max_right _ _,fun q => ?_⟩
  have hphi := kernelQuotientBarrier_one_le a b ha.le hab q
  have hpos : 0<kernelQuotientBarrier a b q := by linarith
  by_cases hq : q∈K
  · rw [Set.indicator_of_mem hq,mul_one,kernelBarrierPotential]
    have hD : -max C 0≤D q := by
      have hn : -‖D q‖≤D q := neg_abs_le (D q)
      exact (neg_le_neg ((hC q).trans (le_max_left C 0))).trans hn
    have hdiv : -max C 0≤D q/kernelQuotientBarrier a b q := by
      apply (le_div_iff₀ hpos).mpr
      have hm : -max C 0*kernelQuotientBarrier a b q≤-max C 0 := by
        nlinarith [mul_nonneg (le_max_right C 0) (sub_nonneg.mpr hphi)]
      exact hm.trans hD
    linarith
  · rw [Set.indicator_of_notMem hq,mul_zero,sub_zero,kernelBarrierPotential]
    have hz : D q=0 := image_eq_zero_of_notMem_tsupport hq
    change 1≤1+D q/kernelQuotientBarrier a b q
    rw [hz,zero_div,add_zero]

lemma cuspBarrier_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrier a b (euclideanToHyperbolic p)=cuspBarrierField a b p.ofLp := by
  rw [cuspBarrierField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma cuspBarrierDefect_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrierDefect a b (euclideanToHyperbolic p)=cuspBarrierDefectField a b p.ofLp := by
  rw [cuspBarrierDefectField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma kernelQuotientBarrier_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelQuotientBarrier a b (kernelEuclideanProjection p)+
          kernelQuotientBarrierDefect a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) q :=
    fun q hq => Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt a b ha.le hab q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hf p hp]
  have he : ∀q : SpatialCoordinates,0<q 2→
      (kernelQuotientBarrier a b (kernelEuclideanProjection (WithLp.toLp 2 q)):ℂ)=
        (cuspBarrierField a b q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq a b (WithLp.toLp 2 q) hq)
  rw [axisLaplacian_congr_positive _ _ he p.ofLp hp]
  have hh := cuspBarrierField_laplace_defect a b ha hab p.ofLp hp
  change -axisLaplacian _ p.ofLp=((cuspBarrier a b (euclideanToHyperbolic p)+
    cuspBarrierDefect a b (euclideanToHyperbolic p):ℝ):ℂ)
  rw [cuspBarrier_euclidean_eq a b p hp,cuspBarrierDefect_euclidean_eq a b p hp,Complex.ofReal_add]
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelBarrierPotential_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelBarrierPotential a b) := by
  apply continuous_const.add
  exact (kernelQuotientBarrierDefect_continuous a b ha hab).div
    (kernelQuotientBarrier_continuous a b ha.le hab) (fun q => by
      have hq := kernelQuotientBarrier_one_le a b ha.le hab q
      linarith)

lemma kernelBarrierPotential_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelBarrierPotential a b (kernelEuclideanProjection p)*
          kernelQuotientBarrier a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  rw [kernelQuotientBarrier_laplace_defect a b ha hab p hp]
  apply congrArg Complex.ofReal
  have hn : kernelQuotientBarrier a b (kernelEuclideanProjection p)≠0 := by
    have hq := kernelQuotientBarrier_one_le a b ha.le hab (kernelEuclideanProjection p)
    linarith
  rw [kernelBarrierPotential,add_mul,one_mul,div_mul_cancel₀ _ hn]

lemma kernelSmoothTest_weighted_mass_integrable (V : KernelQuotient→ℝ) (hV : Continuous V)
    (f : kernelSmoothTests) :
    Integrable (fun q => V q*‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) := by
  apply (hV.mul (f.2.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hn
  have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hn
  apply hq
  change V q*‖f.1 q‖^2=0
  rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]

lemma kernelBarrierPotential_weighted_integrable (a b : ℝ) (ha : 1<a) (hab : a<b)
    (f : kernelSmoothTests) :
    Integrable (fun q => kernelBarrierPotential a b q*‖f.1 q‖^2)
      (integralQuotientVolume globalKubotaKernel) :=
  kernelSmoothTest_weighted_mass_integrable _ (kernelBarrierPotential_continuous a b ha hab) f

end

open scoped ComplexConjugate

theorem ground_state_square_completion (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    ‖d‖^2 - b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) =
      ‖d - (b/a : ℝ)*z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ; ring

theorem ground_state_directional_inequality (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) ≤ ‖d‖^2 := by
  have hh := ground_state_square_completion a b ha z d
  nlinarith [sq_nonneg ‖d - (b/a : ℝ)*z‖]

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstQuantitativeBudget_below_rank (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Γ → 0≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*
          (((Real.exp 1*B)*U)^ε*(Cd+Ct*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*(Ksrc/Z^η)*Chi/Z^(η*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_state_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hstate.row_ge_one
  have hKcut : 0<Ksrc/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hell : 0<X/B^3 := div_pos hstate.column_pos (pow_pos hB0 _)
  have hBsup : 1≤Real.exp 1*B :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  apply hbound p hp hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E oldHeight
    (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U Z η A₀ Vmax N J Ntail
    hC hΓ hE hU hKcut hell hBsup hstate.label_ge_one hH hKU hellU hBU hHU heU hZ0
    hA hV hV₁ hV₂ hVs₁ hVs₂ (fun u=>hstate.coefficient.norm_le hbase u) hb₁ hb₂
  dsimp only
  intro a r j hj ray q hq s
  let source := globalQuantitativeSource p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    globalQuantitativeSource_frequency_ne_zero p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hb₁' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hb₂' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hs := canonicalStateCondition_cutoff_retained p hp base bad Z η Ψ m labels X F Ksrc hstate
    hpbad source side q j hq (if side then a.1 else a.2) r ray B
    hZ hZbig hη hηsmall hB0 hprogress hk hb₁' hb₂' (Finset.mem_filter.mp hj).2.le
  have hr : fixedDepthRank Z (globalLogRep j 8*Real.exp 1)<fixedDepthRank Z Ksrc := by
    have := hs.1
    omega
  exact ⟨(ih _ _ _ _ _ _ hs.2.1 hr s).1,(ih _ _ _ _ _ _ hs.2.2 hr s).2⟩

end

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem reopenedCanonicalFirstErrors (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0→|t|≤M) (ε : ℝ) (hε : 0<ε) (A : ℕ) :
    ∃Czero Ctail : ℝ,0≤Czero ∧ 0≤Ctail ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (Γ t Ksrc Kcut ell B F lengthScale : ℝ),
      0≤Γ → 0<Ksrc → 0<Kcut → 0<ell → 1≤B → 1≤F → 1≤lengthScale → ell*Real.exp M≤lengthScale →
      (∀u,‖Ψ u‖≤1) → (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠⊥) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖≤
        Czero*B^(1+ε)*ell*F*Γ^2*Ksrc) ∧
      (‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖≤
        Ctail*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
          (1+(Ksrc/Kcut)/Real.exp (2*M))^A) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_uniform_canonicalFirstZero_bound ε hε
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_canonicalSourceTail_bound ε hε A
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 g
  have hG : 0≤G := apply_nonneg _ _
  have hgG : ∀x,‖g x‖≤G := fun x=>SchwartzMap.norm_le_seminorm ℝ g x
  have hgupper : ∀x,g x≠0→x≤M := fun x hx=>(le_abs_self x).trans (hgM x hx)
  refine ⟨Cz*Real.exp M*G^2*‖paperRadialFourier rowMajorant 0‖,
    Ct*G^2*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant,by positivity,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool Q labels β Ψ m Γ t Ksrc Kcut ell B F lengthScale
    hΓ hKsrc hKcut hell hB hF hL hML hΨ hβ hQB hI0 hIF
  dsimp only
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  have hb₁ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1
  have hb₂ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2
  have ha : ∀b∈reopenedCubeFamily Q,∀D∈(pool\b.support).powerset,∀I∈labels,
      ‖reopenedPairCoefficient β b D I‖≤Γ^2 :=
    fun b hb D hD I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb D I hI
  constructor
  · have hz := hzero p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G ell Ksrc M B F (sq_nonneg Γ) hG hG hell hB hF
      hΨt hΨt (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper
    change ‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant Ksrc ell‖≤_ at hz
    rw [abs_of_pos hKsrc] at hz
    exact hz.trans_eq (by ring)
  · have ht := htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G M M Ksrc Kcut ell B F lengthScale
      (sq_nonneg Γ) hG hG hKsrc hKcut hell hB hF hL hML hML hΨt hΨt
      (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper hgupper
    exact ht.trans_eq (by rw [show M+M=2*M by ring]; ring)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X oldHeight newHeight : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ oldHeight) m f
      (fun S=>frequencyTwist g newHeight (columnLog p X S)) z‖=
    ‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q β
      (normHeightTwist Ψ oldHeight) m f z g X newHeight hX,
    normHeightTwist_twice,
    reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q β Ψ m f z g X
      (oldHeight+newHeight) hX]

theorem reopenedCanonicalEnergy_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X Ksrc oldHeight newHeight : ℝ) (hX : 0<X) :
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) (normHeightTwist Ψ oldHeight) m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g newHeight (columnLog p X S))) Ksrc).re=
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S))) Ksrc).re := by
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro I hI
  unfold nonzeroRowMajorantSum
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_two_heights p hp hcop hg pool Q (β I) Ψ m _ z g X oldHeight newHeight hX]

end

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem CanonicalStateCondition.row_bound
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40) :
    K≤(X*F)*Z^(-((1:ℝ)/40)) := by
  have hn := element_norm_ge_one m h.mask_ne_zero
  calc
    K = K*1 := (mul_one _).symm
    _ ≤ K*‖eisEmbedding m‖^2 :=
      mul_le_mul_of_nonneg_left hn (zero_le_one.trans h.row_ge_one)
    _ ≤ _ := h.invariant_reserved hZ hη hbudget

theorem canonicalFirstZero_normalization (C Γ X F K B Z ε : ℝ)
    (hC : 0≤C) (hX : 0<X) (hF : 0≤F) (hK : 0≤K) (hB : 1≤B)
    (hrow : K≤(X*F)*Z^(-((1:ℝ)/40))) :
    B*(C*(Real.exp 1*B)^(1+ε)*(X/B^3)*F*Γ^2*K)≤
      (C*(Real.exp 1)^(1+ε))*B^ε*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hc : 0≤C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F) := by
    positivity
  calc
    _ = (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K/B := by
      rw [Real.mul_rpow (Real.exp_pos _).le hB0.le,Real.rpow_add hB0,Real.rpow_one]
      field_simp

    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K :=
      div_le_self (mul_nonneg hc hK) hB
    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*((X*F)*Z^(-((1:ℝ)/40))) :=
      mul_le_mul_of_nonneg_left hrow hc
    _ = _ := by ring

end

theorem canonicalFirstTail_numerator (C Γ B₀ B lengthScale F K U ε : ℝ)
    (hC : 0≤C) (_hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤K) (hU : 1≤U) (hε : 0≤ε)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : K≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*K*(1+lengthScale^3*B^4/K)^2)≤
      4*C*Γ^2*U^(25+ε) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hratio : lengthScale^3*B^4/K≤U^7 := by
    calc
      _ ≤ lengthScale^3*B^4 := div_le_self (mul_nonneg (pow_nonneg hL _) (pow_nonneg hB _)) hK
      _ ≤ U^3*U^4 := by gcongr
      _ = U^7 := by ring
  have hU7 : 1≤U^7 := one_le_pow₀ hU
  have hs : (1+lengthScale^3*B^4/K)^2≤4*U^14 := by
    have hnonneg : 0≤lengthScale^3*B^4/K := div_nonneg (by positivity) hK0.le
    have ha : 1+lengthScale^3*B^4/K≤2*U^7 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤1+lengthScale^3*B^4/K) ha 2
    nlinarith [show (U^7)^2=U^14 by ring]
  calc
    _ ≤ U*(C*U^(4+ε)*U^4*U*Γ^2*U*(4*U^14)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_add hU0,Real.rpow_add hU0]
      norm_num
      ring

theorem canonicalCutoff_ratio (Ksrc Z η : ℝ) (hK : 0<Ksrc) (hZ : 0<Z) :
    Ksrc/(Ksrc/Z^η)=Z^η := by
  have hz := (Real.rpow_pos_of_pos hZ η).ne'
  field_simp

theorem canonicalFirstTail_polynomial (C Γ B₀ B lengthScale F Ksrc U Z η ε M : ℝ) (A : ℕ)
    (hC : 0≤C) (hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤Ksrc) (hU : 1≤U) (hε : 0≤ε) (hZ : 0<Z)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : Ksrc≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
      (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^A)≤
      (4*C*Γ^2*(Real.exp (2*M))^A)*U^(25+ε)/Z^(η*(A:ℝ)) := by
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hK
  have hη : 0<Z^η := Real.rpow_pos_of_pos hZ _
  have hden : 0<(Z^η/Real.exp (2*M))^A := pow_pos (div_pos hη (Real.exp_pos _)) _
  rw [canonicalCutoff_ratio Ksrc Z η hK0 hZ]
  calc
    _ = (B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2))/(1+Z^η/Real.exp (2*M))^A := by ring
    _ ≤ (4*C*Γ^2*U^(25+ε))/(1+Z^η/Real.exp (2*M))^A :=
      div_le_div_of_nonneg_right (canonicalFirstTail_numerator C Γ B₀ B lengthScale F Ksrc U ε
        hC hB₀ hB hL hF hK hU hε hB₀U hBU hLU hFU hKU) (by positivity)
    _ ≤ (4*C*Γ^2*U^(25+ε))/(Z^η/Real.exp (2*M))^A := by
      exact div_le_div_of_nonneg_left (by positivity) hden
        (pow_le_pow_left₀ (div_pos hη (Real.exp_pos _)).le (by linarith) A)
    _ = _ := by
      rw [div_pow,←Real.rpow_natCast (Z^η) A,←Real.rpow_mul hZ.le]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem CanonicalStateCondition.terminal_energy
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbase : ∀u,‖base u‖≤1) (hZ : 1<Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40)
    (V : ℝ→ℂ) (A M t : ℝ) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hstop : fixedDepthRank Z K=0 ∨ X≤1) :
    canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ t) m labels V X K≤
      canonicalTerminalConstant A M*(X*F)^2 := by
  have hKF : K≤F := by
    rcases hstop with hr|hx
    · exact ((fixedDepthRank_zero_iff Z K hZ (zero_lt_one.trans_le hstate.row_ge_one)).mp hr).trans
        hstate.label_ge_one
    · have hi := hstate.invariant_reserved hZ.le hη hbudget
      have hz : Z^(-((1:ℝ)/40))≤1 := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -((1:ℝ)/40)≤0)
      have hi' : K*‖ConcreteTraceCRT.eisEmbedding m‖^2≤X*F :=
        hi.trans ((mul_le_mul_of_nonneg_left hz
          (mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one))).trans_eq (mul_one _))
      exact smallColumn_row_le_label m hstate.mask_ne_zero X F K hx
        (zero_le_one.trans hstate.label_ge_one) (zero_le_one.trans hstate.row_ge_one) hi'
  apply canonicalLogEnergy_terminal p hp hcop hg hc hinj pool (normHeightTwist Ψ t)
    (fun u=>(normHeightTwist_norm_le Ψ t u).trans (hstate.coefficient.norm_le hbase u)) m labels V X F K A M
    hstate.column_pos hstate.label_ge_one hstate.row_ge_one hKF hM hV hVs
  · exact fun I hI=>(hstate.label_bounds I hI).1
  · exact fun I hI=>(hstate.label_bounds I hI).2.2.2

end SecondPassArithmetic

end

end OAI
