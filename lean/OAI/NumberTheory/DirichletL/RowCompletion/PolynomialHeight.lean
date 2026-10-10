import OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation

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

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalCubeSeparation

theorem outside_separated_cube_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m f : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
      (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖ ≤ C*(Real.exp 1*B)^ε := by
  obtain ⟨C,hC,hbound⟩ := reopenedCubeCoefficient_small_power ε hε
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro S D Ψ hΨ m f H₀ B ξ v hB hn hn'
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have ht : ∀ z, ‖rowTwist Ψ (m*excludedGenerator S) f 1 z‖ ≤ 1 :=
    rowTwist_norm Ψ hΨ (m*excludedGenerator S) f 1
  have hβ : ‖reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)‖ ≤
      C*(Real.exp 1*B)^ε := by
    apply (hbound H₀ _ ht _ (cubeIdeal_ne_zero F v)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hε.le) hC.le
  have hh := separatedCubeCoefficient_bound
    (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F u))
    (fun u => (Ideal.absNorm (cubeIdeal F u) : ℝ)) B ξ (C*(Real.exp 1*B)^ε)
    hB (by positivity) v hn hn' hβ
  convert hh using 1 ; ring

end CanonicalRowCompletion

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith

lemma positiveCutoff_one (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    positiveCutoff a b ha x=1 := by
  apply (positiveCutoff a b ha).one_of_mem_closedBall
  change dist x ((a+max a b)/2) ≤ (max a b-a)/2+a/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2,le_max_right a b]

lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]

def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)

def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x

lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right

lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)

lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))

lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤ C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤ ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]

lemma patchedLog_eq_log (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    patchedLog a b ha x=Real.log x := by
  simp only [patchedLog,logCorrection,positiveCutoff_one a b ha x hx,one_mul]
  ring

def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))

lemma sourceTwistCLM_apply (W g : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    sourceTwistCLM W a b ha g x = W x*g (patchedLog a b ha x) := by
  change (SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)
    ((SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha)) g)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  rfl

def normTwistedSource (W : ℝ→ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x)*W x

lemma normTwistedSource_support (W : ℝ→ℂ) (t : ℝ) :
    Function.support (normTwistedSource W t) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by simp only [normTwistedSource,hz,mul_zero])

theorem frequencyTwist_finite_bound (g : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨n,C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  have hh := frequencyTwist_seminorm_polynomial g t z.1 z.2
  exact hh.trans (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn)
    (by positivity) hC.le)

theorem normTwistedSource_schwartz (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ→ℂ) ⊆ Icc a b) :
    ∃ G : ℝ→𝓢(ℝ,ℂ), (∀t x,G t x=normTwistedSource W t x) ∧
      (∀S : Finset (ℕ×ℕ), ∃n : ℕ, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G t)≤C*(1+‖t‖)^n) := by
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0≤M := by dsimp [M]; positivity
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff M hM
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  let G : ℝ→𝓢(ℝ,ℂ) := fun t => sourceTwistCLM W a b ha (frequencyTwist V t)
  refine ⟨G,?_,?_⟩
  · intro t x
    rw [show G t x=sourceTwistCLM W a b ha (frequencyTwist V t) x from rfl,
      sourceTwistCLM_apply,frequencyTwist_apply]
    by_cases hx : W x=0
    · simp only [normTwistedSource,hx,zero_mul,mul_zero]
    · have hxi := hs hx
      rw [patchedLog_eq_log a b ha x hxi]
      have hlog : |Real.log x|≤M := by
        have hlo := Real.log_le_log ha hxi.1
        have hhi := Real.log_le_log (lt_of_lt_of_le ha hxi.1) hxi.2
        rw [abs_le]
        constructor <;> dsimp [M] <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
          abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
      have hv : V (Real.log x)=1 := hvone _ hlog
      simp only [hv,mul_one,normTwistedSource]
      ring
  · intro S
    obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
      (sourceTwistCLM W a b ha) S
    obtain ⟨n,D,hD,hbound⟩ := frequencyTwist_finite_bound V s
    refine ⟨n,C*D,mul_pos hC hD,?_⟩
    intro t
    exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end CompletedHeight

namespace LocalLogFourier

open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
theorem coupled_positive_log_separation_linear_constant
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ → ℂ),
      ContDiffOn ℝ ∞ F (Set.Ioi 0) → ∀ CF : ℝ, 0 ≤ CF →
      (∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
        (1 + x)^A * ‖eulerDeriv F i x‖ ≤ CF) →
      ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C * CF ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C * CF) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P₀ : ℝ := momentConstant K Lwin CW 1
  let B₀ : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P₀ +
    FourierBridge.coefficientMomentBound J P₀)
  let D₀ : ℝ := FourierBridge.fourierPointBound J P₀
  let C₀ : ℝ := (B₀+D₀)/m^A
  have hP₀ : 0 ≤ P₀ := momentConstant_nonneg K Lwin CW 1 hL hCW zero_le_one
  have hB₀ : 0 ≤ B₀ := by
    dsimp [B₀]
    exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 P₀ hP₀)
      (FourierBridge.coefficientMomentBound_nonneg J P₀ hP₀))
  have hD₀ : 0 ≤ D₀ := FourierBridge.fourierPointBound_nonneg J P₀ hP₀
  refine ⟨C₀,by dsimp [C₀]; positivity,?_⟩
  intro F hFpos CF hCF hEuler
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P +
    FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hPeq : P=P₀*CF := by
    dsimp [P,P₀]
    unfold momentConstant derivativeConstant
    simp only [Finset.sum_mul,Finset.mul_sum,mul_one]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B=B₀*CF := by
    dsimp [B,B₀]
    rw [hPeq]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hBpeq : Bpoint=D₀*CF := by
    dsimp [Bpoint,D₀]
    rw [hPeq]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    apply hb.trans
    rw [hBeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₀ : B₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    apply hb.trans
    rw [hBpeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀ : D₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)

end LocalLogFourier

namespace CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

def HasPolynomialKernel (P : ℝ→ℝ→ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P t))) i x‖≤
      C*(1+‖t‖)^n

theorem normTwistedSource_polynomial_kernel (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    HasPolynomialKernel (normTwistedSource W) := by
  let S := vstarSchwartz W a b ha hsupp hW
  have hS : Function.support (S : ℝ→ℂ) ⊆ Set.Icc a b := Vstar_support W a b hsupp
  obtain ⟨G,hG,hbound⟩ := normTwistedSource_schwartz S a b ha hS
  have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W t) := by
    funext x
    rw [hG t x]
    change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W x)
    ring
  have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
    intro x hx
    change G t x≠0 at hx
    rw [hG t x] at hx
    exact hS (normTwistedSource_support S t hx)
  constructor
  · intro t
    rw [←hlink t]
    exact CubicReflectionKernel.paperKernel_compact_source_smooth (G t) a b ha (hGs t) ((G t).smooth ⊤)
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,C,hC,hsource⟩ := hbound s
    refine ⟨n,D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))

theorem polynomial_kernel_log_separation {ι : Type*} [Fintype ι]
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V : ι→ℝ→ℂ) (slope M : ι→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n) := by
  obtain ⟨n,D,hD,hkernel⟩ := hP.2 A (J+(volume : Measure ℝ).integrablePower)
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    V slope M hM hV A J
  refine ⟨n,C*D,mul_nonneg hC hD.le,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hb,hp⟩ := hsep (CubicReflectionKernel.paperKernel (Vstar (P θ))) (hP.1 θ)
    (D*(1+‖θ‖)^n) (by positivity) (hkernel θ) R hR
  refine ⟨B,hB,hi,?_,?_⟩
  · exact hb.trans_eq (by ring)
  · intro t
    exact (hp t).trans_eq (by ring)

theorem polynomial_kernel_three_window
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,C,hC,h⟩ := polynomial_kernel_log_separation P hP V slope M hm hv A 0
  refine ⟨n,C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal ActualEisensteinCubic.O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal ActualEisensteinCubic.O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      (C*(1+‖θ‖)^heightDegree)*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨heightDegree,Ck₀,hCk₀,hkernel⟩ := polynomial_kernel_three_window P hP V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ A
  refine ⟨2*heightDegree,Cq*(Ck₀^2+1),by positivity,?_⟩
  intro θ K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  let Ck := Ck₀*(1+‖θ‖)^heightDegree
  have hCk : 0≤Ck := by dsimp [Ck]; positivity
  have hCoeff : Cq*(Ck^2+1)≤(Cq*(Ck₀^2+1))*(1+‖θ‖)^(2*heightDegree) := by
    have hh : 1≤(1+‖θ‖)^(2*heightDegree) := one_le_pow₀ (by linarith [norm_nonneg θ])
    have he : Ck^2=Ck₀^2*(1+‖θ‖)^(2*heightDegree) := by
      dsimp [Ck]
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    rw [he]
    nlinarith [sq_nonneg Ck₀]
  obtain ⟨g,hsep,hg⟩ := hkernel θ R hR
  change (1+R)^A*(∫t : ℝ,‖g t‖)≤Ck at hg
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal ActualEisensteinCubic.O) (hn : n∈S) (v : Ideal ActualEisensteinCubic.O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal ActualEisensteinCubic.O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal ActualEisensteinCubic.O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(quadraticRow k.val (primaryGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖quadraticRow k.val (primaryGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = (Cq*(Ck^2+1))*((K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)/(1+R)^(2*A) := by ring
    _ ≤ _ := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0≤(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2))
        (by positivity : 0≤(1+R)^(2*A))
      convert hb using 1 ; ring

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨heightDegree,Cbase,hCbase,hquadbase⟩ := polynomial_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n P hP A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨heightDegree,2*Cbase*Cs^2,by positivity,?_⟩
  intro θ K Y H hK hY hH S T hS hT β hβ σ hσ
  let Cq := Cbase*(1+‖θ‖)^heightDegree
  have hCq : 0<Cq := by dsimp [Cq]; positivity
  have hquad := hquadbase θ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by dsimp [Cq]; ring

end CompletedHeight

end

end OAI
