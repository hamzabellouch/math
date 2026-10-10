import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents

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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0<r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a≤_
  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
      2*(7*(C*(M*N)^(260*η)*M*∑J,‖liftingFreeCoefficient N a J‖^2)+
        7*(C*(M*N)^(260*η)*M*∑J,‖liftingDividedCoefficient N a J‖^2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
          (14*C)*(M*N)^(260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖^2)+
            (∑J,‖liftingDividedCoefficient N a J‖^2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

theorem globalCutoffRatio_le (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M≤U^8 := by
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hden : 1≤B^2*F^2 := by nlinarith [sq_nonneg (B-1),sq_nonneg (F-1)]
  have he : H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M =
      (H*K*ell^2*(Real.exp M)^4)/(B^2*F^2) := by
    unfold globalRowScaleFloor
    field_simp

  rw [he]
  calc
    _ ≤ H*K*ell^2*(Real.exp M)^4 := div_le_self (by positivity) hden
    _ ≤ U*U*U^2*U^4 := by gcongr
    _ = U^8 := by ring

theorem globalNormCaps_polynomial (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ∀i, 0<globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i ∧
      globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i≤27*U^22 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hratio := globalCutoffRatio_le K ell B F M H U hU hK hell hB hF hH hKU hellU hHU heU
  have hY := globalRowScaleFloor_pos K ell B F M hK hell hB0 hF0
  have hratio0 : 0≤H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M := by positivity
  have hceil : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤U^8+2 := by
    have hh := Nat.ceil_lt_add_one hratio0
    linarith
  have hpow8 : 1≤U^8 := one_le_pow₀ hU
  have hceil' : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤3*U^8 := by linarith
  have hrow : 3*(ell*Real.exp M)^2*B^2*
      ((⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1)^2≤27*U^22 := by
    calc
      _ ≤ 3*(U^2)^2*U^2*(3*U^8)^2 := by gcongr
      _ = 27*U^22 := by ring
  have hpow2 : U^2≤27*U^22 := by
    calc
      U^2 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hpow4 : U^4≤27*U^22 := by
    calc
      U^4 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hB2 : B^2≤27*U^22 := (pow_le_pow_left₀ hB0.le hBU 2).trans hpow2
  have hLB : (ell*Real.exp M)*B^2≤27*U^22 := by
    calc
      _ ≤ U^2*U^2 := by gcongr
      _ = U^4 := by ring
      _ ≤ _ := hpow4
  intro i
  fin_cases i <;> dsimp [globalNormCaps]
  all_goals constructor
  all_goals first | positivity | exact hL.trans hpow2 | exact hB2 | exact hLB | exact hrow

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0<x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono hx hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

theorem globalLogBox_card_le_log (caps : Fin 10 → ℝ) (Y : ℝ) (hY : 1≤Y)
    (hcaps : ∀i,0<caps i ∧ caps i≤Y) :
    ((globalLogBox caps).card:ℝ)≤(1+Real.log Y)^10 := by
  calc
    ((globalLogBox caps).card:ℝ) = ∏i : Fin 10,((normLogBin (caps i):ℝ)+1) := by
      rw [globalLogBox_card]
      push_cast
      rfl
    _ ≤ ∏_i : Fin 10,(1+Real.log Y) := by
      apply Finset.prod_le_prod₀ (by intro i _; positivity)
      intro i _
      linarith [normLogBin_le_log_upper (caps i) Y (hcaps i).1 (hcaps i).2 hY]
    _ = (1+Real.log Y)^10 := by simp

theorem globalLogBox_card_polynomial_log (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤
      (1+Real.log 27+22*Real.log U)^10 := by
  have hU0 : 0<U := by linarith
  have hY : 1≤27*U^22 := by nlinarith [one_le_pow₀ hU (n:=22)]
  have hh := globalLogBox_card_le_log _ (27*U^22) hY
    (globalNormCaps_polynomial K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU)
  have he : 1+Real.log (27*U^22)=1+Real.log 27+22*Real.log U := by
    rw [Real.log_mul (by norm_num : (27:ℝ)≠0) (pow_ne_zero 22 hU0.ne'),Real.log_pow]
    norm_num
    ring
  rwa [he] at hh

theorem globalLogRep_le_upper (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1

theorem globalBinLossScale_cancel (B : ℝ) (j : GlobalLogIndex) :
    globalBinLossScale B j = Real.exp 5*globalLogRep j 1*globalLogRep j 6*
      globalLogRep j 7*B*Real.sqrt (globalLogRep j 9) := by
  have hj := (globalLogRep_pos j 4).ne'
  have he : Real.exp 5=Real.exp 4*Real.exp 1 := by rw [←Real.exp_add]; norm_num
  rw [he]
  unfold globalBinLossScale globalPooledLabelScale
  field_simp

theorem globalBinLossScale_polynomial (ell B Y M H U : ℝ)
    (hU : 1≤U) (hell : 0<ell) (hB : 1≤B)
    (hellU : ell≤U) (hBU : B≤U) (heU : Real.exp M≤U)
    (j : GlobalLogIndex) (hj : j∈globalLogBox (globalNormCaps ell B Y M H)) :
    globalBinLossScale B j≤Real.exp 5*U^8 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hL0 : 0<ell*Real.exp M := by positivity
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hpow2 : 1≤U^2 := one_le_pow₀ hU
  have h1 : globalLogRep j 1≤U^2 := globalLogRep_le_upper _ j hj 1 (U^2) hL0 hL hpow2
  have h6 : globalLogRep j 6≤U^2 := globalLogRep_le_upper _ j hj 6 (U^2) hL0 hL hpow2
  have h7 : globalLogRep j 7≤U^2 := globalLogRep_le_upper _ j hj 7 (U^2) hL0 hL hpow2
  have h9 : globalLogRep j 9≤U^2 := globalLogRep_le_upper _ j hj 9 (U^2) (by simp [globalNormCaps]; positivity)
    (by simpa [globalNormCaps] using pow_le_pow_left₀ hB0.le hBU 2) hpow2
  have hsqrt : Real.sqrt (globalLogRep j 9)≤U := Real.sqrt_le_iff.mpr ⟨hU0.le,h9⟩
  rw [globalBinLossScale_cancel]
  calc
    _ ≤ Real.exp 5*U^2*U^2*U^2*U*U := by
      gcongr
      all_goals exact (globalLogRep_pos j _).le
    _ = Real.exp 5*U^8 := by ring

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) : HasSieveExponent (2-1/α) := by
  have hα : 0<α := by linarith
  have hfrac : 1/α≤1 := (div_le_one hα).mpr hα1
  have hpos : 0≤1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N →
      sieveNorm M N≤C*(M*N)^ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

theorem finite_family_quadratic_large_sieve :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (M N : ℝ), 1≤M → 1≤N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal O) (cols : n → Ideal O),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i):ℝ)≤M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i))*a j‖^2) ≤
        C*(M*N)^ε*(M+N)*∑j,‖a j‖^2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  have he := FiniteSieveOperator.energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) a
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have hE : 0≤∑j,‖a j‖^2 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hn hE).trans
    (mul_le_mul_of_nonneg_right (hsharp M N hM hN) hE))

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

theorem globalLogFactor_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1≤U →
      (1+Real.log 27+22*Real.log U)^10≤C*U^ε := by
  let deltaLoss := ε/10
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let C0 := 1+Real.log 27+22/deltaLoss
  have hlog : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  refine ⟨C0^10,by positivity,?_⟩
  intro U hU
  have hU0 : 0<U := by linarith
  have hR : 1≤U^deltaLoss := Real.one_le_rpow hU hδ.le
  have hb : Real.log U≤U^deltaLoss/deltaLoss := Real.log_le_rpow_div hU0.le hδ
  have hs : 1+Real.log 27+22*Real.log U≤C0*U^deltaLoss := by
    calc
      _ ≤ (1+Real.log 27)*U^deltaLoss+22*(U^deltaLoss/deltaLoss) := add_le_add
        (le_mul_of_one_le_right (by linarith) hR)
        (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = C0*U^deltaLoss := by dsimp [C0]; ring
  have hs0 : 0≤1+Real.log 27+22*Real.log U := by
    have hu := Real.log_nonneg hU
    positivity
  calc
    _ ≤ (C0*U^deltaLoss)^10 := pow_le_pow_left₀ hs0 hs 10
    _ = C0^10*U^ε := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
      dsimp [deltaLoss]
      congr 1
      ring

theorem globalLogBox_card_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  exact (globalLogBox_card_polynomial_log K ell B F M H U hU hK hell hB hF hH
    hKU hellU hBU hHU heU).trans (hbound U hU)

theorem globalLogBox_total_loss (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∑j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinLossScale B j)^η)≤C*U^(ε+8*η) := by
  obtain ⟨C,hC,hcard⟩ := globalLogBox_card_small_power ε hε
  refine ⟨C*(Real.exp 5)^η,by positivity,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  have hU0 : 0<U := by linarith
  let S := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  have hbound (j : GlobalLogIndex) (hj : j∈S) :
      (globalBinLossScale B j)^η≤(Real.exp 5)^η*U^(8*η) := by
    have hb := globalBinLossScale_polynomial ell B (globalRowScaleFloor K ell B F M) M H U
      hU hell hB hellU hBU heU j hj
    have hnonneg : 0≤globalBinLossScale B j := by
      rw [globalBinLossScale_cancel]
      have h1 := (globalLogRep_pos j 1).le
      have h6 := (globalLogRep_pos j 6).le
      have h7 := (globalLogRep_pos j 7).le
      positivity
    apply (Real.rpow_le_rpow hnonneg hb hη).trans_eq
    rw [Real.mul_rpow (Real.exp_pos _).le (by positivity)]
    congr 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
    norm_num
  calc
    _ ≤ ∑_j∈S,((Real.exp 5)^η*U^(8*η)) := Finset.sum_le_sum hbound
    _ = (S.card:ℝ)*((Real.exp 5)^η*U^(8*η)) := by simp
    _ ≤ (C*U^ε)*((Real.exp 5)^η*U^(8*η)) :=
      mul_le_mul_of_nonneg_right (hcard K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) (by positivity)
    _ = (C*(Real.exp 5)^η)*U^(ε+8*η) := by rw [Real.rpow_add hU0]; ring

theorem globalBinLossScale_nonneg (B : ℝ) (hB : 0≤B) (j : GlobalLogIndex) :
    0≤globalBinLossScale B j := by
  rw [globalBinLossScale_cancel]
  have h1 := (globalLogRep_pos j 1).le
  have h6 := (globalLogRep_pos j 6).le
  have h7 := (globalLogRep_pos j 7).le
  positivity

theorem globalLogBox_radial_decay (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U Z θ : ℝ, ∀ N : ℕ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/
          (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) ≤
        C*U^(ε+8*η)/Z^(θ*N) := by
  obtain ⟨C,hC,hall⟩ := globalLogBox_total_loss ε hε η hη
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ
  let box := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let radial := fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j
  have hbase : 0<Z^θ := Real.rpow_pos_of_pos hZ _
  have hden : 0<Z^(θ*N) := Real.rpow_pos_of_pos hZ _
  have hnum (j : GlobalLogIndex) : 0≤(globalBinLossScale B j)^η :=
    Real.rpow_nonneg (globalBinLossScale_nonneg B (by linarith) j) _
  have hp (j : GlobalLogIndex) (hj : Z^θ≤radial j) :
      Z^(θ*N)≤(1+radial j)^N := by
    rw [Real.rpow_mul hZ.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ hbase.le (by linarith) N
  calc
    _ ≤ ∑j∈box.filter (fun j => Z^θ≤radial j), (globalBinLossScale B j)^η/Z^(θ*N) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_left (hnum j) hden (hp j (Finset.mem_filter.mp hj).2)
    _ = (∑j∈box.filter (fun j => Z^θ≤radial j),(globalBinLossScale B j)^η)/Z^(θ*N) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (∑j∈box,(globalBinLossScale B j)^η)/Z^(θ*N) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hnum j)
    _ ≤ C*U^(ε+8*η)/Z^(θ*N) := div_le_div_of_nonneg_right
      (hall K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hden.le

end SecondPassArithmetic

end

end OAI
