import OAI.NumberTheory.DirichletL.CubicSieve.ReopeningBounds
import OAI.NumberTheory.DirichletL.CubicSieve.CutoffOrders

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

private theorem two_windows_bound (windows : Fin 7→ℝ→ℂ)
    (hc : ∀i,HasCompactSupport (windows i)) (hs : ∀i,Continuous (windows i)) :
    ∃Vmax : ℝ,0≤Vmax ∧ (∀t,‖windows 5 t‖≤Vmax) ∧ (∀t,‖windows 6 t‖≤Vmax) := by
  have hb (i : Fin 7) : ∃B : ℝ,0≤B ∧ ∀t,‖windows i t‖≤B := by
    obtain ⟨B,hB⟩ := ((hc i).isCompact_range (hs i)).bddAbove_image continuous_norm.continuousOn
    have he (t : ℝ) : ‖windows i t‖≤B := hB ⟨windows i t,⟨t,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  obtain ⟨B₅,h₅,hb₅⟩ := hb 5
  obtain ⟨B₆,h₆,hb₆⟩ := hb 6
  exact ⟨B₅+B₆,by linarith,fun t=>(hb₅ t).trans (by linarith),fun t=>(hb₆ t).trans (by linarith)⟩

theorem reopenedCanonicalRow_state_step
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (N J Ntail : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ)
      (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ Clo Chi Vmax₁ Vmax₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧ 0<Clo ∧ 0<Chi ∧
      0≤Vmax₁ ∧ 0≤Vmax₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B H U Tmax E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H → 0≤Tmax →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      (X/B^3)*Real.exp M≤U → Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
      let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      (Real.exp 5*Cfirst*Real.sqrt D₁*Real.sqrt D₂)*Γ^2*(X*F)^2*
        (Ksrc/(Ksrc/Z^η))*(globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
        U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    reopenedCanonicalRow_nonzero_twoPassage g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ (N+1) (2*J) Ntail
  obtain ⟨Clo,Chi,hClo,hChi,hbudget⟩ := globalFirstQuantitativeBudget_bounded deltaLoss hδ ε hε
  obtain ⟨Vmax₁,hVmax₁,hw₁₅,hw₁₆⟩ := two_windows_bound w₁ hwc₁ (fun i=>(hws₁ i).continuous)
  obtain ⟨Vmax₂,hVmax₂,hw₂₅,hw₂₆⟩ := two_windows_bound w₂ hwc₂ (fun i=>(hws₂ i).continuous)
  have hwb₁' : ∀i t,w₁ i t≠0→|t|≤M+7 := by convert hwb₁ using 1 ; ring_nf
  have hwb₂' : ∀i t,w₂ i t≠0→|t|≤M+7 := by convert hwb₂ using 1 ; ring_nf
  refine ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hVmax₁,hVmax₂,
    hwc₁,hws₁,hwb₁',hwc₂,hws₂,hwb₂',?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B H U Tmax E hbase hpbad hZ hZbig hη hηsmall hΓ hE hU hB hH hTmax hKU hellU hBU hHU heU
    hMU hprogress hβ hQ hQB htail hterminal ih
  dsimp only
  have hX:=hstate.column_pos
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hell : 0<X/B^3:=div_pos hX (pow_pos hB0 _)
  have hKcut : 0<Ksrc/Z^η:=div_pos hK0 (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hΨ : ∀u,‖Ψ u‖≤1:=fun u=>hstate.coefficient.norm_le hbase u
  have he := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F H U hΓ hK0 hKcut hell hBsup hF0 hH hU hMU hΨ hβ hQ hQB
    (fun I hI=>(hstate.label_bounds I hI).2.1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  let blocks:=canonicalSourceBlocks pool (reopenedCubeFamily Q)
  have hb₁ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).1
  have hb₂ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).2
  have hbL:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks true w₁
    C₁ Cd₁ Ct₁ Tmax (Γ^2) E t B M H U (M+7) Vmax₁ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₁ hCd₁.le hCt₁.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₁ hw₁₅ hw₁₆ (hwb₁' 5) (hwb₁' 6)
    hb₁ hb₂ htail hterminal (ih true)
  have hbR:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks false w₂
    C₂ Cd₂ Ct₂ Tmax (Γ^2) E t B M H U (M+7) Vmax₂ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₂ hCd₂.le hCt₂.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₂ hw₂₅ hw₂₆ (hwb₂' 5) (hwb₂' 6)
    hb₁ hb₂ htail hterminal (ih false)
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  have hD₁ : 0≤D₁:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₁ hCd₁.le hCt₁.le hTmax hClo.le hChi.le
  have hD₂ : 0≤D₂:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₂ hCd₂.le hCt₂.le hTmax hClo.le hChi.le
  have hpairs:=canonicalPairBudget_normalized X F B Ksrc (Ksrc/Z^η) Cf
    ((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss) U (deltaLoss+8*ε) E t
    (D₁*Γ^2) (D₂*Γ^2) _ _ J hX hF0.le hB0 hK0.le hKcut hCf
    (Real.rpow_nonneg (globalFirstRowCap_pos _ _ _ _ hKcut hell (zero_lt_one.trans_le hBsup) hF0).le _)
    (zero_le_one.trans hU) (zero_le_one.trans hE) (mul_nonneg hD₁ (sq_nonneg Γ)) (mul_nonneg hD₂ (sq_nonneg Γ))
    (by simpa only [mul_assoc] using hbL) (by simpa only [mul_assoc] using hbR)
  have hsqrt : Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=Real.sqrt D₁*Real.sqrt D₂*Γ^2 := by
    rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂,Real.sqrt_sq_eq_abs]
    calc
      _ = Real.sqrt D₁*Real.sqrt D₂*(|Γ|^2) := by ring
      _ = _ := by rw [sq_abs]
  have hscaled:=mul_le_mul_of_nonneg_left he hB0.le
  calc
    _ ≤ B*(‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖+
       ‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
       B*((X/B^3)*(Real.exp 1*B)^2*F*(Ksrc/(Ksrc/Z^η))*Cf*
         (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₁
           C₁ Cd₁ Ct₁ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail true)*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₂
           C₂ Cd₂ Ct₂ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail false)) :=
      hscaled.trans_eq (by ring)
    _ ≤ _ := by
      apply (add_le_add le_rfl hpairs).trans_eq
      calc
        _ = _ := by rw [show Real.exp 5*Cf*Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=
            Real.exp 5*Cf*(Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)) by ring,hsqrt];ring

theorem reopenedCanonicalRow_polynomial_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤E → 1≤B → B^3≤Real.exp A*X →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨N,hN,hterminal⟩ := reopening_terminal_order η 0 hη
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hV₁,hV₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_state_step g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ N J 80
  let Cs:=reopeningScaleConstant A M
  let Tmax:=4096*Cs^20
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  have hTmax : 0≤Tmax:=by dsimp [Tmax]; positivity
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  let Cbase:=Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂
  let Cpow:=((Real.exp 1)^8)^deltaLoss*Cs^(deltaLoss+8*ε)
  have hCbase : 0≤Cbase:=by dsimp [Cbase]; positivity
  have hCpow : 0≤Cpow:=by dsimp [Cpow]; positivity
  refine ⟨w₁,w₂,Cbase*Cpow,mul_nonneg hCbase hCpow,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ.le hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  have htail : globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (Cs*Z^4) Z 80≤Tmax := by
    have hh:=globalFirstTailFactor_reopening_nat_decay A M Z η X F Ksrc B 0
      hZ.le hη.le hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one,zero_add] using hh
  have ht : (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 := by
    simpa only [neg_zero,Real.rpow_zero] using hterminal Z Ksrc hZ.le
      (zero_le_one.trans hstate.row_ge_one) hstate.row_le_global
  have hb:=hstep p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B Z (Cs*Z^(4:ℕ)) Tmax E hbase hpbad hZ hZbig hη.le hηsmall hΓ hE hU hB
    (zero_le_one.trans hZ.le) hTmax hKU hellU hBU hHU heU hMU hprogress hβ hQ hQB htail ht ih
  dsimp only at hb ⊢
  have hm:=reopening_recursive_with_ratio A M Z η X F Ksrc B deltaLoss ε hZ.le hη.le
    (by linarith) hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hB hδ.le hε.le
  have hx := mul_le_mul_of_nonneg_left hm
    (show 0≤Cbase*Γ^2*(X*F)^2*E*(1+‖t‖)^(2*J) by positivity)
  apply hb.trans
  apply add_le_add le_rfl
  convert hx using 1 <;> dsimp [Cbase,Cpow,D₁,D₂,Cs] <;> ring

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

theorem reopenedCanonicalFirstErrors_power
    (g : 𝓢(ℝ,ℂ)) (A M : ℝ) (hgM : ∀t,g t≠0→|t|≤M)
    (ε η : ℝ) (hε : 0<ε) (hη : 0<η) (hbudget : 3000*η≤(1:ℝ)/40) :
    ∃C : ℝ,0≤C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B : ℝ),
      (∀u,‖base u‖≤1) → 1≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤B → B^3≤Real.exp A*X →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)≤
      C*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
  obtain ⟨N,hN,horder⟩:=canonicalFirstTail_reopening_order η ε ((1:ℝ)/40) hη hε.le
  obtain ⟨Cz,Ct,hCz,hCt,herrors⟩:=reopenedCanonicalFirstErrors g M hgM ε hε N
  let Cs:=reopeningScaleConstant A M
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  let Cz':=Cz*(Real.exp 1)^(1+ε)*Cs^ε
  let Ct':=4*Ct*(Real.exp (2*M))^N*Cs^(25+ε)
  have hCz' : 0≤Cz':=by dsimp [Cz']; positivity
  have hCt' : 0≤Ct':=by dsimp [Ct']; positivity
  refine ⟨Cz'+Ct',add_nonneg hCz' hCt',?_⟩
  intro ι _ p hp _ hcop hg hinj hc base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ hX hXZ hFZ hΓ hB hactive hβ hQB
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hX0 : 0<X:=zero_lt_one.trans_le hX
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  let U:=Cs*Z^(4:ℕ)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hB0U : B≤U := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans hBU
  have hKsrcU : Ksrc≤U := by
    calc
      _ ≤ Z^3:=hstate.row_le_global
      _ ≤ Z^4:=by nlinarith [sq_nonneg Z,show 0≤Z^2*(Z-1)^2 by positivity]
      _ ≤ U:=le_mul_of_one_le_left (by positivity) hCs
  have herr:=herrors p hp hcop hg hinj hc pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F U hΓ hK0 (by positivity) (by positivity) hBsup
    hstate.label_ge_one hU hMU (fun u=>hstate.coefficient.norm_le hbase u) hβ hQB
    (fun I hI=>(hstate.label_bounds I hI).1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  dsimp only at herr ⊢
  have hzero:=canonicalFirstZero_normalization Cz Γ X F Ksrc B Z ε hCz hX0 hF0.le hK0.le hB
    (hstate.row_bound hZ hη.le hbudget)
  have hBpow : B^ε≤Cs^ε*Z^(3*ε) := by
    have hh : B≤Cs*Z^3 := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans
      (reopening_cube_bound A M Z X B hZ hX hXZ hB hactive)
    apply (Real.rpow_le_rpow hB0.le hh hε.le).trans_eq
    rw [Real.mul_rpow (by linarith) (by positivity),←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hz : B*‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖≤
      Cz'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    apply ((mul_le_mul_of_nonneg_left herr.1 hB0.le).trans hzero).trans
    calc
      _ ≤ (Cz*(Real.exp 1)^(1+ε))*(Cs^ε*Z^(3*ε))*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by gcongr
      _ = _ := by rw [show 3*ε-(1:ℝ)/40=3*ε+(-((1:ℝ)/40)) by ring,Real.rpow_add hZ0]; dsimp [Cz']; ring
  have ht0:=horder Cs Ct Γ B (Real.exp 1*B) U F Ksrc Z M hCs hCt hB0.le
    (by positivity) (by positivity) hF0.le hstate.row_ge_one hZ hB0U hBU le_rfl hFU hKsrcU
  have ht : B*‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖≤
      Ct'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    have hpow : Z^(-((1:ℝ)/40))≤Z^(3*ε-(1:ℝ)/40):=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have hXF : 1≤(X*F)^2:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le hX hstate.label_ge_one)
    apply ((mul_le_mul_of_nonneg_left herr.2 hB0.le).trans ht0).trans
    calc
      _ = Ct'*Γ^2*Z^(-((1:ℝ)/40)):=by dsimp [Ct']; ring
      _ ≤ Ct'*Γ^2*((X*F)^2*Z^(3*ε-(1:ℝ)/40)):=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt' (sq_nonneg Γ))
        exact hpow.trans (le_mul_of_one_le_left (by positivity) hXF)
      _ = _:=by ring
  rw [mul_add]
  exact (add_le_add hz ht).trans_eq (by ring)

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem reopenedCanonicalRow_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤E → 1≤B → B^3≤Real.exp A*X →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cp,hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_polynomial_step g V A M Nv hM hNv hgM hV hWin ε deltaLoss η hε hδ hη hηsmall J
  obtain ⟨Ce,hCe,herrors⟩:=reopenedCanonicalFirstErrors_power g A M hgM ε η hε hη hbudget
  refine ⟨w₁,w₂,Ce+Cp,add_nonneg hCe hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hpstep:=hstep p hp hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have herr:=herrors p hp hcop hg hinj hc base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ.le hX hXZ hFZ hΓ hB hactive hβ hQB
  dsimp only at hpstep herr
  have hpow : Z^(3*ε-(1:ℝ)/40)≤Z^(η+17*deltaLoss+32*ε):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hEH : 1≤E*(1+‖t‖)^(2*J):=
    one_le_mul_of_one_le_of_one_le hE (one_le_pow₀ (by linarith [norm_nonneg t]))
  have he : Ce*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40)≤
      Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
    calc
      _ ≤ Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε):=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε))*(E*(1+‖t‖)^(2*J)):=
        le_mul_of_one_le_right (by positivity) hEH
      _ = _:=by ring
  apply hpstep.trans
  exact (add_le_add (herr.trans he) le_rfl).trans_eq (by ring)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · simp only [hpq,ite_true] at ht
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha ht <;> omega
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci : 0<(normalizedFactors I).count P :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    simp only [hpq,not_false_eq_true,ite_true] at hr0
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha hr0 <;> omega

theorem nonresidual_prime_transport (I J F Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj : 0<(normalizedFactors J).count P := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp : 0<(normalizedFactors (rowResidualPart I Q)).count P := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]

lemma completedResidualScale_eq_on_fiber (K : ℝ) (I J Q : Ideal ActualEisensteinCubic.O)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q) :
    completedResidualScale K I Q=completedResidualScale K J Q := by
  simp only [completedResidualScale,hA,hT]

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma compact_estimate_prod_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.prod K) := by
  let R := max A 0+max B 0
  have hR : 0≤R := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨⟨Real.sqrt R,Real.sqrt_nonneg _⟩,(T.prod K).antilipschitz_of_bound (fun u => ?_)⟩
  have hT : ‖T u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le (T u,K u))
  have hK : ‖K u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_snd_le (T u,K u))
  have hh : ‖u‖^2≤R*‖(T.prod K) u‖^2 := calc
    _ ≤A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤max A 0*‖(T.prod K) u‖^2+max B 0*‖(T.prod K) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hT (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hK (le_max_right _ _))
    _ = _ := by dsimp only [R]; ring
  change ‖u‖≤Real.sqrt R*‖(T.prod K) u‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hR] using hh

lemma finiteDimensional_ker_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    FiniteDimensional ℂ T.ker := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hc : IsCompactOperator (K.comp T.ker.subtypeL) := hK.comp_clm T.ker.subtypeL
  have hid : IsCompactOperator (ContinuousLinearMap.id ℂ T.ker) := by
    apply compact_of_norm_le_compact _ _ hc
    refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
    have ht : T (u:E)=0 := u.2
    have hh := hest (u:E)
    rw [ht,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_add] at hh
    have hh' : ‖u‖^2≤max B 0*‖K (u:E)‖^2 :=
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    change ‖u‖≤Real.sqrt (max B 0)*‖K (u:E)‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt (le_max_right B 0)] using hh'
  exact FiniteDimensional.of_isCompactOperator_id hid

lemma antilipschitz_of_injective_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) (hT : Function.Injective T) :
    ∃D : NNReal,AntilipschitzWith D T := by
  by_contra hanti
  have hex (ε : ℝ) (hε : 0<ε) : ∃u : E,‖u‖=1 ∧ ‖T u‖<ε := by
    by_contra! hn
    apply hanti
    refine ⟨⟨ε⁻¹,inv_nonneg.mpr hε.le⟩,antilipschitz_of_bound_of_norm_one T (fun u hu => ?_)⟩
    change 1≤ε⁻¹*‖T u‖
    have hh := mul_le_mul_of_nonneg_left (hn u hu) (inv_nonneg.mpr hε.le)
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  obtain ⟨eps,hepsAnti,hepsPos,heps⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose u hunorm huT using fun n : ℕ => hex (eps n) (hepsPos n)
  have huTlim : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (huT n).le) heps
  obtain ⟨S,hS,hsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨k,hk,seq,hseq,hklim⟩ := hS.tendsto_subseq
    (fun n => hsub ⟨u n,by simp only [Metric.mem_closedBall,dist_zero_right,hunorm,le_refl],rfl⟩)
  let P := T.prod K
  obtain ⟨D,hD⟩ := compact_estimate_prod_antilipschitz T K A B hest
  have hlim : Tendsto (fun n => P (u (seq n))) atTop (𝓝 (0,k)) :=
    (huTlim.comp hseq.tendsto_atTop).prodMk_nhds hklim
  have hmem : (0,k)∈Set.range P :=
    (hD.isClosed_range P.uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => ⟨u (seq n),rfl⟩))
  obtain ⟨v,hv⟩ := hmem
  have hvlim : Tendsto (fun n => u (seq n)) atTop (𝓝 v) := by
    apply (hD.isInducing P.continuous).tendsto_nhds_iff.mpr
    change Tendsto (fun n => P (u (seq n))) atTop (𝓝 (P v))
    rw [hv]
    exact hlim
  have hvzero : v=0 := hT (by
    have hh := congrArg Prod.fst hv
    change T v=0 at hh
    simpa only [map_zero] using hh)
  have hnorm : ‖v‖=1 := tendsto_nhds_unique hvlim.norm (by simpa only [hunorm] using tendsto_const_nhds)
  rw [hvzero,norm_zero] at hnorm
  norm_num at hnorm

end CubicEisenstein

end

end OAI
