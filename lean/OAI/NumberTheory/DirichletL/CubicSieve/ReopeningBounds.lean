import OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential

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
namespace SecondPassArithmetic
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_filter (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι→ℂ)
    (keep : (ι→₀ℕ)→Prop) [DecidablePred keep]
    (hβ : ∀v∈Q,¬keep v→β v=0) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z=
      reopenedCanonicalRow p hp hcop hg pool (Q.filter keep) β Ψ m f H z := by
  unfold reopenedCanonicalRow
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬keep v := fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  simp only [hβ v hv hn,zero_mul,Finset.sum_const_zero]

theorem reopenedCanonicalRow_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι→ℂ)
    (hβ : ∀v∈Q,β v=0) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z=0 := by
  unfold reopenedCanonicalRow
  apply Finset.sum_eq_zero
  intro v hv
  simp only [hβ v hv,zero_mul,Finset.sum_const_zero]

end SecondPassArithmetic

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation

def progressingCubes (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (H₀ : ℝ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))

theorem separatedCubeCoefficient_eq_zero_of_small (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (B ξ : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
    (hsmall : ¬H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)) :
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ Ψ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v=0 := by
  have hz : reopenedCubeCoefficient H₀ Ψ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hn
    exact hsmall (reopenedCubeCoefficient_support H₀ Ψ _ hn).2
  simp only [separatedCubeCoefficient,hz,zero_mul]

theorem outsideCanonicalBin_filter (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X H₀ : ℝ) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=
      outsideCanonicalBin S D hbad (progressingCubes S D H₀ Q) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  have hz : largeCubeCoefficient H₀ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (largeCubeCoefficient_support H₀ _ hh).2
  simp only [hz,zero_mul]

theorem progressingCubes_progress (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z F B : ℝ) (hF : 1≤F) (hB : 1≤B)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) Q).Nonempty)
    (hupper : ∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B) :
    Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F := by
  by_cases hsmall : F<Z^((1:ℝ)/1000)
  · obtain ⟨v,hv⟩ := hQ
    obtain ⟨hvQ,hlo⟩ := Finset.mem_filter.mp hv
    simp only [ite_eq_left hsmall] at hlo
    have he := hlo.trans (hupper v hvQ)
    have hbpos : 0≤Real.exp 1*B := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hB)
    exact he.trans (le_mul_of_one_le_right hbpos hF)
  · have hb : 1≤Real.exp 1*B :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
    exact (le_of_not_gt hsmall).trans (le_mul_of_one_le_left (zero_le_one.trans hF) hb)

theorem progressingActiveBin_progress (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (b X Z F : ℝ) (j : ℕ) (hF : 1≤F)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)
      (activeCubeLogBin S D b X j)).Nonempty) :
    Z^((1:ℝ)/1000)≤(Real.exp 1*normLogScale j)*F :=
  progressingCubes_progress S D (activeCubeLogBin S D b X j) Z F (normLogScale j) hF
    (normLogScale_ge_one j) hQ (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)

theorem outsideCanonicalBin_zero_of_empty_filter (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (hQ : progressingCubes S D H₀ Q=∅) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=0 := by
  rw [outsideCanonicalBin_filter S D hbad Q Ψ m f z W X H₀,hQ]
  simp only [outsideCanonicalBin,Finset.sum_empty]

theorem reopenedCanonicalRow_progressing (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ Ξ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
    (H : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D))→ℂ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀ Ξ (cubeIdeal F v))
      (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) B ξ
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q β Ψ m f H z=
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ
      (progressingCubes S D H₀ Q) β Ψ m f H z := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply reopenedCanonicalRow_filter
  intro v hv hsmall
  exact separatedCubeCoefficient_eq_zero_of_small S D H₀ Ξ B ξ v hsmall

end CanonicalRowCompletion

namespace SecondPassArithmetic

section

open MeasureTheory
open FirstPassCubeLabels (firstLogDensity)

def canonicalBudgetCoefficient (C Cd Ct Tmax Clo Chi A M : ℝ) : ℝ :=
  (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*
    (Cd+Ct*Tmax+C*globalRayTripleConstant*
      (6*(∫t : ℝ,firstLogDensity 0 t)^3*Clo+globalTerminalConstant A M*Chi))

theorem canonicalBudgetCoefficient_nonneg (C Cd Ct Tmax Clo Chi A M : ℝ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (hClo : 0≤Clo) (hChi : 0≤Chi) :
    0≤canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M := by
  have hi : 0≤∫t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have ht := globalTerminalConstant_nonneg A M
  unfold canonicalBudgetCoefficient globalRayTripleConstant
  positivity

theorem canonicalBudgetScalar_bound
    (C Cd Ct Tmax Clo Chi A M Γ P E t B U deltaLoss ε tailFactor terminalFactor : ℝ) (J : ℕ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (_hClo : 0≤Clo) (hChi : 0≤Chi) (hΓ : 0≤Γ) (hP : 0≤P)
    (hE : 1≤E) (hB : 0≤B) (hBU : B≤U) (hU : 1≤U) (hδ : 0≤deltaLoss) (hε : 0≤ε)
    (htail : tailFactor≤Tmax) (hterminal : terminalFactor≤1) :
    (∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P*
      ((B*U)^ε*(Cd+Ct*tailFactor)+C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
        (canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor))≤
    canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M*
      Γ*P*U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  have ht := globalTerminalConstant_nonneg A M
  have hRT : 0≤globalRayTripleConstant := by unfold globalRayTripleConstant;positivity
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpow : (B*U)^ε≤U^(deltaLoss+8*ε) := by
    calc
      _ ≤ (U^2)^ε := Real.rpow_le_rpow (mul_nonneg hB hU0.le) (by nlinarith) hε
      _ = U^(2*ε) := by rw [←Real.rpow_natCast U 2,←Real.rpow_mul hU0.le];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hheight : 1≤(1+‖t‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg t])
  have he : 1≤E*(1+‖t‖)^(2*J) := one_le_mul_of_one_le_of_one_le hE hheight
  have hdiag : (B*U)^ε*(Cd+Ct*tailFactor)≤
      U^(deltaLoss+8*ε)*(Cd+Ct*Tmax)*(E*(1+‖t‖)^(2*J)) := by
    calc
      _ ≤ (B*U)^ε*(Cd+Ct*Tmax) := by gcongr
      _ ≤ U^(deltaLoss+8*ε)*(Cd+Ct*Tmax) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  have hchild : canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor≤
      (6*(∫s : ℝ,firstLogDensity 0 s)^3*Clo+globalTerminalConstant A M*Chi)*
        (E*(1+‖t‖)^(2*J)) := by
    have hterm : globalTerminalConstant A M*Chi*terminalFactor≤
        globalTerminalConstant A M*Chi*(E*(1+‖t‖)^(2*J)) :=
      mul_le_mul_of_nonneg_left (hterminal.trans he) (mul_nonneg ht hChi)
    unfold canonicalDensityConstant
    nlinarith
  have hrest := mul_le_mul_of_nonneg_left hchild
    (mul_nonneg (mul_nonneg hC hRT) (Real.rpow_nonneg hU0.le (deltaLoss+8*ε)))
  have hsum := add_le_add hdiag hrest
  have hwhole := mul_le_mul_of_nonneg_left hsum
    (show 0≤(∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P by positivity)
  exact hwhole.trans_eq (by unfold canonicalBudgetCoefficient;ring)

end
section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstQuantitativeBudget_bounded (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Cd → 0≤Ct → 0≤Tmax → 0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A₀ Vmax*
          Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*U^(deltaLoss+8*ε)*E*(1+‖oldHeight‖)^(2*J) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_below_rank deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hCd hCt hTmax hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ htail hterminal ih
  have hb := hbound p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate
    pool blocks side windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ (zero_le_one.trans hE) hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hX:=hstate.column_pos
  have hF : 0≤F:=zero_le_one.trans hstate.label_ge_one
  have hP : 0≤((X/B^3)*(Real.exp 1*B)^3)*F := by positivity
  have hs := canonicalBudgetScalar_bound C Cd Ct Tmax Clo Chi A₀ Vmax Γ
    (((X/B^3)*(Real.exp 1*B)^3)*F) E oldHeight (Real.exp 1*B) U deltaLoss ε
    (globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)
    ((Ksrc/Z^η)/Z^(η*(N:ℝ))) J hC hCd hCt hTmax hClo.le hChi.le hΓ hP hE
    (by positivity) hBU hU hδ.le hε.le htail hterminal
  apply hb.trans
  convert hs using 1 ; ring

end

def reopeningScaleConstant (A M : ℝ) : ℝ := 1+Real.exp (A+1)+Real.exp M

def reopeningAuxiliaryScale (A M κ Z : ℝ) : ℝ := reopeningScaleConstant A M*Z^(κ+3)

lemma reopeningScaleConstant_one (A M : ℝ) : 1≤reopeningScaleConstant A M := by
  unfold reopeningScaleConstant
  linarith [Real.exp_pos (A+1),Real.exp_pos M]

lemma reopeningScaleConstant_exp (A M : ℝ) : Real.exp A≤reopeningScaleConstant A M := by
  have h : Real.exp A≤Real.exp (A+1) := Real.exp_le_exp.mpr (by linarith)
  unfold reopeningScaleConstant
  linarith [Real.exp_pos M]

theorem globalFirstRowCap_reopening (Z η X F Ksrc B : ℝ)
    (hZ : 0<Z) (hK : 0<Ksrc) (hB : 0<B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F =
      (Real.exp 1)^8*X^2*F^2*Z^η/Ksrc := by
  unfold globalFirstRowCap
  field_simp

theorem globalFirstRowCap_reopening_bound (Z η X F Ksrc B : ℝ)
    (hZ : 1≤Z) (_hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F ≤ (Real.exp 1)^8*Z^13 := by
  rw [globalFirstRowCap_reopening Z η X F Ksrc B (by linarith) (by linarith) (by linarith)]
  have hηZ : Z^η≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hη1
  calc
    _ ≤ (Real.exp 1)^8*X^2*F^2*Z^η := div_le_self (by positivity) hK
    _ ≤ (Real.exp 1)^8*(Z^3)^2*(Z^3)^2*Z := by gcongr
    _ = _ := by ring

theorem globalFirstRowCap_reopening_small_power (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F))^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hb := globalFirstRowCap_reopening_bound Z η X F Ksrc B hZ hη hη1 hX hXZ hF hFZ hK hB
  have hmax : max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)≤(Real.exp 1)^8*Z^13 :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he) (one_le_pow₀ hZ)) hb
  apply (Real.rpow_le_rpow (by positivity) hmax hδ).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
  norm_num

theorem reopeningAuxiliaryScale_bounds (A M κ Z η X F Ksrc B : ℝ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (_hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    let U := reopeningAuxiliaryScale A M κ Z
    1≤U ∧ Ksrc/Z^η≤U ∧ X/B^3≤U ∧ Real.exp 1*B≤U ∧ F≤U ∧ Z^κ≤U ∧
      Real.exp M≤U ∧ (X/B^3)*Real.exp M≤U ∧ (X/B^3)⁻¹≤U := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hCZ : C≤C*Z^(κ+3) := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hZ (by linarith))
  have hZ3 : Z^3≤Z^(κ+3) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; linarith)
  have hZκ : Z^κ≤Z^(κ+3) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hbase : Z^(κ+3)≤C*Z^(κ+3) := le_mul_of_one_le_left (by positivity) hC
  have hKcut : Ksrc/Z^η≤Z^3 :=
    (div_le_self (by linarith) (Real.one_le_rpow hZ hη)).trans hKZ
  have hell : X/B^3≤X := div_le_self (by linarith) (one_le_pow₀ hB)
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hBsup : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hCA : Real.exp (A+1)≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos M]
  have hCM : Real.exp M≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos (A+1)]
  have hinv : (X/B^3)⁻¹≤Real.exp A := by
    rw [inv_div]
    exact (div_le_iff₀ (by linarith : 0<X)).mpr hactive
  change 1≤C*Z^(κ+3) ∧ _
  refine ⟨hC.trans hCZ,hKcut.trans (hZ3.trans hbase),
    (hell.trans hXZ).trans (hZ3.trans hbase),?_,hFZ.trans (hZ3.trans hbase),
    hZκ.trans hbase,hCM.trans hCZ,?_,hinv.trans ((reopeningScaleConstant_exp A M).trans hCZ)⟩
  · exact hBsup.trans (mul_le_mul hCA hZ3 (by positivity) (by linarith))
  · calc
      _ ≤ Z^3*Real.exp M := mul_le_mul_of_nonneg_right (hell.trans hXZ) (Real.exp_pos _).le
      _ ≤ Z^(κ+3)*C := mul_le_mul hZ3 hCM (Real.exp_pos _).le (by positivity)
      _ = _ := mul_comm _ _

theorem globalFirstTailFactor_envelope (K ell B F U H : ℝ) (N : ℕ)
    (hK : 0≤K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F)
    (hU : 1≤U) (hH : 0≤H) (hKU : K≤U) (hiell : ell⁻¹≤U) :
    globalFirstTailFactor K ell B F U H N≤4096*U^20/(1+H)^N := by
  have hBi : B⁻¹≤1 := inv_le_one_of_one_le₀ hB
  have hFi : F⁻¹≤1 := inv_le_one_of_one_le₀ hF
  have hratio : K*U^2/(ell^2*B^2*F^2)≤U^5 := by
    calc
      _ = K*U^2*(ell⁻¹)^2*(B⁻¹)^2*(F⁻¹)^2 := by field_simp
      _ ≤ U*U^2*U^2*1^2*1^2 := by gcongr
      _ = _ := by ring
  have hone : 1+U≤2*U := by linarith
  have hinner : 1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2))≤16*U^8 := by
    calc
      _ ≤ 1+(2*U)^3*U^5 := by gcongr
      _ = 1+8*U^8 := by ring
      _ ≤ _ := by have hh : 1≤U^8 := one_le_pow₀ hU; linarith
  unfold globalFirstTailFactor
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (2*U)^4*(16*U^8)^2 := by gcongr
    _ = _ := by ring

theorem globalFirstTailFactor_reopening_power (A M κ Z η X F Ksrc B : ℝ) (N : ℕ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(20*(κ+3)-κ*N) := by
  have hZ0 : 0<Z := by linarith
  have hB0 : 0<B := by linarith
  have hX0 : 0<X := by linarith
  have hs := reopeningAuxiliaryScale_bounds A M κ Z η X F Ksrc B hκ hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hBsup : 1≤Real.exp 1*B := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hbound := globalFirstTailFactor_envelope (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
    (reopeningAuxiliaryScale A M κ Z) (Z^κ) N (by positivity) (by positivity) hBsup hF hs.1
    (by positivity) hs.2.1 hs.2.2.2.2.2.2.2.2
  apply hbound.trans
  have hden : (Z^κ)^N≤(1+Z^κ)^N := pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 κ]) N
  calc
    _ ≤ 4096*(reopeningAuxiliaryScale A M κ Z)^20/(Z^κ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      unfold reopeningAuxiliaryScale
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_mul_natCast hZ0.le,
        Real.rpow_sub hZ0]
      ring_nf

theorem globalFirstTailFactor_reopening_arbitrary_decay (A M κ R : ℝ) (hκ : 0<κ) :
    ∃N : ℕ,0<N ∧ ∀Z η X F Ksrc B : ℝ,
      1≤Z → 0≤η → 1≤X → X≤Z^3 → 1≤F → F≤Z^3 →
      1≤Ksrc → Ksrc≤Z^3 → 1≤B → B^3≤Real.exp A*X →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
        (4096*(reopeningScaleConstant A M)^20)*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((20*(κ+3)+R)/κ))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (20*(κ+3)+R)/κ<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : 20*(κ+3)-κ*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hκ).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro Z η X F Ksrc B hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  exact (globalFirstTailFactor_reopening_power A M κ Z η X F Ksrc B N hκ.le hZ hη
    hX hXZ hF hFZ hK hKZ hB hactive).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))

theorem globalFirstTailFactor_reopening_nat_decay (A M Z η X F Ksrc B : ℝ) (R : ℕ)
    (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningScaleConstant A M*Z^4) Z (R+80) ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(-(R:ℝ)) := by
  have h := globalFirstTailFactor_reopening_power A M 1 Z η X F Ksrc B (R+80)
    (by norm_num) hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hpow : 20*((1:ℝ)+3)-1*((R+80:ℕ):ℝ)=-(R:ℝ) := by push_cast; ring
  rw [hpow] at h
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at h ⊢
  exact h

lemma reopening_cutoff_ratio (Z η Ksrc : ℝ) (hZ : 0<Z) (hK : 0<Ksrc) :
    Ksrc/(Ksrc/Z^η)=Z^η := by field_simp

lemma globalFirstRowCap_reopening_rpow (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have hcap : 0≤globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F := by
    unfold globalFirstRowCap
    positivity
  exact (Real.rpow_le_rpow hcap (le_max_right 1 _) hδ).trans
    (globalFirstRowCap_reopening_small_power Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ)

lemma reopening_cube_bound (A M Z X B : ℝ) (hZ : 1≤Z) (_hX : 1≤X)
    (hXZ : X≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    Real.exp 1*B≤reopeningScaleConstant A M*Z^3 := by
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hC : Real.exp (A+1)≤reopeningScaleConstant A M := by
    unfold reopeningScaleConstant
    linarith [Real.exp_pos M]
  calc
    _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
    _ = Real.exp (A+1)*Z^3 := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem reopening_diagonal_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(13*deltaLoss+7*ε) := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hb := reopening_cube_bound A M Z X B hZ hX hXZ hB hactive
  have hprod : (Real.exp 1*B)*(C*Z^4)≤C^2*Z^7 := by
    calc
      _ ≤ (C*Z^3)*(C*Z^4) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hpow : ((Real.exp 1*B)*(C*Z^4))^ε≤(C^2)^ε*Z^(7*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hprod hε).trans_eq
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    norm_num
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*((C^2)^ε*Z^(7*ε)) :=
      mul_le_mul hcap hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0<Z)]; dsimp [C]; ring

theorem reopening_recursive_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (_hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(17*deltaLoss+32*ε) := by
  have hC : 0<reopeningScaleConstant A M := lt_of_lt_of_le zero_lt_one (reopeningScaleConstant_one A M)
  have he : (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)=
      reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε) := by
    rw [Real.mul_rpow hC.le (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    congr 2
    ring
  rw [he]
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*
      (reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε)) :=
      mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by
      have hh : 17*deltaLoss+32*ε=13*deltaLoss+(4*deltaLoss+32*ε) := by ring
      rw [hh]
      simp only [Real.rpow_add (by linarith : 0<Z)]
      ring

theorem reopening_diagonal_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(η+13*deltaLoss+7*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_diagonal_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hactive hδ hε) (by positivity)).trans_eq
  rw [show η+13*deltaLoss+7*ε=η+(13*deltaLoss+7*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

theorem reopening_recursive_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(η+17*deltaLoss+32*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_recursive_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hδ hε) (by positivity)).trans_eq
  rw [show η+17*deltaLoss+32*ε=η+(17*deltaLoss+32*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

end SecondPassArithmetic

end

end OAI
