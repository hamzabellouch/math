import OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization

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

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem outside_pool_coprime_excluded
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)) :
    IsCoprime (Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i})
      (∏P∈S,P) := by
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply (Ideal.isMaximal_def.mp (inferInstance : i.val.IsMaximal)).not_le_iff_codisjoint.mp
  intro hle
  apply excludedGenerator_not_mem_pool S D hSp i
  apply hle
  have hm : excludedGenerator S ∈ Ideal.span {excludedGenerator S} :=
    Ideal.subset_span (by simp)
  simpa only [excludedGenerator,span_idealGenerator] using hm

theorem cubeIdeal_eq_primeProduct_span (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    Ideal.span {primeProduct (poolPrimary F) v.support v}=cubeIdeal F v := by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  simp only [←Ideal.span_singleton_pow,poolPrimary_span F hF]
  unfold cubeIdeal
  apply Finset.prod_subset (Finset.subset_univ v.support)
  intro i hi hni
  rw [Finsupp.notMem_support_iff.mp hni,pow_zero]

theorem cubeIdeal_primeProduct_norm (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2=
      (Ideal.absNorm (cubeIdeal F v):ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,cubeIdeal_eq_primeProduct_span F hF]

theorem progressingActiveBin_cube_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X H₀ : ℝ) (j : ℕ)
    (hQ : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty) :
    (normLogScale j)^3≤b*X := by
  obtain ⟨v,hv⟩:=hQ
  have hbin := (Finset.mem_filter.mp hv).1
  have hactive := (Finset.mem_filter.mp hbin).1
  have hnorm := (activeCubeLogBin_norms S D b X j v hbin).1
  exact (pow_le_pow_left₀ (normLogScale_pos j).le hnorm 3).trans
    (Finset.mem_filter.mp hactive).2

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

theorem progressingCanonicalBin_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : ActualEisensteinCubic.O→*ℂ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      ∀j∈cubeLogRange (Real.exp A) X,
      let B:=normLogScale j
      let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
      Q'.Nonempty → ∀ξ : ℝ,
      B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ Q'
          (separatedCubeCoefficient
            (fun v=>reopenedCubeCoefficient H₀
              (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1)
              (cubeIdeal P v))
            (fun v=>(Ideal.absNorm (cubeIdeal P v):ℝ)) B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist g (oldHeight+ξ) (columnLog (poolPrimary P) (X/B^3) T)) z) K≤
        C*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cβ,hCβ,hβbound⟩:=outside_separated_cube_coefficient_bound ε hε
  let Cg:=Cβ*(Real.exp (A+1))^ε
  refine ⟨w₁,w₂,C₀*Cg^2,by positivity,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE
  dsimp only
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih j hj hQ ξ
  let B:=normLogScale j
  let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
  let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
  let β:=fun I v=>separatedCubeCoefficient
    (fun u=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal P u))
    (fun u=>(Ideal.absNorm (cubeIdeal P u):ℝ)) B ξ v
  have hB : 1≤B:=normLogScale_ge_one j
  have hBp : 0<B:=normLogScale_pos j
  have hactive : B^3≤Real.exp A*X:=progressingActiveBin_cube_bound S D (Real.exp A) X H₀ j hQ
  have hBscale : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*(Real.exp A*X) :=
        mul_le_mul_of_nonneg_left ((le_self_pow₀ hB (by decide : (3:ℕ)≠0)).trans hactive) (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add];ring
  have hbgrowth : (Real.exp 1*B)^ε≤(Real.exp (A+1))^ε*Z^(3*ε) := by
    calc
      _ ≤ (Real.exp (A+1)*Z^3)^ε :=
        Real.rpow_le_rpow (by positivity) hBscale hε.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
        norm_num
  have hΨ : ∀u,‖normHeightTwist Ψ oldHeight u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hstate.coefficient.norm_le hbase u)
  have hcoeff : ∀I∈labels,∀v∈Q',‖β I v‖≤Cg*Z^(3*ε) := by
    intro I hI v hv
    have hvbin: v∈activeCubeLogBin S D (Real.exp A) X j:=(Finset.mem_filter.mp hv).1
    obtain ⟨hlo,hhi⟩:=activeCubeLogBin_norms S D (Real.exp A) X j v hvbin
    exact (hβbound S D _ hΨ m (idealGenerator I) H₀ B ξ v hBp hlo hhi).trans
      ((mul_le_mul_of_nonneg_left hbgrowth hCβ.le).trans_eq (by dsimp only [Cg];ring))
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i k he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  have hpr (i : primePool P) : lambda^2∣poolPrimary P i-1 :=
    (primaryPrime_spec i.val (poolPrimary_ne_zero P hP i)).2.2.2
  have hn : ∀v∈Q',‖ConcreteTraceCRT.eisEmbedding
      (FirstPassCubeLabels.primeProduct (poolPrimary P) v.support v)‖^2≤Real.exp 1*B := by
    intro v hv
    rw [cubeIdeal_primeProduct_norm P hP]
    exact (activeCubeLogBin_norms S D (Real.exp A) X j v (Finset.mem_filter.mp hv).1).2
  have hp := hstep (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj hpr base (∏Q∈S,Q) Z Ψ m labels
    X F K hstate Finset.univ Q' β (Cg*Z^(3*ε)) (oldHeight+ξ) B E hbase
    (outside_pool_coprime_excluded S D hbad hSp) hZ hZbig hX hXZ hFZ
    (by dsimp only [Cg];positivity) hE hB hactive
    (progressingActiveBin_progress S D (Real.exp A) X Z F j hstate.label_ge_one hQ)
    hcoeff (fun v hv=>Finset.subset_univ _) hn ih
  have hpower : (Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε)=Z^(η+17*deltaLoss+38*ε) := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤Z),←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    norm_num
    ring
  have heq : C₀*(Cg*Z^(3*ε))^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖oldHeight+ξ‖)^(2*J)=
      (C₀*Cg^2)*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
    rw [Real.norm_eq_abs]
    calc
      _ = (C₀*Cg^2)*(X*F)^2*((Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε))*E*(1+|oldHeight+ξ|)^(2*J) := by ring
      _ = _ := by rw [hpower]
  exact (show _≤_ from hp).trans_eq heq

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
open UniqueFactorizationMonoid
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

def unitSupplement (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom u.val (Ideal.span {n}) else 0
  map_one' := by
    have hs : Supported (1:Ideal ActualEisensteinCubic.O):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:ActualEisensteinCubic.O)}=(1:Ideal ActualEisensteinCubic.O) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],ite_eq_left hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton, supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

private lemma supported_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp:=prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩

lemma unitSupplement_norm (u : ActualEisensteinCubic.Oˣ) (n : ActualEisensteinCubic.O) : ‖unitSupplement u n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

private lemma norm_eval_residue (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

lemma norm_residue_congruent (m : ℕ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(m:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Ideal.absNorm (Ideal.span {x})%m=Ideal.absNorm (Ideal.span {y})%m := by
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c:=(coords y).1
  let d:=(coords y).2
  let e:=(coords z).1
  let f:=(coords z).2
  have hy : y=eval c d:=(eval_coords y).symm
  have hx : x=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f) := by
    calc
      x=y+(m:ActualEisensteinCubic.O)*z:=by linear_combination hz
      _=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f):=by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  apply (ZMod.natCast_eq_natCast_iff' _ _ m).mp
  rw [hx,hy,norm_eval_residue,norm_eval_residue]
  simp

lemma supported_span_congruent_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Supported (Ideal.span {x})↔Supported (Ideal.span {y}) := by
  have h36:(36:ActualEisensteinCubic.O)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have hlam : lambda∣(36:ActualEisensteinCubic.O):=
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three).trans ⟨12,by norm_num⟩
  have htwo : (2:ActualEisensteinCubic.O)∣(36:ActualEisensteinCubic.O):=⟨18,by norm_num⟩
  have he (a : ActualEisensteinCubic.O) (ha : a∣x-y) : a∣x↔a∣y := by
    constructor
    · intro hx
      convert dvd_sub hx ha using 1 ; ring
    · intro hy
      convert dvd_add ha hy using 1 ; ring
  rw [supported_span_iff,supported_span_iff,he lambda (hlam.trans h36),he 2 (htwo.trans h36)]

theorem unitSupplement_periodic (u : ActualEisensteinCubic.Oˣ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    unitSupplement u x=unitSupplement u y := by
  have hs:=supported_span_congruent_mod_thirty_six x y hxy
  change (if _ then _ else _)=(if _ then _ else _)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [ite_eq_left hx,ite_eq_left hy]
    exact idealRowHom_unit_eq_of_norm_mod_thirty_six u _ _ hx.1 hy.1
      (supported_good _ hx) (supported_good _ hy) (norm_residue_congruent 36 x y hxy)
  · rw [ite_eq_right hx,ite_eq_right (fun hy=>hx (hs.mpr hy))]

private lemma rowTwist_zero_of_common_prime (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O)
    (P : Ideal ActualEisensteinCubic.O) (hp : Prime P) (hm : m∈P) (hn : n∈P) :
    rowTwist Ψ m f z n=0 := by
  have hPI:P∣Ideal.span {n}:=Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hn))
  have hm6:m^6∈P:=by
    rw [show m^6=m^5*m by ring]
    exact P.mul_mem_left _ hm
  have hx:m^6*f^4*z∈P:=P.mul_mem_right _ (P.mul_mem_right _ hm6)
  change Ψ n*idealRowHom _ (Ideal.span {n})=0
  rw [idealRowHom_zero_of_dvd _ hp hPI hx,mul_zero]

theorem rowTwist_unitSupplement (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    rowTwist Ψ m f (u.val*z)=unitSupplement u*rowTwist Ψ m f z := by
  ext n
  by_cases hn:Supported (Ideal.span {n})
  · change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n})=
      (if Supported (Ideal.span {n}) then _ else 0)*(Ψ n*idealRowHom _ (Ideal.span {n}))
    rw [ite_eq_left hn,show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,idealRowHom_argument_mul]
    ring
  · have hz:rowTwist Ψ m f (u.val*z) n=0 := by
      have hbad : lambda∣n ∨ (2:ActualEisensteinCubic.O)∣n := by
        simpa only [supported_span_iff,not_and_or,not_not] using hn
      rcases hbad with hLam|h2
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {lambda})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            exact PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) lambdaIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hmLam) (Ideal.mem_span_singleton.mpr hLam)
      · exact rowTwist_zero_of_common_prime Ψ m f _ n (Ideal.span {(2:ActualEisensteinCubic.O)})
          (Ideal.prime_of_isPrime (by
            rw [ne_eq,Ideal.span_singleton_eq_bot]
            norm_num) twoIdeal_maximal.isPrime)
          (Ideal.mem_span_singleton.mpr hm2) (Ideal.mem_span_singleton.mpr h2)
    change rowTwist Ψ m f (u.val*z) n=(if Supported (Ideal.span {n}) then _ else 0)*_
    rw [hz,ite_eq_right hn,zero_mul]

theorem rowTwist_unitSupplement_base (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    rowTwist Ψ m f (u.val*z)=rowTwist (unitSupplement u*Ψ) m f z := by
  rw [rowTwist_unitSupplement Ψ m f z u hmLam hm2]
  ext n
  change unitSupplement u n*(Ψ n*idealRowHom _ _)=(unitSupplement u n*Ψ n)*idealRowHom _ _
  ring

theorem unitRowFamily_transport (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ}
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) (hmLam : lambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m) :
    CompletedUnitRows.unitRowFamily Ψ m u f I=
      CompletedUnitRows.unitRowFamily (unitSupplement u*Ψ) m 1 f I := by
  simp only [CompletedUnitRows.unitRowFamily,Units.val_one,one_mul]
  exact rowTwist_unitSupplement_base Ψ m (ConcretePrimeRowBridge.idealGenerator f.val)
    (ConcretePrimeRowBridge.idealGenerator I) u hmLam hm2

theorem unitSupplement_mul_periodic (u : ActualEisensteinCubic.Oˣ) (Ψ : ActualEisensteinCubic.O→*ℂ) (Q : Ideal ActualEisensteinCubic.O)
    (hΨ : ∀x y : ActualEisensteinCubic.O,x-y∈Q→Ψ x=Ψ y) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈Q*Ideal.span {(36:ActualEisensteinCubic.O)}) :
    (unitSupplement u*Ψ) x=(unitSupplement u*Ψ) y := by
  simp only [MonoidHom.mul_apply]
  rw [unitSupplement_periodic u x y (Ideal.mul_le_right hxy),hΨ x y (Ideal.mul_le_left hxy)]

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma kernelBarrier_sublevel_isCompact (T : ℝ) :
    IsCompact {q : KernelQuotient | kernelQuotientBarrier 2 3 q≤T} := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max 3 T)
  apply hcompact.of_isClosed_subset
    (isClosed_le (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)) continuous_const)
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max 3 T) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max 3 T) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    have hh : 3<p.1.2 := (le_max_left 3 T).trans_lt hp.2.2
    change kernelQuotientBarrier 2 3 (fordOrbitChart globalKubotaKernel r p)≤T at hq
    rw [kernelQuotientBarrier_fordCusp 2 3 (by norm_num) (by norm_num) r p hh] at hq
    exact (not_lt_of_ge hq) ((le_max_right 3 T).trans_lt hp.2.2)

def kernelExhaustionProfile (n : ℕ) (v : ℝ) : ℝ :=
  1-cuspTransition 1 2 (v/((n:ℝ)+1))

def kernelExhaustionCutoff (n : ℕ) (q : KernelQuotient) : ℝ :=
  kernelExhaustionProfile n (kernelQuotientBarrier 2 3 q)

lemma kernelExhaustionProfile_smooth (n : ℕ) :
    ContDiff ℝ ∞ (kernelExhaustionProfile n) := by
  unfold kernelExhaustionProfile cuspTransition
  fun_prop

lemma kernelExhaustionCutoff_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelExhaustionCutoff n) :=
  (kernelExhaustionProfile_smooth n).contMDiff.comp
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))

lemma kernelExhaustionProfile_bounds (n : ℕ) (v : ℝ) :
    0≤kernelExhaustionProfile n v ∧ kernelExhaustionProfile n v≤1 := by
  have h0 := Real.smoothTransition.nonneg ((v/((n:ℝ)+1)-1)/(2-1))
  have h1 := Real.smoothTransition.le_one ((v/((n:ℝ)+1)-1)/(2-1))
  change 0≤1-Real.smoothTransition _ ∧ 1-Real.smoothTransition _≤1
  constructor <;> linarith

lemma kernelExhaustionProfile_one (n : ℕ) (v : ℝ) (hv : v≤(n:ℝ)+1) :
    kernelExhaustionProfile n v=1 := by
  rw [kernelExhaustionProfile,cuspTransition_zero 1 2 _ (by norm_num)
    ((div_le_one (by positivity)).mpr hv),sub_zero]

lemma kernelExhaustionProfile_zero (n : ℕ) (v : ℝ) (hv : 2*((n:ℝ)+1)≤v) :
    kernelExhaustionProfile n v=0 := by
  rw [kernelExhaustionProfile,cuspTransition_one 1 2 _ (by norm_num)
    ((le_div_iff₀ (by positivity)).mpr hv),sub_self]

lemma kernelExhaustionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (kernelExhaustionCutoff n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (kernelBarrier_sublevel_isCompact (2*((n:ℝ)+1)))
  intro q hq
  change kernelQuotientBarrier 2 3 q≤2*((n:ℝ)+1)
  by_contra h
  exact hq (kernelExhaustionProfile_zero n _ (le_of_not_ge h))

lemma kernelExhaustionCutoff_bounds (n : ℕ) (q : KernelQuotient) :
    0≤kernelExhaustionCutoff n q ∧ kernelExhaustionCutoff n q≤1 :=
  kernelExhaustionProfile_bounds n _

lemma kernelExhaustionCutoff_eventually_one (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n q=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply kernelExhaustionProfile_one
  have hh : (N:ℝ)≤n := by exact_mod_cast hn
  linarith

lemma kernelExhaustionCutoff_eventually_one_near (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n =ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : kernelQuotientBarrier 2 3 q<(n:ℝ)+1 := by
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  filter_upwards [(kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hh]
    with p hp
  exact kernelExhaustionProfile_one n _ hp.le

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspTransition_euler_bounded (a b : ℝ) (hab : a<b) :
    ∃C : ℝ,0≤C ∧ ∀v,|v*deriv (cuspTransition a b) v|≤C := by
  have hc : HasCompactSupport (fun v => v*deriv (cuspTransition a b) v) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro v hv
    by_contra hnot
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hnot
    exact hv (by change v*deriv (cuspTransition a b) v=0; rw [(cuspTransition_derivatives a b v hab hout).1,mul_zero])
  have hcont : Continuous (fun v => v*deriv (cuspTransition a b) v) :=
    continuous_id.mul ((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2.continuous)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max C 0,le_max_right _ _,fun v => (hC v).trans (le_max_left _ _)⟩

lemma cuspRemainderProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspRemainderProfile a b s) v :=
  (positiveHeightPower_contDiffAt s v hv.ne').sub (cuspSeedProfile_contDiffAt a b s v hv)

lemma cuspRemainderProfile_euler (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    (v:ℂ)*deriv (cuspRemainderProfile a b s) v=
      positiveHeightPower s v *
        (((1-cuspTransition a b v:ℝ):ℂ)*s-((v*deriv (cuspTransition a b) v:ℝ):ℂ)) := by
  have h := (positiveHeightPower_hasDerivAt s v hv.ne').sub
    (cuspSeedProfile_hasDerivAt a b s v hv.ne')
  change HasDerivAt (cuspRemainderProfile a b s) _ v at h
  rw [h.deriv]
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ; ring

lemma cuspRemainderProfile_euler_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C) (v : ℝ) (hv : 0<v) :
    ‖(v:ℂ)*deriv (cuspRemainderProfile a b s) v‖≤(‖s‖+C)*v^s.re := by
  rw [cuspRemainderProfile_euler a b s v hv,norm_mul,
    positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hχ0 : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hχ1 : 1-cuspTransition a b v≤1 := by
    have h := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at h
    linarith
  have hfactor : ‖((1-cuspTransition a b v:ℝ):ℂ)*s-
      ((v*deriv (cuspTransition a b) v:ℝ):ℂ)‖≤‖s‖+C := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul,Complex.norm_of_nonneg hχ0,Complex.norm_real,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_right hχ1 (norm_nonneg s)
    linarith [hC v]
  have hh := mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hv.le s.re)
  simpa only [mul_comm (v^s.re)] using hh

lemma cuspRemainderProfile_deriv_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b<v) : deriv (cuspRemainderProfile a b s) v=0 := by
  have he : cuspRemainderProfile a b s =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hv,Ioi_mem_nhds hbv] with y hy hyb
    exact cuspRemainderProfile_zero a b s y hab hy hyb.le
  exact he.deriv_eq.trans (deriv_const v 0)

lemma rowLogD_hyperbolic_bound (u : Fin 2→ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) : |p 2*rowLogD u p j|≤1 := by
  have he := rowLog_eikonal u hu p hp
  have hsq : (p 2*rowLogD u p j)^2≤1 := by
    fin_cases j
    · change (p 2*rowLogD u p 0)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 1),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 1)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 2)^2≤1
      nlinarith [sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 1)]
  exact (abs_le).mpr ⟨by nlinarith,by nlinarith⟩

lemma cuspRemainder_row_scaled_deriv_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*(rowHeight u p)^s.re := by
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
  rw [hd.deriv]
  have he : (p 2:ℂ)*(deriv (cuspRemainderProfile a b s) (rowHeight u p)*
      (rowHeight u p:ℂ)*(rowLogD u p j:ℂ))=
      (((p 2*rowLogD u p j):ℝ):ℂ)*
        ((rowHeight u p:ℂ)*deriv (cuspRemainderProfile a b s) (rowHeight u p)) := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) (rowLogD_hyperbolic_bound u hu p hp j)).trans
  exact cuspRemainderProfile_euler_bound a b s C hC _ (rowHeight_pos u hu p hp)

end CubicEisenstein

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem progressingCanonicalFamily_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (hgOne : ∀u,|u|≤columnWindowRadius (Real.exp (-A)) (Real.exp A)→g u=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀(W : ℝ→ℂ) (hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A))
      (hW : ContDiff ℝ ∞ W), HasCompactSupport W →
      ∃C : ℝ,0≤C ∧
      ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : ActualEisensteinCubic.O→*ℂ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      Real.exp A*X≤D →
      let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
        m (idealGenerator I) z W X) K≤
      2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z)
          W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K+
      C*(X*F)^2*Z^(η+17*deltaLoss+39*ε)*E*(1+|oldHeight|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩:=
    progressingCanonicalBin_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cb,hCb,hcard⟩:=cubeLogRange_sq_small_power (Real.exp A) ε (Real.exp_pos _).le hε
  refine ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro W hs hW hWc
  let moment:=∫ξ : ℝ,‖reopeningCoefficient W (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hs hW ξ‖*(1+|ξ|)^J
  refine ⟨2*Cb*C₀*moment^2,by positivity,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE hD
  dsimp only
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih
  have hsource:=hstep S D hbad hSp base Z Ψ m labels X F K E oldHeight
    hstate hbase hZ hZbig hX hXZ hFZ hE ih
  have hwhole:=progressingCanonicalFamily_energy S D hbad hSp labels Ψ m W
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) (Real.exp_pos _).le hs hW hWc
    g hgOne X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) K
    (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E) oldHeight J hstate.column_pos
    (zero_lt_one.trans_le hstate.row_ge_one) (by positivity) hD hsource
  have hcount:=hcard X Z hstate.column_pos.le hZ.le hXZ
  have hpower : Z^ε*Z^(η+17*deltaLoss+38*ε)=Z^(η+17*deltaLoss+39*ε) := by
    rw [←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    ring
  apply hwhole.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 2*(Cb*Z^ε)*(C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2 := by
      change 2*((cubeLogRange (Real.exp A) X).card:ℝ)^2*
        (C₀*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E)*(1+|oldHeight|)^(2*J)*moment^2≤_
      gcongr
    _ = (2*Cb*C₀*moment^2)*(X*F)^2*(Z^ε*Z^(η+17*deltaLoss+38*ε))*E*(1+|oldHeight|)^(2*J) := by ring
    _ = _ := by rw [hpower]

end CanonicalRowCompletion

end

end OAI
