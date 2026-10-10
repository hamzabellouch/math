import OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
import OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy

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
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalShortState_from_certificate
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (ε κ : ℝ) (hε : 0<ε) (hκ : 0<κ) :
    ∃d : ℕ,∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
      ∃C : ℝ,0≤C ∧ ∀(θ Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      C*(X*F)^2*Z^(κ+7*ε-(1:ℝ)/40)*(1+|θ|)^d := by
  obtain ⟨d,hshort⟩:=canonicalShortState_uniform_twist
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨Cs,hCs,hsbound⟩:=hshort W hs hW
  obtain ⟨Cm,hCm,hm⟩:=hmodels A hA W hs hW κ hκ
  refine ⟨Cs*Cm,mul_nonneg hCs hCm,?_⟩
  intro θ Z η Ψ m labels X F K hstate hZ hZbig hη hbudget hfixed
  by_cases hF : F<Z^((1:ℝ)/1000)
  · have hgeometry:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    obtain ⟨rays,lengthScale,hsize,hformula⟩:=hm Z K X F θ hZ hstate.row_ge_one hstate.column_pos
      hstate.label_ge_one hF.le Ψ hstate.coefficient m hstate.mask_ne_zero hgeometry.2.2.2.2
    have hb:=hsbound θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed lengthScale (fun _=>hformula)
    calc
      _ ≤ (Cs*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=hb
      _ = Cs*(1+|θ|)^d*((rays:ℝ)^2*‖lengthScale‖^2)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by
        rw [Real.norm_eq_abs]
        ring
      _ ≤ Cs*(1+|θ|)^d*(Cm*Z^κ)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by gcongr
      _ = _ := by
        rw [show κ+7*ε-(1:ℝ)/40=κ+(7*ε-(1:ℝ)/40) by ring,
          Real.rpow_add (zero_lt_one.trans_le hZ)]
        ring
  · have hb:=hsbound θ 0 S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed 0 (fun hf=>False.elim (hF hf))
    have hz : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤0 := by
      simpa only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul] using hb
    exact hz.trans (by positivity)

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalLog_actual_step
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) :
    ∃d : ℕ,∀J : ℕ,d≤2*J →
    ∃child : Bool→Bool→ℝ→ℂ,
      (∀side neg,ContDiff ℝ ∞ (child side neg)) ∧
      (∀side neg s,child side neg s≠0→|s|≤2*A+11) ∧
      ∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
      ∃C : ℝ,0≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K E t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      1≤X → Real.exp A*X≤D → 1≤E →
      (∀side neg (Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏P∈S,P) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        outsideLogEnergy S D hbad (normHeightTwist Ψ' s) m' labels' (child side neg) X' K'≤
          E*(X'*F')^2*(1+‖s‖)^(2*J)) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
  obtain ⟨d,hshort⟩:=canonicalShortState_from_certificate S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels A hA η η hη hη
  refine ⟨d,?_⟩
  intro J hJ
  obtain ⟨g,v,hgc,hvc,hgone,hgb,hwin,hvb⟩:=fixed_reopening_profiles A hA
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  obtain ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hlarge⟩:=
    progressingCanonicalFamily_closed_step g v A (2*A+4) (2*A+5) (by linarith) (by linarith)
      hgb hvb hwin hgone η η η hη hη hη hηsmall hbudget' J
  let child : Bool→Bool→ℝ→ℂ:=fun side neg=>
    orientedLogProfile neg ((if side then w₁ else w₂) (if neg then 5 else 6))
  have hcs : ∀side neg,ContDiff ℝ ∞ (child side neg) := by
    intro side neg
    cases side <;> cases neg
    · exact hws₂ 6
    · exact Complex.conjCLE.contDiff.comp (hws₂ 5)
    · exact hws₁ 6
    · exact Complex.conjCLE.contDiff.comp (hws₁ 5)
  have hcb : ∀side neg s,child side neg s≠0→|s|≤2*A+11 := by
    intro side neg s hn
    have hnorm (w : Fin 7→ℝ→ℂ) (hw : ∀i t,w i t≠0→|t|≤(2*A+4)+7)
        (i : Fin 7) (hi : w i s≠0) : |s|≤2*A+11 := by
      have hh:=hw i s hi
      linarith
    cases side <;> cases neg
    · exact hnorm w₂ hwb₂ 6 hn
    · apply hnorm w₂ hwb₂ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
    · exact hnorm w₁ hwb₁ 6 hn
    · apply hnorm w₁ hwb₁ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
  refine ⟨child,hcs,hcb,?_⟩
  intro V hVs hV
  let W : ℝ→ℂ:=radialFromLog V hVs A hV
  have hW : ContDiff ℝ ∞ W:=(radialFromLog V hVs A hV).smooth ⊤
  have hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A):=
    fun s hs=>radialFromLog_support V hVs A hV s hs
  obtain ⟨Cs,hCs,hsmall⟩:=hshort W hs hW
  obtain ⟨Cl,hCl,hlong⟩:=hlarge W hs hW (radialFromLog_hasCompactSupport V hVs A hV)
  refine ⟨Cs+Cl,add_nonneg hCs hCl,?_⟩
  intro D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hD hE ih
  obtain ⟨hXZ,hFZ⟩:=canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
    hZbig hX hstate.label_ge_one hstate.mass_le
  have hsbound:=hsmall t Z η Ψ m labels X F K hstate hZ.le hZbig hη.le hbudget hfixed
  have hb:=hlong S D hbad hSp base Z Ψ m labels X F K E t hstate hbase hZ hZbig
    hX hXZ hFZ hE hD
  dsimp only at hb
  have hlbound:=hb (by
    intro side Ψ' m' labels' X' F' K' hs' hr s
    exact ⟨ih side true Ψ' m' labels' X' F' K' hs' hr s,
      ih side false Ψ' m' labels' X' F' K' hs' hr s⟩)
  have he : η+17*η+39*η=57*η:=by ring
  rw [he] at hlbound
  have hp : Z^(η+7*η-(1:ℝ)/40)≤Z^(57*η):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have ht : (1+|t|)^d≤(1+|t|)^(2*J):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hs' : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ t) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      Cs*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
    calc
      _ ≤ Cs*(X*F)^2*Z^(η+7*η-(1:ℝ)/40)*(1+|t|)^d:=hsbound
      _ ≤ Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=by gcongr
      _ ≤ (Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J))*E:=
        le_mul_of_one_le_right (by positivity) hE
      _ = _:=by ring
  rw [outsideLogEnergy_eq_completed S D hbad (normHeightTwist Ψ t) m labels V hVs A hV X K hstate.column_pos]
  exact hlbound.trans ((add_le_add hs' le_rfl).trans_eq (by ring))

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem outsideLogEnergy_finite_rank
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    ∀(A : ℝ),0≤A → ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V →
    (∀s,V s≠0→|s|≤A) → ∃C : ℝ,1≤C ∧
    ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      fixedDepthRank Z K≤r → Real.exp (radiusIter A r)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^(57*η*(r:ℝ))*(X*F)^2*(1+|t|)^d := by
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  induction r with
  | zero =>
    intro A hA
    refine ⟨0,?_⟩
    intro V hVs hV
    obtain ⟨C,hC,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget'
      (Or.inl (Nat.eq_zero_of_le_zero hr))
    simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,pow_zero] using
      hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (sq_nonneg (X*F)))
  | succ r ih =>
    intro A hA
    obtain ⟨dc,hchild⟩:=ih (2*A+11) (by linarith)
    obtain ⟨ds,hstep⟩:=canonicalLog_actual_step S hSp hbad base hbase ρ q levelBound
      hρ hq hlevel hmodels A hA η hη hηsmall hbudget
    let J : ℕ:=dc+ds
    have hdchild : dc≤2*J:=by dsimp [J];omega
    have hdstep : ds≤2*J:=by dsimp [J];omega
    obtain ⟨child,hcs,hcb,hparent⟩:=hstep J hdstep
    choose childC hchildC using (fun side neg=>hchild (child side neg) (hcs side neg) (hcb side neg))
    have hcnonneg (side neg : Bool) : 0≤childC side neg:=zero_le_one.trans (hchildC side neg).1
    let E0 : ℝ:=1+∑side : Bool,∑neg : Bool,childC side neg
    have hE0 : 1≤E0:=by
      have hs : 0≤∑side : Bool,∑neg : Bool,childC side neg:=
        Finset.sum_nonneg (fun side _=>Finset.sum_nonneg (fun neg _=>hcnonneg side neg))
      exact le_add_of_nonneg_right hs
    have hcE (side neg : Bool) : childC side neg≤E0:=by
      have h1 : childC side neg≤∑j : Bool,childC side j:=
        Finset.single_le_sum (fun j _=>hcnonneg side j) (Finset.mem_univ neg)
      have h2 : (∑j : Bool,childC side j)≤∑i : Bool,∑j : Bool,childC i j:=
        Finset.single_le_sum (fun i _=>Finset.sum_nonneg (fun j _=>hcnonneg i j)) (Finset.mem_univ side)
      exact h1.trans (h2.trans (le_add_of_nonneg_left zero_le_one))
    refine ⟨2*J,?_⟩
    intro V hVs hV
    obtain ⟨Ct,hCt,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    obtain ⟨Cp,hCp,hp⟩:=hparent V hVs hV
    let C : ℝ:=1+Ct+Cp*E0
    have hC : 1≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have htC : Ct≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have hpC : Cp*E0≤C:=by dsimp [C];linarith
    refine ⟨C,hC,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hZ0 : 0<Z:=zero_lt_one.trans hZ
    have hpow : 1≤Z^(57*η*((r+1:ℕ):ℝ)):=
      Real.one_le_rpow hZ.le (by positivity)
    have hheight : 1≤(1+|t|)^(2*J):=one_le_pow₀ (by linarith [abs_nonneg t])
    by_cases hstop : fixedDepthRank Z K=0 ∨ X≤1
    · have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget' hstop
      apply hb.trans
      calc
        Ct*(X*F)^2≤C*(X*F)^2:=mul_le_mul_of_nonneg_right htC (sq_nonneg _)
        _ ≤ C*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by
          calc
            _ ≤ (C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)):=
              le_mul_of_one_le_right (by positivity) hpow
            _ ≤ ((C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)))*(1+|t|)^(2*J):=
              le_mul_of_one_le_right (by positivity) hheight
            _ = _:=by ring
    · have hX : 1≤X:=(lt_of_not_ge (fun hh=>hstop (Or.inr hh))).le
      have hXZ : X≤Z^3:=(canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
        hZbig hX hstate.label_ge_one hstate.mass_le).1
      have hDparent : Real.exp A*X≤D:=
        common_pool_parent A Z X D (r+1) hA hZ0.le hstate.column_pos.le hXZ hD
      let E : ℝ:=E0*Z^(57*η*(r:ℝ))
      have hEr : 1≤Z^(57*η*(r:ℝ)):=Real.one_le_rpow hZ.le (by positivity)
      have hE : 1≤E:=by
        change 1≤E0*Z^(57*η*(r:ℝ))
        simpa only [one_mul] using mul_le_mul hE0 hEr zero_le_one (zero_le_one.trans hE0)
      have hb:=hp D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hDparent hE
      have hbound : outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
          Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=hb (by
        intro side neg Ψ' m' labels' X' F' K' hs hr' s
        have hrchild : fixedDepthRank Z K'≤r:=by omega
        have hDchild : Real.exp (radiusIter (2*A+11) r)*Z^3≤D:=by
          simpa only [radiusIter_succ] using hD
        have hh:=(hchildC side neg).2 D Z Ψ' m' labels' X' F' K' s hs hZ hZbig hfixed hrchild hDchild
        apply hh.trans
        rw [Real.norm_eq_abs]
        change childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2*(1+|s|)^dc≤_
        have hcscale : childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2≤
            (E0*Z^(57*η*(r:ℝ)))*(X'*F')^2:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcE side neg) (Real.rpow_nonneg hZ0.le _)) (sq_nonneg _)
        have hheight' : (1+|s|)^dc≤(1+|s|)^(2*J):=
          pow_le_pow_right₀ (by linarith [abs_nonneg s]) hdchild
        exact mul_le_mul hcscale hheight' (by positivity) (by positivity))
      apply hbound.trans
      have hexp : Z^(57*η*(r:ℝ))*Z^(57*η)=Z^(57*η*((r+1:ℕ):ℝ)):=by
        rw [←Real.rpow_add hZ0]
        congr 1
        push_cast
        ring
      calc
        Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J)=
            (Cp*E0)*(Z^(57*η*(r:ℝ))*Z^(57*η))*(X*F)^2*(1+|t|)^(2*J):=by dsimp [E];ring
        _ = (Cp*E0)*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by rw [hexp]
        _ ≤ _:=by gcongr

def canonicalDescentPadding (ε : ℝ) : ℝ:=canonicalPadding ε 57/2

theorem canonicalDescentPadding_budget (ε : ℝ) (hε : 0<ε) :
    0<canonicalDescentPadding ε ∧ canonicalDescentPadding ε≤(1:ℝ)/1000 ∧
    3000*canonicalDescentPadding ε≤(1:ℝ)/80 ∧
    171000*canonicalDescentPadding ε≤ε := by
  have h:=canonicalPadding_budget ε 57 hε (by norm_num)
  dsimp [canonicalDescentPadding]
  refine ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2.1],?_⟩
  have ht:=h.2.2.2.2.1
  nlinarith [h.1]

theorem outsideLogEnergy_state_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (hloss : 171000*η≤ε)
    (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_finite_rank S hSp hbad base hbase ρ q levelBound
    hρ hq hlevel hmodels η hη hηsmall hbudget 3000 A hA
  refine ⟨d,?_⟩
  intro V hVs hV
  obtain ⟨C,hC,hbound⟩:=hd V hVs hV
  refine ⟨C,hC,?_⟩
  intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hD
  have hr:=fixedDepthRank_initial Z K hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global
  have hb:=hbound D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
  have he : 57*η*(3000:ℝ)≤ε:=by linarith
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) (zero_le_one.trans hC)

theorem outsideLogEnergy_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z (canonicalDescentPadding ε) Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  have h:=canonicalDescentPadding_budget ε hε
  exact outsideLogEnergy_state_small_power S hSp hbad base hbase ρ q levelBound hρ hq hlevel hmodels
    ε (canonicalDescentPadding ε) h.1 h.2.1 h.2.2.1 h.2.2.2 A hA

end CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels (primeProductNorm)
open InitialMeanSquare hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)
open ConcreteTraceCRT (eisEmbedding)

theorem initialCanonicalState
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (base Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : IsBaseRayTwist base Ψ) (Z η X lengthScale K : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hX : 1≤X) (hL : 1≤lengthScale) (hK : 1≤K)
    (R : Finset (OutsidePrimeIndex S D)) (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O))
    (hmass : X*lengthScale≤Z^2)
    (hinv : K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R)≤
      X*lengthScale*Z^(-(1:ℝ)/20))
    (hlabels : ∀z∈T,Admissible z.1 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale)
    (houtside : ∀z∈T,IsCoprime z.1 (∏P∈S,P)) :
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ
      (primeSubsetGenerator (fun i=>Ideal.span {outsidePrime S D i}) R)
      (T.image Prod.fst) X lengthScale K := by
  let p:=outsidePrime S D
  have hp:=outsidePrime_ne_zero S hbad D
  let:=outsidePrime_maximal S hbad D
  have hN : 1≤primeProductNorm p R:=primeProductNorm_ge_one p hp R
  have hN0 : 0≤primeProductNorm p R:=zero_le_one.trans hN
  have hmod : 1 ≤ initialExcludedNorm S*primeProductNorm p R:=
    one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hN
  have hdecay : Z^(-(1:ℝ)/20)≤1:=by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -(1:ℝ)/20≤0)
  have hKmass : K≤X*lengthScale := by
    calc
      K ≤ K*(initialExcludedNorm S*primeProductNorm p R):=
        le_mul_of_one_le_right (zero_le_one.trans hK) hmod
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale:=mul_le_of_le_one_right (by positivity) hdecay
  have hKg : K≤Z^3 :=
    (hKmass.trans hmass).trans (pow_le_pow_right₀ hZ (by decide : (2:ℕ)≤3))
  refine ⟨hΨ,primeSubsetGenerator_ne_zero _ _,by linarith,hL,hK,hKg,
    hmass.trans (canonicalRankMass_initial Z _),?_,?_⟩
  · rw [primeSubsetGenerator_norm_eq_productNorm]
    calc
      K*primeProductNorm p R ≤ K*(initialExcludedNorm S*primeProductNorm p R) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
        exact le_mul_of_one_le_left hN0 (initialExcludedNorm_ge_one S)
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hZ
        unfold canonicalRankMargin
        have hn : 0≤η*((3000-fixedDepthRank Z K:ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
        linarith
  · intro I hI
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact ⟨(hlabels z hz).1.1,(hlabels z hz).1.2.1,houtside z hz,(hlabels z hz).2⟩

theorem canonicalInitialThreshold (S : Finset (Ideal ActualEisensteinCubic.O)) :
    ∃Z₀ : ℝ,1≤Z₀ ∧ ∀Z : ℝ,Z₀≤Z →
      1<Z ∧ Real.exp 9000≤Z ∧
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) := by
  let c:=2*‖eisEmbedding (excludedGenerator S)‖^2
  let Z₀:=2+Real.exp 9000+c^80
  have hc : 0≤c:=by dsimp only [c];positivity
  have hp : 0≤c^80:=pow_nonneg hc _
  have he:=Real.exp_pos (9000:ℝ)
  refine ⟨Z₀,by dsimp only [Z₀];linarith,?_⟩
  intro Z hZ
  have hZ1 : 1<Z:=by dsimp only [Z₀] at hZ;linarith
  refine ⟨hZ1,by dsimp only [Z₀] at hZ;linarith,?_⟩
  have hpow : c^80≤Z:=by dsimp only [Z₀] at hZ;linarith
  have hh := (Real.le_rpow_inv_iff_of_pos hc (by linarith : 0≤Z) (by norm_num : (0:ℝ)<80)).mpr
    (show c^(80:ℝ)≤Z by simpa only [Real.rpow_ofNat] using hpow)
  simpa only [one_div] using hh

end CanonicalRowCompletion

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

theorem densityChildEnergy_from_canonical_heights {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ→ℂ)
    (X F K E : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels) (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K)
    (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hl (a : ℝ) : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₁ m
      T labels V₁ X K a 0 hX hK true false hlabels hrows hzero
    simp only [secondSignedHeight,ite_true,zero_sub] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ (-a)) (by norm_num : (0:ℝ)≤6)).trans_eq
      (by rw [norm_neg];ring))
  have hr (a : ℝ) : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₂ m
      T labels V₂ X K a 0 hX hK false true hlabels hrows hzero
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ a) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2:=by positivity
  have hd:=densityChildEnergy_polynomial_bound p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X J
    (6*E*(X*F)^2) (6*E*(X*F)^2) hb hb hl hr
  rwa [Real.mul_self_sqrt hb] at hd

end SecondPassIntegration
end

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O
open FiniteGaussPhase hiding O

theorem quadratic_ray_cross (a b : ActualEisensteinCubic.O) (ha : a≠0) (hb : b≠0)
    [(Ideal.span {a}).IsMaximal] [(Ideal.span {b}).IsMaximal]
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (hca : ringChar (ActualEisensteinCubic.O⧸Ideal.span {a})≠2)
    (hcb : ringChar (ActualEisensteinCubic.O⧸Ideal.span {b})≠2) :
    quadraticRayValue (residue (a*b))=
      character (Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)*
      character (Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a)*
      quadraticRayValue (residue a)*quadraticRayValue (residue b) := by
  let p : Bool→ActualEisensteinCubic.O:=fun i=>if i then a else b
  have hp : ∀i,p i≠0:=by
    intro i
    cases i
    · exact hb
    · exact ha
  let (i : Bool) : (Ideal.span {p i}).IsMaximal := by
    cases i <;> dsimp [p] <;> infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [p,Function.onFun,isCoprime_comm]
  have hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2 := by
    intro i
    cases i
    · exact hcb
    · exact hca
  have h:=quadraticGamma_product p hp hcop hc
  simp only [quadraticGammaO_eq_rayValue] at h
  have ht : cofactor p true=b:=by
    apply mul_left_cancel₀ ha
    simpa [p] using prime_mul_cofactor p true
  have hf : cofactor p false=a:=by
    apply mul_left_cancel₀ hb
    simpa [p,mul_comm] using prime_mul_cofactor p false
  simp only [Fintype.prod_bool,ht,hf] at h
  simpa [p,mul_comm,mul_left_comm,mul_assoc] using h

theorem quadraticRayValue_ne_zero_of_odd (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : quadraticRayValue r≠0 := by
  rcases r with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      zpow_neg,Complex.I_sq,Complex.I_pow_three,Complex.inv_I,ZMod.val] at * <;>
      intro h <;> solve | (have hh:=congrArg Complex.re h; norm_num at hh) | (have hh:=congrArg Complex.im h; norm_num at hh)

end QuadraticAllOddCRT

end

end OAI
