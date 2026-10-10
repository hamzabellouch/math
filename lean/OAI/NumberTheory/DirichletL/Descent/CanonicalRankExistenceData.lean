import OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteRankNormalized
import OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteBudget
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankPuncture

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CompletePoolRankMoments (q D:ℕ) {σ:Type}[DecidableEq σ]
    (slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (base:O→*ℂ)(W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
  let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q);
  letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
  CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ base slots lists a W
    Z Mmax Fcap z c eps A K degree

def rankRowCap (n:ℕ)(cutoff:ℝ):ℝ:=3*((n:ℝ)-1)*cutoff/4

def rankTotalCap (n:ℕ)(L eta:ℝ):ℝ:=L-15*(n:ℝ)*eta

def rankMargin (n:ℕ)(cstar eta:ℝ):ℝ:=cstar/2+7*(n:ℝ)*eta

def rankLoss (n:ℕ)(eta:ℝ):ℝ:=62*(n:ℝ)*eta

def RankEnergyExists (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) C K degree

theorem rank_energy_exists_zero (L cstar cutoff eta:ℝ)(hcut:0<cutoff)(K:ℕ)(W:𝓢(ℝ,ℂ)):
    RankEnergyExists 0 L cstar cutoff eta K W :=by
  refine ⟨0,1,le_rfl,?_⟩
  intro q hq
  refine ⟨1,2,by norm_num,by norm_num,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments]
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply canonical_rank_negative
  simp only [rankRowCap,Nat.cast_zero]
  linarith

theorem actual_rank_successor_caps (n:ℕ)(L cstar cutoff eta M F c:ℝ)
    (hM:M≤rankRowCap (n+1) cutoff)(hF:F≤rankTotalCap (n+1) L eta)
    (hc:rankMargin (n+1) cstar eta≤c):
    M-3*cutoff/4≤rankRowCap n cutoff ∧ F+15*eta≤rankTotalCap n L eta ∧
      rankMargin n cstar eta≤c-7*eta :=by
  unfold rankRowCap rankTotalCap rankMargin at *
  push_cast at *
  constructor <;> first | linarith | constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI
