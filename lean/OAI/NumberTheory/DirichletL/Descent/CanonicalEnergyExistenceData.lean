import OAI.NumberTheory.DirichletL.Descent.CanonicalRankEnergyMonotone

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CanonicalEnergyExists (Mcap Fcap c eps L:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
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
      CompletePoolRankMoments q D slots lists a base W Z Mcap Fcap z c eps C K degree

theorem canonical_energy_of_rank (n:ℕ)(L cstar cutoff eta Mcap Fcap c eps:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ))
    (hM:Mcap≤rankRowCap n cutoff)(hF:Fcap≤rankTotalCap n L eta)
    (hc:rankMargin n cstar eta≤c)(he:rankLoss n eta≤eps)
    (h:RankEnergyExists n L cstar cutoff eta K W):
    CanonicalEnergyExists Mcap Fcap c eps L K W :=by
  obtain ⟨degree,B,hB,h⟩:=h
  refine ⟨degree,B,hB,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,h⟩:=h q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  have hmom:=h Z hZ D hD slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments] at hmom ⊢
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  apply canonical_rank_loss_le (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap Fcap z c (rankLoss n eta) eps C K degree
    (by linarith) hC.le he
  exact canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap (rankRowCap n cutoff)
    Fcap (rankTotalCap n L eta) z c (rankMargin n cstar eta) (rankLoss n eta) C K degree hM hF hc hmom

end SevenEighths.InverseMoment

end

end OAI
