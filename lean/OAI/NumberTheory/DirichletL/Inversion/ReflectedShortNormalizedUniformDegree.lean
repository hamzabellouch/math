import OAI.NumberTheory.DirichletL.Inversion.ShortCanonicalNormalization
import OAI.NumberTheory.DirichletL.Inversion.ReflectedShortGeneratorUniformDegree

namespace OAI
noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem canonical_short_normalized_energy_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q : ℕ) (_hq : q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,hu⟩ := canonical_short_normalized_generator_energy_uniform_degree lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  exact he m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc hRn
    hmargin hreserve hVd hcutd hd labels hlabelsN ConcretePrimeRowBridge.idealGenerator
    (fun f _ => ConcretePrimeRowBridge.span_idealGenerator f) T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI
