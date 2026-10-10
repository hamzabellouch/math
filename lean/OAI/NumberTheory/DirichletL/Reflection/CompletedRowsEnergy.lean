import OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
import OAI.NumberTheory.DirichletL.Reflection.CompletedAggregation
import OAI.NumberTheory.DirichletL.Reflection.CanonicalCaps

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_completed_rows_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,P∉reflectionExcludedPrimes q) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_completed_fiber_energy q hq lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation (2*L+1) (cstar/32) (by linarith) (by positivity)
  let B : Ideal Eis := Ideal.span {excludedGenerator (reflectionExcludedPrimes q)}
  let Z₁ := max Z₀ (max 2 (Ideal.absNorm B:ℝ))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hZ
  have hmask : ActualFiber.maskIdeal q m F=B*F*Ideal.span {m} := by
    dsimp only [ActualFiber.maskIdeal,ActualFiber.maskElement,B]
    rw [←Ideal.span_singleton_mul_span_singleton]
    ring
  have hmaskn : (Ideal.absNorm (ActualFiber.maskIdeal q m F):ℝ)≤Z^(2*L+1) := by
    rw [hmask]
    exact canonical_mask_norm_cap B F (Ideal.span {m}) Z V L L hz1 hBn hFn hRn hVc le_rfl
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2*L+1) := by
    intro I hI
    exact ⟨(hparents I hI).1,(hparents I hI).2.trans
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))⟩
  have hh := ha Z hZ2 parents (ActualFiber.maskIdeal q m F) hparentn
    (ActualFiber.maskIdeal_ne_zero q m hm F hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^(N+V-cstar/16))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J F (hparents J hJ).1 hF m hm Z N V M z₀ margin hhat d
      hZZ hN hM hMc hVc hzc hhc (hparents J hJ).2 hFn hRn hinv hmargin hVd hhd hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/32)*Z^(N+V-cstar/16)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
