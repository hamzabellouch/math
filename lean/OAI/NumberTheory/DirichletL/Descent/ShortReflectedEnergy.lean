import OAI.NumberTheory.DirichletL.Descent.ShortCompletionEnergy
import OAI.NumberTheory.DirichletL.Reflection.CubeCompletedEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

theorem completed_tuple_mark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ)
    (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (hW:HasCompactSupport W)
    (X:ℝ) (hX:0<X) (H:Ideal Eis):
    markedCompletedT Ψ W X (fun A=>tupleDivisibilityMark lists w (H^3*A))=
      ∑p:∀i,lists i,(∏i,w i (p i))*markedCompletedT Ψ W X
        (fun A=>∏i,if (p i).val∣H^3*A then (1:ℂ) else 0) := by
  unfold tupleDivisibilityMark
  rw [markedCompletedT_finset_sum Finset.univ Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

theorem short_cube_exact_scale (Z N:ℝ) (hZ:1<Z) (H:Ideal Eis) (hH:H≠0):
    Z^(N-3*Real.logb Z (Ideal.absNorm H:ℝ))=Z^N/(Ideal.absNorm H:ℝ)^3 := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(Ideal.absNorm H:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hH (Ideal.absNorm_eq_zero_iff.mp hn))
  rw [Real.rpow_sub hz,show 3*Real.logb Z (Ideal.absNorm H:ℝ)=Real.logb Z (Ideal.absNorm H:ℝ)*3 by ring,
    show Z^(Real.logb Z (Ideal.absNorm H:ℝ)*3)=(Z^(Real.logb Z (Ideal.absNorm H:ℝ)))^3 from
      Real.rpow_mul_natCast hz.le _ 3,Real.rpow_logb hz (ne_of_gt hZ) hn]

theorem canonical_short_completed_energy (q:ℕ) (hq:q≠0)
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤cstar/100000) (rmax:ℕ):
    ∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(256*(columnDyadicLength (Z^hcut)+1:ℝ))^2 := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=canonical_cube_shifted_completed_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hZ1:1<Z:=lt_of_lt_of_le hZ₀ hZ
  have hz:0<Z:=zero_lt_one.trans hZ1
  have htw:HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hcompleted (J:Ideal Eis) (hJ:J∈shortCubeRange (Z^hcut)):
      (∑I∈parents,‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64):=by
    obtain ⟨hJ0,hJnorm⟩:=(mem_shortCubeRange _ J).mp hJ
    have hn:0<(Ideal.absNorm J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hJ0 (Ideal.absNorm_eq_zero_iff.mp hn))
    have hc:Real.logb Z (Ideal.absNorm J:ℝ)≤hcut:=
      (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
    have hjpow:(Ideal.absNorm J:ℝ)≤Z^(Real.logb Z (Ideal.absNorm J:ℝ)):=by
      rw [Real.rpow_logb hz (ne_of_gt hZ1) hn]
    have h:=he F hF m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
      hZ hN hM hMc hVc hzc (hc.trans hcutc) hFn hRn hmargin hreserve hVd (hc.trans hcutd) hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod J hJ0 hjpow u θ w hw
    rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
    simpa only [completed_tuple_mark lists w _ _ htw _ (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
  have hh:=marked_short_completed_energy
    (fun I:parents=>rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val))
    (fun I n=>rowTwist_norm Ψ hΨ _ _ _ n) (fun _=>tupleDivisibilityMark lists w)
    (normTwistedSource W θ) (Z^N) (Z^hcut) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/64))
    (by positivity) (fun J hJ=>by
      rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)]
      exact hcompleted J hJ)
  rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI
