import OAI.NumberTheory.DirichletL.Reflection.CrudeCoefficient
import OAI.NumberTheory.DirichletL.Reflection.RawTail

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalRawCoefficient (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  if Squarefree n ∧ primaryGenerator n≠0 ∧ primaryGenerator b≠0 then
    (s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ)
  else 0

lemma literalRawCoefficient_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖literalRawCoefficient G D s hc j S u m n.val b.val‖≤(Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  unfold literalRawCoefficient
  split_ifs
  · have hr : 1≤ramifiedScale 1 completedRamifiedStep m := by
      simpa only [ramifiedScale,one_mul] using one_le_pow₀ completedRamifiedStep_gt_one.le (n:=m)
    have hn : 1≤Real.sqrt (Ideal.absNorm n.val:ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by simpa using norm_at_least_one n.val n.property)
    have hb := norm_at_least_one b.val b.property
    have hden : 1≤ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr hn) hb
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (le_trans zero_le_one hden)]
    apply (div_le_div_of_nonneg_right (literal_mixed_coefficient_crude G D s hc hN hbase hchar j hj S u m n.val b.val)
      (le_trans zero_le_one hden)).trans
    exact div_le_self (Nat.cast_nonneg _) hden
  · simp only [norm_zero]
    exact Nat.cast_nonneg _

theorem literal_reflected_raw_tail (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := raw_kernel_tail a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI
