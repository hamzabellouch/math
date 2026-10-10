import OAI.NumberTheory.DirichletL.Reflection.FullRaw

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalDyadicBlock (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    literalRawSeries G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem mixedReflectedValue_eq_dyadic (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, literalDyadicBlock G D s hc j S W X u i := by
  have hs := (literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [mixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)

lemma dyadic_kernel_argument_lower (scale rho q : ℝ) (hs : 0≤scale)
    (hr : 0≤rho) (hq : 0≤q) (i : ℕ×ℕ×ℕ)
    (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
    scale*(ramifiedScale rho q i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3/16 ≤
      scale*(ramifiedScale rho q i.1)^3*(Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ)^3 := by
  have hn := (dualIdealDyad_bounds _ _ n.property).2.1
  have hb := (dualIdealDyad_bounds _ _ b.property).2.1
  have hp : 0≤scale*(ramifiedScale rho q i.1)^3 := by
    unfold ramifiedScale
    positivity
  have hh := mul_le_mul hn (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
    (Nat.cast_nonneg (Ideal.absNorm n.val))
  have hh' := mul_le_mul_of_nonneg_left hh hp
  nlinarith only [hh']

end
end SevenEighths.InverseReflectedPhase

end OAI
