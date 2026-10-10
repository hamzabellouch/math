import OAI.NumberTheory.DirichletL.Reflection.DyadicTail
import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

theorem literal_dyadic_tail_uniform_height (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  let V := vstarSchwartz W lo hi hlo hWs hW
  have hV : Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
    (literalRawScale G s X) T (literalRawScale_pos G s hc X hX) hT cut hcut
  have hleft : (∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm (H θ) (literalRawScale G s X) 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0 := by
    simp only [rawDualKernelTerm,hlink,literalDyadicBlock,literalRawSeries]
  rw [hleft] at hh
  apply hh.trans
  have hsemi' := mul_le_mul_of_nonneg_left (hsemi θ) hC.le
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by positivity
  calc
    _ = (C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (H θ))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) := by ring
    _ ≤ (C*(C₁*(1+‖θ‖)^degree))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hsemi' hrest
    _ = _ := by ring
end
end SevenEighths.InverseReflectedPhase

end OAI
