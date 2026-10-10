import OAI.NumberTheory.DirichletL.Inversion.ReflectedNormalization

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open InverseReflectedNormalization InverseTerminalWidths MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem normalized_actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z H v ell el S₀ B₀ Td za : ℝ), 1 ≤ Z →
    ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      X = Z^H → extractedDualScale (frozenExtracted F jF e 1) Y = Z^v →
      extractedDualScale (frozenExtracted F jF e 2) B = Z^ell → L = Z^za →
      ‖scalar‖*frozenBranchScale F jF e = outsideScalar Z v ell el S₀ B₀ Td →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      (6*C)*Z^(InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := integrated_actual_reflected_branch_energy (Ω := Ω) (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro Z H v ell el S₀ B₀ Td za hZ X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
    hscaleX hscaleY hscaleB hscaleL hscalar
  have hh := he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  dsimp only at hh
  rw [hscaleX,hscaleY,hscaleB,hscaleL] at hh
  have hs : ‖scalar‖^2*(frozenBranchScale F jF e)^2 =
      outsideScalar Z v ell el S₀ B₀ Td ^2 := by rw [← mul_pow,hscalar]
  have heq : ‖scalar‖^2*((frozenBranchScale F jF e)^2*
      (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) =
      C*((outsideScalar Z v ell el S₀ B₀ Td)^2 *
        ((Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) := by
    calc
      _ = (‖scalar‖^2*(frozenBranchScale F jF e)^2)*
        (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) := by ring
      _ = _ := by rw [hs]; ring
  rw [heq] at hh
  apply hh.trans
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (normalized_hybrid_shape hZ H v ell el S₀ B₀ Td za ε) hC.le)
    (sq_nonneg (∫ t, ‖density t‖ ∂μ))
  convert hbnd using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
