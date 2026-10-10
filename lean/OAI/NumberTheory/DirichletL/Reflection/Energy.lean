import OAI.NumberTheory.DirichletL.Reflection.ActualBounds
import OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization
import OAI.NumberTheory.DirichletL.Descent.Sharp

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : Eisˣ) (m : ℕ) (K : Ideal Eis) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0

def reflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
      (frozenBranchColumn F jF e A) K

lemma hybridRow_frozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (Pset nset bset : Finset (Ideal Eis))
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      (frozenBranchScale F jF e:ℂ)*hybridRow Pset nset bset aP (normalizedFrozenColumn F jF e A) K := by
  unfold hybridRow hybridInner
  simp_rw [frozenBranchColumn_eq_normalized]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
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
      (S : Ideal Eis → PrimeFamily σ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∑ K ∈ rows, ‖reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Y*B*L)^ε*(X+Y*B)*B*(Y+L+(Y*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S hrows hrowcop _hproducts hScop hSN hSchar hn hb hP
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m‖ ≤ 1 :=
    (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2
  have hcolumn : ∀ n b, ‖normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m) n b‖ ≤ 1 :=
    normalizedFrozenColumn_norm_le_one F jF e _ (actualCuspColumn_norm_le_one D0 s hc u m)
  have hh := he X Y B L hX hY hB hL rows nset bset Pset
    (fun P => actualSlotPhase F (S P) jF s u m)
    (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) hrows hn hb hP hslot
    (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
          (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤ _)
  rw [reflectedBranchHybridRow,hybridRow_frozenColumn]
  have hp := frozenBranchScale_pos F jF e
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK)
  rw [norm_mul,norm_mul (frozenBranchScale F jF e:ℂ) _,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow,mul_pow]
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖^2 ≤ 1 := by
    have hpos := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*actualRowPhaseExtension F jF s u m K)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hs (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI
