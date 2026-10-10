import OAI.NumberTheory.DirichletL.Reflection.FrozenNorms

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualFrozenPhase (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  star κ * frozenCore F.generator_ne_zero F.generator_good c jF Finset.univ *
    ramifiedBlock F.generator_good jF Finset.univ
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

lemma sourceFrozenPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m = actualFrozenPhase F jF D.fixedFactor s u m := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceFrozenPhase frozenIndices
  rw [← frozenCore_transport (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good c (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ,
    ← ramifiedBlock_transport (F.reflected K hK S).generator_good
      (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ]
  rfl

lemma frozenExtracted_ne_zero (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v ≠ 0 := by
  apply reflectionExtractedDivisor_ne_zero
  intro i
  rw [F.generator_span]
  exact NeZero.ne _

lemma frozenBranchScale_pos (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) :
    0 < frozenBranchScale F jF e := by
  have hn (v : Fin 3) : (0:ℝ) < Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (hn 1)) (Real.sqrt_pos.mpr (hn 2)))
    (Real.sqrt_pos.mpr (hn 0))

def normalizedFrozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  (frozenBranchScale F jF e : ℂ)⁻¹ * frozenBranchColumn F jF e A n b

lemma normalizedFrozenColumn_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖normalizedFrozenColumn F jF e A n b‖ ≤ 1 := by
  have hp := frozenBranchScale_pos F jF e
  rw [normalizedFrozenColumn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  calc
    _ ≤ (frozenBranchScale F jF e)⁻¹*frozenBranchScale F jF e :=
      mul_le_mul_of_nonneg_left (frozenBranchColumn_norm_le F jF e A hA n b) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma frozenBranchColumn_eq_normalized (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e A n b =
      (frozenBranchScale F jF e : ℂ)*normalizedFrozenColumn F jF e A n b := by
  rw [normalizedFrozenColumn,← mul_assoc,mul_inv_cancel₀,one_mul]
  exact_mod_cast (frozenBranchScale_pos F jF e).ne'

end
end SevenEighths.InverseReflectedPhase

end OAI
