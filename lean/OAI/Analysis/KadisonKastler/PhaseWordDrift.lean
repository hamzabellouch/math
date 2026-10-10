import OAI.Analysis.KadisonKastler.PhaseQuotient
import OAI.Analysis.KadisonKastler.RandomizedPairing

namespace OAI

/-! # Phase averaging of the actual word commutators

The commutator applied to a vector is linear in its algebra argument.
Consequently the exact multiset expansion and finite Parseval identity
identify the word's root-mean-square drift with its coefficient-column norm.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

/-- A represented commutator tested on one vector. -/
def commutatorVector (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) (z : H) :
    A →ₗ[ℂ] H where
  toFun a := (T * ρ a - ρ a * T) z
  map_add' a b := by
    simp only [map_add, mul_add, add_mul, add_apply, sub_apply]
    abel
  map_smul' c a := by
    simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_apply, sub_apply, smul_sub, RingHom.id_apply]

variable {q : ℕ} [NeZero q]

/-- Exact positive-word drift identity, before taking a sequence limit. -/
theorem positive_phase_word_drift
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) (z : H)
    (e : ι → A) (v : A) (r : ℕ) (hr : r + 1 < q) :
    finiteRMS (fun θ : ι → ZMod q =>
      (T * ρ ((diagonalPhase e θ * v) ^ r * diagonalPhase e θ) -
        ρ ((diagonalPhase e θ * v) ^ r * diagonalPhase e θ) * T) z) =
      ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) =>
        (T * ρ (positivePhaseCoefficient e v (r + 1) s) -
          ρ (positivePhaseCoefficient e v (r + 1) s) * T) z)‖ := by
  let L := commutatorVector ρ T z
  have he (θ : ι → ZMod q) :
      L ((diagonalPhase e θ * v) ^ r * diagonalPhase e θ) =
        finitePhaseSum (fun s : Sym ι (r + 1) => multisetCharacter (s : Multiset ι))
          (fun s => L (positivePhaseCoefficient e v (r + 1) s)) θ := by
    rw [positivePhase_power_expansion]
    simp only [map_sum, map_smul, finitePhaseSum]
  change Real.sqrt (Finset.univ.expect (fun θ : ι → ZMod q =>
    ‖L ((diagonalPhase e θ * v) ^ r * diagonalPhase e θ)‖ ^ 2)) = _
  simp_rw [he]
  rw [multiset_phases_mean_square hr]
  have hn := (PiLp.norm_sq_eq_of_L2 (fun _ : Sym ι (r + 1) => H)
    (WithLp.toLp 2 (fun s => L (positivePhaseCoefficient e v (r + 1) s)))).symm
  rw [hn, Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- The inverse characters give the negative-word drift identity. -/
theorem negative_phase_word_drift
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) (z : H)
    (e : ι → A) (v : A) (r : ℕ) (hr : r + 1 < q) :
    finiteRMS (fun θ : ι → ZMod q =>
      (T * ρ ((star v * star (diagonalPhase e θ)) ^ (r + 1)) -
        ρ ((star v * star (diagonalPhase e θ)) ^ (r + 1)) * T) z) =
      ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) =>
        (T * ρ (negativePhaseCoefficient e v (r + 1) s) -
          ρ (negativePhaseCoefficient e v (r + 1) s) * T) z)‖ := by
  let L := commutatorVector ρ T z
  have he (θ : ι → ZMod q) :
      L ((star v * star (diagonalPhase e θ)) ^ (r + 1)) =
        finitePhaseSum (fun s : Sym ι (r + 1) =>
          ⇑((multisetCharacter (q := q) (s : Multiset ι))⁻¹ : AddChar (ι → ZMod q) ℂ))
          (fun s => L (negativePhaseCoefficient e v (r + 1) s)) θ := by
    rw [negativePhase_power_expansion]
    simp only [map_sum, map_smul, finitePhaseSum]
  change Real.sqrt (Finset.univ.expect (fun θ : ι → ZMod q =>
    ‖L ((star v * star (diagonalPhase e θ)) ^ (r + 1))‖ ^ 2)) = _
  simp_rw [he]
  rw [negative_multiset_phases_mean_square hr]
  have hn := (PiLp.norm_sq_eq_of_L2 (fun _ : Sym ι (r + 1) => H)
    (WithLp.toLp 2 (fun s => L (negativePhaseCoefficient e v (r + 1) s)))).symm
  rw [hn, Real.sqrt_sq (norm_nonneg _)]
  rfl

end

end KadisonKastler

end OAI
