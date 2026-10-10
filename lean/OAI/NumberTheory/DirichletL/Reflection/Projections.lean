import OAI.NumberTheory.DirichletL.Reflection.Moving

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

def actualRowPhase (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceRowPhase s (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good (Sum.elim jF (fun _ => 1))
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

def actualSlotPhase (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceSlotPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
    (Sum.elim jF (fun _ => 0)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

omit [Fintype σ] in
theorem sourceRowPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (residualIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualRowPhase F K hK jF s u m := by
  classical
  let f : φ ⊕ PrimeIndex K → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceRowPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) =
      (F.sum (PrimeFamily.residual K hK)).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 1) := by
    funext i
    cases i <;> rfl
  have hh := sourceRowPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualRowPhase,residualIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

theorem sourceSlotPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualSlotPhase F S jF s u m := by
  classical
  let f : φ ⊕ σ → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceSlotPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) = (F.sum S).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 0) := by
    funext i
    cases i <;> rfl
  have hh := sourceSlotPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum S).generator_ne_zero (F.sum S).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualSlotPhase,slotIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
