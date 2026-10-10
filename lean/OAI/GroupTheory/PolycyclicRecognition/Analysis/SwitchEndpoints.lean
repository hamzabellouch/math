import OAI.GroupTheory.PolycyclicRecognition.Analysis.SampledSuccessfulVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DifferenceAmplitudeWord

namespace OAI

/-! # The polynomial difference word is the endpoint of the successful switches -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

/-- The last state after the specified sequence of switches. -/
def switchEndpoint : (m : ℕ) → G → SwitchParameters G m → G
  | 0, x, _ => x
  | m + 1, x, p => switchEndpoint m (x * p.1 * p.2.1⁻¹) p.2.2

theorem switchEndpoint_vector (m : ℕ) (x : G) (p : Fin m → G × G) :
    switchEndpoint m x (vectorSwitchParameters m p) =
      x * (List.ofFn (fun j => (p j).1 * (p j).2⁻¹)).prod := by
  induction m generalizing x with
  | zero => simp [switchEndpoint]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons]
    change switchEndpoint m (x * (p 0).1 * (p 0).2⁻¹)
      (vectorSwitchParameters m (fun j => p j.succ)) = _
    rw [ih]
    simp only [mul_assoc]

omit [Group G] in
theorem mapSwitchParameters_vector (f : ℕ → ℝ → G) (n m : ℕ) (p : Fin m → ℝ × ℝ) :
    mapSwitchParameters f n m (vectorSwitchParameters m p) =
      vectorSwitchParameters m (fun j => (f (n + j.val) (p j).1, f (n + j.val) (p j).2)) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    simp only [vectorSwitchParameters, mapSwitchParameters, Fin.val_zero, Nat.add_zero]
    rw [ih]
    simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

theorem sampledSwitchEndpoint_eq (f : ℕ → ℝ → G) (m : ℕ)
    (hf : ∀ j s t, f j s * (f j t)⁻¹ = f j (s - t))
    (x : G) (t : Fin (m + m) → ℝ) :
    switchEndpoint m x (sampledSwitchParameters f m t) =
      x * (List.ofFn (fun j : Fin m =>
        f j.val (t (Fin.castAdd m j) - t (Fin.natAdd m j)))).prod := by
  unfold sampledSwitchParameters flatSwitchSamples
  rw [mapSwitchParameters_vector, switchEndpoint_vector]
  simp only [Nat.zero_add, flatSamplePairs, hf]

/-- Exponentiating the actual polynomial endpoint gives precisely the
ordered product of the sampled difference increments. -/
theorem exp_differenceAmplitudeWordEndpoint {I : Type*} {n m c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hg : PolynomialGroupLaws (dynkinProduct a B)) (X : I → Fin n → ℝ)
    (letters : Fin m → I) (t : Fin (m + m) → ℝ) :
    PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      (differenceAmplitudeWordEndpoint a letters (B, X) t) =
    (List.ofFn (fun j => PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      ((t (Fin.castAdd m j) - t (Fin.natAdd m j)) • X (letters j)))).prod := by
  unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  rw [exp_polynomialListProduct, List.map_ofFn]
  rfl

end PolycyclicRecognition

end

end OAI
