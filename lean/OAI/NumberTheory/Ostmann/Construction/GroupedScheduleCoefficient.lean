import OAI.NumberTheory.Ostmann.Construction.ExpandedWordPairBound

namespace OAI

/-! # Original grouped-atom amplitudes in the independent prime variables -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

def expandedPrimeNatValues {V : Type*} (n : ℕ) (x : V → ℕ) : ExpandedScheduledVariable V n → ℕ
  | .inl v => x v
  | .inr _ => 1

theorem expandedPrimeNatValues_cast {V : Type*} (n : ℕ) (x : V → ℕ) :
    (fun i => (expandedPrimeNatValues n x i : ℤ)) =
      expandedPrimeValues n (fun i => (x i : ℤ)) := by
  funext i
  cases i <;> rfl

noncomputable def groupedScheduleFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
    (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
    (fun _ _ _ _ => 1) n ⟨n, fun i => ((words i).map x).prod⟩ t

theorem groupedScheduleFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedScheduleFourierWeight role n words childBound pivotBound ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        (expandedRootTemplate role n words childBound pivotBound) t ht
        (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  have he := expandedRootTemplate_weight_coefficient role n words childBound pivotBound
    (expandedPrimeNatValues n x) t ht ψ hreal X lo hi hlo hhi
  have hx : (fun i => (((words i).map Sum.inl).map (expandedPrimeNatValues n x)).prod) =
      fun i => ((words i).map x).prod := by
    funext i
    rw [List.map_map]
    rfl
  rw [hx, expandedPrimeNatValues_cast] at he
  exact he

/-- The entire original expectation is preserved; no tuple normalization
or probability law is introduced for the reconstructed pivot coordinates. -/
theorem groupedScheduleFourierWeight_pair_mean {I V A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n : ℕ) (words words' : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (x : A → V → ℕ) (weight phase : A → ℂ) :
    (∑ a, weight a * (phase a *
      (groupedScheduleFourierWeight role n words childBound pivotBound ψ X lo hi t (x a) *
        conj (groupedScheduleFourierWeight role n words' childBound pivotBound ψ X lo hi t' (x a))))) =
    ∑ a, weight a * (phase a *
      ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        (expandedRootTemplate role n words childBound pivotBound) t ht
        (expandedPrimeValues n (fun i => (x a i : ℤ))) *
      conj ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        (expandedRootTemplate role n words' childBound pivotBound) t' ht'
        (expandedPrimeValues n (fun i => (x a i : ℤ)))))) := by
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun z : ℂ => weight a * (phase a * z))
  exact congrArg₂ (fun z z' : ℂ => z * conj z')
    (groupedScheduleFourierWeight_coefficient role n words childBound pivotBound ψ hreal
      X lo hi hlo hhi t ht (x a))
    (groupedScheduleFourierWeight_coefficient role n words' childBound pivotBound ψ hreal
      X lo hi hlo hhi t' ht' (x a))

end Ostmann

end OAI
