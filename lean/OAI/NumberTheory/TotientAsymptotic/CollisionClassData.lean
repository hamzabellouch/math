import OAI.NumberTheory.TotientAsymptotic.ActualComparison
import OAI.NumberTheory.TotientAsymptotic.CollisionCanceled

namespace OAI

/-! Recovering the fixed-prime data in an actual finite collision class. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def canceledIndices (i k : ℕ) (I : Finset ℕ) : Finset ℕ := Finset.Icc i k \ I

def canceledPrimesAt (x : ℝ) (H i k : ℕ) (I : Finset ℕ)
    (τ : TotientTuple (R x H)) : Fin (canceledIndices i k I).card → ℕ :=
  fun j => wholeWitnessPrime τ.head (chosenRemainder x H τ.tail)
    ((canceledIndices i k I).orderEmbOfFin rfl j)

lemma canceledIndices_eq {x : ℝ} {H i k p q : ℕ} {η ξ : RemainderDatum (L x H)} :
    canceledIndices i k (collisionSurvivors p q η ξ i k) =
      (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) := by
  ext j
  simp only [canceledIndices,collisionSurvivors,Finset.mem_sdiff,Finset.mem_filter]
  tauto

lemma canceledPrimesAt_product {x : ℝ} {H i k : ℕ}
    (τ σ : TotientTuple (R x H)) (I : Finset ℕ)
    (hI : collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
      (chosenRemainder x H σ.tail) i k=I) :
    shiftedProduct (canceledPrimesAt x H i k I τ)=
      collisionCanceledProduct τ.head σ.head (chosenRemainder x H τ.tail)
        (chosenRemainder x H σ.tail) i k := by
  unfold shiftedProduct canceledPrimesAt
  have he := Finset.prod_image
    (s := (Finset.univ : Finset (Fin (canceledIndices i k I).card)))
    (g := (canceledIndices i k I).orderEmbOfFin rfl)
    (f := fun j => wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j-1)
    (fun a _ b _ hab => ((canceledIndices i k I).orderEmbOfFin rfl).injective hab)
  rw [← he,(canceledIndices i k I).image_orderEmbOfFin_univ rfl,← hI,canceledIndices_eq]
  rfl

lemma comparisonPairAt_survivors {x : ℝ} {H i k : ℕ}
    (τ σ : TotientTuple (R x H)) :
    comparisonPairAt x H k (collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
      (chosenRemainder x H σ.tail) i k) (τ,σ) =
      survivingPair τ.head σ.head (chosenRemainder x H τ.tail) (chosenRemainder x H σ.tail) i k := rfl

/-- The fixed pref and the canceled-prime list provide precisely the
fixed-coordinate hypothesis needed to recover an actual pair from Ford data. -/
lemma fixed_primes_of_canceled_data {x : ℝ} {H i k : ℕ} (I : Finset ℕ)
    (τ σ : TotientTuple (R x H)) (pref : ℕ → ℕ)
    (v : Fin (canceledIndices i k I).card → ℕ)
    (hI : collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
      (chosenRemainder x H σ.tail) i k=I)
    (hpref : ∀ j < i, wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j=pref j ∧
      wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j=pref j)
    (hv : canceledPrimesAt x H i k I τ=v) :
    ∀ j ≤ k, j ∉ I →
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
        (if h : j ∈ canceledIndices i k I then
          v ((canceledIndices i k I).orderIsoOfFin rfl |>.symm ⟨j,h⟩) else pref j) ∧
      wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j =
        (if h : j ∈ canceledIndices i k I then
          v ((canceledIndices i k I).orderIsoOfFin rfl |>.symm ⟨j,h⟩) else pref j) := by
  intro j hj hnot
  by_cases hji : j < i
  · have hc : j ∉ canceledIndices i k I := by
      intro hh
      have := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hh).1).1
      omega
    simpa only [dite_eq_right hc] using hpref j hji
  · have hc : j ∈ canceledIndices i k I :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hj⟩,hnot⟩
    have heq : wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j=
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j := by
      rw [← hI,canceledIndices_eq] at hc
      exact (Finset.mem_filter.mp hc).2
    have hleft : wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
        v ((canceledIndices i k I).orderIsoOfFin rfl |>.symm ⟨j,hc⟩) := by
      rw [← hv]
      simp only [canceledPrimesAt,Finset.orderEmbOfFin]
      simp
    simpa only [dite_eq_left hc] using And.intro hleft (heq.symm.trans hleft)

end TotientAsymptotic

end

end OAI
