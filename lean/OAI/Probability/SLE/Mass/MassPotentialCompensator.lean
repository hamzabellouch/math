import OAI.Probability.SLE.Mass.MassCompensatorVariance

namespace OAI

/-! A remaining-mass potential determines the predictable mass increments. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The difference of the current potential and the one-step averaged
future potential is the conditional expectation of the mass increment. -/
theorem remainingPotential_increment
    (ℱ : Filtration ℕ mΩ) (A V : ℕ → Ω → ℝ) (L : Ω → ℝ)
    (hA : StronglyAdapted ℱ A) (hAI : ∀ i, Integrable (A i) P) (hLI : Integrable L P)
    (hV : ∀ i, V i =ᵐ[P] P[L-A i|ℱ i]) (i : ℕ) :
    V i-P[V (i+1)|ℱ i] =ᵐ[P] P[A (i+1)-A i|ℱ i] := by
  have hnext := (condExp_congr_ae (m := ℱ i) (hV (i+1))).trans
    (condExp_condExp_of_le (ℱ.mono (Nat.le_succ i)) (ℱ.le (i+1)))
  have hcur := (hV i).trans (condExp_sub hLI (hAI i) (ℱ i))
  have hnext' := hnext.trans (condExp_sub hLI (hAI (i+1)) (ℱ i))
  have hinc := condExp_sub (hAI (i+1)) (hAI i) (ℱ i)
  have hz := condExp_of_stronglyMeasurable (ℱ.le i) (hA i) (hAI i)
  filter_upwards [hcur,hnext',hinc] with ω hc hn hi
  simp only [Pi.sub_apply,hz] at hc hn hi ⊢
  linarith

omit [IsProbabilityMeasure P] in
/-- Pathwise telescoping after identifying each predictable increment. -/
lemma predictable_mass_sum_eq
    (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → ℝ)
    (q : ℕ → Ω → ℝ)
    (hq : ∀ i, q i =ᵐ[P] P[A (i+1)-A i|ℱ i]) (N : ℕ) :
    (fun ω => ∑ i ∈ Finset.range N, q i ω) =ᵐ[P]
      fun ω => A N ω-A 0 ω-centeredMassPartialSum P ℱ
        (fun i => A (i+1)-A i) N ω := by
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  simp only [centeredMassPartialSum,Pi.sub_apply]
  have hs := Finset.sum_sub_distrib (s := Finset.range N)
    (f := fun i => A (i+1) ω-A i ω)
    (g := fun i => condExp (ℱ i) P (A (i+1)-A i) ω)
  rw [Finset.sum_range_sub (fun i => A i ω) N] at hs
  have hq' : (∑ i ∈ Finset.range N, q i ω) =
      ∑ i ∈ Finset.range N, condExp (ℱ i) P (A (i+1)-A i) ω :=
    Finset.sum_congr rfl (fun i _ => hω i)
  rw [hq']
  linarith

end SLEExactGauge

end

end OAI
