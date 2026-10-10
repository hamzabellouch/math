import OAI.NumberTheory.DukePrimeDegree.Entropy.FinitePatchEntropy

namespace OAI

/-! # A countable cover by neutral future patches has zero conditional entropy rate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_finite_patch_complement_lt
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (E : ℕ → Set Y) (hE : ∀ i, MeasurableSet (E i))
    (hfull : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, μ.real (⋃ i : Fin (N+1), E i.val)ᶜ < ε := by
  have hz : μ (⋂ i, (E i)ᶜ)=0 := by
    rw [←compl_iUnion]
    exact ae_iff.mp hfull
  have ht := tendsto_measure_iInter_le (μ := μ) (s := fun i => (E i)ᶜ)
    (fun i => (hE i).compl.nullMeasurableSet) ⟨0,measure_ne_top _ _⟩
  rw [hz] at ht
  have ht' : Tendsto (fun N : ℕ => μ.real (⋂ i ≤ N, (E i)ᶜ)) atTop (𝓝 0) := by
    simpa only [Measure.real,ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨N,hN⟩ := (ht'.eventually (gt_mem_nhds hε)).exists
  refine ⟨N,?_⟩
  have he : (⋃ i : Fin (N+1), E i.val)ᶜ = ⋂ i ≤ N, (E i)ᶜ := by
    ext y
    simp only [mem_compl_iff,mem_iUnion,not_exists,mem_iInter]
    constructor
    · intro h i hi
      exact h ⟨i,by omega⟩
    · intro h i
      exact h i.val (by omega)
  rw [he]
  exact hN

theorem countable_patch_name_entropy_sublinear {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (E : ℕ → Set (X n)) (hE : ∀ i, MeasurableSet (E i))
    (hpair : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hfull : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i)
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (fullFutureSigma
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N) ≤ C+N*ε := by
  obtain ⟨δ,η,hδ,hδ1,hη,hcost⟩ := rareLabelCost_small k hε
  obtain ⟨B,r,R,hB,hsmall,hr,hrobust⟩ := exists_robust_finite_observation μ P hP
    (ENNReal.ofReal (η/2)) (by simp only [ne_eq,ENNReal.ofReal_eq_zero]; linarith)
  have hsmall' : μ.real B < η/2 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [Measure.real,ENNReal.toReal_ofReal (show 0 ≤ η/2 by positivity)] using h
  obtain ⟨p,hp⟩ := exists_finite_patch_complement_lt μ E hE hfull
    (show 0 < η/2 by positivity)
  obtain ⟨M,hM⟩ := finite_patch_name_entropy_bound ell hell Q hQ
    (fun i : Fin (p+1) => E i.val) (fun i => hE i.val)
    (fun i => hpair i.val) μ hT P hP B hB R hr hrobust hδ hδ1
  refine ⟨Real.log M,fun N => (hM N).trans ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  exact (hcost _ (add_nonneg measureReal_nonneg measureReal_nonneg)
    (by linarith)).le

end DukePrimeDegree

end

end OAI
