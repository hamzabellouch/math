import OAI.Probability.SATComputability.RelaxedEnergy
import OAI.Probability.DilutedSpin.PoissonVariance

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

abbrev RelaxedClause (n : ℕ) := (Fin 3 → Fin n) × (Fin 3 → Bool)

noncomputable def clauseMinimum {n m : ℕ} (cs : Fin m → RelaxedClause n) : ℕ :=
  relaxedMinimumViolations (fun j => (cs j).1) (fun j => (cs j).2)

theorem relaxedViolations_eq_sum {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    relaxedViolations s indices signs =
      ∑ j, if relaxedClauseSatisfied s (indices j) (signs j) then 0 else 1 := by
  simp only [relaxedViolations, Finset.card_eq_sum_ones, Finset.sum_filter, ite_not]

theorem clauseMinimum_le_length {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs ≤ m := by
  exact (relaxedMinimum_le _ _ (fun _ => false)).trans
    ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m))

theorem clauseMinimum_le_add_one {n m : ℕ} (cs ds : Fin m → RelaxedClause n)
    (q : Fin m) (h : ∀ j, j ≠ q → cs j = ds j) :
    clauseMinimum cs ≤ clauseMinimum ds + 1 := by
  classical
  obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (ds j).1) (fun j => (ds j).2)
  apply (relaxedMinimum_le _ _ s).trans
  unfold clauseMinimum
  rw [← hs]
  let S := Finset.univ.filter fun j => ¬relaxedClauseSatisfied s (ds j).1 (ds j).2
  have hsub : (Finset.univ.filter fun j =>
      ¬relaxedClauseSatisfied s (cs j).1 (cs j).2) ⊆ insert q S := by
    intro j hj
    by_cases hjq : j = q
    · exact Finset.mem_insert.mpr (Or.inl hjq)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← h j hjq]
      exact (Finset.mem_filter.mp hj).2
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem clauseMinimum_update_bound {n m : ℕ} (cs : Fin m → RelaxedClause n)
    (q : Fin m) (c : RelaxedClause n) :
    |(clauseMinimum cs : ℝ) - clauseMinimum (Function.update cs q c)| ≤ 1 := by
  have h : ∀ j, j ≠ q → cs j = Function.update cs q c j := by
    intro j hj
    exact (Function.update_of_ne hj c cs).symm
  have h₁ := clauseMinimum_le_add_one cs (Function.update cs q c) q h
  have h₂ := clauseMinimum_le_add_one (Function.update cs q c) cs q
    (fun j hj => (h j hj).symm)
  have h₁' : (clauseMinimum cs : ℝ) ≤ clauseMinimum (Function.update cs q c) + 1 := by
    exact_mod_cast h₁
  have h₂' : (clauseMinimum (Function.update cs q c) : ℝ) ≤ clauseMinimum cs + 1 := by
    exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem clauseMinimum_cons_bounds {n m : ℕ} (cs : Fin m → RelaxedClause n)
    (c : RelaxedClause n) :
    clauseMinimum cs ≤ clauseMinimum (Fin.cons c cs) ∧
      clauseMinimum (Fin.cons c cs) ≤ clauseMinimum cs + 1 := by
  have he (s : Fin n → Bool) :
      relaxedViolations s (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).1)
        (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).2) =
        (if relaxedClauseSatisfied s c.1 c.2 then 0 else 1) +
          relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) := by
    simp only [relaxedViolations_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  constructor
  · obtain ⟨s, hs⟩ := relaxedMinimum_attained
      (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).1)
      (fun j => ((Fin.cons c cs : Fin (m+1) → RelaxedClause n) j).2)
    apply (relaxedMinimum_le _ _ s).trans
    change _ ≤ relaxedMinimumViolations _ _
    rw [← hs, he]
    omega
  · obtain ⟨s, hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
    apply (relaxedMinimum_le _ _ s).trans
    change _ ≤ relaxedMinimumViolations _ _ + 1
    rw [he, ← hs]
    split <;> omega

noncomputable def rootMinimum (n m : ℕ) (x : RootPath (RelaxedClause n) m) : ℝ :=
  clauseMinimum (rootArray m x)

theorem rootMinimum_bound (n m : ℕ) (x : RootPath (RelaxedClause n) m) :
    |rootMinimum n m x| ≤ m := by
  rw [rootMinimum, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast clauseMinimum_le_length (rootArray m x)

theorem rootMinimum_replace (n m : ℕ) (q : Fin m)
    (x : RootPath (RelaxedClause n) m) (c : RelaxedClause n) :
    |rootMinimum n m x - rootMinimum n m (replaceRoot m x q c)| ≤ 1 := by
  simp only [rootMinimum, rootArray_replace]
  exact clauseMinimum_update_bound _ _ _

theorem rootMinimum_cons (n m : ℕ) (c : RelaxedClause n)
    (x : RootPath (RelaxedClause n) m) :
    |rootMinimum n (m+1) (c,x) - rootMinimum n m x| ≤ 1 := by
  obtain ⟨hlo,hhi⟩ := clauseMinimum_cons_bounds (rootArray m x) c
  have hlo' : (clauseMinimum (rootArray m x) : ℝ) ≤
      clauseMinimum (Fin.cons c (rootArray m x)) := by exact_mod_cast hlo
  have hhi' : (clauseMinimum (Fin.cons c (rootArray m x)) : ℝ) ≤
      clauseMinimum (rootArray m x) + 1 := by exact_mod_cast hhi
  change |(clauseMinimum (Fin.cons c (rootArray m x)) : ℝ)-clauseMinimum (rootArray m x)| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rootMinimum_variance (n : ℕ) (μ : Measure (RelaxedClause n))
    [IsProbabilityMeasure μ] (r : ℝ≥0) :
    (∫ m : ℕ, ∫ x, (rootMinimum n m x - poissonRootAverage μ r (rootMinimum n))^2
      ∂rootLaw m (fun _ => μ) ∂poissonMeasure r) ≤ 3/2 * (r : ℝ) := by
  have h := poisson_root_second_moment μ r
    (fun m => measurable_of_countable (rootMinimum n m)) (rootMinimum_bound n)
    (show (0 : ℝ) ≤ 1 by norm_num) (rootMinimum_replace n) (rootMinimum_cons n)
    (poissonRootAverage μ r (rootMinimum n))
  norm_num only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, one_pow] at h
  exact h

noncomputable def rootSatisfiableProbability (n : ℕ) (μ : Measure (RelaxedClause n))
    (r : ℝ≥0) : ℝ :=
  poissonRootAverage μ r (fun m x => if rootMinimum n m x = 0 then 1 else 0)

theorem rootMinimum_mean_sq (n : ℕ) (μ : Measure (RelaxedClause n))
    [IsProbabilityMeasure μ] (r : ℝ≥0) :
    rootSatisfiableProbability n μ r * (poissonRootAverage μ r (rootMinimum n))^2 ≤
      3/2 * (r : ℝ) := by
  let c := poissonRootAverage μ r (rootMinimum n)
  have hinner (m : ℕ) : Integrable (fun x : RootPath (RelaxedClause n) m =>
      (rootMinimum n m x-c)^2) (rootLaw m (fun _ => μ)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((m+|c|)^2)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := (abs_sub (rootMinimum n m x) c).trans
      (add_le_add (rootMinimum_bound n m x) le_rfl)
    nlinarith [sq_abs (rootMinimum n m x-c), abs_nonneg (rootMinimum n m x-c),
      abs_nonneg c, Nat.cast_nonneg (α := ℝ) m]
  have houter : Integrable (fun m : ℕ => ∫ x, (rootMinimum n m x-c)^2
      ∂rootLaw m (fun _ => μ)) (poissonMeasure r) := by
    apply poisson_integrable_quadratic r (A := 2*c^2) (B := 2)
    intro m
    apply abs_integral_le_bound
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := rootMinimum_bound n m x
    have hsq : (rootMinimum n m x)^2 ≤ (m : ℝ)^2 := by
      nlinarith [sq_abs (rootMinimum n m x), abs_nonneg (rootMinimum n m x),
        Nat.cast_nonneg (α := ℝ) m]
    nlinarith [sq_nonneg (rootMinimum n m x+c)]
  have hpoint (m : ℕ) (x : RootPath (RelaxedClause n) m) :
      (if rootMinimum n m x = 0 then (1 : ℝ) else 0)*c^2 ≤
        (rootMinimum n m x-c)^2 := by
    split_ifs with h
    · rw [h]; ring_nf; exact le_rfl
    · simpa only [zero_mul] using sq_nonneg (rootMinimum n m x-c)
  have hb := integral_mono_of_nonneg (μ := poissonMeasure r)
    (ae_of_all _ (fun m => integral_nonneg (fun x => by positivity))) houter
    (ae_of_all _ (fun m => integral_mono_of_nonneg
      (ae_of_all _ (fun x => by positivity)) (hinner m) (ae_of_all _ (hpoint m))))
  simp only [integral_mul_const] at hb
  exact hb.trans (rootMinimum_variance n μ r)

end FixedClauseThreshold.Computability

end OAI
