import OAI.Analysis.KadisonKastler.FiniteCentralAveraging

namespace OAI

/-! # Norm convergence of iterated central averaging -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- Geometric refinement makes the central corrections summable and produces
an actual central element in the norm-closed unitary orbit hull. -/
theorem exists_central_mem_closed_orbit (x : Algebra M) :
    ∃ c : Algebra (concreteCenter M),
      c.val ∈ closure (convexHull ℝ (innerUnitaryOrbit M x.val)) := by
  have hex (y : Algebra M) : ∃ (B : FiniteInnerAverage M)
      (d : Algebra (concreteCenter M)), ‖B.apply y.val - d.val‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    by_cases hy : y = 0
    · refine ⟨FiniteInnerAverage.identity M, 0, ?_⟩
      simp [hy]
    · obtain ⟨B, d, hd⟩ := exists_central_average y (‖y‖ / 2) (by positivity)
      exact ⟨B, d, by linarith⟩
  choose B d hd using hex
  let err (s : FiniteInnerAverage M × Algebra (concreteCenter M)) : H →L[ℂ] H :=
    s.1.apply x.val - s.2.val
  let residual (s : FiniteInnerAverage M × Algebra (concreteCenter M)) : Algebra M :=
    s.1.algebraApply x - centralInclusion s.2
  have hres (s) : (residual s).val = err s := by
    change (s.1.algebraApply x).val - s.2.val = _
    rw [FiniteInnerAverage.algebraApply_val]
  let step (s : FiniteInnerAverage M × Algebra (concreteCenter M)) :=
    ((B (residual s)).comp s.1, s.2 + d (residual s))
  have herr (s) : err (step s) =
      (B (residual s)).apply (residual s).val - (d (residual s)).val := by
    dsimp only [err, step]
    rw [FiniteInnerAverage.comp_apply, hres]
    dsimp only [err]
    rw [FiniteInnerAverage.apply_sub, FiniteInnerAverage.apply_central]
    change _ - (s.2.val + (d (residual s)).val) = _
    abel
  have hstep (s) : ‖err (step s)‖ ≤ (1 / 2 : ℝ) * ‖err s‖ := by
    rw [herr]
    exact (hd (residual s)).trans_eq (by rw [← hres]; rfl)
  have hcorr (s) : ‖(step s).2 - s.2‖ ≤ (3 / 2 : ℝ) * ‖err s‖ := by
    change ‖s.2 + d (residual s) - s.2‖ ≤ _
    rw [add_sub_cancel_left]
    have hn : ‖d (residual s)‖ = ‖(d (residual s)).val‖ := rfl
    rw [hn]
    have ht : ‖(d (residual s)).val‖ ≤
        ‖(B (residual s)).apply (residual s).val‖ +
          ‖(B (residual s)).apply (residual s).val - (d (residual s)).val‖ := by
      calc
        _ = ‖(B (residual s)).apply (residual s).val -
            ((B (residual s)).apply (residual s).val - (d (residual s)).val)‖ := by
          rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h1 := (B (residual s)).norm_apply_le (residual s).val
    have h2 := hd (residual s)
    have hn' : ‖residual s‖ = ‖err s‖ := by rw [← hres]; rfl
    rw [← hn']
    have hnval : ‖(residual s).val‖ = ‖residual s‖ := rfl
    rw [hnval] at h1
    linarith
  let seq : ℕ → FiniteInnerAverage M × Algebra (concreteCenter M) :=
    fun n => Nat.rec (FiniteInnerAverage.identity M, 0) (fun _ s => step s) n
  have he0 : err (seq 0) = x.val := by
    change (FiniteInnerAverage.identity M).apply x.val - (0 : Algebra (concreteCenter M)).val = _
    simp
  have hpow (n : ℕ) : ‖err (seq n)‖ ≤ (1 / 2 : ℝ)^n * ‖x‖ := by
    induction n with
    | zero => rw [he0]; simp only [pow_zero, one_mul]; rfl
    | succ n ih =>
      have h := hstep (seq n)
      change ‖err (seq (n + 1))‖ ≤ (1 / 2 : ℝ) * ‖err (seq n)‖ at h
      rw [pow_succ]
      nlinarith
  have hcauchy : CauchySeq (fun n => (seq n).2) := by
    apply SeminormedAddCommGroup.cauchySeq_of_le_geometric (r := (1 / 2 : ℝ))
      (C := (3 / 2 : ℝ) * ‖x‖) (by norm_num)
    intro n
    have h := hcorr (seq n)
    change ‖(seq (n + 1)).2 - (seq n).2‖ ≤ (3 / 2 : ℝ) * ‖err (seq n)‖ at h
    have hp := hpow n
    rw [norm_sub_rev]
    nlinarith
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hzero : Tendsto (fun n => err (seq n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) hpow
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖x‖
  have hcval : Tendsto (fun n => (seq n).2.val) atTop (𝓝 c.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hc
  have havg : Tendsto (fun n => (seq n).1.apply x.val) atTop (𝓝 c.val) := by
    simpa only [err, sub_add_cancel, zero_add] using hzero.add hcval
  refine ⟨c, isClosed_closure.mem_of_tendsto havg ?_⟩
  exact Eventually.of_forall (fun n => subset_closure ((seq n).1.apply_mem_orbitHull x.val))

omit [Nontrivial H] in
/-- The exact published averaging input, in every represented von Neumann algebra. -/
theorem publishedDixmierAveraging (N : VonNeumannAlgebra H) : PublishedDixmierAveraging N := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    intro x _
    refine ⟨0, (concreteCenter N).zero_mem, subset_closure (subset_convexHull ℝ _ ?_)⟩
    refine ⟨1, ?_⟩
    exact Subsingleton.elim _ _
  let := hH
  intro x hx
  obtain ⟨c, hc⟩ := exists_central_mem_closed_orbit (M := N) ⟨x, hx.1⟩
  exact ⟨c.val, c.property, hc⟩

end

end KadisonKastler

end OAI
