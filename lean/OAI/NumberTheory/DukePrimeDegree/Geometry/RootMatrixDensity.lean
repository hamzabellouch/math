import OAI.NumberTheory.DukePrimeDegree.Geometry.RootVectorDensity

namespace OAI

/-!
# Finite distributions in a root conjugation representation

Root conjugation is polynomial of degree at most two in its parameter.
Recurrence first kills the lower-left coefficient and then every linear
coefficient. A finite invariant matrix distribution is therefore supported
on the actual root centralizer.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree

private lemma linear_coefficient_zero_of_recurrence
    {α : Type*} [TopologicalSpace α] (f : α → α) (x : α)
    (hrec : ∀ U ∈ 𝓝 x, ∃ᶠ m : ℕ in atTop, f^[m] x ∈ U)
    (p : α → ℝ) (hp : Continuous p) (c : ℝ)
    (hlin : ∀ m : ℕ, p (f^[m] x) = p x + (m : ℝ) * c) : c = 0 := by
  by_contra hc
  let U : Set α := {y | |p y - p x| < 1}
  have hU : U ∈ 𝓝 x := by
    apply (isOpen_lt (hp.sub continuous_const).abs continuous_const).mem_nhds
    change |p x - p x| < 1
    simp
  have hgrowth : Tendsto (fun m : ℕ => (m : ℝ) * |c|) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (abs_pos.mpr hc) tendsto_natCast_atTop_atTop
  obtain ⟨m, hm, hm'⟩ := ((hrec U hU).and_eventually (hgrowth.eventually_ge_atTop 1)).exists
  change |p (f^[m] x) - p x| < 1 at hm
  rw [hlin] at hm
  have he : |p x + (m : ℝ) * c - p x| = (m : ℝ) * |c| := by
    rw [add_sub_cancel_left, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)]
  rw [he] at hm
  exact (not_lt_of_ge hm') hm

lemma rootMatrixConjugation_add {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (s t : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    rootMatrixConjugation i j s (rootMatrixConjugation i j t M) =
      rootMatrixConjugation i j (s + t) M := by
  unfold rootMatrixConjugation
  calc
    _ = (Matrix.transvection i j s * Matrix.transvection i j t) * M *
        (Matrix.transvection i j (-t) * Matrix.transvection i j (-s)) := by noncomm_ring
    _ = _ := by
      rw [Matrix.transvection_mul_transvection_same i j hij,
        Matrix.transvection_mul_transvection_same i j hij]
      congr 2
      ring

lemma rootMatrixConjugation_iterate {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    (rootMatrixConjugation i j 1)^[m] M = rootMatrixConjugation i j (m : ℝ) M := by
  induction m with
  | zero => simp [rootMatrixConjugation]
  | succ m hm =>
    rw [Function.iterate_succ_apply', hm, rootMatrixConjugation_add i j hij]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]

lemma rootMatrixConjugation_entry {n : ℕ} (i j : Fin n) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    rootMatrixConjugation i j t M a b = M a b +
      t * ((if a = i then M j b else 0) - (if b = j then M a i else 0)) -
      t ^ 2 * (if a = i ∧ b = j then M j i else 0) := by
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp [rootMatrixConjugation]
      ring
    · simp [rootMatrixConjugation, hbj]
  · by_cases hbj : b = j
    · subst b
      simp [rootMatrixConjugation, hai]
    · simp [rootMatrixConjugation, hai, hbj]

/-- Root-conjugation recurrence forces every matrix to commute with the
root, almost everywhere for any finite invariant distribution. -/
theorem ae_commute_root_of_conjugation_invariance {n : ℕ}
    (ν : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure ν]
    (i j : Fin n) (hij : i ≠ j)
    (hinv : ν.map (rootMatrixConjugation i j 1) = ν) :
    ∀ᵐ M ∂ν, Commute M (Matrix.transvection i j (1 : ℝ)) := by
  let f := rootMatrixConjugation i j 1
  have hf : MeasurePreserving f ν ν :=
    ⟨(continuous_rootMatrixConjugation i j 1).measurable, hinv⟩
  filter_upwards [hf.conservative.ae_frequently_mem_of_mem_nhds] with M hrec
  have hji : M j i = 0 := by
    have he := linear_coefficient_zero_of_recurrence f M hrec (fun N => N j j)
      (by fun_prop) (-M j i) (by
        intro m
        rw [rootMatrixConjugation_iterate i j hij, rootMatrixConjugation_entry]
        simp [hij.symm])
    exact neg_eq_zero.mp he
  have hcoeff (a b : Fin n) :
      (if a = i then M j b else 0) - (if b = j then M a i else 0) = 0 := by
    apply linear_coefficient_zero_of_recurrence f M hrec (fun N => N a b) (by fun_prop)
    intro m
    rw [rootMatrixConjugation_iterate i j hij, rootMatrixConjugation_entry]
    simp only [hji, ite_self, mul_zero, sub_zero]
  have hfixed : rootMatrixConjugation i j 1 M = M := by
    ext a b
    rw [rootMatrixConjugation_entry, hcoeff]
    simp only [hji, ite_self, mul_zero, sub_zero, add_zero]
  have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ =>
    N * Matrix.transvection i j (1 : ℝ)) hfixed
  have hu : Matrix.transvection i j (-1 : ℝ) * Matrix.transvection i j (1 : ℝ) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij]
    simp
  change M * Matrix.transvection i j (1 : ℝ) = Matrix.transvection i j (1 : ℝ) * M
  simpa only [rootMatrixConjugation, mul_assoc, hu, mul_one] using he.symm

end DukePrimeDegree

end

end OAI
