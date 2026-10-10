import OAI.Probability.DilutedSpin.ColorIterate

namespace OAI

section
section
open scoped ContDiff

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma eventually_positive_insertion {n : ℕ} {A : FinitePath Ω n → ℝ}
    (hA : ∀ y, 0 < A y) : ∀ᶠ B in nhds A, ∀ y, 0 < B y := by
  rw [Filter.eventually_all]
  intro y
  exact (isOpen_lt continuous_const (continuous_apply y)).mem_nhds (hA y)

/-- The actual iterated Fréchet derivative is the ordered colored expansion.
The reverse only records the outermost-first convention of iteratedFDeriv. -/
lemma iteratedFDeriv_anchorAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (k : ℕ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) (ds : Fin k → FinitePath Ω n → ℝ) :
    iteratedFDeriv ℝ k (anchorAt S T m U paths G) A ds =
      coloredAt T m (List.ofFn ds).reverse S U paths G A := by
  induction k generalizing A with
  | zero => simp [coloredAt]
  | succ k ih =>
    have hh := (contDiffAt_anchorAt S T m U paths G hA).differentiableAt_iteratedFDeriv
      (m := k) (by simp)
    rw [hh.iteratedFDeriv_succ_apply_left']
    have heq : (fun B => iteratedFDeriv ℝ k (anchorAt S T m U paths G) B (Fin.tail ds))
        =ᶠ[nhds A] (fun B => coloredAt T m (List.ofFn (Fin.tail ds)).reverse S U paths G B) := by
      filter_upwards [eventually_positive_insertion hA] with B hB
      exact ih hB (Fin.tail ds)
    rw [heq.fderiv_eq, fderiv_coloredAt_apply T m hm hroot hend _ S U paths G hA]
    rw [List.ofFn_succ, List.reverse_cons]
    rfl

lemma coloredAt_replicate {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] (k : ℕ) (D : FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) (t : ℝ) :
    coloredAt T m (List.replicate k D) S U paths G (fun y => 1+t*D y) =
      anchorIterate T m D k S U paths G t := by
  induction k generalizing S U with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, coloredAt, anchorIterate, ih]

lemma iteratedFDeriv_anchorAt_diagonal {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (k : ℕ) (D : FinitePath Ω n → ℝ)
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) :
    iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1) (fun _ => D) =
      anchorIterate T m D k S U paths G 0 := by
  rw [iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G (by simp)]
  simpa using coloredAt_replicate T m k D S U paths G 0

/-- Hence colored histories are symmetric in the actual mixed directions;
this is a theorem about the original finite-kernel function. -/
lemma coloredAt_reverse_perm {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] {k : ℕ}
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y)
    (ds : Fin k → FinitePath Ω n → ℝ) (π : Equiv.Perm (Fin k)) :
    coloredAt T m (List.ofFn (ds ∘ π)).reverse S U paths G A =
      coloredAt T m (List.ofFn ds).reverse S U paths G A := by
  rw [← iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G hA,
      ← iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G hA]
  exact (contDiffAt_anchorAt S T m U paths G hA).iteratedFDeriv_comp_perm ds π
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
