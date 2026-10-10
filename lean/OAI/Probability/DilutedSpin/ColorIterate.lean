import OAI.Probability.DilutedSpin.ColoredAnchor

namespace OAI

section
section
open scoped ContDiff

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma contDiffAt_protectedAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    ContDiffAt ℝ ω (protectedAt S T m G) A := by
  apply contDiffAt_tilt_sample_expect
  · intro y
    exact (contDiffAt_apply ℝ ℝ y A).log (hA y).ne'
  · intro x
    apply contDiffAt_const.mul
    apply ContDiffAt.exp
    apply ContDiffAt.neg
    simp only [leafSum_eq_sum]
    apply ContDiffAt.sum
    intro a _
    exact (contDiffAt_apply ℝ ℝ (pathAt S a x) A).log (hA _).ne'

lemma contDiffAt_anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    ContDiffAt ℝ ω (anchorAt S T m U paths G) A := by
  apply contDiffAt_tilt_sample_expect
  · intro y
    exact (contDiffAt_apply ℝ ℝ y A).log (hA y).ne'
  · intro x
    apply ContDiffAt.mul
    · apply contDiffAt_const.mul
      exact contDiffAt_prod (fun i _ => contDiffAt_apply ℝ ℝ (paths i x) A)
    · apply ContDiffAt.exp
      apply ContDiffAt.neg
      simp only [leafSum_eq_sum]
      apply ContDiffAt.sum
      intro a _
      exact (contDiffAt_apply ℝ ℝ (pathAt S a x) A).log (hA _).ne'

/-- The literal ordered colored extension calculus. Each color either uses
one unused old leaf, which is then removed from the available list, or grows
one fresh branch with its original signed gamma coefficient. -/
noncomputable def coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] : List (FinitePath Ω n → ℝ) →
      (S : PrescribedTree n) → Finset ι → (ι → Sample Ω S → FinitePath Ω n) →
        (Sample Ω S → ℝ) → (FinitePath Ω n → ℝ) → ℝ
  | [], S, U, paths, G, A => anchorAt S T m U paths G A
  | D :: ds, S, U, paths, G, A =>
    (∑ i ∈ U, coloredAt T m ds S (U.erase i) paths (fun x => G x * D (paths i x)) A) +
    ∑ v : Internal S, gamma S m v * coloredAt T m ds (grow S v) U
      (fun i x => paths i (oldSample S v x))
      (fun x => G (oldSample S v x) * D (newPath S v x)) A

lemma contDiffAt_coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    ContDiffAt ℝ ω (coloredAt T m ds S U paths G) A := by
  induction ds generalizing S U with
  | nil => exact contDiffAt_anchorAt S T m U paths G hA
  | cons D ds ih =>
    apply ContDiffAt.add
    · exact ContDiffAt.sum (fun i _ => ih S (U.erase i) paths (fun x => G x * D (paths i x)))
    · exact ContDiffAt.sum (fun v _ => contDiffAt_const.mul
        (ih (grow S v) U (fun i x => paths i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x))))

/-- Differentiating a colored history inserts the next color at the end of
the ordered history. No symmetrization is imposed as a definition. -/
lemma hasDerivAt_coloredAt {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => coloredAt T m ds S U paths G (A t))
      (coloredAt T m (ds ++ [D]) S U paths G (A u)) u := by
  induction ds generalizing S U with
  | nil => exact hasDerivAt_anchorAt S T m hm hroot hend U paths G hA hdA
  | cons E ds ih =>
    have h₁ := HasDerivAt.fun_sum (u := U) (fun i _ => ih S (U.erase i) paths
      (fun x => G x * E (paths i x)))
    have h₂ := HasDerivAt.fun_sum (u := Finset.univ) (fun v _ => (ih (grow S v) U
        (fun i x => paths i (oldSample S v x))
        (fun x => G (oldSample S v x) * E (newPath S v x))).const_mul (gamma S m v))
    apply (h₁.add h₂).congr_of_eventuallyEq
    filter_upwards [] with parameter
    rfl

lemma fderiv_coloredAt_apply {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (ds : List (FinitePath Ω n → ℝ))
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) (D : FinitePath Ω n → ℝ) :
    fderiv ℝ (coloredAt T m ds S U paths G) A D =
      coloredAt T m (ds ++ [D]) S U paths G A := by
  have hF : DifferentiableAt ℝ (coloredAt T m ds S U paths G) A :=
    (contDiffAt_coloredAt T m ds S U paths G hA).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => A + t • D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add A
  have hF' : HasFDerivAt (coloredAt T m ds S U paths G)
      (fderiv ℝ (coloredAt T m ds S U paths G) A) (A + (0 : ℝ) • D) := by
    simpa using hF.hasFDerivAt
  have hcomp := hF'.comp_hasDerivAt 0 hline
  have hd := hasDerivAt_coloredAt T m hm hroot hend ds S U paths G
    (A := fun t y => A y + t * D y) (D := D) (u := 0) (by simpa using hA)
    (fun y => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (D y)).const_add (A y))
  simpa using hcomp.unique hd

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
