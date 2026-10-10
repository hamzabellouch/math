import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

/-- Replace the k-th coordinate by the potential itself. -/
def levelCoordinates {d : ℕ} (g : (Fin d → ℝ) → ℝ) (k : Fin d)
    (x : Fin d → ℝ) : Fin d → ℝ := Function.update x k (g x)

def levelDerivative {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => if i = k then L else ContinuousLinearMap.proj i

lemma levelDerivative_apply {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (x : Fin d → ℝ) (i : Fin d) :
    levelDerivative L k x i = if i = k then L x else x i := by
  by_cases hi : i = k <;> simp [levelDerivative, hi]

lemma exists_nonzero_coordinate {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ k : Fin d, L (Pi.single k 1) ≠ 0 := by
  classical
  by_contra! h
  apply hL
  ext x
  have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [h]

lemma levelDerivative_injective {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (hk : L (Pi.single k 1) ≠ 0) : Function.Injective (levelDerivative L k) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hxk : L x = 0 := by
    have := congrFun hx k
    simpa [levelDerivative_apply] using this
  have hxi (i : Fin d) (hi : i ≠ k) : x i = 0 := by
    have := congrFun hx i
    simpa [levelDerivative_apply, hi] using this
  have he : x = x k • Pi.single k (1 : ℝ) := by
    ext i
    by_cases hi : i = k
    · subst i; simp
    · simp [hi, hxi i hi]
  have hkx : x k = 0 := by
    rw [he, map_smul, smul_eq_mul] at hxk
    exact (mul_eq_zero.mp hxk).resolve_right hk
  rw [he, hkx, zero_smul]

def levelDerivativeEquiv {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (hk : L (Pi.single k 1) ≠ 0) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.ofBijective (levelDerivative L k)
    (LinearMap.ker_eq_bot.mpr (levelDerivative_injective L k hk))
    (LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (levelDerivative_injective L k hk)))

lemma hasFDerivAt_levelCoordinates {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {L : (Fin d → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L x) (k : Fin d) :
    HasFDerivAt (levelCoordinates g k) (levelDerivative L k) x := by
  classical
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = k
  · subst i; simpa [levelCoordinates, levelDerivative] using hg
  · simpa [levelCoordinates, levelDerivative, hi] using (hasFDerivAt_apply i x)

lemma contDiffAt_levelCoordinates {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {r : WithTop ℕ∞} (hg : ContDiffAt ℝ r g x) (k : Fin d) :
    ContDiffAt ℝ r (levelCoordinates g k) x := by
  classical
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i = k
  · subst i; simpa [levelCoordinates] using hg
  · simpa [levelCoordinates, hi] using (contDiffAt_apply ℝ ℝ i (f := x))

/-- A genuine C2 chart flattening a regular level. No boundary decomposition is assumed. -/
theorem exists_regular_level_chart {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hg : ContDiffAt ℝ 2 g x) (hreg : fderiv ℝ g x ≠ 0) :
    ∃ (k : Fin d) (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)),
      x ∈ e.source ∧ (∀ z, e z = levelCoordinates g k z) ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target := by
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate (fderiv ℝ g x) hreg
  let L := levelDerivativeEquiv (fderiv ℝ g x) k hk
  have hd : HasFDerivAt (levelCoordinates g k) (L : _ →L[ℝ] _) x :=
    hasFDerivAt_levelCoordinates (hg.differentiableAt (by simp)).hasFDerivAt k
  have hc := contDiffAt_levelCoordinates hg k
  let e := hc.toOpenPartialHomeomorph (levelCoordinates g k) hd (by simp)
  have hx : x ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he : (e : (Fin d → ℝ) → (Fin d → ℝ)) = levelCoordinates g k :=
    hc.toOpenPartialHomeomorph_coe hd (by simp)
  have hi : ContDiffAt ℝ 2 e.symm (e x) := by
    apply e.contDiffAt_symm (f₀' := L) (e.map_source hx)
    · rw [e.left_inv hx, he]
      exact hd
    · rw [e.left_inv hx, he]
      exact hc
  refine ⟨k, e.restrContDiff ℝ 2 (by simp), ?_, ?_, ?_, ?_⟩
  · exact ⟨hx, hc, hi⟩
  · intro z; rfl
  · exact e.contDiffOn_restrContDiff_source ℝ (by simp)
  · exact e.contDiffOn_restrContDiff_target ℝ (by simp)

end MahlerStokes

end

end OAI
