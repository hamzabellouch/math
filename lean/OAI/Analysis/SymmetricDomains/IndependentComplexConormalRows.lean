import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex

theorem complex_conormal_normal_form
    {E : Type*} [AddCommGroup E] [Module ℂ E] {k : ℕ}
    (L : (E × (Fin k → ℂ)) →ₗ[ℂ] ℂ)
    (hL : ∀ z : E, ∀ x : Fin k → ℝ, (L (z,fun i => x i)).re = 0) :
    ∃ β : Fin k → ℝ, ∀ z w, L (z,w) = Complex.I * ∑ i, (β i : ℂ) * w i := by
  classical
  have hzfun : (fun i : Fin k => ((0 : Fin k → ℝ) i : ℂ)) = 0 := by ext i; simp
  have hz : ∀ z : E, L (z,0) = 0 := by
    intro z
    apply Complex.ext
    · simpa only [hzfun,zero_re] using hL z 0
    · have h := hL (Complex.I • z) 0
      have he : (Complex.I • z, (0 : Fin k → ℂ)) = Complex.I • (z,0) := by simp
      rw [hzfun,he,L.map_smul] at h
      simpa using h
  let β : Fin k → ℝ := fun i => (L (0,Pi.single i 1)).im
  have he : ∀ i, L (0,Pi.single i 1) = Complex.I * (β i : ℂ) := by
    intro i
    apply Complex.ext
    · have h := hL 0 (Pi.single i 1)
      have hi : (fun j : Fin k => ((Pi.single i 1 : Fin k → ℝ) j : ℂ)) = Pi.single i 1 := by
        ext j
        simp only [Pi.single_apply]
        split_ifs <;> simp
      rw [hi] at h
      simpa using h
    · simp [β]
  refine ⟨β,?_⟩
  intro z w
  have hw : (0,w) = ∑ i : Fin k, w i • ((0 : E),Pi.single i 1) := by
    apply Prod.ext
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum]
      ext j
      simp [Finset.sum_apply,Pi.single_apply]
  calc
    L (z,w) = L (z,0)+L (0,w) := by rw [←map_add]; simp
    _ = L (0,w) := by rw [hz,zero_add]
    _ = ∑ i, w i * (Complex.I*(β i : ℂ)) := by rw [hw,map_sum]; simp only [map_smul,smul_eq_mul,he]
    _ = Complex.I * ∑ i, (β i : ℂ)*w i := by rw [Finset.mul_sum]; congr 1; funext i; ring

def normalRealCovector {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ} :
    (Fin k → ℝ) →ₗ[ℝ] Module.Dual ℝ (E × (Fin k → ℂ)) :=
  -∑ i : Fin k, (LinearMap.proj i).smulRight
    (Complex.imLm.comp ((LinearMap.proj i).comp (LinearMap.snd ℝ E (Fin k → ℂ))))

theorem normalRealCovector_apply {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (β : Fin k → ℝ) (x : E × (Fin k → ℂ)) :
    normalRealCovector β x = -∑ i, β i * (x.2 i).im := by
  simp [normalRealCovector]

theorem independent_complex_conormal_rows
    {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    {ι : Type*} {k : ℕ} (L : ι → (E × (Fin k → ℂ)) →ₗ[ℂ] ℂ)
    (hL : ∀ j (z : E) (x : Fin k → ℝ), (L j (z,fun i => x i)).re = 0)
    (hI : LinearIndependent ℝ (fun j => Complex.reLm.comp ((L j).restrictScalars ℝ))) :
    ∃ β : ι → Fin k → ℝ, LinearIndependent ℝ β ∧
      ∀ j z w, L j (z,w) = Complex.I * ∑ i, (β j i : ℂ)*w i := by
  classical
  choose β hβ using fun j => complex_conormal_normal_form (L j) (hL j)
  refine ⟨β,?_,hβ⟩
  apply LinearIndependent.of_comp (normalRealCovector (E := E))
  have he : (fun j => normalRealCovector (E := E) (β j)) =
      (fun j => Complex.reLm.comp ((L j).restrictScalars ℝ)) := by
    funext j
    apply LinearMap.ext
    intro x
    rw [normalRealCovector_apply]
    change _ = (L j x).re
    rcases x with ⟨z,w⟩
    rw [hβ]
    simp [Complex.mul_re,Complex.im_sum]
  change LinearIndependent ℝ (fun j => normalRealCovector (E := E) (β j))
  rw [he]
  exact hI

end Release061

end

end OAI
