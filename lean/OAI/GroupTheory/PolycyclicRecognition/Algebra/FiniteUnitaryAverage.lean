import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitAverage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HilbertOrbitAverage

namespace OAI

/-! # Finite simultaneous averages in a unitary representation

Each finite convex averaging operator is a contraction. Successively averaging
each of finitely many vectors preserves all earlier bounds. This is the
Hilbert averaging step used for the abelian cohomology base case.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def FiniteOrbitAverage.onVector (A : FiniteOrbitAverage G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E := ∑ i, A.weight i • ρ (A.element i) x

theorem FiniteOrbitAverage.onVector_sub (A : FiniteOrbitAverage G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    A.onVector ρ (x - y) = A.onVector ρ x - A.onVector ρ y := by
  simp only [FiniteOrbitAverage.onVector, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem FiniteOrbitAverage.norm_onVector_le (A : FiniteOrbitAverage G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : ‖A.onVector ρ x‖ ≤ ‖x‖ := by
  calc
    ‖A.onVector ρ x‖ ≤ ∑ i, ‖A.weight i • ρ (A.element i) x‖ := norm_sum_le _ _
    _ = ∑ i, A.weight i * ‖x‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (A.nonneg i), (ρ _).norm_map]
    _ = ‖x‖ := by rw [← Finset.sum_mul, A.mass, one_mul]

theorem exists_finiteVectorAverage (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E)
    (hy : y ∈ convexHull ℝ (range (fun g : G => ρ g x))) :
    ∃ A : FiniteOrbitAverage G, A.onVector ρ x = y := by
  obtain ⟨ι, hι, a, z, ha, hs, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hy
  let := hι
  choose g hg using hz
  let A : FiniteOrbitAverage G :=
    { index := ι
      finiteIndex := hι
      weight := a
      nonneg := ha
      mass := hs
      element := g }
  refine ⟨A, ?_⟩
  change (∑ i, a i • ρ (g i) x) = y
  simpa only [hg] using he

def FiniteOrbitAverage.compose (A B : FiniteOrbitAverage G) : FiniteOrbitAverage G where
  index := A.index × B.index
  weight ij := A.weight ij.1 * B.weight ij.2
  nonneg ij := mul_nonneg (A.nonneg _) (B.nonneg _)
  mass := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, B.mass, mul_one, A.mass]
  element ij := A.element ij.1 * B.element ij.2

theorem FiniteOrbitAverage.compose_onVector (A B : FiniteOrbitAverage G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (A.compose B).onVector ρ x = A.onVector ρ (B.onVector ρ x) := by
  change (∑ ij : A.index × B.index, (A.weight ij.1 * B.weight ij.2) •
    ρ (A.element ij.1 * B.element ij.2) x) = _
  rw [Fintype.sum_prod_type]
  simp [FiniteOrbitAverage.onVector,
    Finset.smul_sum, map_sum, map_smul, mul_smul]

theorem zero_mem_unitaryOrbitHull [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hfixed : ∀ x : E, (∀ g, ρ g x = x) → x = 0) (x : E) :
    (0 : E) ∈ hilbertOrbitHull ρ x := by
  obtain ⟨y, hy, hf⟩ := exists_fixed_in_hilbertOrbitHull ρ x
  exact hfixed y hf ▸ hy

theorem exists_small_convex_unitaryOrbit
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (hx : (0 : E) ∈ hilbertOrbitHull ρ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ convexHull ℝ (range (fun g : G => ρ g x)), ‖y‖ < ε := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ε hε
  exact ⟨y, hy, by simpa only [dist_zero_left] using hd⟩

theorem exists_unitaryAverage_small_finset [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hfixed : ∀ x : E, (∀ g, ρ g x = x) → x = 0)
    (s : Finset E) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : FiniteOrbitAverage G, ∀ x ∈ s, ‖A.onVector ρ x‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let A : FiniteOrbitAverage G :=
      { index := Fin 1
        weight := fun _ => 1
        nonneg := fun _ => zero_le_one
        mass := by simp
        element := fun _ => 1 }
    exact ⟨A, by simp⟩
  | @insert x s _ ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨y, hy, hnorm⟩ := exists_small_convex_unitaryOrbit ρ (A.onVector ρ x)
      (zero_mem_unitaryOrbitHull ρ hfixed _) hε
    obtain ⟨B, hB⟩ := exists_finiteVectorAverage ρ (A.onVector ρ x) y hy
    refine ⟨B.compose A, fun z hz => ?_⟩
    rw [B.compose_onVector]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [hB]
      exact hnorm
    · exact (B.norm_onVector_le ρ _).trans_lt (hA z hz)

theorem exists_unitaryAverage_small_finite [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hfixed : ∀ x : E, (∀ g, ρ g x = x) → x = 0)
    {ι : Type*} [Fintype ι] (v : ι → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : FiniteOrbitAverage G, ∀ i, ‖A.onVector ρ (v i)‖ < ε := by
  classical
  obtain ⟨A, hA⟩ := exists_unitaryAverage_small_finset ρ hfixed (Finset.univ.image v) hε
  exact ⟨A, fun i => hA _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

end PolycyclicRecognition

end

end OAI
