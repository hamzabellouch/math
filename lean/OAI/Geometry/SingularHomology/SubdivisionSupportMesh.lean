import OAI.Geometry.SingularHomology.SingularSubdivision
import OAI.Geometry.SingularHomology.RecursiveSubdivisionMesh

namespace OAI

noncomputable section

namespace Problem340.SingularSubdivision

open SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def barycentricCenters : Centers E :=
  fun _ v => faceCenter v Finset.univ

private lemma mem_support_linearCombination {α β : Type*}
    (v : α → β →₀ ℝ) (c : α →₀ ℝ) {q : β}
    (h : q ∈ (Finsupp.linearCombination ℝ v c).support) :
    ∃ p ∈ c.support, q ∈ (v p).support := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
  obtain ⟨p, hp, hq⟩ := Finsupp.mem_support_finsetSum q h
  exact ⟨p, hp, Finsupp.support_smul hq⟩

lemma mem_support_cone {V : Type*} (a : V) (n : ℕ) (c : Chains V n)
    {q : Fin (n + 1) → V} (h : q ∈ (cone a n c).support) :
    ∃ p ∈ c.support, q = Fin.cons a p := by
  obtain ⟨p, hp, hq⟩ := mem_support_linearCombination
    (fun p => generator (Fin.cons a p)) c h
  refine ⟨p, hp, ?_⟩
  simpa [generator] using hq

@[simp] lemma barycentricCenters_zero (v : Fin 1 → E) :
    barycentricCenters 0 v = v 0 := by
  simp [barycentricCenters, faceCenter, Finset.centerMass]

@[simp] lemma subdivision_barycentric_one (v : Fin 1 → E) :
    subdivision barycentricCenters 1 (generator v) = generator v := by
  rw [subdivision_generator]
  simp only [boundary_generator, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero,
    one_smul, subdivision_zero, cone_generator, barycentricCenters_zero]
  congr 1
  ext i
  fin_cases i
  rfl

theorem subdivision_support_barycentricCell {n : ℕ} (v : Fin (n + 1) → E)
    {w : Fin (n + 1) → E}
    (h : w ∈ (subdivision barycentricCenters (n + 1) (generator v)).support) :
    BarycentricCell n v w := by
  classical
  induction n with
  | zero =>
      rw [subdivision_barycentric_one] at h
      change w = v
      simpa [generator] using h
  | succ n ih =>
      rw [subdivision_generator] at h
      obtain ⟨u, hu, rfl⟩ := mem_support_cone _ _ _ h
      rw [boundary_generator, map_sum] at hu
      obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum u hu
      rw [map_smul] at hi
      have hu' := Finsupp.support_smul hi
      exact ⟨i, u, ih _ hu', rfl⟩

theorem subdivision_support_carrier {n : ℕ} (v : Fin (n + 1) → E)
    {w : Fin (n + 1) → E}
    (h : w ∈ (subdivision barycentricCenters (n + 1) (generator v)).support) :
    Set.range w ⊆ convexHull ℝ (Set.range v) :=
  (subdivision_support_barycentricCell v h).carrier

theorem subdivision_support_diam_le {n : ℕ} (v : Fin (n + 1) → E)
    {w : Fin (n + 1) → E}
    (h : w ∈ (subdivision barycentricCenters (n + 1) (generator v)).support) :
    Metric.diam (convexHull ℝ (Set.range w)) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (convexHull ℝ (Set.range v)) :=
  (subdivision_support_barycentricCell v h).diam_le

end Problem340.SingularSubdivision

end

end OAI
