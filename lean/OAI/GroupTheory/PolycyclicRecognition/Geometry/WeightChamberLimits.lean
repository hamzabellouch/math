import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightChambers
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Approaching an incident chamber and identifying its ray labels -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem isClosed_closedWeightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    IsClosed (closedWeightChamber α σ) := by
  change IsClosed {w | ∀ i, 0 ≤ orientedWeight α σ i w}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (orientedWeight α σ i).continuous)

theorem mem_chamber_add_smul (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    {w v : W} (hw : w ∈ closedWeightChamber α σ) (hv : v ∈ weightChamber α σ)
    {t : ℝ} (ht : 0 < t) : w + t • v ∈ weightChamber α σ := by
  intro i
  simpa only [map_add, map_smul, smul_eq_mul] using
    add_pos_of_nonneg_of_pos (hw i) (mul_pos ht (hv i))

theorem closure_weightChamber (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hσ : (weightChamber α σ).Nonempty) :
    closure (weightChamber α σ) = closedWeightChamber α σ := by
  apply Subset.antisymm
  · apply (isClosed_closedWeightChamber α σ).closure_subset_iff.mpr
    exact fun _ hx i => (hx i).le
  · intro w hw
    obtain ⟨v, hv⟩ := hσ
    have ht : Tendsto (fun n : ℕ => w + (1 / ((n : ℝ) + 1)) • v) atTop (𝓝 w) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n =>
      mem_chamber_add_smul α σ hw hv (by positivity)))

/-- The approximating horizontal vectors are explicit: add a vanishing
multiple of any lift of an interior chamber vector. -/
theorem exists_lifted_chamber_sequence
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (α : I → W →L[ℝ] ℝ) (v : V) (σ : I → Bool)
    (hσ : incidentWeightChamber α (π v) σ) :
    ∃ u : ℕ → V, Tendsto u atTop (𝓝 v) ∧ ∀ n, π (u n) ∈ weightChamber α σ := by
  obtain ⟨w, hw⟩ := hσ.1
  obtain ⟨x, hx⟩ := hπ w
  refine ⟨fun n => v + (1 / ((n : ℝ) + 1)) • x, ?_, ?_⟩
  · simpa using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x)
  · intro n
    rw [map_add, map_smul, hx]
    exact mem_chamber_add_smul α σ hσ.2 hw (by positivity)

variable [FiniteDimensional ℝ W] [Finite I]

/-- Agreement on the incident chamber images gives agreement on the ray. -/
theorem map_mem_ray_of_incident_chambers
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w))
    (A B : W ≃ₗ[ℝ] W)
    (himages : ∀ σ, incidentWeightChamber α w σ →
      A '' closedWeightChamber α σ = B '' closedWeightChamber α σ) :
    B w ∈ nonnegativeRay (A w) := by
  have hpre : A.symm (B w) ∈ nonnegativeRay w := by
    rw [← incident_chamber_intersection_eq_ray α hα hsep σ₀ hσ₀ hExt]
    intro σ hσ
    have hb : B w ∈ A '' closedWeightChamber α σ := by
      rw [himages σ hσ]
      exact mem_image_of_mem B hσ.2
    obtain ⟨x, hx, he⟩ := hb
    have hxe : A.symm (B w) = x := by rw [← he, A.symm_apply_apply]
    exact hxe ▸ hx
  obtain ⟨r, hr, he⟩ := hpre
  have he' : B w = r • A w := by
    have hh := congrArg A he
    simpa only [A.apply_symm_apply, map_smul] using hh
  exact ⟨r, hr, he'⟩

/-- Agreement of the images of all incident closed chambers determines the
value of norm-preserving labels on the extreme ray. -/
theorem eq_on_extreme_ray_of_incident_chambers
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w))
    (A B : W ≃ₗ[ℝ] W) (hA : ∀ x, ‖A x‖ = ‖x‖) (hB : ∀ x, ‖B x‖ = ‖x‖)
    (himages : ∀ σ, incidentWeightChamber α w σ →
      A '' closedWeightChamber α σ = B '' closedWeightChamber α σ) : A w = B w := by
  exact (eq_of_mem_nonnegativeRay_of_norm_eq
    (map_mem_ray_of_incident_chambers α hα hsep σ₀ hσ₀ hExt A B himages)
    ((hB w).trans (hA w).symm)).symm

/-- Any positive homogeneous gauge suffices; in particular the existing
segment support norm can be used without changing normed-space instances. -/
theorem eq_on_extreme_ray_of_incident_chambers_of_gauge
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {w : W} (σ₀ : I → Bool) (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay w))
    (p : W → ℝ) (hp : ∀ x, x ≠ 0 → 0 < p x)
    (hsmul : ∀ x r, 0 ≤ r → p (r • x) = r * p x)
    (A B : W ≃ₗ[ℝ] W) (hA : p (A w) = p w) (hB : p (B w) = p w)
    (himages : ∀ σ, incidentWeightChamber α w σ →
      A '' closedWeightChamber α σ = B '' closedWeightChamber α σ) : A w = B w := by
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨r, hr, he⟩ := map_mem_ray_of_incident_chambers α hα hsep σ₀ hσ₀ hExt A B himages
  have hval : r * p w = p w := by
    rw [he, hsmul _ _ hr, hA] at hB
    exact hB
  have hr1 : r = 1 := by nlinarith [hp w hw]
  simpa only [hr1, one_smul] using he.symm

end PolycyclicRecognition

end

end OAI
