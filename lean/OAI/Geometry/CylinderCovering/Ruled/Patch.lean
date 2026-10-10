import OAI.Geometry.CylinderCovering.Ruled.Retention

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace RuledApproximation.OrthogonalRetention

lemma retained_mono {D S : Set Plane} (hDS : D ⊆ S) (p : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (ell M radius : ℝ) :
    retained D p R ell M radius ⊆ retained S p R ell M radius := by
  classical
  intro ij hij
  simp only [retained, Finset.mem_filter] at hij ⊢
  obtain ⟨hbox, w, hw, hdist⟩ := hij
  exact ⟨hbox, w, hDS hw, hdist⟩

lemma mem_retained_iff_infDist {S : Set Plane} (hS : IsCompact S) (hne : S.Nonempty)
    (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) {ell M radius : ℝ}
    (hell : 0 < ell) (hM : ∀ w ∈ S, ‖w - p‖ ≤ M) (ij : ℤ × ℤ) :
    ij ∈ retained S p R ell M radius ↔ Metric.infDist (center p R ell ij) S ≤ radius := by
  rw [mem_retained_iff p R hell hM]
  constructor
  · rintro ⟨w, hw, hdist⟩
    exact (Metric.infDist_le_dist_of_mem hw).trans (by simpa [dist_eq_norm] using hdist)
  · intro hdist
    obtain ⟨w, hw, he⟩ := hS.exists_infDist_eq_dist hne (center p R ell ij)
    exact ⟨w, hw, by simpa [he, dist_eq_norm] using hdist⟩

theorem physical_patch_cover {D S : Set Plane} (hDS : D ⊆ S) (p v₀ : Plane)
    (A : Plane →L[ℝ] Plane) (v : Plane → Plane) {κ ell error M h : ℝ}
    (htrace : LinearMap.trace ℝ Plane A.toLinearMap = 0)
    (hdet : LinearMap.det A.toLinearMap < 0)
    (hA : ‖A‖ ≤ κ) (hκ : κ < 1) (hell : 0 < ell) (hh : 0 < h)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (herror : ∀ w ∈ D, ‖v w - affineVelocity p v₀ A w‖ ≤ error) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      let F := retained S p R ell M ((ell + error) / (1 - κ))
      (∀ i, (physicalFamily h p v₀ R A ell F i).parallelogram) ∧
      physicalRuled h D v 1 ⊆ familySet (physicalFamily h p v₀ R A ell F) ∧
      F.card ≤ (2 * ⌈(M + (ell + error) / (1 - κ)) / ell⌉₊ + 1) ^ 2 := by
  classical
  obtain ⟨R, hcover⟩ := finite_retained_cover p v₀ A v htrace hdet hA hκ hell
    (fun w hw => hM w (hDS hw)) herror
  let F := retained S p R ell M ((ell + error) / (1 - κ))
  refine ⟨R, (fun i => physicalFamily_parallelogram hh hell p v₀ R A F i), ?_,
    retained_card_le S p R ell M _⟩
  rintro z ⟨w, hw, t, ht, rfl⟩
  obtain ⟨ij, hij, hmem⟩ := hcover w hw t ht
  have hijS : ij ∈ F := retained_mono hDS p R ell M _ hij
  let j : F := ⟨ij, hijS⟩
  apply Set.mem_iUnion.mpr
  refine ⟨F.equivFin j, ?_⟩
  change _ ∈ (physicalFamily h p v₀ R A ell F (F.equivFin j)).carrier
  simpa only [physicalFamily, Equiv.symm_apply_apply] using
    physicalRuled_mem_projectedCylinder h v w
      (affineVelocity p v₀ A (center p R ell ij)) t hmem

def meshRadius (κ : ℝ) (η : ℝ → ℝ) (a : ℝ) : ℝ :=
  (a ^ 2 + η a * a) / (1 - κ)

lemma meshRadius_div (κ : ℝ) (η : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) :
    meshRadius κ η a / a = (a + η a) / (1 - κ) := by
  unfold meshRadius
  by_cases hk : 1 - κ = 0
  · simp [hk]
  · field_simp

theorem meshRadius_isLittleO (κ : ℝ) {η : ℝ → ℝ}
    (hη : Tendsto η (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    Asymptotics.IsLittleO (nhdsWithin 0 (Ioi 0)) (meshRadius κ η) (fun a : ℝ => a) := by
  apply Asymptotics.isLittleO_of_tendsto (fun a ha => by simp [ha, meshRadius])
  have hid : Tendsto (fun a : ℝ => a) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun a : ℝ => (a + η a) / (1 - κ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hid.add hη).div_const (1 - κ)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (meshRadius_div κ η (ne_of_gt ha)).symm

end RuledApproximation.OrthogonalRetention

end

end OAI
