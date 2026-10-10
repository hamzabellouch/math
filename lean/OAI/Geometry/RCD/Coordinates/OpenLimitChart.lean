import OAI.Geometry.RCD.Sobolev.CoerciveOpenMapping
import OAI.Geometry.RCD.Coordinates.ChartTopology

namespace OAI

/-! # Openness of the coordinate limit from its actual approximating maps -/

open Set Filter Topology
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- Only the actual smooth approximants and their uniform lower differential
bound are needed for openness of the final bi-Lipschitz chart. -/
theorem hasOpenBilipschitzChart_of_coercive_limit
    {X : Type*} [MetricSpace X] {n : ℕ} {p : X}
    {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    {O : Set (Euclidean n)} (hO : IsOpen O) (u : U ≃ₜ O)
    {f : ℕ → Euclidean n → Euclidean n} {H : U → Euclidean n}
    {M L : ℝ} (hM : 0 < M) (hL : 1 ≤ L)
    (hd : ∀ i z, z ∈ O → DifferentiableAt ℝ (f i) z)
    (hb : ∀ i z, z ∈ O → ∀ v, ‖v‖ ≤ M*‖fderiv ℝ (f i) z v‖)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (herr : ∀ i x, dist (f i (u x)) (H x) ≤ e i)
    (hbound : ∀ x z : U, L⁻¹*dist (x:X) (z:X) ≤ dist (H x) (H z) ∧
      dist (H x) (H z) ≤ L*dist (x:X) (z:X)) :
    HasOpenBilipschitzChart n p := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨hLip,hAnti⟩ := lipschitz_antilipschitz_of_dist_bounds
    (inv_pos.mpr hLpos) hLpos.le hbound
  let F : Euclidean n → Euclidean n := fun z => if hz : z ∈ O then H (u.symm ⟨z,hz⟩) else 0
  have hFval (z : O) : F z = H (u.symm z) := by simp only [F, dite_eq_left z.property]
  have hF : ContinuousOn F O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hLip.continuous.comp u.symm.continuous using 1
    exact funext hFval
  have hrange : F '' O = range H := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [hFval ⟨z,hz⟩]
      exact mem_range_self _
    · rintro ⟨x,rfl⟩
      refine ⟨u x, (u x).property, ?_⟩
      rw [hFval, u.symm_apply_apply]
  have hopen : IsOpen (range H) := by
    rw [← hrange]
    apply isOpen_image_of_uniform_limit_differential_bound hO hF hM hd hb he
    intro i z hz
    rw [hFval ⟨z,hz⟩]
    simpa only [u.apply_symm_apply] using herr i (u.symm ⟨z,hz⟩)
  have hEmb : IsEmbedding H := hAnti.isEmbedding hLip.continuous
  exact ⟨U, range H, hU, hp, hopen, hEmb.toHomeomorph, L, hL, hbound⟩

end RegularPointCoordinates

end

end OAI
