import OAI.Probability.SLE.Stochastic.PlanarRetractComplement
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! A finite simple planar arc has connected complement. The argument
uses its interval-coordinate retraction, the circle obstruction, and a
large sphere meeting every unbounded complementary component. -/
noncomputable section
open Set Complex Metric Function

namespace SLEExactGauge

theorem simple_arc_retraction (p : C(unitInterval,ℂ)) (hi : Injective p) :
    ∃ r : C(ℂ,ℂ), (∀ z, r z ∈ range p) ∧ ∀ z ∈ range p, r z=z := by
  let t : C(unitInterval,ℝ) := ⟨fun u => u,continuous_subtype_val⟩
  obtain ⟨g,hg⟩ := t.exists_extension' (p.continuous.isClosedEmbedding hi)
  let v (z : ℂ) : unitInterval := ⟨max 0 (min 1 (g z)),
    le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  have hv : Continuous v := (continuous_const.max
    (continuous_const.min g.continuous)).subtype_mk _
  refine ⟨⟨fun z => p (v z),p.continuous.comp hv⟩,
    fun z => mem_range_self (v z),?_⟩
  rintro _ ⟨u,rfl⟩
  have hgu : g (p u)=(u:ℝ) := congr_fun hg u
  have hvu : v (p u)=u := by
    apply Subtype.ext
    simp only [v,hgu,min_eq_right u.property.2,max_eq_right u.property.1]
  exact congrArg p hvu

lemma unbounded_component_meets_sphere {K : Set ℂ} {z : ℂ}
    (hz : z ∈ K) (hK : IsPreconnected K) (hu : ¬ Bornology.IsBounded K)
    {R : ℝ} (hR : ‖z‖ ≤ R) : (K ∩ sphere (0:ℂ) R).Nonempty := by
  have he : ∃ v ∈ K, R < ‖v‖ := by
    by_contra he
    push Not at he
    apply hu
    apply (isBounded_closedBall (x := (0:ℂ)) (r := R)).subset
    intro v hv
    simpa only [mem_closedBall,dist_zero_right] using he v hv
  obtain ⟨v,hv,hvR⟩ := he
  obtain ⟨w,hw,hwR⟩ := hK.intermediate_value hz hv continuous_norm.continuousOn
    (show R ∈ Icc ‖z‖ ‖v‖ from ⟨hR,hvR.le⟩)
  exact ⟨w,hw,by simpa only [mem_sphere,dist_zero_right] using hwR⟩

theorem bounded_complement_connected_of_unbounded_components
    {K : Set ℂ} (hb : Bornology.IsBounded K)
    (hu : ∀ z ∉ K, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z)) :
    IsConnected Kᶜ := by
  obtain ⟨R,hR,hKR⟩ := hb.subset_ball_lt 0 (0:ℂ)
  have hbase : ((R+1:ℝ):ℂ) ∈ Kᶜ := by
    intro h
    have hh := hKR h
    simp only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < R+1)] at hh
    linarith
  let w : ℂ := ((R+1:ℝ):ℂ)
  have heq : Kᶜ = connectedComponentIn Kᶜ w := by
    apply Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro z hz
    let S := max R (max ‖z‖ ‖w‖)+1
    have hRS : R < S := by dsimp [S]; linarith [le_max_left R (max ‖z‖ ‖w‖)]
    have hzS : ‖z‖ ≤ S := by
      dsimp [S]
      linarith [(le_max_left ‖z‖ ‖w‖).trans (le_max_right R (max ‖z‖ ‖w‖))]
    have hwS : ‖w‖ ≤ S := by
      dsimp [S]
      linarith [(le_max_right ‖z‖ ‖w‖).trans (le_max_right R (max ‖z‖ ‖w‖))]
    have hsK : sphere (0:ℂ) S ⊆ Kᶜ := by
      intro v hv hvK
      have hbv := hKR hvK
      have hsv : ‖v‖=S := by simpa only [mem_sphere,dist_zero_right] using hv
      rw [mem_ball,dist_zero_right,hsv] at hbv
      linarith
    have hs : IsPreconnected (sphere (0:ℂ) S) :=
      isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) _ _
    obtain ⟨u,huC,huS⟩ := unbounded_component_meets_sphere
      (mem_connectedComponentIn hz) isPreconnected_connectedComponentIn (hu z hz) hzS
    obtain ⟨v,hvC,hvS⟩ := unbounded_component_meets_sphere
      (mem_connectedComponentIn hbase) isPreconnected_connectedComponentIn (hu w hbase) hwS
    have huv := hs.subset_connectedComponentIn huS hsK hvS
    rw [← connectedComponentIn_eq huC] at huv
    have hwv := connectedComponentIn_eq hvC
    rw [hwv,← connectedComponentIn_eq huv]
    exact mem_connectedComponentIn hz
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hbase

theorem simple_arc_plane_complement_connected
    (p : C(unitInterval,ℂ)) (hi : Injective p) :
    IsConnected (range p)ᶜ := by
  obtain ⟨r,hr,hrfix⟩ := simple_arc_retraction p hi
  exact bounded_complement_connected_of_unbounded_components
    (isCompact_range p.continuous).isBounded
    (fun _ hz => retract_complement_component_unbounded
      (p.continuous.isClosedEmbedding hi).isClosed_range r r.continuous hr hrfix hz)

end SLEExactGauge

end

end OAI
