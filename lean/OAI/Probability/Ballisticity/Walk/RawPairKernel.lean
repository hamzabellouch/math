import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairEndpoint

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma hit_prefixEndpoint_iff {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (A : Set (Lattice d)) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H ∩ A) ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      prefixEndpoint (realPosition (step e)) x H X ∈ A := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n := ⟨hn.1.1,hn.2⟩
    refine ⟨Set.mem_iUnion.mpr ⟨n,hh⟩,?_⟩
    dsimp [prefixEndpoint]
    rw [coordinate_hitAt_record e x X h0 hnn hH hh]
    simpa only [add_sub_cancel] using hn.1.2
  · rintro ⟨h,hA⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    dsimp [prefixEndpoint] at hA
    rw [coordinate_hitAt_record e x X h0 hnn hH hn] at hA
    exact Set.mem_iUnion.mpr ⟨n,⟨hn.1,by simpa only [add_sub_cancel] using hA⟩,hn.2⟩

lemma hitKernel_eq_map_prefixEndpoint {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) =
      ((quenchedKernel (ω,x)).restrict (Hit (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H))).map (prefixEndpoint (realPosition (step e)) x H) := by
  apply Measure.ext
  intro A hA
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _),Measure.map_apply
    (measurable_prefixEndpoint _ _ _) hA,Measure.restrict_apply ((measurable_prefixEndpoint _ _ _) hA)]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  have := hit_prefixEndpoint_iff e x hH A X h0 hnn
  apply propext
  exact this.trans and_comm

noncomputable def rawPairEndpointLaw {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) : Measure (Lattice d × Lattice d) :=
  (hitKernel (Strip ℓ x.1 H) (Upper ℓ x.1 H) (ω,x.1)).prod
    (hitKernel (Strip ℓ x.2 H) (Upper ℓ x.2 H) (ω,x.2))

lemma rawPairEndpointLaw_eq {d : ℕ} (e f : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (ω : Environment d) :
    rawPairEndpointLaw (realPosition (step e)) H ω x {y | z ≤ signedCoordinate f (y.2-y.1)} =
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2)))
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 H z) := by
  have hgap : MeasurableSet {y : Lattice d × Lattice d | z ≤ signedCoordinate f (y.2-y.1)} := Set.to_countable _ |>.measurableSet
  have hm := (measurable_prefixEndpoint (realPosition (step e)) x.1 H).prodMap
    (measurable_prefixEndpoint (realPosition (step e)) x.2 H)
  unfold rawPairEndpointLaw
  rw [hitKernel_eq_map_prefixEndpoint e x.1 hH,hitKernel_eq_map_prefixEndpoint e x.2 hH,
    Measure.map_prod_map _ _ (measurable_prefixEndpoint _ _ _) (measurable_prefixEndpoint _ _ _),
    Measure.prod_restrict,Measure.map_apply hm hgap,
    Measure.restrict_apply (hm hgap)]
  congr 1
  ext p
  simp only [PairEndpointEvent,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_ofPred_eq,Set.mem_prod]
  tauto
end DirectionalTransience

end

end

end OAI
