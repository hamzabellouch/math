import OAI.Combinatorics.Crossing.EndpointVisits

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem continuous_path_squared_distance {a b : Plane} (γ : Path a b) (z : Plane) :
    Continuous (fun t : ℝ => squaredLength (γ.extend t-z)) := by
  unfold squaredLength
  fun_prop

theorem path_round_disk_visits {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ)
    (h0 : a ∉ closedRoundDisk z r) (h1 : b ∉ closedRoundDisk z r)
    (τ : unitInterval) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
    (hτ : squaredLength (γ τ-z) < r^2) :
    ∃ u v : unitInterval, 0 < u.val ∧ u < τ ∧ τ < v ∧ v.val < 1 ∧
      squaredLength (γ u-z)=r^2 ∧ squaredLength (γ v-z)=r^2 ∧
      (∀ t : unitInterval, γ t ∈ closedRoundDisk z r → u ≤ t ∧ t ≤ v) := by
  obtain ⟨u,v,hu0,huτ,hτv,hv1,hu,hv,hh⟩ := first_last_sublevel_visits
    (fun t => squaredLength (γ.extend t-z)) (continuous_path_squared_distance γ z) (r^2) τ.val
    (by simpa [closedRoundDisk] using (lt_of_not_ge h0))
    (by simpa [closedRoundDisk] using (lt_of_not_ge h1)) ⟨hτ0,hτ1⟩
    (by simpa using hτ)
  let u' : unitInterval := ⟨u,hu0.le,(huτ.trans hτ1).le⟩
  let v' : unitInterval := ⟨v,(hτ0.trans hτv).le,hv1.le⟩
  refine ⟨u',v',hu0,huτ,hτv,hv1,?_,?_,?_⟩
  · rw [show γ.extend u=γ u' from γ.extend_extends' u'] at hu
    exact hu
  · rw [show γ.extend v=γ v' from γ.extend_extends' v'] at hv
    exact hv
  · intro t ht
    exact hh t.val t.property (by simpa [closedRoundDisk] using ht)

theorem path_initial_disk_last_visit {a b : Plane} (γ : Path a b) (r : ℝ)
    (hr : 0 < r) (hb : b ∉ closedRoundDisk a r) :
    ∃ v : unitInterval, 0 < v.val ∧ v.val < 1 ∧ squaredLength (γ v-a)=r^2 ∧
      (∀ t : unitInterval, γ t ∈ closedRoundDisk a r → t ≤ v) := by
  obtain ⟨v,hv0,hv1,hv,hh⟩ := last_sublevel_visit
    (fun t => squaredLength (γ.extend t-a)) (continuous_path_squared_distance γ a) (r^2)
    (by simpa [squaredLength] using sq_pos_of_pos hr)
    (by simpa [closedRoundDisk] using (lt_of_not_ge hb))
  let v' : unitInterval := ⟨v,hv0.le,hv1.le⟩
  refine ⟨v',hv0,hv1,?_,?_⟩
  · rw [show γ.extend v=γ v' from γ.extend_extends' v'] at hv
    exact hv
  · intro t ht
    exact hh t.val t.property (by simpa [closedRoundDisk] using ht)

end Zarankiewicz

end

end OAI
