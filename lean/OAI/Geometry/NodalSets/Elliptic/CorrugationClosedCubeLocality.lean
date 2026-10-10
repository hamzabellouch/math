import OAI.Geometry.NodalSets.Elliptic.CorrugationGridAssembly

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugationCube_closed_open_disjoint (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin 4 → Fin n) (hkj : k ≠ j) :
    Disjoint (closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
      (ball (corrugationCubeCenter o L n j) ((L/(n:ℝ))/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ j i := Function.ne_iff.mp hkj
  have hi' : (k i).val ≠ (j i).val := fun h ↦ hi (Fin.ext h)
  have hd : (1:ℝ) ≤ |(k i:ℝ)-(j i:ℝ)| := by
    rcases lt_or_gt_of_ne hi' with h | h
    · have hh : (k i:ℝ)+1 ≤ (j i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j i:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  apply closedBall_disjoint_ball
  have hcoord := norm_le_pi_norm (corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i
  have he : ‖(corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i‖ =
      (L/(n:ℝ))*|(k i:ℝ)-(j i:ℝ)| := by
    change |(o i+_)-(o i+_)| = _
    rw [add_sub_add_left_eq_sub,← mul_sub,abs_mul,abs_of_pos hR]
    congr 2
    ring
  rw [he] at hcoord
  rw [dist_eq_norm]
  nlinarith

lemma corrugationGridSum_closed_cube_eventually (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (χ : Coord → ℝ) (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord)
    (i : Fin 4 → Fin n) (x : Coord)
    (hx : x ∈ closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)) :
    corrugationGridSum o L n χ amp J s e =ᶠ[𝓝 x]
      localizedCorrugation χ (corrugationPeriodicWell amp) (s i) J (L/(n:ℝ))
        (frozenFrameCovector (e i) 2) (frozenFrameCovector (e i) 3) (corrugationCubeCenter o L n i) := by
  classical
  let w := fun j ↦ localizedCorrugation χ (corrugationPeriodicWell amp) (s j) J (L/(n:ℝ))
    (frozenFrameCovector (e j) 2) (frozenFrameCovector (e j) 3) (corrugationCubeCenter o L n j)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hz : ∀ j, j ≠ i → w j =ᶠ[𝓝 x] 0 := by
    intro j hji
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hj
    have hb := localizedCorrugation_cube χ _ hχ _ _ (div_pos hL hnR) _ _ _ hj
    exact Set.disjoint_left.mp (corrugationCube_closed_open_disjoint o hL hn i j hji.symm) hx hb
  have he : ∀ᶠ z in 𝓝 x, ∀ j, j ≠ i → w j z = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j=i
    · simp [hji]
    · filter_upwards [hz j hji] with z hz
      exact fun _ ↦ hz
  filter_upwards [he] with z hz
  change ∑ j ∈ (Finset.univ : Finset (Fin 4 → Fin n)), w j z = w i z
  exact Finset.sum_eq_single i (fun j _ hji ↦ hz j hji) (by simp)

end
end Yau.Geometry

end OAI
