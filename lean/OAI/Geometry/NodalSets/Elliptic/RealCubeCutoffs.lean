import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau
open Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_cube_smooth_cutoff (r R : ℝ) (h : r < R) :
    ∃ eta : Jets.Coord → ℝ, ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
      tsupport eta ⊆ realCenteredCube 4 R ∧ (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧
      ∀ x ∈ realCenteredCube 4 r, eta =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  let U : Set Jets.Coord := univ.pi (fun _ ↦ Ioo (-R) R)
  have ho : IsOpen U := isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Ioo)
  have hi : realCenteredCube 4 r ⊆ U := by
    intro x hx j hj
    have ha := hx j hj
    exact ⟨lt_of_lt_of_le (neg_lt_neg h) ha.1,lt_of_le_of_lt ha.2 h⟩
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Yau.Geometry.compact_smooth_cutoff (realCenteredCube_isCompact 4 r) ho hi
  refine ⟨eta,he,hc,hs.trans ?_,hb,h1⟩
  intro x hx j hj
  exact ⟨(hx j hj).1.le,(hx j hj).2.le⟩

theorem real_interior_difference_cutoffs :
    ∃ eta theta : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ theta ∧ HasCompactSupport eta ∧ HasCompactSupport theta ∧
      tsupport eta ⊆ realCenteredCube 4 1 ∧ tsupport theta ⊆ realCenteredCube 4 (3/4) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 (1/2), theta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/8 → ∀ x ∈ tsupport theta,
        eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff (7/8) 1 (by norm_num)
  obtain ⟨theta,ht,htc,hts,htb,ht1⟩ := real_cube_smooth_cutoff (1/2) (3/4) (by norm_num)
  refine ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,?_⟩
  intro i h hh x hx
  have hxt : x ∈ realCenteredCube 4 (3/4) := hts hx
  refine ⟨he1 x (realCenteredCube_mono (by norm_num) hxt),he1 _ ?_⟩
  have hz : (x+Pi.single i h)+(Pi.single i (-h) : Jets.Coord)=x := by
    simp only [Pi.single_neg,add_neg_cancel_right]
  apply realCenteredCube_shift i (h := -h) (r := 3/4)
    (by simpa only [abs_neg] using (show |h| ≤ (7/8:ℝ)-3/4 by linarith))
  rw [hz]
  exact hxt

end
end Yau

end OAI
