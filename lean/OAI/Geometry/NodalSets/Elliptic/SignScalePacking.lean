import OAI.Geometry.NodalSets.Elliptic.PackingVolumeWeight
import OAI.Geometry.NodalSets.Elliptic.SignScaleContinuity

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section

lemma compact_sign_scale_dilates {Q U : Set Coord} (hQ : IsCompact Q)
    (hU : IsOpen U) (hQU : Q ⊆ U) (s : Coord → ℝ)
    (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ x ∈ Q,
      sourceClosedBall x (5/((n:ℝ)*s x)) ⊆ U ∧
      ∀ y ∈ Q ∩ sourceClosedBall x (5/((n:ℝ)*s x)), s y ≤ 2*s x := by
  obtain ⟨ρ,hρ,hinner⟩ := compact_inner_ball hQ hU hQU
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hQ.uniformContinuousOn_of_continuous hs) 1 (by norm_num)
  have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
  filter_upwards [ht.eventually (eventually_gt_atTop (5/ρ)),
    ht.eventually (eventually_gt_atTop (5/δ)),eventually_gt_atTop (0:ℕ)] with n hnρ hnδ hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  refine ⟨hn,?_⟩
  intro x hx
  have hsx : 0 < s x := by linarith [hlo x hx]
  have hrad : 5/((n:ℝ)*s x) < min ρ δ := by
    apply lt_min
    · apply (div_lt_iff₀ (mul_pos hn' hsx)).mpr
      have hh := (div_lt_iff₀ hρ).mp hnρ
      nlinarith [hlo x hx]
    · apply (div_lt_iff₀ (mul_pos hn' hsx)).mpr
      have hh := (div_lt_iff₀ hδ).mp hnδ
      nlinarith [hlo x hx]
  have hdist : ∀ y ∈ sourceClosedBall x (5/((n:ℝ)*s x)), dist y x ≤ 5/((n:ℝ)*s x) := by
    intro y hy
    exact (norm_le_sourceEuclideanNorm (y-x)).trans hy
  constructor
  · intro y hy
    apply hinner x hx
    exact (hdist y hy).trans (hrad.le.trans (min_le_left _ _))
  · intro y hy
    have hh := hd y hy.1 x hx ((hdist y hy.2).trans_lt (hrad.trans_le (min_le_right _ _)))
    rw [Real.dist_eq] at hh
    linarith [(abs_lt.mp hh).2,hlo x hx]

lemma compact_sign_scale_packing {Q U : Set Coord} (hQ : IsCompact Q)
    (hU : IsOpen U) (hQU : Q ⊆ U) (s : Coord → ℝ)
    (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ t : Finset Coord,
      let r := fun x ↦ ((n:ℝ)*s x)⁻¹
      (↑t : Set Coord) ⊆ Q ∧
      (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) ∧
      (∀ x ∈ t, 0 < r x ∧ sourceClosedBall x (5*r x) ⊆ U) ∧
      (n:ℝ)*(∫ x in Q, s x) ≤ 2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 := by
  filter_upwards [compact_sign_scale_dilates hQ hU hQU s hs hlo] with n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn.1
  let r := fun x ↦ ((n:ℝ)*s x)⁻¹
  have hr : ∀ x ∈ Q, 0 < r x := fun x hx ↦ inv_pos.mpr (mul_pos hn' (by linarith [hlo x hx]))
  obtain ⟨t,htQ,htdis,htcov⟩ := source_finite_fivefold_packing hQ r hr
  refine ⟨hn.1,t,htQ,htdis,htcov,?_,?_⟩
  · intro x hx
    refine ⟨hr x (htQ hx),?_⟩
    simpa only [r,div_eq_mul_inv] using (hn.2 x (htQ hx)).1
  · refine packing_volume_weight hQ hs t r hn'.le htQ
      (fun x hx ↦ (hr x (htQ hx)).le) (fun x hx ↦ by linarith [hlo x hx]) ?_ htcov ?_
    · intro x hx
      exact mul_inv_cancel₀ (mul_pos hn' (show 0 < s x by linarith [hlo x (htQ hx)])).ne'
    · intro x hx y hy
      apply (hn.2 x (htQ hx)).2 y
      simpa only [r,div_eq_mul_inv] using hy

namespace LocalCompactWaveData
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
    {D : Set Coord} {m J K k0 : ℕ}

lemma source_sign_scale_packing (a : LocalCompactWaveData g w S D m J K k0)
    {Q U : Set Coord} (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUD : U ⊆ D) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ t : Finset Coord,
      let r := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
      (↑t : Set Coord) ⊆ Q ∧
      (↑t : Set Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) ∧
      (∀ x ∈ t, 0 < r x ∧ sourceClosedBall x (5*r x) ⊆ U) ∧
      (n:ℝ)*(∫ x in Q, sourceSignScale g S x) ≤
        2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 :=
  compact_sign_scale_packing hQ hU hQU _ (a.source_sign_scale_continuousOn (hQU.trans hUD))
    (fun x hx ↦ a.source_sign_scale_lower x (hUD (hQU hx)))

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
