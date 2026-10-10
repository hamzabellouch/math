import OAI.Geometry.CylinderCovering.Beams.BeamStrip
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CylinderCovering.BeamStrip
open RadialRiemann

lemma exists_adjacent_interval (p : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {t : ℝ}
    (hfirst : p 0 ≤ t) (hlast : t ≤ p N) :
    ∃ i : Fin N, t ∈ Icc (p i) (p (i+1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨⟨0,by omega⟩,hfirst,hlast⟩
    · by_cases ht : t ≤ p N
      · obtain ⟨i,hi⟩ := ih (Nat.pos_of_ne_zero hzero) ht
        exact ⟨⟨i,by omega⟩,hi⟩
      · exact ⟨⟨N,by omega⟩,le_of_not_ge ht,hlast⟩

lemma exists_cell {a b : ℝ} {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc a b) : ∃ i : Fin N, t ∈ cell a b N i := by
  apply exists_adjacent_interval (point a b N) hN
  · simpa only [point_zero] using ht.1
  · simpa only [point_last hN] using ht.2

lemma strip_cost_continuous {a b β : ℝ} {W q : ℝ → ℝ}
    (hW : ContinuousOn W (Icc a b)) (hq : ContinuousOn q (Icc a b)) :
    ContinuousOn (fun t => 2*β*W t/denominator (q t)) (Icc a b) := by
  apply (hW.const_mul (2*β)).div
  · exact ((hq.pow 2).const_add 1 |>.const_mul 2).sqrt
  · intro t _
    exact (denominator_pos (q t)).ne'

lemma frozen_area_bound {a b β M η : ℝ} {W q : ℝ → ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hη : 0 ≤ η) (hab : a < b)
    {N : ℕ} (hN : 0 < N) (i : Fin N)
    (hW : 0 ≤ W (point a b N i)) :
    (rectangleCylinder (q (point a b N i))
      (β*(W (point a b N i)+(1+2*M)*η)/denominator (q (point a b N i)))
      (point a b N i) (point a b N (i+1))).area ≤
      step a b N * (2*β*W (point a b N i)/denominator (q (point a b N i))) +
      step a b N * (2*β*(1+2*M)*η) := by
  have hd := (step_pos hab hN).le
  have hden := denominator_pos (q (point a b N i))
  have hA : 0 ≤ β*(W (point a b N i)+(1+2*M)*η)/denominator (q (point a b N i)) := by
    positivity
  have hlr : point a b N i ≤ point a b N (i+1) := by
    have := point_succ a b N i
    linarith
  rw [rectangleCylinder_area hA hlr, point_succ]
  have hdiv : (2*β*(1+2*M)*η)/denominator (q (point a b N i)) ≤ 2*β*(1+2*M)*η :=
    div_le_self (by positivity) (denominator_ge_one _)
  calc
    _ = step a b N * (2*β*W (point a b N i)/denominator (q (point a b N i))) +
      step a b N * ((2*β*(1+2*M)*η)/denominator (q (point a b N i))) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiv hd)

theorem finite_strip_cover {a b β M : ℝ} {W q : ℝ → ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M) (hab : a < b)
    (hW : ContinuousOn W (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) {ε : ℝ} (hε : 0 < ε) :
    RuledApproximation.HasFiniteCover IsHorizontalRectangle (strip β M a b W q)
      ((∫ t in a..b, 2*β*W t/denominator (q t)) + ε) := by
  let K : ℝ := 1+2*M
  have hK : 0 < K := by dsimp [K]; positivity
  have hlen : 0 < b-a := sub_pos.mpr hab
  let η : ℝ := ε/(4*β*K*(b-a))
  have hη : 0 < η := by dsimp [η]; positivity
  have huW := isCompact_Icc.uniformContinuousOn_of_continuous hW
  have huq := isCompact_Icc.uniformContinuousOn_of_continuous hq
  obtain ⟨δW,hδW,hcloseW⟩ := Metric.uniformContinuousOn_iff.mp huW η hη
  obtain ⟨δq,hδq,hcloseq⟩ := Metric.uniformContinuousOn_iff.mp huq η hη
  have hlim := taggedSum_tendsto hab (strip_cost_continuous (β := β) hW hq)
    (fun N i => point a b N i) (leftTagged hab)
  have hevent : ∀ᶠ N : ℕ in atTop,
      0 < N ∧ step a b N < δW ∧ step a b N < δq ∧
      (∑ i : Fin N, step a b N * (2*β*W (point a b N i)/denominator (q (point a b N i)))) <
        (∫ t in a..b, 2*β*W t/denominator (q t)) + ε/2 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      (step_tendsto a b).eventually_lt_const hδW,
      (step_tendsto a b).eventually_lt_const hδq,
      hlim.eventually_lt_const (by linarith :
        (∫ t in a..b, 2*β*W t/denominator (q t)) <
        (∫ t in a..b, 2*β*W t/denominator (q t)) + ε/2)] with N hN hNW hNq hcost
    exact ⟨hN,hNW,hNq,hcost⟩
  obtain ⟨N,hN,hNW,hNq,hcost⟩ := hevent.exists
  let C : Fin N → RuledApproximation.Cylinder := fun i =>
    rectangleCylinder (q (point a b N i))
      (β*(W (point a b N i)+K*η)/denominator (q (point a b N i)))
      (point a b N i) (point a b N (i+1))
  refine ⟨N,C,?_,?_,?_⟩
  · intro i
    apply rectangleCylinder_shape
    · have hp := hW0 _ (point_mem hab hN i.isLt.le)
      have hden := denominator_pos (q (point a b N i))
      positivity
    · have hd := step_pos hab hN
      have hs := point_succ a b N i
      linarith
  · rintro z ⟨x,y,t,rfl,ht,hx,hy,hs⟩
    obtain ⟨i,hi⟩ := exists_cell hN ht
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    change vec (β*x) (β*y) t ∈ (C i).carrier
    dsimp [C]
    rw [rectangleCylinder_carrier]
    have htag := leftTagged hab N i
    have htagI := cell_subset hab i htag
    have hd := cell_dist_le hi htag
    apply frozen_rectangle_covers hβ.le hη.le hx hy _ _ hs hi
    · exact (hcloseq t ht _ htagI (hd.trans_lt hNq)).le
    · exact (hcloseW t ht _ htagI (hd.trans_lt hNW)).le
  · have hsum : RuledApproximation.familyArea C ≤
        (∑ i : Fin N, step a b N * (2*β*W (point a b N i)/denominator (q (point a b N i)))) +
          2*β*K*η*(b-a) := by
      unfold RuledApproximation.familyArea
      calc
        _ ≤ ∑ i : Fin N,
            (step a b N * (2*β*W (point a b N i)/denominator (q (point a b N i))) +
            step a b N * (2*β*K*η)) := by
          apply Finset.sum_le_sum
          intro i _
          exact frozen_area_bound hβ.le hM hη.le hab hN i
            (hW0 _ (point_mem hab hN i.isLt.le))
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          rw [show (N : ℝ) * (step a b N * (2*β*K*η)) =
              2*β*K*η*((N : ℝ)*step a b N) by ring,count_step hN]
    have hmargin : 2*β*K*η*(b-a) = ε/2 := by
      dsimp [η]
      field_simp
      ring
    rw [hmargin] at hsum
    linarith

end CylinderCovering.BeamStrip

end

end OAI
