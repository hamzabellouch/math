import OAI.Geometry.NodalSets.Elliptic.CoordinateMatrixEllipticity

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Set
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_parameter_matrix_ellipticity
    (B : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) {Q : Set Yau.Jets.Coord}
    (hQ : IsCompact Q)
    (hB : ∀ i j, Continuous (fun z : T × Q ↦ B z.1 z.2 i j))
    (hp : ∀ t x, x ∈ Q → (B t x).PosDef) :
    ∃ k > 0, ∃ L > 0, ∀ t x, x ∈ Q → ∀ v : Yau.Jets.Coord,
      k*(∑ i, v i^2) ≤ (∑ i, ∑ j, v i*B t x i j*v j) ∧
      (∑ i, ∑ j, v i*B t x i j*v j) ≤ L*(∑ i, v i^2) := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let g := fun z : T × Q ↦ coordMatrixForm (B z.1 z.2)
  obtain ⟨k,hk,L,hL,hb⟩ := uniform_metric_coercivity g
    (coordMatrixForm_continuous (fun z : T × Q ↦ B z.1 z.2) hB)
    (fun z v hv ↦ coordMatrixForm_positive _ (hp z.1 z.2 z.2.property) v hv)
  refine ⟨k/4,by positivity,L,hL,?_⟩
  intro t x hx v
  have h := hb (t,⟨x,hx⟩)
  have hlo : k*‖v‖^2 ≤ coordMatrixForm (B t x) v v := h.2 v
  have hhi : coordMatrixForm (B t x) v v ≤ L*‖v‖^2 := calc
    _ ≤ |coordMatrixForm (B t x) v v| := le_abs_self _
    _ ≤ ‖g (t,⟨x,hx⟩)‖*‖v‖*‖v‖ := bilinear_pairing_bound _ v v
    _ ≤ L*‖v‖^2 := by nlinarith [mul_le_mul_of_nonneg_right h.1 (sq_nonneg ‖v‖)]
  rw [coordMatrixForm_apply] at hlo hhi
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (coord_sum_sq_le_four_norm_sq v) hk.le]
  · exact hhi.trans (mul_le_mul_of_nonneg_left (coord_norm_sq_le_sum_sq v) hL.le)

lemma compact_parameter_scalar_bound (f : T → Yau.Jets.Coord → ℝ)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : Continuous (fun z : T × Q ↦ f z.1 z.2)) :
    ∃ M > 0, ∀ t x, x ∈ Q → |f t x| ≤ M := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨M,hM,hb⟩ := (isCompact_univ.image hf).isBounded.exists_pos_norm_le
  refine ⟨M,hM,?_⟩
  intro t x hx
  exact hb _ ⟨(t,⟨x,hx⟩),mem_univ _,rfl⟩

end

open Metric
attribute [local instance] clmTopology clmAdd clmModule

theorem local_bilinear_coercivity
    (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (x0 : Yau.Jets.Coord)
    (hp : ∀ v : Yau.Jets.Coord, v ≠ 0 → 0 < g x0 v v) :
    ∃ r > 0, ∃ a > 0, ∀ x ∈ ball x0 r, ∀ v : Yau.Jets.Coord,
      a*(∑ i, (v i)^2) ≤ g x v v := by
  obtain ⟨c,hc,C,hC,hbase⟩ := uniform_metric_coercivity (fun _ : Unit ↦ g x0)
    continuous_const (fun _ v hv ↦ hp v hv)
  obtain ⟨r,hr,hnear⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := x0)) (c/2) (by positivity)
  refine ⟨r,hr,c/8,by positivity,?_⟩
  intro x hx v
  have hn : ‖g x-g x0‖ ≤ c/2 := by
    exact (show ‖g x-g x0‖ < c/2 from by simpa only [dist_eq_norm] using hnear hx).le
  have habs : |g x v v-g x0 v v| ≤ (c/2)*‖v‖^2 := by
    have h := bilinear_pairing_bound (g x-g x0) v v
    simp only [_root_.sub_apply] at h
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖v‖)])
  have hb := (hbase ()).2 v
  have hs := mul_le_mul_of_nonneg_left (coord_sum_sq_le_four_norm_sq v) hc.le
  have hlo := (abs_le.mp habs).1
  change c*‖v‖^2 ≤ g x0 v v at hb
  nlinarith only [hb,hs,hlo]

end Yau.Geometry

end

end OAI
