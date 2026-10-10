import OAI.Analysis.LipschitzHilbert.Geometry.FarGroupEnergy

namespace OAI

/-! The far-pair overlap estimate for an actual rectangle selection,
combining popular-projection packing with the group energy bound. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem selected_far_overlap {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (s : Finset ι) (hsub : s ⊆ selected.toFinset) (ρ : ι) (hρ : ρ ∈ previous)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hRef : (R ρ).Admissible v K δ)
    (hR : ∀ j ∈ s, (R j).Admissible v K δ)
    (hL : ∀ j ∈ s, (R j).long ≤ (R ρ).long)
    (hinter : ∀ j ∈ s, ((R ρ).carrier ∩ (R j).carrier).Nonempty)
    (hfar : ∀ j ∈ s, 64*(R j).short < (R j).long*dist ((R ρ).axes 0) ((R j).axes 0)) :
    (δ : ℝ≥0∞)*(∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).carrier)) ≤
      960*volume (R ρ).carrier := by
  let S := R ρ
  let θ := fun i => dist (S.axes 0) ((R i).axes 0)
  have hgeom (i : ι) (hi : i ∈ s) : 0 < θ i ∧ θ i ≤ 1/20 ∧ 32*S.short < θ i*S.long := by
    obtain ⟨p,hprev,_,hn⟩ := hrun.selected_previous_witness i (List.mem_toFinset.mp (hsub hi))
    have hw := far_selected_earlier_width (fun i => (D i).orthogonalCoordinates) R p ρ i
      (hprev hρ) (hL i hi) (hinter i hi) (hfar i hi) hn
    have ha := far_selected_angle_bound S (R i) hv hu hδ hRef (hR i hi)
      (hL i hi) (hinter i hi) (hfar i hi) hw
    refine ⟨?_,ha.2,hw⟩
    by_contra hnθ
    have hm := mul_nonpos_of_nonneg_of_nonpos (R i).long_pos.le (le_of_not_gt hnθ)
    have hf := hfar i hi
    change 64*(R i).short < (R i).long*θ i at hf
    linarith [(R i).short_pos]
  have ha (j : ι) (hj : j ∈ s) : dist ((R j).axes 0) (S.axes 0) ≤ 1/4 := by
    rw [dist_comm]
    exact (hgeom j hj).2.1.trans (by norm_num)
  obtain ⟨centers,hcenters,hpack,hcover⟩ := exists_projected_popularity_groups R s S
    hv.continuous hδ hR hL (fun j hj => by simpa only [inter_comm] using hinter j hj) ha
  let group := fun i => s.filter (fun j => (R j).long ≤ (R i).long ∧
    (S.coordinateProjection ((R i).popularSet v) ∩ S.coordinateProjection ((R j).popularSet v)).Nonempty)
  have hg (i : ι) (hi : i ∈ centers) :
      (∑ j ∈ group i, volume ((R j).carrier ∩ S.carrier)) ≤
        ENNReal.ofReal 80*ENNReal.ofReal (R i).long*ENNReal.ofReal S.short := by
    have his := hcenters hi
    have hdirs (j : ι) (hj : j ∈ group i) : dist ((R i).axes 0) ((R j).axes 0) ≤ θ i/2 := by
      have hj' := Finset.mem_filter.mp hj
      apply Rectangle.projected_popularity_directions S (R i) (R j) hv hu hRef.1
        (hL i his) hj'.2.1 (by simpa only [inter_comm] using hinter i his) (by simpa only [inter_comm] using hinter j hj'.1)
        (hfar i his).le (hfar j hj'.1).le _ hj'.2.2
      nlinarith [(hgeom i his).2.2]
    have hupper (j : ι) (hj : j ∈ group i) : dist (S.axes 0) ((R j).axes 0) ≤ 2*θ i := by
      have ht := dist_triangle (S.axes 0) ((R i).axes 0) ((R j).axes 0)
      change dist (S.axes 0) ((R j).axes 0) ≤ θ i+_ at ht
      linarith [hdirs j hj,(hgeom i his).1]
    have hlower (j : ι) (hj : j ∈ group i) : θ i/2 ≤ dist (S.axes 0) ((R j).axes 0) := by
      have ht := dist_triangle (S.axes 0) ((R j).axes 0) ((R i).axes 0)
      rw [dist_comm ((R j).axes 0) ((R i).axes 0)] at ht
      change θ i ≤ _ at ht
      linarith [hdirs j hj]
    let F : SelectedFarFamily ι := {
      n := n
      directions := D
      direction_net := hD
      rectangles := R
      previous := previous
      stock := stock
      selected := selected
      run := hrun
      members := group i
      members_selected := fun j hj => hsub (Finset.mem_filter.mp hj).1
      reference := ρ
      reference_previous := hρ
      angle := θ i
      angle_pos := (hgeom i his).1
      angle_small := (hgeom i his).2.1
      lengths := fun j hj => hL j (Finset.mem_filter.mp hj).1
      intersects := fun j hj => hinter j (Finset.mem_filter.mp hj).1
      far := fun j hj => hfar j (Finset.mem_filter.mp hj).1
      angle_upper := hupper
      angle_lower := hlower }
    exact F.group_overlap_bound (R i) v (fun j hj => (Finset.mem_filter.mp hj).2.1)
      (fun j hj => (Finset.mem_filter.mp hj).2.2)
  have hcover' (j : ι) (hj : j ∈ s) : ∃ i ∈ centers, j ∈ group i := by
    obtain ⟨i,hi,hji,hp⟩ := hcover j hj
    exact ⟨i,hi,Finset.mem_filter.mpr ⟨hj,hji,hp⟩⟩
  let f := fun j => volume ((R j).carrier ∩ S.carrier)
  have hsum : (∑ j ∈ s, f j) ≤ ∑ i ∈ centers, ∑ j ∈ group i, f j := by
    calc
      _ ≤ ∑ j ∈ s, ∑ i ∈ centers, if j ∈ group i then f j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨i,hi,hji⟩ := hcover' j hj
        have hh := Finset.single_le_sum (f := fun i => if j ∈ group i then f j else 0)
          (fun _ _ => zero_le) hi
        simpa only [ite_eq_left hji] using hh
      _ = ∑ i ∈ centers, ∑ j ∈ s, if j ∈ group i then f j else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [←Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter,and_iff_right_iff_imp]
        exact fun hj => (Finset.mem_filter.mp hj).1
  have henergy : (∑ j ∈ s, f j) ≤
      (ENNReal.ofReal 80*ENNReal.ofReal S.short)*(∑ i ∈ centers, ENNReal.ofReal (R i).long) := by
    refine hsum.trans ?_
    calc
      _ ≤ ∑ i ∈ centers, ENNReal.ofReal 80*ENNReal.ofReal (R i).long*ENNReal.ofReal S.short :=
        Finset.sum_le_sum hg
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  calc
    _ ≤ (δ : ℝ≥0∞)*((ENNReal.ofReal 80*ENNReal.ofReal S.short)*
        (∑ i ∈ centers, ENNReal.ofReal (R i).long)) := mul_le_mul' le_rfl henergy
    _ = (ENNReal.ofReal 80*ENNReal.ofReal S.short)*
        ((δ : ℝ≥0∞)*(∑ i ∈ centers, ENNReal.ofReal (R i).long)) := by ring
    _ ≤ (ENNReal.ofReal 80*ENNReal.ofReal S.short)*(12*ENNReal.ofReal S.long) :=
      mul_le_mul' le_rfl hpack
    _ = _ := by rw [S.volume_carrier]; norm_num; ring

end LipschitzHilbert

end

end OAI
