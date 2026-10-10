import OAI.Geometry.Kahler.HartogsJetLinearity

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma baseHessian_contDiffAt {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (baseHessian f) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact _root_.OAI.ContDiffAt.hartogs_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := ∞) (by simp) j) (by simp) i

lemma _root_.OAI.ContDiffAt.hartogs_baseHessian {f : Base → ℝ} {z : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f z) (hmn : m + 2 ≤ n) : ContDiffAt ℝ m (baseHessian f) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact _root_.OAI.ContDiffAt.hartogs_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := m+1) (by convert hmn using 1; norm_num [add_assoc]) j) (m := m) le_rfl i

lemma liftedHessian_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i j : Fin 2) :
    liftedHessian f q i.castSucc j.castSucc = baseHessian f q.1 i j := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases i <;> fin_cases j <;> rfl

lemma liftedHessian_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (j : Fin 3) : liftedHessian f q 2 j = 0 := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases j <;> rfl

lemma liftedHessian_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i : Fin 3) : liftedHessian f q i 2 = 0 := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases i <;> rfl

lemma liftedHessian_horizontal_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i j : Fin 2) :
    (fun r => liftedHessian f r i.castSucc j.castSucc) =ᶠ[𝓝 q]
      (fun r => baseHessian f r.1 i j) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_horizontal hr i j

lemma liftedHessian_vertical_left_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (j : Fin 3) :
    (fun r => liftedHessian f r 2 j) =ᶠ[𝓝 q] (fun _ => 0) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_vertical_left hr j

lemma liftedHessian_vertical_right_eventually {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i : Fin 3) :
    (fun r => liftedHessian f r i 2) =ᶠ[𝓝 q] (fun _ => 0) := by
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
  change ContDiffAt ℝ 2 f r.1 at hr
  exact liftedHessian_vertical_right hr i

lemma liftedThird_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (a c d : Fin 2) :
    liftedThird f q a.castSucc c.castSucc d.castSucc =
      dzBase (fun z => baseHessian f z c d) q.1 a := by
  have hd := (contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 1) (by norm_num)) c) d).differentiableAt (by simp)
  rw [liftedThird, dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d), dz_lift_base hd]
  fin_cases a <;> rfl

lemma liftedBarThird_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (b c d : Fin 2) :
    liftedBarThird f q b.castSucc c.castSucc d.castSucc =
      dbarBase (fun z => baseHessian f z c d) q.1 b := by
  have hd := (contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 1) (by norm_num)) c) d).differentiableAt (by simp)
  rw [liftedBarThird, dbar_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d), dbar_lift_base hd]
  fin_cases b <;> rfl

lemma liftedThird_vertical_middle {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a d : Fin 3) : liftedThird f q a 2 d = 0 := by
  rw [liftedThird, dz_congr (liftedHessian_vertical_left_eventually hf d)]
  simp [dz]

lemma liftedThird_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a c : Fin 3) : liftedThird f q a c 2 = 0 := by
  rw [liftedThird, dz_congr (liftedHessian_vertical_right_eventually hf c)]
  simp [dz]

lemma liftedThird_vertical_left_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (c d : Fin 2) :
    liftedThird f q 2 c.castSucc d.castSucc = 0 := by
  have hd := (contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 1) (by norm_num)) c) d).differentiableAt (by simp)
  rw [liftedThird, dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d), dz_lift_base hd]
  rfl

lemma liftedThird_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (c d : Fin 3) : liftedThird f q 2 c d = 0 := by
  refine Fin.lastCases ?_ (fun c => ?_) c
  · exact liftedThird_vertical_middle (hf.of_le (by norm_num)) 2 d
  · refine Fin.lastCases ?_ (fun d => ?_) d
    · exact liftedThird_vertical_right (hf.of_le (by norm_num)) 2 c.castSucc
    · exact liftedThird_vertical_left_horizontal hf c d

lemma liftedFourth_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a b c d : Fin 2) :
    liftedFourth f q a.castSucc b.castSucc c.castSucc d.castSucc =
      dzBase (fun z => dbarBase (fun t => baseHessian f t c d) z b) q.1 a := by
  have hc : ContDiffAt ℝ 2 (fun z => baseHessian f z c d) q.1 := contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 2) (by norm_num)) c) d
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d)]
  erw [← dz_dbar_comm (hc.comp (f := fun r : Ambient => r.1) q contDiffAt_fst)]
  have he : (fun r : Ambient => dbar (fun t : Ambient => baseHessian f t.1 c d) r b.castSucc) =ᶠ[𝓝 q]
      (fun r => dbarBase (fun t => baseHessian f t c d) r.1 b) := by
    have hf2 := hc.of_le (show (2 : WithTop ℕ∞) ≤ 2 from le_rfl)
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf2.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 2 (fun z => baseHessian f z c d) r.1 at hr
    rw [dbar_lift_base (hr.differentiableAt (by norm_num))]
    fin_cases b <;> rfl
  erw [dz_congr he, dz_lift_base ((_root_.OAI.ContDiffAt.hartogs_dbarBase hc (m := 1) (by norm_num) b).differentiableAt (by norm_num))]
  fin_cases a <;> rfl

lemma liftedFourth_vertical_middle {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a b d : Fin 3) : liftedFourth f q a b 2 d = 0 := by
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_vertical_left_eventually hf d)]
  simp [dz, dbar]

lemma liftedFourth_vertical_right {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (a b c : Fin 3) : liftedFourth f q a b c 2 = 0 := by
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_vertical_right_eventually hf c)]
  simp [dz, dbar]

lemma liftedFourth_vertical_left {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (b c d : Fin 3) : liftedFourth f q 2 b c d = 0 := by
  have he : (fun r => liftedThird f r 2 c d) =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hf.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 3 f r.1 at hr
    exact liftedThird_vertical_left hr c d
  rw [liftedFourth, dbar_congr he]
  simp [dbar]

lemma liftedFourth_vertical_second_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a : Fin 3) (c d : Fin 2) :
    liftedFourth f q a 2 c.castSucc d.castSucc = 0 := by
  have hc : ContDiffAt ℝ 2 (fun z => baseHessian f z c d) q.1 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (_root_.OAI.ContDiffAt.hartogs_baseHessian hf (m := 2) (by norm_num)) c) d
  unfold liftedFourth liftedThird
  rw [dbar_dz_congr (liftedHessian_horizontal_eventually (hf.of_le (by norm_num)) c d)]
  erw [← dz_dbar_comm (hc.comp (f := fun r : Ambient => r.1) q contDiffAt_fst)]
  have he : (fun r : Ambient => dbar (fun t : Ambient => baseHessian f t.1 c d) r 2) =ᶠ[𝓝 q]
      (fun _ => 0) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hc.eventually (by norm_num))] with r hr
    change ContDiffAt ℝ 2 (fun z => baseHessian f z c d) r.1 at hr
    exact dbar_lift_base (hr.differentiableAt (by norm_num)) 2
  erw [dz_congr he]
  simp [dz]

lemma liftedFourth_vertical_second {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 4 f q.1) (a c d : Fin 3) : liftedFourth f q a 2 c d = 0 := by
  refine Fin.lastCases ?_ (fun c => ?_) c
  · exact liftedFourth_vertical_middle (hf.of_le (by norm_num)) a 2 d
  · refine Fin.lastCases ?_ (fun d => ?_) d
    · exact liftedFourth_vertical_right (hf.of_le (by norm_num)) a 2 c.castSucc
    · exact liftedFourth_vertical_second_horizontal hf a c d

end PinchedHartogs

end

end OAI
