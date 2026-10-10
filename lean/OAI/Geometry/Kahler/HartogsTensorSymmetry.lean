import OAI.Geometry.Kahler.HartogsNormalBlocks

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dbar_complexHessian_conj {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 3 f p) (b c d : Fin 3) :
    dbar (fun q => complexHessian f q c d) p b =
      star (dz (fun q => complexHessian f q d c) p b) := by
  have he : (fun q => complexHessian f q c d) =ᶠ[𝓝 p]
      (fun q => star (complexHessian f q d c)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_hermitian (hq.of_le (by norm_num)) c d
  have hd : DifferentiableAt ℝ (fun q => complexHessian f q d c) p :=
    (_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 2) (by norm_num) c) (m := 1) (by norm_num) d).differentiableAt (by norm_num)
  rw [dbar_congr he, dbar_conj hd]

lemma dbar_dz_star {f : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (a b : Fin 3) :
    dbar (fun q => dz (fun r => star (f r)) q a) p b =
      star (dz (fun q => dbar f q a) p b) := by
  have he : (fun q => dz (fun r => star (f r)) q a) =ᶠ[𝓝 p]
      (fun q => star (dbar f q a)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact dz_conj (hq.differentiableAt (by norm_num)) a
  rw [dbar_congr he, dbar_conj ((_root_.OAI.ContDiffAt.hartogs_dbar hf (m := 1) (by norm_num) a).differentiableAt (by norm_num))]

lemma complexHessian_fourth_reality {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    star (dbar (fun q => dz (fun r => complexHessian f r c d) q a) p b) =
      dbar (fun q => dz (fun r => complexHessian f r d c) q b) p a := by
  have he : (fun q => complexHessian f q c d) =ᶠ[𝓝 p]
      (fun q => star (complexHessian f q d c)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_hermitian (hq.of_le (by norm_num)) c d
  have hh : ContDiffAt ℝ 2 (fun q => complexHessian f q d c) p :=
    _root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 3) (by norm_num) c) (m := 2) (by norm_num) d
  rw [dbar_dz_congr he, dbar_dz_star hh, star_star, dz_dbar_comm hh]

lemma complexHessian_curvature_hol {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    curvature (complexHessian f) p a b c d = curvature (complexHessian f) p c b a d := by
  have he : (fun q => dz (fun r => complexHessian f r c d) q a) =ᶠ[𝓝 p]
      (fun q => dz (fun r => complexHessian f r a d) q c) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact complexHessian_closed (hq.of_le (by norm_num)) a d c
  unfold curvature
  rw [dbar_congr he]
  congr 1
  apply Finset.sum_congr rfl
  intro e he'
  apply Finset.sum_congr rfl
  intro k hk
  rw [complexHessian_closed (hf.of_le (by norm_num)) a e c]

lemma complexHessian_curvature_reality {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    star (curvature (complexHessian f) p a b c d) = curvature (complexHessian f) p b a d c := by
  have hM : (complexHessian f p).IsHermitian := by
    ext i j
    exact (complexHessian_hermitian (hf.of_le (by norm_num)) i j).symm
  have hi (e k : Fin 3) : star ((complexHessian f p)⁻¹ e k) = (complexHessian f p)⁻¹ k e := hM.inv.apply k e
  have hd (i j k : Fin 3) : star (dz (fun q => complexHessian f q i j) p k) = dbar (fun q => complexHessian f q j i) p k :=
    (dbar_complexHessian_conj (hf.of_le (by norm_num)) k j i).symm
  unfold curvature
  simp only [star_add, star_neg, star_sum, star_mul]
  rw [complexHessian_fourth_reality hf]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro e he
  rw [hi, hd, dbar_complexHessian_conj (hf.of_le (by norm_num)), star_star]
  ring

lemma complexHessian_curvature_anti {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 4 f p) (a b c d : Fin 3) :
    curvature (complexHessian f) p a b c d = curvature (complexHessian f) p a d c b := by
  apply star_injective
  rw [complexHessian_curvature_reality hf, complexHessian_curvature_reality hf,
    complexHessian_curvature_hol hf b a d c]

lemma liftedBarThird_conj {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 3 f q.1) (b c d : Fin 3) :
    liftedBarThird f q b c d = star (liftedThird f q b d c) :=
  dbar_complexHessian_conj (hf.comp (f := fun r : Ambient => r.1) q contDiffAt_fst) b c d

end PinchedHartogs

end

end OAI
