import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.InducedSphereAlgebra

namespace OAI

namespace CKSLorentz
end CKSLorentz

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

abbrev U : Set E := {x | x ≠ 0}
lemma U_open : IsOpen U := isClosed_singleton.isOpen_compl

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

lemma expand_vec (x : E) : x = ∑ i : Ix, x i • e i := by
  ext j
  simp [e_apply]

def grad (F : E → ℝ) (x : E) : Vec := fun i => pd i F x

def hess (F : E → ℝ) (x : E) : Mat := fun i j => pd i (pd j F) x

def third (F : E → ℝ) (x : E) : Ix → Mat := fun k i j => pd k (pd i (pd j F)) x

lemma partial_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    ContDiffOn ℝ ∞ (pd i F) U :=
  (hF.fderiv_of_isOpen U_open (by simp)).clm_apply contDiffOn_const

lemma hess_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun x => hess F x i j) U :=
  partial_smooth (partial_smooth hF j) i

lemma partial_of_clm (A : E →L[ℝ] ℝ) (i : Ix) (x : E) : pd i A x = A (e i) := by
  rw [pd, A.fderiv]

lemma partial_partial {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) :
    pd i (pd j F) x = fderiv ℝ (fderiv ℝ F) x (e i) (e j) := by
  have hd := ((hF.fderiv_of_isOpen (m := ∞) U_open (by simp)).contDiffAt
    (U_open.mem_nhds hx)).differentiableAt (by simp)
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const (e j))]
  simp

lemma partial_comm {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) : pd i (pd j F) x = pd j (pd i F) x := by
  rw [partial_partial hF hx, partial_partial hF hx]
  exact ((hF.contDiffAt (U_open.mem_nhds hx)).isSymmSndFDerivAt (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using (ENat.LEInfty.out (m := 2)))).eq _ _

lemma third_cycle {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k i j : Ix) : third F x k i j = third F x j k i := by
  change pd k (pd i (pd j F)) x = pd j (pd k (pd i F)) x
  have he : pd i (pd j F) =ᶠ[𝓝 x] pd j (pd i F) := by
    filter_upwards [U_open.mem_nhds hx] with y hy
    exact partial_comm hF hy i j
  have he' := congrArg (fun A : E →L[ℝ] ℝ => A (e k)) (he.fderiv_eq)
  change pd k (pd i (pd j F)) x = pd k (pd j (pd i F)) x at he'
  rw [he', partial_comm (partial_smooth hF i) hx k j]

lemma fderiv_expand (F : E → ℝ) (x v : E) : fderiv ℝ F x v = ∑ i, v i * grad F x i := by
  conv_lhs => rw [expand_vec v]
  simp only [map_sum, map_smul, smul_eq_mul, grad, pd]

lemma smooth_diff {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ F x := (hF.contDiffAt (U_open.mem_nhds hx)).differentiableAt (by simp)

lemma pd_add {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y + G y) x = pd k F x + pd k G x := by
  simp only [pd, fderiv_fun_add hF hG, add_apply]

lemma pd_sub {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y - G y) x = pd k F x - pd k G x := by
  simp only [pd, fderiv_fun_sub hF hG, sub_apply]

lemma pd_mul {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y * G y) x = pd k F x * G x + F x * pd k G x := by
  rw [pd, fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul, pd]
  ring

lemma pd_sum {J : Type*} (s : Finset J) {A : J → E → ℝ} {x : E}
    (hA : ∀ j ∈ s, DifferentiableAt ℝ (A j) x) (k : Ix) :
    pd k (fun y => ∑ j ∈ s, A j y) x = ∑ j ∈ s, pd k (A j) x := by
  simp only [pd, fderiv_fun_sum hA, _root_.sum_apply]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

lemma pd_const_mul {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (c : ℝ) (k : Ix) : pd k (fun y => c * F y) x = c * pd k F x := by
  erw [pd_mul (differentiableAt_const c) hF, pd_const, zero_mul, zero_add]

lemma pd_div_const {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (c : ℝ) (k : Ix) : pd k (fun y => F y / c) x = pd k F x / c := by
  simp_rw [div_eq_mul_inv, mul_comm _ c⁻¹]
  exact pd_const_mul hF _ k

lemma coordinate_smooth (i : Ix) : ContDiffOn ℝ ∞ (fun x : E => x i) U :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).contDiff.contDiffOn

@[simp] lemma pd_coordinate (k i : Ix) (x : E) :
    pd k (fun y : E => y i) x = if k = i then 1 else 0 := by
  change pd k (EuclideanSpace.proj i) x = _
  rw [partial_of_clm]
  simp [eq_comm]

lemma proj_smooth (i j : Ix) : ContDiffOn ℝ ∞ (fun x : E => proj (fun a => x a) i j) U :=
  contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))

lemma pd_proj (x : E) (k i j : Ix) :
    pd k (fun y : E => proj (fun a => y a) i j) x = dproj (fun a => x a) k i j := by
  unfold proj
  erw [pd_sub (differentiableAt_const (if i = j then (1 : ℝ) else 0)) ((EuclideanSpace.proj i).differentiableAt.fun_mul
    (EuclideanSpace.proj j).differentiableAt), pd_const,
    pd_mul (EuclideanSpace.proj i).differentiableAt (EuclideanSpace.proj j).differentiableAt]
  simp only [partial_of_clm, EuclideanSpace.proj, PiLp.proj_apply, e_apply, eq_comm, dproj]
  ring

lemma trace_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => tangentTrace (fun a => x a) (hess F x)) U := by
  unfold tangentTrace
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (proj_smooth i j).mul (hess_smooth hF i j)))

lemma pd_tangentTrace {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k : Ix) : pd k (fun y => tangentTrace (fun a => y a) (hess F y)) x =
      dTangentTrace (fun a => x a) (hess F x) (third F x) k := by
  unfold tangentTrace dTangentTrace
  rw [pd_sum univ (fun i _ => smooth_diff
    (ContDiffOn.sum (fun j _ => (proj_smooth i j).mul (hess_smooth hF i j))) hx)]
  apply sum_congr rfl
  intro i hi
  rw [pd_sum univ (fun j _ => smooth_diff ((proj_smooth i j).mul (hess_smooth hF i j)) hx)]
  apply sum_congr rfl
  intro j hj
  erw [pd_mul (smooth_diff (proj_smooth i j) hx) (smooth_diff (hess_smooth hF i j) hx), pd_proj]
  rfl

def roundLaplacian (F : E → ℝ) (x : E) : ℝ := roundLap (fun i => x i) (grad F x) (hess F x)

def traceFreeHess (F : E → ℝ) (x : E) (i j : Ix) : ℝ := hessTF (fun a => x a) (hess F x) i j

def tensorDivergence (T : E → Mat) (x : E) (j : Ix) : ℝ :=
  ∑ k, ∑ i, ∑ l, proj (fun a => x a) k i * proj (fun a => x a) j l *
    pd k (fun y => T y i l) x

def sphereGradient (F : E → ℝ) (x : E) (j : Ix) : ℝ :=
  ∑ k, proj (fun a => x a) j k * grad F x k

lemma roundLaplacian_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (roundLaplacian F) U :=
  (trace_smooth hF).sub (contDiffOn_const.mul (ContDiffOn.sum (fun i _ =>
    (coordinate_smooth i).mul (partial_smooth hF i))))

lemma pd_roundLaplacian {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k : Ix) : pd k (roundLaplacian F) x =
      dRoundLap (fun a => x a) (grad F x) (hess F x) (third F x) k := by
  have hs : ContDiffOn ℝ ∞ (fun y => ∑ i : Ix, y i * pd i F y) U :=
    ContDiffOn.sum (fun i _ => (coordinate_smooth i).mul (partial_smooth hF i))
  change pd k (fun y => tangentTrace (fun a => y a) (hess F y) -
    2 * ∑ i : Ix, y i * pd i F y) x = _
  erw [pd_sub (smooth_diff (trace_smooth hF) hx) (smooth_diff ((contDiffOn_const (c := (2 : ℝ))).mul hs) hx),
    pd_tangentTrace hF hx, pd_const_mul (smooth_diff hs hx),
    pd_sum univ (fun i _ => smooth_diff ((coordinate_smooth i).mul (partial_smooth hF i)) hx)]
  simp only [grad, pd_mul (smooth_diff (coordinate_smooth _) hx)
    (smooth_diff (partial_smooth hF _) hx), pd_coordinate,
    ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq, Finset.mem_univ, ite_true,
    dRoundLap, hess]

lemma traceFreeHess_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun x => traceFreeHess F x i j) U := by
  unfold traceFreeHess hessTF
  exact (ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ =>
    ((proj_smooth i a).mul (hess_smooth hF a b)).mul (proj_smooth b j)))).sub
      (((trace_smooth hF).div_const 2).mul (proj_smooth i j))

lemma pd_traceFreeHess {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (k i j : Ix) : pd k (fun y => traceFreeHess F y i j) x =
      dHessTF (fun a => x a) (hess F x) (third F x) k i j := by
  have hp (a b : Ix) := smooth_diff (proj_smooth a b) hx
  have hh (a b : Ix) := smooth_diff (hess_smooth hF a b) hx
  have hcore : DifferentiableAt ℝ (fun y : E =>
      ∑ a, ∑ b, proj (fun c => y c) i a * hess F y a b * proj (fun c => y c) b j) x :=
    DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ => ((hp i a).fun_mul (hh a b)).fun_mul (hp b j)))
  unfold traceFreeHess hessTF
  erw [pd_sub hcore ((smooth_diff ((trace_smooth hF).div_const 2) hx).fun_mul (hp i j)),
    pd_mul (smooth_diff ((trace_smooth hF).div_const 2) hx) (hp i j),
    pd_div_const (smooth_diff (trace_smooth hF) hx), pd_tangentTrace hF hx, pd_proj]
  rw [pd_sum univ (fun a _ => DifferentiableAt.fun_sum (fun b _ =>
    ((hp i a).fun_mul (hh a b)).fun_mul (hp b j)))]
  have hs (a : Ix) : pd k (fun y : E => ∑ b,
      proj (fun c => y c) i a * hess F y a b * proj (fun c => y c) b j) x =
      ∑ b, (dproj (fun c => x c) k i a * hess F x a b * proj (fun c => x c) b j +
      proj (fun c => x c) i a * third F x k a b * proj (fun c => x c) b j +
      proj (fun c => x c) i a * hess F x a b * dproj (fun c => x c) k b j) := by
    rw [pd_sum univ (fun b _ => ((hp i a).fun_mul (hh a b)).fun_mul (hp b j))]
    apply sum_congr rfl
    intro b hb
    erw [pd_mul ((hp i a).fun_mul (hh a b)) (hp b j), pd_mul (hp i a) (hh a b), pd_proj, pd_proj]
    change (_ * _ + _ * third F x k a b) * _ + _ * _ = _
    ring
  simp_rw [hs]
  unfold dHessTF
  ring

lemma unit_sum_sq {x : E} (hx : ‖x‖ = 1) : ∑ i, x i ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

theorem divergence_traceFreeHess {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {x : E} (hx : ‖x‖ = 1) (j : Ix) :
    tensorDivergence (traceFreeHess F) x j = sphereGradient (fun y => F y + roundLaplacian F y / 2) x j := by
  have hxU : x ∈ U := by intro h; simp [h] at hx
  have hc : tensorDivergence (traceFreeHess F) x j =
      divHessTF (fun a => x a) (hess F x) (third F x) j := by
    simp only [tensorDivergence, divHessTF, pd_traceFreeHess hF hxU]
  rw [hc, divHessTF_eq (unit_sum_sq hx) (grad F x) (hess F x) (third F x)
    (fun i j => partial_comm hF hxU i j) (fun k i j => third_cycle hF hxU k i j)]
  unfold sphereGradient grad
  apply sum_congr rfl
  intro k hk
  rw [pd_add (smooth_diff hF hxU) (smooth_diff ((roundLaplacian_smooth hF).div_const 2) hxU),
    pd_div_const (smooth_diff (roundLaplacian_smooth hF) hxU), pd_roundLaplacian hF hxU]
  rfl

end
end CKSInducedSphere

end

end OAI
