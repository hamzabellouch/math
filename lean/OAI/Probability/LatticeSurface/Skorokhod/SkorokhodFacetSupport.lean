import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodDriver

namespace OAI

namespace ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def facetPath (x y : E) (t : ℝ) : E := x+(min (2*t) 1) • (y-x)

def facetDriver (x y n : E) (a t : ℝ) : E :=
  (min (2*t) 1) • (y-x)+(max (2*t-1) 0) • (a • n)

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma project_outward_ray (B : Body E) (y n : E) (hy : y∈B.carrier)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y)  ≤  0) (a : ℝ) (ha : 0 ≤ a) :
    project B (y+a • n)=y := by
  let p := project B (y+a • n)
  have hi := project_variational B (y+a • n) y hy
  have hs := hsupport p (project_mem B _)
  have he : p-(y+a • n)=(p-y)-a • n := by abel
  have he' : y-p=-(p-y) := by abel
  change 0  ≤  inner ℝ (p-(y+a • n)) (y-p) at hi
  rw [he,he',inner_neg_right,inner_sub_left,inner_smul_left,real_inner_self_eq_norm_sq] at hi
  simp only [conj_trivial] at hi
  have hp : ‖p-y‖=0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hs,norm_nonneg (p-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hp)

omit [CompleteSpace E] in
lemma facetPath_continuous (x y : E) : Continuous (facetPath x y) := by
  unfold facetPath;fun_prop

omit [CompleteSpace E] in
lemma facetDriver_continuous (x y n : E) (a : ℝ) : Continuous (facetDriver x y n a) := by
  unfold facetDriver;fun_prop

omit [CompleteSpace E] in
lemma facetPath_mem (B : Body E) (x y : E) (hx : x∈B.carrier) (hy : y∈B.carrier)
    (t : ℝ) (ht : 0 ≤ t) : facetPath x y t∈B.carrier := by
  have hq₀ : 0 ≤ min (2*t) 1 := le_min (by positivity) zero_le_one
  have hq₁ : min (2*t) 1 ≤ 1 := min_le_right _ _
  have hb := B.convex hx hy (sub_nonneg.mpr hq₁) hq₀ (by ring : (1-min (2*t) 1)+min (2*t) 1=1)
  convert hb using 1
  unfold facetPath
  module

lemma facet_projection_step (B : Body E) (x y n : E) (a : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y)  ≤  0) (ha : 0 ≤ a)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    project B (facetPath x y s+(facetDriver x y n a t-facetDriver x y n a s))=
      facetPath x y t := by
  have ht : 0 ≤ t := hs.trans hst
  have he : facetPath x y s+(facetDriver x y n a t-facetDriver x y n a s)=
      facetPath x y t+((max (2*t-1) 0-max (2*s-1) 0)*a) • n := by
    unfold facetPath facetDriver
    module
  rw [he]
  by_cases hsmall : 2*t ≤ 1
  · have hsmalls : 2*s ≤ 1 := by linarith
    rw [max_eq_right (by linarith : 2*t-1 ≤ 0),max_eq_right (by linarith : 2*s-1 ≤ 0)]
    simp only [sub_self,zero_mul,zero_smul,add_zero]
    exact project_eq_self B _ (facetPath_mem B x y hx hy t ht)
  · have heq : facetPath x y t=y := by
      rw [facetPath,min_eq_right (le_of_not_ge hsmall),one_smul];abel
    rw [heq]
    apply project_outward_ray B y n hy hsupport
    apply mul_nonneg _ ha
    exact sub_nonneg.mpr (max_le_max_right 0 (by linarith))

lemma facet_walk (B : Body E) (x y n : E) (a : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y)  ≤  0) (ha : 0 ≤ a)
    (N i : ℕ) (_hN : 0<N) :
    walk B x (sampledDriver (facetDriver x y n a) N) i=facetPath x y ((i:ℝ)/N) := by
  induction i with
  | zero => simp [walk,facetPath]
  | succ i ih =>
    rw [walk,ih]
    exact facet_projection_step B x y n a hx hy hsupport ha _ _ (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (Nat.cast_nonneg N))

lemma facet_mesh_tendsto (B : Body E) (x y n : E) (a : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y)  ≤  0) (ha : 0 ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun m => mesh B x (facetDriver x y n a) (m+1) t) atTop (nhds (facetPath x y t)) := by
  have he : (fun m => mesh B x (facetDriver x y n a) (m+1) t)=
      fun m => facetPath x y ((⌊t*((m+1:ℕ):ℝ)⌋₊:ℝ)/((m+1:ℕ):ℝ)) := by
    funext m
    exact facet_walk B x y n a hx hy hsupport ha (m+1) _ (Nat.succ_pos _)
  rw [he]
  exact (facetPath_continuous x y).continuousAt.tendsto.comp (sample_floor_tendsto t ht)

end ConvexSkorokhod

end OAI
