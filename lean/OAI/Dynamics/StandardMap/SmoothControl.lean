import OAI.Dynamics.StandardMap.SmoothCap

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma c2_deriv_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  apply ContDiff.deriv'
  convert! hf using 1
lemma c2_compact_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃C≥0,(∀x∈Icc a b,|deriv f x|≤C) ∧ (∀x∈Icc a b,|deriv (deriv f) x|≤C) := by
  obtain ⟨C1,h1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc a b)
  obtain ⟨C2,h2⟩ := isCompact_Icc.exists_bound_of_continuousOn ((c2_deriv_contDiff hf).continuous_deriv_one).continuousOn (s := Icc a b)
  refine ⟨max 0 (max C1 C2),le_max_left _ _,?_,?_⟩
  · intro x hx
    exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x hx
    exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
lemma deriv_bound_lipschitz {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b C x y : ℝ}
    (hb : ∀u∈Icc a b,|deriv f u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f y-f x|≤C*|y-x| := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => hf u) hb (convex_Icc _ _) hx hy
lemma c2_remainder_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x z : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hz : z∈Icc a b) :
    |f x-f z-deriv f z*(x-z)|≤C*(x-z)^2 := by
  have hsub : uIcc z x⊆Icc a b := by
    intro u hu
    rw [mem_uIcc] at hu
    rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
    · exact ⟨hz.1.trans hzu,hux.trans hx.2⟩
    · exact ⟨hx.1.trans hxu,huz.trans hz.2⟩
  let R : ℝ → ℝ := fun u => f u-f z-deriv f z*(u-z)
  have hd (u : ℝ) : HasDerivAt R (deriv f u-deriv f z) u := by
    convert! (((hf.differentiable (by norm_num) u).hasDerivAt.sub_const (f z)).sub
      (((hasDerivAt_id u).sub_const z).const_mul (deriv f z))) using 1 ; simp
  have hR : ∀u∈uIcc z x,|deriv R u|≤C*|x-z| := by
    intro u hu
    rw [(hd u).deriv]
    have h1 := deriv_bound_lipschitz hf.differentiable_deriv_two hb hz (hsub hu)
    have hu' : |u-z|≤|x-z| := by
      rw [mem_uIcc] at hu
      rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
      · rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hu' hC)
  have hr := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (hd u).differentiableAt)
    hR (convex_uIcc z x) (left_mem_uIcc) (right_mem_uIcc)
  change |R x-R z|≤(C*|x-z|)*|x-z| at hr
  have he : R z=0 := by dsimp [R]; ring
  rw [he,sub_zero,mul_assoc,←pow_two, sq_abs] at hr
  exact hr
lemma c2_midpoint_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f ((x+y)/2)-(f x+f y)/2|≤(C/4)*(x-y)^2 := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have h1 := c2_remainder_bound hf hC hb hx hm
  have h2 := c2_remainder_bound hf hC hb hy hm
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1,h1.2,h2.1,h2.2]
lemma c2_capped_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y z : ℝ} (hC : 0≤C)
    (h1 : ∀u∈Icc a b,|deriv f u|≤C) (h2 : ∀u∈Icc a b,|deriv (deriv f) u|≤C)
    (hx : x∈Icc a b) (hy : y∈Icc a b) (hz : z∈Icc a b) (hJ : 0≤z-(x+y)/2) :
    |f z-(f x+f y)/2|≤C*((z-(x+y)/2)+(x-y)^2) := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have hh := deriv_bound_lipschitz (hf.differentiable (by norm_num)) h1 hm hz
  rw [abs_of_nonneg hJ] at hh
  have ht := c2_midpoint_bound hf hC h2 hx hy
  have htri := abs_add_le (f z-f ((x+y)/2)) (f ((x+y)/2)-(f x+f y)/2)
  rw [sub_add_sub_cancel] at htri
  nlinarith [mul_nonneg hC (sq_nonneg (x-y))]
lemma entropyCap_upper {α : ℝ} (hα : 0≤α) (hα1 : α≤1) :
    ∃C>0,∀u∈Icc (0:ℝ) 1,entropyCap α u≤C*u := by
  obtain ⟨C,hC,h1,_⟩ := c2_compact_bounds (entropyCap_contDiff α) 0 1
  refine ⟨C+1,by linarith,?_⟩
  intro u hu
  have hh := deriv_bound_lipschitz ((entropyCap_contDiff α).differentiable (by norm_num)) h1
    (by constructor <;> norm_num : (0:ℝ)∈Icc 0 1) hu
  rw [entropyCap_linear (u := 0) (by norm_num),mul_zero,sub_zero,sub_zero,abs_of_nonneg hu.1,
    abs_of_nonneg (entropyCap_bounds hα hα1 hu).1] at hh
  nlinarith [hu.1]
end StandardMapEntropy

end OAI
