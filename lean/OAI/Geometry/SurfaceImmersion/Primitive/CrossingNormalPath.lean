import OAI.Geometry.SurfaceImmersion.Geometry.ActualCurveAvoidance

namespace OAI

/-! The preferred-normal adjustment at a crossing: a normalized straight path
stays away from both forbidden antipodes and ends with positive pairings. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma nonzero_of_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : v ≠ 0 := by
  intro hz
  rw [hz,zero_dotProduct] at h
  exact (lt_irrefl _ h)

lemma normalize_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : 0 < normalize v ⬝ᵥ m := by
  have hv := nonzero_of_dot_pos h
  have hnorm : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr (dot_self_pos hv)
  simpa only [normalize,smul_dotProduct,smul_eq_mul] using mul_pos (inv_pos.mpr hnorm) h

lemma crossing_blend_nonzero {n p m : Vec} {t : ℝ} (hn : n ⬝ᵥ n = 1)
    (hnm : n ⬝ᵥ m = 0) (hp : 0 < p ⬝ᵥ m) (ht : t ∈ Icc (0 : ℝ) 1) :
    blend n (normalize p) t ≠ 0 := by
  by_cases ht0 : t = 0
  · intro hz
    have hzero : n = 0 := by simpa only [blend,ht0,sub_zero,one_smul,zero_smul,add_zero] using hz
    rw [hzero,zero_dotProduct] at hn
    norm_num at hn
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    apply nonzero_of_dot_pos (m := m)
    simp only [blend,add_dotProduct,smul_dotProduct,smul_eq_mul,hnm,mul_zero,zero_add]
    exact mul_pos htp (normalize_dot_pos hp)

theorem crossing_normal_path {n p q m : Vec} (hn : n ⬝ᵥ n = 1)
    (hnm : n ⬝ᵥ m = 0) (hp : 0 < p ⬝ᵥ m) (hq : 0 < q ⬝ᵥ m)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    first n (normalize p) t ⬝ᵥ first n (normalize p) t = 1 ∧
    first n (normalize p) t ≠ -normalize p ∧
    first n (normalize p) t ≠ -normalize q := by
  have hb := crossing_blend_nonzero hn hnm hp ht
  have hbm : 0 ≤ blend n (normalize p) t ⬝ᵥ m := by
    simp only [blend,add_dotProduct,smul_dotProduct,smul_eq_mul,hnm,mul_zero,zero_add]
    exact mul_nonneg ht.1 (normalize_dot_pos hp).le
  have hfm : 0 ≤ first n (normalize p) t ⬝ᵥ m := by
    change 0 ≤ normalize (blend n (normalize p) t) ⬝ᵥ m
    simp only [normalize,smul_dotProduct,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hbm
  refine ⟨normalize_unit hb,?_,?_⟩
  · intro he
    rw [he,neg_dotProduct] at hfm
    linarith [normalize_dot_pos hp]
  · intro he
    rw [he,neg_dotProduct] at hfm
    linarith [normalize_dot_pos hq]

theorem crossing_normal_path_endpoint {n p q m : Vec}
    (hp : 0 < p ⬝ᵥ m) (hpq : 0 < p ⬝ᵥ q) :
    0 < p ⬝ᵥ first n (normalize p) 1 ∧ 0 < q ⬝ᵥ first n (normalize p) 1 := by
  rw [first_one (normalize_unit (nonzero_of_dot_pos hp))]
  constructor
  · rw [dotProduct_comm]
    exact normalize_dot_pos (dot_self_pos (nonzero_of_dot_pos hp))
  · rw [dotProduct_comm]
    exact normalize_dot_pos hpq

lemma crossing_normal_path_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n p m : E → Vec} {t : E → ℝ} {x : E}
    (hn : ContDiffAt ℝ ∞ n x) (hp : ContDiffAt ℝ ∞ p x) (ht : ContDiffAt ℝ ∞ t x)
    (hnn : n x ⬝ᵥ n x = 1) (hnm : n x ⬝ᵥ m x = 0)
    (hpm : 0 < p x ⬝ᵥ m x) (ht01 : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => first (n y) (normalize (p y)) (t y)) x :=
  first_smoothAt_of_nonzero hn (normalize_smoothAt hp (nonzero_of_dot_pos hpm)) ht
    (crossing_blend_nonzero hnn hnm hpm ht01)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
