import Mathlib
import OAI.GroupTheory.FiniteType.CWCylinder

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace SphereQuotient
open Set Topology Metric
open scoped unitInterval
universe u
abbrev Disk := CWCylinder.Disk
abbrev Boundary := CWCylinder.Boundary

def height (r : ℝ) : ℝ := min 1 (max (-1) (6*r-3))
def scale (r : ℝ) : ℝ := min 1 (3*(1-r)) / max r (1/3)

theorem height_low {r : ℝ} (h : r ≤ 1/3) : height r = -1 := by
  unfold height
  rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
theorem scale_low {r : ℝ} (h : r ≤ 1/3) : scale r = 3 := by
  unfold scale
  rw [max_eq_right h,min_eq_left (by linarith)]
  norm_num

theorem height_mid {r : ℝ} (h : 1/3 ≤ r) (h' : r ≤ 2/3) : height r = 6*r-3 := by
  unfold height
  rw [max_eq_right (by linarith),min_eq_right (by linarith)]
theorem scale_mid {r : ℝ} (h : 1/3 ≤ r) (h' : r ≤ 2/3) : scale r = 1/r := by
  unfold scale
  rw [max_eq_left h,min_eq_left (by linarith)]

theorem height_high {r : ℝ} (h : 2/3 ≤ r) : height r = 1 := by
  unfold height
  rw [max_eq_right (by linarith),min_eq_left (by linarith)]
theorem scale_high {r : ℝ} (h : 2/3 ≤ r) : scale r = 3*(1-r)/r := by
  unfold scale
  rw [max_eq_left (by linarith),min_eq_right (by linarith)]

theorem scale_nonneg {r : ℝ} (h : 0 ≤ r) (h' : r ≤ 1) : 0 ≤ scale r := by
  unfold scale
  exact div_nonneg (le_min (by norm_num) (by linarith)) (le_max_of_le_left h)

def point (n : ℕ) (v : Disk n) : Fin (n+1) → ℝ :=
  Fin.cons (height ‖v.1‖) (scale ‖v.1‖ • v.1)

theorem point_norm (n : ℕ) (v : Disk n) : ‖point n v‖ = 1 := by
  have hr : 0 ≤ ‖v.1‖ := norm_nonneg _
  have hr' : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
  rw [point,CWCylinder.norm_cons,norm_smul,Real.norm_of_nonneg (scale_nonneg hr hr')]
  by_cases hlo : ‖v.1‖ ≤ 1/3
  · rw [height_low hlo,scale_low hlo]
    norm_num
    linarith
  by_cases hhi : 2/3 ≤ ‖v.1‖
  · rw [height_high hhi,scale_high hhi]
    have hn : ‖v.1‖ ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hn]
    norm_num
    linarith
  · rw [height_mid (le_of_not_ge hlo) (le_of_not_ge hhi),scale_mid (le_of_not_ge hlo) (le_of_not_ge hhi)]
    have hn : ‖v.1‖ ≠ 0 := by linarith
    rw [one_div_mul_cancel hn,max_eq_right]
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith

def quotient (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨point n v,by simpa only [mem_sphere,dist_zero_right] using point_norm n v⟩,by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun v : Disk n => height ‖v.1‖)
      unfold height
      fun_prop
    · change Continuous (fun v : Disk n => scale ‖v.1‖ * v.1 j)
      apply Continuous.mul
      · unfold scale
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro v
          have : (0:ℝ) < max ‖v.1‖ (1/3) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
          exact ne_of_gt this
      · exact (continuous_apply j).comp continuous_subtype_val⟩

def pole (n : ℕ) : Boundary (n+1) :=
  ⟨Fin.cons 1 0,by rw [mem_sphere,dist_zero_right,CWCylinder.norm_cons]; simp⟩

theorem quotient_boundary {n : ℕ} (v : Disk n) (hv : ‖v.1‖ = 1) : quotient n v = pole n := by
  apply Subtype.ext
  change (Fin.cons (height ‖v.1‖) (scale ‖v.1‖ • v.1) : Fin (n+1) → ℝ) = Fin.cons 1 0
  rw [hv,height_high (by norm_num),scale_high (by norm_num)]
  norm_num

theorem height_eq_low_iff (r : ℝ) : height r = -1 ↔ r ≤ 1/3 := by
  constructor
  · intro he
    by_contra hr
    have hh : -1 < height r := by
      apply lt_min (by norm_num)
      exact lt_max_of_lt_right (by linarith)
    linarith
  · exact height_low

theorem height_eq_high_iff (r : ℝ) : height r = 1 ↔ 2/3 ≤ r := by
  constructor
  · intro he
    by_contra hr
    have hh : height r < 1 := by
      apply lt_of_le_of_lt (min_le_right _ _)
      exact max_lt (by norm_num) (by linarith)
    linarith
  · exact height_high

theorem profile_injective {r s : ℝ} (hh : height r = height s)
    (ht : scale r * r = scale s * s) : r = s := by
  by_cases hr : r ≤ 1/3
  · have hs : s ≤ 1/3 := (height_eq_low_iff s).mp (hh.symm.trans (height_low hr))
    rw [scale_low hr,scale_low hs] at ht
    linarith
  by_cases hr' : 2/3 ≤ r
  · have hs' : 2/3 ≤ s := (height_eq_high_iff s).mp (hh.symm.trans (height_high hr'))
    rw [scale_high hr',scale_high hs',div_mul_cancel₀ _ (by linarith : r ≠ 0),
      div_mul_cancel₀ _ (by linarith : s ≠ 0)] at ht
    linarith
  · have hs : ¬s ≤ 1/3 := fun hs => hr ((height_eq_low_iff r).mp (hh.trans (height_low hs)))
    have hs' : ¬2/3 ≤ s := fun hs' => hr' ((height_eq_high_iff r).mp (hh.trans (height_high hs')))
    rw [height_mid (le_of_not_ge hr) (le_of_not_ge hr'),
      height_mid (le_of_not_ge hs) (le_of_not_ge hs')] at hh
    linarith

theorem quotient_eq {n : ℕ} {v w : Disk n} (h : quotient n v = quotient n w) :
    v = w ∨ (‖v.1‖ = 1 ∧ ‖w.1‖ = 1) := by
  have hv : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
  have hw : ‖w.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using w.2
  have h₀ : height ‖v.1‖ = height ‖w.1‖ := congrArg (fun z : Boundary (n+1) => z.1 0) h
  have hs : scale ‖v.1‖ • v.1 = scale ‖w.1‖ • w.1 :=
    congrArg (fun z : Boundary (n+1) => Fin.tail z.1) h
  have hn : scale ‖v.1‖ * ‖v.1‖ = scale ‖w.1‖ * ‖w.1‖ := by
    simpa only [norm_smul,Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hv),
      Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hw)] using congrArg norm hs
  have hr := profile_injective h₀ hn
  by_cases hr1 : ‖v.1‖ = 1
  · exact Or.inr ⟨hr1,hr.symm.trans hr1⟩
  · apply Or.inl
    have hp : 0 < scale ‖v.1‖ := by
      apply div_pos
      · exact lt_min (by norm_num) (by have := lt_of_le_of_ne hv hr1; linarith)
      · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    apply Subtype.ext
    rw [← hr] at hs
    exact smul_right_injective _ (ne_of_gt hp) hs

theorem quotient_eq_pole {n : ℕ} {v : Disk n} (h : quotient n v = pole n) : ‖v.1‖ = 1 := by
  have h₀ : height ‖v.1‖ = 1 := congrArg (fun z : Boundary (n+1) => z.1 0) h
  have hs : scale ‖v.1‖ • v.1 = (0 : Fin n → ℝ) :=
    congrArg (fun z : Boundary (n+1) => Fin.tail z.1) h
  have hv := (height_eq_high_iff _).mp h₀
  have hn : scale ‖v.1‖ * ‖v.1‖ = 0 := by
    have hv' : ‖v.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
    simpa only [norm_smul,Real.norm_of_nonneg (scale_nonneg (norm_nonneg _) hv'),norm_zero] using congrArg norm hs
  rw [scale_high hv,div_mul_cancel₀ _ (by linarith : ‖v.1‖ ≠ 0)] at hn
  linarith

theorem boundary_ext {n : ℕ} {v w : Boundary (n+1)}
    (h₀ : v.1 0 = w.1 0) (ht : Fin.tail v.1 = Fin.tail w.1) : v = w := by
  apply Subtype.ext
  funext i
  exact Fin.cases h₀ (fun j => congrFun ht j) i

theorem quotient_surjective_or_pole (n : ℕ) (z : Boundary (n+1)) :
    z = pole n ∨ ∃ v,quotient n v = z := by
  have hz : ‖z.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2
  have hs : ‖Fin.tail z.1‖ ≤ 1 := (CWCylinder.norm_tail_le z.1).trans_eq hz
  have ha : |z.1 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs,hz] using norm_le_pi_norm z.1 0
  have hal := (abs_le.mp ha).1
  have hau := (abs_le.mp ha).2
  by_cases hlo : z.1 0 = -1
  · apply Or.inr
    let x : Fin n → ℝ := (1/3 : ℝ) • Fin.tail z.1
    have hx : ‖x‖ = (1/3 : ℝ) * ‖Fin.tail z.1‖ := by
      rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
    have hx' : ‖x‖ ≤ 1/3 := by rw [hx]; linarith
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right]; linarith⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · exact (height_low hx').trans hlo.symm
    · change scale ‖x‖ • x = _
      rw [scale_low hx']
      dsimp [x]
      rw [smul_smul]
      norm_num
  by_cases hhi : z.1 0 = 1
  · by_cases hs0 : Fin.tail z.1 = 0
    · exact Or.inl (boundary_ext hhi hs0)
    apply Or.inr
    have hspos : 0 < ‖Fin.tail z.1‖ := norm_pos_iff.mpr hs0
    let r : ℝ := 1 - ‖Fin.tail z.1‖/3
    have hrlo : 2/3 ≤ r := by dsimp [r]; linarith
    have hrhi : r ≤ 1 := by dsimp [r]; linarith
    have hrpos : 0 < r := by linarith
    let x : Fin n → ℝ := (r/‖Fin.tail z.1‖) • Fin.tail z.1
    have hx : ‖x‖ = r := by
      rw [norm_smul,Real.norm_of_nonneg (div_nonneg hrpos.le hspos.le),div_mul_cancel₀ _ (ne_of_gt hspos)]
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right,hx]; exact hrhi⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · change height ‖x‖ = z.1 0
      rw [hx,height_high hrlo,hhi]
    · change scale ‖x‖ • x = _
      rw [hx,scale_high hrlo]
      dsimp only [x]
      rw [smul_smul]
      have he : 3*(1-r)/r * (r/‖Fin.tail z.1‖) = 1 := by
        field_simp [ne_of_gt hrpos,ne_of_gt hspos]
        dsimp [r]
        ring
      rw [he,one_smul]
  · apply Or.inr
    have ht : ‖Fin.tail z.1‖ = 1 := by
      have hmax : max ‖z.1 0‖ ‖Fin.tail z.1‖ = 1 := by rw [← CWCylinder.norm_eq_max,hz]
      have hne : ‖z.1 0‖ ≠ 1 := by
        intro he
        rw [Real.norm_eq_abs] at he
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp he with he | he
        · exact hhi he
        · exact hlo he
      exact (max_eq_iff.mp hmax).resolve_left (fun h => hne h.1) |>.1
    let r : ℝ := (z.1 0 + 3)/6
    have hrlo : 1/3 ≤ r := by dsimp [r]; linarith
    have hrhi : r ≤ 2/3 := by dsimp [r]; linarith
    have hrpos : 0 < r := by linarith
    let x : Fin n → ℝ := r • Fin.tail z.1
    have hx : ‖x‖ = r := by rw [norm_smul,Real.norm_of_nonneg hrpos.le,ht,mul_one]
    let v : Disk n := ⟨x,by rw [mem_closedBall,dist_zero_right,hx]; linarith⟩
    refine ⟨v,boundary_ext ?_ ?_⟩
    · change height ‖x‖ = z.1 0
      rw [hx,height_mid hrlo hrhi]
      dsimp [r]
      ring
    · change scale ‖x‖ • x = _
      rw [hx,scale_mid hrlo hrhi]
      dsimp only [x]
      rw [smul_smul,one_div_mul_cancel (ne_of_gt hrpos),one_smul]

def sphereQuot (n : ℕ) : C(Disk n ⊕ Unit,Boundary (n+1)) :=
  ⟨Sum.elim (quotient n) (fun _ => pole n),
    continuous_sum_dom.mpr ⟨(quotient n).continuous,continuous_const⟩⟩

theorem sphereQuot_surjective (n : ℕ) : Function.Surjective (sphereQuot n) := by
  intro z
  rcases quotient_surjective_or_pole n z with hz | ⟨v,hv⟩
  · exact ⟨Sum.inr (),hz.symm⟩
  · exact ⟨Sum.inl v,hv⟩

theorem sphereQuot_isQuotientMap (n : ℕ) : IsQuotientMap (sphereQuot n) :=
  IsQuotientMap.of_surjective_continuous (sphereQuot_surjective n) (sphereQuot n).continuous

end SphereQuotient

end

end OAI
