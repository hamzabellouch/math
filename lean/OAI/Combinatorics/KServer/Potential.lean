import Mathlib

namespace OAI

/-! Deterministic heavy-center schedule and its clipped distance profile.
Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.HeavyCenters

/-- The heavy profile is zero up to radius 3 and one from radius 4. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (u-3))
lemma ramp_bounds (u : ℝ) : ramp u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 3) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : u-3 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 4 ≤ u) : ramp u=1 := by
  exact min_eq_left ((by linarith : 1 ≤ u-3).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (u-v) <;> have h2 := neg_le_abs (u-v) <;> linarith

variable {Y : Type*} [MetricSpace Y]

/-- Finite minimum with a default value 1, also for the empty center set. -/
def profile (r : ℝ) (C : Finset Y) (y : Y) : ℝ :=
  (insert 1 (C.image (fun a => ramp (dist a y/r)))).min' ⟨1,mem_insert_self _ _⟩

lemma profile_nonneg (r : ℝ) (C : Finset Y) (y : Y) : 0 ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    exact (ramp_bounds _).1

lemma profile_le_one (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma profile_bounds (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ∈ Set.Icc 0 1 :=
  ⟨profile_nonneg _ _ _,profile_le_one _ _ _⟩
lemma profile_le (r : ℝ) {C : Finset Y} {a : Y} (ha : a∈C) (y : Y) :
    profile r C y ≤ ramp (dist a y/r) :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨a,ha,rfl⟩))
lemma le_profile (r : ℝ) (C : Finset Y) (y : Y) {u : ℝ} (hu : u ≤ 1)
    (h : ∀ a∈C,u ≤ ramp (dist a y/r)) : u ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact h a ha
lemma profile_empty (r : ℝ) (y : Y) : profile r ∅ y=1 := by
  simp [profile]
lemma profile_eq_one {r : ℝ} (hr : 0<r) {C : Finset Y} {y : Y}
    (h : ∀ a∈C,4*r ≤ dist a y) : profile r C y=1 := by
  apply le_antisymm (profile_le_one _ _ _)
  apply le_profile _ _ _ le_rfl
  intro a ha
  rw [ramp_one ((le_div_iff₀ hr).mpr (h a ha))]
lemma profile_eq_zero {r : ℝ} (hr : 0<r) {C : Finset Y} {a y : Y}
    (ha : a∈C) (hay : dist a y ≤ 3*r) : profile r C y=0 := by
  apply le_antisymm _ (profile_nonneg _ _ _)
  exact (profile_le r ha y).trans_eq (ramp_zero ((div_le_iff₀ hr).mpr hay))

lemma profile_gt_witness {r : ℝ} {C : Finset Y} {y : Y} {u : ℝ}
    (hu : u ≤ 1) (h : profile r C y<u) :
    ∃ a∈C,ramp (dist a y/r)<u := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (le_profile r C y hu hn)) h

lemma profile_lipschitz {r : ℝ} (hr : 0<r) (C : Finset Y) (y z : Y) :
    |profile r C y-profile r C z| ≤ dist y z/r := by
  have hdir (y z : Y) : profile r C y-profile r C z ≤ dist y z/r := by
    suffices profile r C y-dist y z/r ≤ profile r C z by linarith
    apply le_profile r C z
    · linarith [profile_le_one r C y,div_nonneg (dist_nonneg (x := y) (y := z)) hr.le]
    · intro a ha
      have hl := ramp_lipschitz (dist a y/r) (dist a z/r)
      have hm : |dist a y-dist a z| ≤ dist y z := by
        simpa only [dist_comm a] using abs_dist_sub_le y z a
      rw [←sub_div,abs_div,abs_of_pos hr] at hl
      have hb := hl.trans (div_le_div_of_nonneg_right hm hr.le)
      have hc := (le_abs_self (ramp (dist a y/r)-ramp (dist a z/r))).trans hb
      linarith [profile_le r ha y]
  rw [abs_sub_le_iff]
  exact ⟨hdir y z,by simpa only [dist_comm z y] using hdir z y⟩

/-- Delete centers at distance at most 100r, then insert the heavy request. -/
def replace (r : ℝ) (C : Finset Y) (x : Y) : Finset Y :=
  insert x (C.filter (fun a => 100*r<dist a x))

lemma new_profile_zero {r : ℝ} (hr : 0<r) (C : Finset Y) {x y : Y}
    (hy : dist x y ≤ 3*r) : profile r (replace r C x) y=0 :=
  profile_eq_zero hr (mem_insert_self _ _) hy

lemma profile_increase_support {r : ℝ} (hr : 0<r) (C : Finset Y) (x y : Y)
    (h : profile r C y < profile r (replace r C x) y) :
    3*r<dist x y ∧ dist x y ≤ 104*r := by
  constructor
  · by_contra hh
    rw [new_profile_zero hr C (le_of_not_gt hh)] at h
    exact (not_lt_of_ge (profile_nonneg _ _ _)) h
  · obtain ⟨a,ha,hai⟩ := profile_gt_witness (profile_le_one r (replace r C x) y) h
    have har : dist a y<4*r := by
      by_contra hn
      rw [ramp_one ((le_div_iff₀ hr).mpr (le_of_not_gt hn))] at hai
      linarith [profile_le_one r (replace r C x) y]
    have han : a∉replace r C x := by
      intro he
      exact (not_lt_of_ge (profile_le r he y)) hai
    have had : dist a x ≤ 100*r := by
      by_contra hd
      exact han (mem_insert_of_mem (mem_filter.mpr ⟨ha,lt_of_not_ge hd⟩))
    have ht := dist_triangle x a y
    rw [dist_comm x a] at ht
    linarith

lemma near_profile_edit {r : ℝ} (hr : 0<r) {C : Finset Y} {x s : Y}
    (hfar : ∀ a∈C,8*r<dist a x) (hs : dist s x<r/4) :
    profile r C s=1 ∧ profile r (replace r C x) s=0 := by
  constructor
  · apply profile_eq_one hr
    intro a ha
    have ht := dist_triangle a s x
    have hf := hfar a ha
    linarith
  · apply new_profile_zero hr
    rw [dist_comm]
    linarith

end KServer.HeavyCenters

end


/- The finite variational pilot potential. -/

noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.Pilot

structure Template where
  σ : ℝ
  R : ℝ
  L : ℝ
  σ_pos : 0 < σ
  σ_le : σ ≤ 1
  R_ge : 256 ≤ R
  L_nonneg : 0 ≤ L

def b (T : Template) (v : ℝ) : ℝ := max 0 (min 1 (2 - v / T.σ))
def a (T : Template) (v : ℝ) : ℝ :=
  if v ≤ T.R then min (v ^ 2 / T.σ ^ 2) 1
  else if v ≤ 2 * T.R then 2 - v / T.R else 0
def G (T : Template) (v : ℝ) : ℝ := max 0 (min 1 (v / (10 * T.R) - 1))

lemma b_nonneg (T : Template) (v : ℝ) : 0 ≤ b T v := le_max_left _ _
lemma b_le_one (T : Template) (v : ℝ) : b T v ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
lemma b_eq_one {T : Template} {v : ℝ} (hv : v ≤ T.σ) : b T v = 1 := by
  have : v / T.σ ≤ 1 := (div_le_one T.σ_pos).mpr hv
  simp [b, min_eq_left (show 1 ≤ 2 - v / T.σ by linarith)]
lemma b_eq_zero {T : Template} {v : ℝ} (hv : 2 * T.σ ≤ v) : b T v = 0 := by
  have : 2 ≤ v / T.σ := (le_div_iff₀ T.σ_pos).mpr hv
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
lemma b_pos_iff {T : Template} {v : ℝ} : 0 < b T v ↔ v < 2 * T.σ := by
  simp only [b, lt_max_iff, lt_self_iff_false, false_or, lt_min_iff]
  constructor
  · intro h
    have : v / T.σ < 2 := by linarith [h.2]
    exact (div_lt_iff₀ T.σ_pos).mp this
  · intro h
    have : v / T.σ < 2 := (div_lt_iff₀ T.σ_pos).mpr h
    exact ⟨by norm_num, by linarith⟩
lemma a_nonneg (T : Template) (v : ℝ) : 0 ≤ a T v := by
  unfold a
  split_ifs with h h'
  · exact le_min (div_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one
  · have : v / T.R ≤ 2 := (div_le_iff₀ (by linarith [T.R_ge])).mpr h'
    linarith
  · rfl
lemma a_le_one (T : Template) (v : ℝ) : a T v ≤ 1 := by
  unfold a
  split_ifs with h h'
  · exact min_le_right _ _
  · have : 1 ≤ v / T.R := (le_div_iff₀ (by linarith [T.R_ge])).mpr (by linarith)
    linarith
  · norm_num
lemma a_eq_zero {T : Template} {v : ℝ} (hv : 2 * T.R ≤ v) : a T v = 0 := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  unfold a
  split_ifs with h h'
  · linarith
  · have he : v = 2 * T.R := le_antisymm h' hv
    rw [he]; field_simp; ring
  · rfl
lemma G_nonneg (T : Template) (v : ℝ) : 0 ≤ G T v := le_max_left _ _
lemma G_le_one (T : Template) (v : ℝ) : G T v ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
lemma G_eq_zero {T : Template} {v : ℝ} (hv : v ≤ 10 * T.R) : G T v = 0 := by
  have : v / (10 * T.R) ≤ 1 := (div_le_one (by linarith [T.R_ge])).mpr hv
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
lemma G_eq_one {T : Template} {v : ℝ} (hv : 20 * T.R ≤ v) : G T v = 1 := by
  have : 2 ≤ v / (10 * T.R) := (le_div_iff₀ (by linarith [T.R_ge])).mpr (by linarith)
  simp [G, min_eq_left (show 1 ≤ v / (10 * T.R) - 1 by linarith)]

variable {Y : Type*} [Fintype Y] [MetricSpace Y]

def Feasible (T : Template) (r : ℝ) (z : Y → ℝ) : Prop :=
  (∀ s, 0 ≤ z s) ∧
  (∀ p, ∑ s, max (z s - G T (dist s p / r)) 0 ≤ 1) ∧
  ∀ s t, s ≠ t → dist s t < 5 * T.σ * r → z s * z t = 0

def integrand (T : Template) (r : ℝ) (g z : Y → ℝ) (p : Y) : ℝ :=
  (1 + g p) * (1 - ∑ s, z s * b T (dist s p / r)) +
    256 * ∑ s, z s * (1 + g s) * a T (dist s p / r)

def objective (T : Template) (r : ℝ) (μ g z : Y → ℝ) : ℝ :=
  r * ∑ p, μ p * integrand T r g z p

lemma feasible_zero (T : Template) (r : ℝ) : Feasible (Y := Y) T r 0 := by
  refine ⟨fun _ => le_rfl, fun p => ?_, fun _ _ _ _ => by simp⟩
  have : ∀ s : Y, max (0 - G T (dist s p / r)) 0 = 0 :=
    fun s => max_eq_right (by linarith [G_nonneg T (dist s p / r)])
  simp only [Pi.zero_apply, this, sum_const_zero, zero_le_one]

lemma coordinate_le_one {T : Template} {r : ℝ} {z : Y → ℝ}
    (hz : Feasible T r z) (s : Y) : z s ≤ 1 := by
  have hG : G T (dist s s / r) = 0 := G_eq_zero (by simp; linarith [T.R_ge])
  have hs := single_le_sum (s := (univ : Finset Y))
    (fun t _ => le_max_right (z t - G T (dist t s / r)) 0) (mem_univ s)
  rw [hG, sub_zero, max_eq_left (hz.1 s)] at hs
  exact hs.trans (hz.2.1 s)

lemma feasible_closed (T : Template) (r : ℝ) : IsClosed {z : Y → ℝ | Feasible T r z} := by
  unfold Feasible
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter ?_
  refine (isClosed_iInter fun p => isClosed_le ?_ continuous_const).inter ?_
  · fun_prop
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq ((continuous_apply s).mul (continuous_apply t)) continuous_const

lemma feasible_compact (T : Template) (r : ℝ) : IsCompact {z : Y → ℝ | Feasible T r z} := by
  apply (isCompact_pi_infinite fun _ : Y => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (feasible_closed T r)
  intro z hz s
  exact ⟨hz.1 s, coordinate_le_one hz s⟩

lemma objective_continuous (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    Continuous (objective T r μ g) := by
  unfold objective integrand
  fun_prop

lemma exists_minimizer (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    ∃ z, Feasible T r z ∧ IsMinOn (objective T r μ g) {z | Feasible T r z} z := by
  exact (feasible_compact T r).exists_isMinOn ⟨0, feasible_zero T r⟩
    (objective_continuous T r μ g).continuousOn

/-- A canonical tie-break using choice is legitimate on the finite input tree. -/
def minimizer (T : Template) (r : ℝ) (μ g : Y → ℝ) : Y → ℝ :=
  (exists_minimizer T r μ g).choose
lemma minimizer_spec (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    Feasible T r (minimizer T r μ g) ∧
    IsMinOn (objective T r μ g) {z | Feasible T r z} (minimizer T r μ g) :=
  (exists_minimizer T r μ g).choose_spec

def potential (T : Template) (r : ℝ) (μ g : Y → ℝ) : ℝ :=
  objective T r μ g (minimizer T r μ g)

lemma potential_le {T : Template} {r : ℝ} {μ g z : Y → ℝ}
    (hz : Feasible T r z) : potential T r μ g ≤ objective T r μ g z :=
  (minimizer_spec T r μ g).2 hz

lemma weighted_bump_le_capacity {T : Template} {r : ℝ} {z f : Y → ℝ} {p : Y}
    (hz : Feasible T r z) (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (hG : ∀ s, 0 < f s → G T (dist s p / r) = 0) : ∑ s, z s * f s ≤ 1 := by
  apply le_trans (sum_le_sum fun s _ => ?_) (hz.2.1 p)
  by_cases hs : 0 < f s
  · rw [hG s hs, sub_zero, max_eq_left (hz.1 s)]
    exact mul_le_of_le_one_right (hz.1 s) (hf1 s)
  · have he : f s = 0 := le_antisymm (le_of_not_gt hs) (hf0 s)
    rw [he, mul_zero]
    exact le_max_right _ _

lemma sum_b_le_one {T : Template} {r : ℝ} {z : Y → ℝ} (hz : Feasible T r z) (p : Y) :
    ∑ s, z s * b T (dist s p / r) ≤ 1 := by
  apply weighted_bump_le_capacity hz (fun _ => b_nonneg _ _) (fun _ => b_le_one _ _)
  intro s hs
  apply G_eq_zero
  exact (b_pos_iff.mp hs).le.trans (by linarith only [T.σ_le, T.R_ge])

lemma sum_a_le_one {T : Template} {r : ℝ} {z : Y → ℝ} (hz : Feasible T r z) (p : Y) :
    ∑ s, z s * a T (dist s p / r) ≤ 1 := by
  apply weighted_bump_le_capacity hz (fun _ => a_nonneg _ _) (fun _ => a_le_one _ _)
  intro s hs
  apply G_eq_zero
  have hv : dist s p / r < 2 * T.R := by
    by_contra hv
    rw [a_eq_zero (le_of_not_gt hv)] at hs
    exact lt_irrefl _ hs
  exact hv.le.trans (by linarith only [T.R_ge])

lemma integrand_bounds {T : Template} {r : ℝ} {g z : Y → ℝ}
    (hz : Feasible T r z) (hg : ∀ s, g s ∈ Set.Icc 0 1) (p : Y) :
    integrand T r g z p ∈ Set.Icc 0 514 := by
  have hb0 : 0 ≤ ∑ s, z s * b T (dist s p / r) :=
    sum_nonneg fun s _ => mul_nonneg (hz.1 s) (b_nonneg _ _)
  have hb1 := sum_b_le_one hz p
  have ha0 : 0 ≤ ∑ s, z s * (1 + g s) * a T (dist s p / r) := by
    exact sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (a_nonneg _ _)
  have ha1 : (∑ s, z s * (1 + g s) * a T (dist s p / r)) ≤ 2 := by
    calc _ ≤ ∑ s, 2 * (z s * a T (dist s p / r)) := by
           apply sum_le_sum
           intro s _
           have := mul_le_mul_of_nonneg_left (hg s).2 (mul_nonneg (hz.1 s) (a_nonneg T (dist s p / r)))
           nlinarith
         _ = 2 * ∑ s, z s * a T (dist s p / r) := (mul_sum _ _ _).symm
         _ ≤ 2 := by linarith [sum_a_le_one hz p]
  have hres : (1 + g p) * (1 - ∑ s, z s * b T (dist s p / r)) ∈ Set.Icc 0 2 := by
    constructor
    · exact mul_nonneg (by linarith [(hg p).1]) (by linarith)
    · nlinarith [(hg p).1, (hg p).2, mul_nonneg (by linarith [(hg p).1] : 0 ≤ 1 + g p) hb0]
  unfold integrand
  constructor <;> linarith [hres.1, hres.2]

lemma potential_bounds {T : Template} {r : ℝ} {μ g : Y → ℝ}
    (hr : 0 ≤ r) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1) :
    potential T r μ g ∈ Set.Icc 0 (2 * r * ∑ p, μ p) := by
  constructor
  · exact mul_nonneg hr (sum_nonneg fun p _ => mul_nonneg (hμ p)
      (integrand_bounds (minimizer_spec T r μ g).1 hg p).1)
  · apply le_trans (potential_le (feasible_zero T r))
    unfold objective integrand
    simp only [Pi.zero_apply, zero_mul, sum_const_zero, sub_zero, mul_zero, add_zero, mul_one]
    calc _ ≤ r * ∑ p, μ p * 2 := by
           apply mul_le_mul_of_nonneg_left _ hr
           apply sum_le_sum
           intro p _
           exact mul_le_mul_of_nonneg_left (by linarith [(hg p).2]) (hμ p)
         _ = _ := by rw [← sum_mul]; ring

lemma objective_mix (T : Template) (r θ : ℝ) (μ₀ μ₁ g z : Y → ℝ) :
    objective T r (fun p => θ * μ₀ p + (1 - θ) * μ₁ p) g z =
      θ * objective T r μ₀ g z + (1 - θ) * objective T r μ₁ g z := by
  unfold objective
  simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
  ring

lemma potential_concave (T : Template) (r : ℝ) (g μ₀ μ₁ : Y → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 1) :
    θ * potential T r μ₀ g + (1 - θ) * potential T r μ₁ g ≤
      potential T r (fun p => θ * μ₀ p + (1 - θ) * μ₁ p) g := by
  unfold potential
  rw [objective_mix]
  have hz := (minimizer_spec T r (fun p => θ * μ₀ p + (1 - θ) * μ₁ p) g).1
  exact add_le_add (mul_le_mul_of_nonneg_left (potential_le hz) hθ.1)
    (mul_le_mul_of_nonneg_left (potential_le hz) (by linarith [hθ.2]))

lemma positive_b_support_disjoint {T : Template} {r : ℝ} {z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z) {s t p : Y}
    (hs : 0 < z s) (ht : 0 < z t) (hb : 0 < b T (dist s p / r))
    (hb' : 0 < b T (dist t p / r)) : s = t := by
  by_contra hst
  have hs' : dist s p < 2 * T.σ * r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hb)
  have ht' : dist t p < 2 * T.σ * r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hb')
  have hd : dist s t < 5 * T.σ * r := by
    have := dist_triangle s p t
    rw [dist_comm p t] at this
    nlinarith [mul_pos T.σ_pos hr]
  have he := hz.2.2 s t hst hd
  have := mul_pos hs ht
  linarith

lemma feasible_downward {T : Template} {r : ℝ} {z w : Y → ℝ}
    (hz : Feasible T r z) (hw : ∀ s, 0 ≤ w s) (hle : ∀ s, w s ≤ z s) :
    Feasible T r w := by
  refine ⟨hw, fun p => ?_, fun s t hst hd => ?_⟩
  · exact (sum_le_sum fun s _ => max_le_max (sub_le_sub_right (hle s) _) le_rfl).trans (hz.2.1 p)
  · have hm := mul_le_mul (hle s) (hle t) (hw t) (hz.1 s)
    rw [hz.2.2 s t hst hd] at hm
    exact le_antisymm hm (mul_nonneg (hw s) (hw t))

def coefficient (T : Template) (r : ℝ) (μ g : Y → ℝ) (s : Y) : ℝ :=
  ∑ p, μ p * (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r))

lemma objective_linear (T : Template) (r : ℝ) (μ g z : Y → ℝ) :
    objective T r μ g z = r * ((∑ p, μ p * (1 + g p)) + ∑ s, z s * coefficient T r μ g s) := by
  have hi : ∀ p, integrand T r g z p = (1 + g p) +
      ∑ s, z s * (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r)) := by
    intro p
    calc _ = (1 + g p) + (256 * (∑ s, z s * (1 + g s) * a T (dist s p / r)) -
        (1 + g p) * ∑ s, z s * b T (dist s p / r)) := by unfold integrand; ring
      _ = _ := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro s _
        ring
  unfold objective
  congr 1
  calc
    _ = ∑ p, (μ p * (1 + g p) + ∑ s, μ p * (z s *
        (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r)))) := by
      apply sum_congr rfl
      intro p _
      rw [hi, mul_add, mul_sum]
    _ = _ := by
      rw [sum_add_distrib, sum_comm]
      congr 1
      unfold coefficient
      simp only [mul_sum]
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro p _
      ring

lemma minimizer_zero_of_coefficient_pos {T : Template} {r : ℝ} {μ g z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    {s : Y} (hc : 0 < coefficient T r μ g s) : z s = 0 := by
  let w := Function.update z s 0
  have hw : Feasible T r w := by
    apply feasible_downward hz
    · intro t; by_cases ht : t = s <;> simp [w, ht, hz.1]
    · intro t; by_cases ht : t = s <;> simp [w, ht, hz.1]
  have hs := hmin hw
  change objective T r μ g z ≤ objective T r μ g w at hs
  rw [objective_linear, objective_linear] at hs
  have he : (∑ t, w t * coefficient T r μ g t) =
      (∑ t, z t * coefficient T r μ g t) - z s * coefficient T r μ g s := by
    classical
    rw [← sum_erase_add _ _ (mem_univ s), ← sum_erase_add _ _ (mem_univ s)]
    have hsum : (∑ t ∈ univ.erase s, w t * coefficient T r μ g t) =
        ∑ t ∈ univ.erase s, z t * coefficient T r μ g t := by
      apply sum_congr rfl
      intro t ht
      simp [w, ne_of_mem_erase ht]
    rw [hsum]
    simp [w]
  rw [he] at hs
  have : r * z s * coefficient T r μ g s ≤ 0 := by nlinarith
  have : z s ≤ 0 := by nlinarith [mul_pos hr hc]
  exact le_antisymm this (hz.1 s)

lemma a_middle_lower {T : Template} {v : ℝ}
    (hv : 15 * T.σ / 64 ≤ v) (hR : v ≤ T.R) : 225 / 4096 ≤ a T v := by
  rw [a, ite_eq_left hR]
  apply le_min _ (by norm_num)
  apply (le_div_iff₀ (sq_pos_of_pos T.σ_pos)).mpr
  have hv0 : 0 ≤ v := by linarith [T.σ_pos]
  nlinarith [sq_nonneg (v - 15 * T.σ / 64), mul_nonneg
    (sub_nonneg.mpr hv) (show 0 ≤ v + 15 * T.σ / 64 by linarith [T.σ_pos])]

/-- Closed metric balls. -/
def ball (x : Y) (r : ℝ) : Finset Y := univ.filter fun p => dist x p ≤ r

/-- Only the near-site region in pilot-local(2) uses a strict inequality. -/
def nearBall (x : Y) (r : ℝ) : Finset Y := univ.filter fun p => dist x p < r

def mass (μ : Y → ℝ) (S : Finset Y) : ℝ := ∑ p ∈ S, μ p

lemma coefficient_middle_pos {T : Template} {r γ δ : ℝ} {μ g : Y → ℝ} {x s : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hslo : T.σ * r / 4 ≤ dist s x) (hshi : dist s x ≤ T.R * r / 2)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r)) ≤ (1 + δ) * mass μ (ball x (γ * r))) :
    0 < coefficient T r μ g s := by
  have ha : ∀ p ∈ ball x (γ * r), 225 / 4096 ≤ a T (dist s p / r) := by
    intro p hp
    have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
    have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    apply a_middle_lower
    · apply (le_div_iff₀ hr).mpr
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      linarith
    · apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      have hσr : T.σ * r ≤ r := by nlinarith [T.σ_le]
      have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
  have hb : ∀ p, b T (dist s p / r) ≠ 0 → p ∈ ball x (100 * T.R * r) := by
    intro p hp
    have hbpos : 0 < b T (dist s p / r) := lt_of_le_of_ne (b_nonneg _ _) (Ne.symm hp)
    have hd := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hσr : T.σ * r ≤ r := by nlinarith [T.σ_le]
    have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    linarith
  have hapos : 225 / 16 * mass μ (ball x (γ * r)) ≤
      ∑ p, μ p * (256 * (1 + g s) * a T (dist s p / r)) := by
    calc _ ≤ ∑ p ∈ ball x (γ * r), μ p * (256 * (1 + g s) * a T (dist s p / r)) := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p hp
           have h := ha p hp
           have had := mul_nonneg (hg s).1 (a_nonneg T (dist s p / r))
           have hh : 225 / 16 ≤ 256 * (1 + g s) * a T (dist s p / r) := by nlinarith
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ =>
           mul_nonneg (hμ p) (mul_nonneg (by linarith [(hg s).1]) (a_nonneg _ _))
  have hbneg : (∑ p, μ p * ((1 + g p) * b T (dist s p / r))) ≤
      2 * mass μ (ball x (100 * T.R * r)) := by
    calc _ = ∑ p ∈ ball x (100 * T.R * r), μ p * ((1 + g p) * b T (dist s p / r)) := by
           apply (sum_subset (subset_univ _) ?_).symm
           intro p _ hnot
           have hz : b T (dist s p / r) = 0 := by by_contra hn; exact hnot (hb p hn)
           simp [hz]
         _ ≤ _ := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p _
           have hg0 := (hg p).1
           have hg1 := (hg p).2
           have hb0 := b_nonneg T (dist s p / r)
           have hb1 := b_le_one T (dist s p / r)
           have hh : (1 + g p) * b T (dist s p / r) ≤ 2 := by
             nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hb1)]
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
  unfold coefficient
  simp only [mul_sub, sum_sub_distrib]
  have htwo := mul_le_mul_of_nonneg_left hconc (show (0 : ℝ) ≤ 2 by norm_num)
  have hdel := mul_le_mul_of_nonneg_right hδ hM.le
  nlinarith

lemma no_middle_site {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x s : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hslo : T.σ * r / 4 ≤ dist s x) (hshi : dist s x ≤ T.R * r / 2)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r)) ≤ (1 + δ) * mass μ (ball x (γ * r))) : z s = 0 :=
  minimizer_zero_of_coefficient_pos hr hz hmin
    (coefficient_middle_pos hr hγ hδ hμ hg hslo hshi hM hconc)

/-- The clear-and-insert competitor; the clearing radius is 5D*. -/
def insertUnit (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) : Y → ℝ :=
  fun s => if s = x then 1 else if dist x s < 50 * T.R * r then 0 else z s

omit [Fintype Y] in
lemma insertUnit_self (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) :
    insertUnit T r z x x = 1 := by simp [insertUnit]

lemma insertUnit_le {T : Template} {r : ℝ} {z : Y → ℝ} {x s : Y}
    (hz : Feasible T r z) (hs : s ≠ x) : insertUnit T r z x s ≤ z s := by
  simp only [insertUnit, ite_eq_right hs]
  split_ifs <;> simp [hz.1]

lemma G_lt_one {T : Template} {v : ℝ} (hv : G T v < 1) : v < 20 * T.R := by
  by_contra h
  rw [G_eq_one (le_of_not_gt h)] at hv
  exact lt_irrefl _ hv

lemma insertUnit_feasible {T : Template} {r : ℝ} {z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z) (x : Y) : Feasible T r (insertUnit T r z x) := by
  have hnon : ∀ s, 0 ≤ insertUnit T r z x s := by
    intro s
    unfold insertUnit
    split_ifs <;> simp [hz.1]
  refine ⟨hnon, fun p => ?_, fun s t hst hd => ?_⟩
  · by_cases hp : 0 < 1 - G T (dist x p / r)
    · have hxp : dist x p < 20 * T.R * r :=
        (div_lt_iff₀ hr).mp (G_lt_one (by linarith))
      have he : ∀ s ≠ x, max (insertUnit T r z x s - G T (dist s p / r)) 0 = 0 := by
        intro s hs
        by_cases hclear : dist x s < 50 * T.R * r
        · simp only [insertUnit, ite_eq_right hs, ite_eq_left hclear]
          exact max_eq_right (by linarith [G_nonneg T (dist s p / r)])
        · have hsp : 20 * T.R ≤ dist s p / r := by
            apply (le_div_iff₀ hr).mpr
            have ht := dist_triangle x p s
            rw [dist_comm p s] at ht
            have hRr : 0 < T.R * r := mul_pos (by linarith [T.R_ge]) hr
            linarith
          rw [G_eq_one hsp]
          exact max_eq_right (by linarith [insertUnit_le hz hs, coordinate_le_one hz s])
      rw [sum_eq_single x]
      · rw [insertUnit_self]
        exact max_le (by linarith [G_nonneg T (dist x p / r)]) (by norm_num)
      · intro s _ hs; exact he s hs
      · simp
    · apply le_trans (sum_le_sum fun s _ => ?_) (hz.2.1 p)
      by_cases hs : s = x
      · subst s
        rw [insertUnit_self, max_eq_right (le_of_not_gt hp)]
        exact le_max_right _ _
      · exact max_le_max (sub_le_sub_right (insertUnit_le hz hs) _) le_rfl
  · by_cases hs : s = x
    · subst s
      have ht : dist x t < 50 * T.R * r := by
        have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
        have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
        linarith
      simp [insertUnit, Ne.symm hst, ht]
    · by_cases ht : t = x
      · subst t
        have hs' : dist x s < 50 * T.R * r := by
          have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
          have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
          rw [dist_comm s x] at hd
          linarith
        simp [insertUnit, hs, hs']
      · have hm := mul_le_mul (insertUnit_le hz hs) (insertUnit_le hz ht) (hnon t) (hz.1 s)
        rw [hz.2.2 s t hst hd] at hm
        exact le_antisymm hm (mul_nonneg (hnon s) (hnon t))

/-- No changed bump reaches the complement of the outer ball. -/
lemma insertUnit_integrand_outside {T : Template} {r : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hp : 100 * T.R * r ≤ dist x p) :
    integrand T r g (insertUnit T r z x) p = integrand T r g z p := by
  have hab : ∀ s, insertUnit T r z x s ≠ z s →
      a T (dist s p / r) = 0 ∧ b T (dist s p / r) = 0 := by
    intro s hs
    have hxs : dist x s ≤ 50 * T.R * r := by
      by_cases he : s = x
      · subst s; simp; nlinarith [T.R_ge]
      · by_contra hn
        have hnc : ¬ dist x s < 50 * T.R * r := not_lt.mpr (le_of_not_ge hn)
        exact hs (by simp [insertUnit, he, hnc])
    have ht := dist_triangle x s p
    have hd : 2 * T.R ≤ dist s p / r := by
      apply (le_div_iff₀ hr).mpr
      have hRr : 0 ≤ T.R * r := mul_nonneg (by linarith [T.R_ge]) hr.le
      linarith
    exact ⟨a_eq_zero hd, b_eq_zero (by linarith [T.σ_le, T.R_ge])⟩
  unfold integrand
  congr 2
  · congr 1
    apply sum_congr rfl
    intro s _
    by_cases hs : insertUnit T r z x s = z s
    · rw [hs]
    · simp [(hab s hs).2]
  · apply sum_congr rfl
    intro s _
    by_cases hs : insertUnit T r z x s = z s
    · rw [hs]
    · simp [(hab s hs).1]

/-- Dimension-free repair inequality used in relocating a pilot site. -/
lemma sum_min_ge_min_sum {I : Type*} [Fintype I] {q : ℝ} {β : I → ℝ}
    (hq : 0 ≤ q) (hβ : ∀ i, 0 ≤ β i) :
    min q (∑ i, β i) ≤ ∑ i, min q (β i) := by
  by_cases h : ∃ i, q ≤ β i
  · obtain ⟨i, hi⟩ := h
    calc _ ≤ q := min_le_left _ _
         _ = min q (β i) := (min_eq_left hi).symm
         _ ≤ _ := single_le_sum (fun j _ => le_min hq (hβ j)) (mem_univ i)
  · push Not at h
    simp only [min_eq_right (le_of_lt (h _))]
    exact min_le_right _ _

lemma capacity_repair {I : Type*} [Fintype I] {q A A' : ℝ} {β : I → ℝ}
    (hq : 0 ≤ q) (hβ : ∀ i, 0 ≤ β i)
    (hcap : A + ∑ i, β i ≤ 1) (hA' : A' ≤ 1) (hchange : A' - A ≤ q) :
    A' + ∑ i, max (β i - q) 0 ≤ 1 := by
  have he : (∑ i, max (β i - q) 0) = (∑ i, β i) - ∑ i, min q (β i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases h : q ≤ β i
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right (le_of_not_ge h)]
      ring
  rw [he]
  have h := sum_min_ge_min_sum hq hβ
  by_cases hB : q ≤ ∑ i, β i
  · rw [min_eq_left hB] at h
    linarith
  · rw [min_eq_right (le_of_not_ge hB)] at h
    linarith

def nearWeight (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) : ℝ :=
  ∑ s ∈ nearBall x (T.σ * r / 4), z s

def innerMoment (μ : Y → ℝ) (x : Y) (γ r : ℝ) : ℝ :=
  ∑ p ∈ ball x (γ * r), μ p * (dist x p / r)

lemma innerMoment_le {μ : Y → ℝ} {x : Y} {γ r : ℝ}
    (hr : 0 < r) (hμ : ∀ p, 0 ≤ μ p) :
    innerMoment μ x γ r ≤ γ * mass μ (ball x (γ * r)) := by
  unfold innerMoment mass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hd : dist x p / r ≤ γ := (div_le_iff₀ hr).mpr (mem_filter.mp hp).2
  nlinarith [mul_le_mul_of_nonneg_left hd (hμ p)]

lemma nearWeight_eq_b_sum {T : Template} {r γ : ℝ} {z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hp : p ∈ ball x (γ * r)) : ∑ s, z s * b T (dist s p / r) = nearWeight T r z x := by
  have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
  have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  have hσr0 : 0 < T.σ * r := mul_pos T.σ_pos hr
  have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
  unfold nearWeight nearBall
  rw [sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases hs : dist x s < T.σ * r / 4
  · simp only [hs, ite_true]
    have hb : b T (dist s p / r) = 1 := by
      apply b_eq_one
      apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      rw [dist_comm s x] at ht
      linarith
    simp [hb]
  · simp only [hs, ite_false]
    by_cases hm : dist s x ≤ T.R * r / 2
    · rw [hmiddle s (by simpa only [dist_comm s x] using le_of_not_gt hs) hm, zero_mul]
    · have hb : b T (dist s p / r) = 0 := by
        apply b_eq_zero
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle s p x
        rw [dist_comm p x] at ht
        linarith
      simp [hb]

lemma old_integrand_inner_lower {T : Template} {r γ : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hz : Feasible T r z)
    (hg : ∀ s, g s ∈ Set.Icc 0 1)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hp : p ∈ ball x (γ * r)) : 1 - nearWeight T r z x ≤ integrand T r g z p := by
  have hb := nearWeight_eq_b_sum hr hγ hmiddle hp
  have hZ : nearWeight T r z x ≤ 1 := by rw [← hb]; exact sum_b_le_one hz p
  have ha : 0 ≤ ∑ s, z s * (1 + g s) * a T (dist s p / r) :=
    sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (a_nonneg _ _)
  unfold integrand
  rw [hb]
  nlinarith [mul_nonneg (hg p).1 (sub_nonneg.mpr hZ)]

lemma insertUnit_integrand_inner {T : Template} {r γ : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hg : ∀ s, g s ∈ Set.Icc 0 1)
    (hp : p ∈ ball x (γ * r)) :
    integrand T r g (insertUnit T r z x) p ≤ 512 * γ / T.σ ^ 2 * (dist x p / r) := by
  have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
  have hv0 : 0 ≤ dist x p / r := div_nonneg dist_nonneg hr.le
  have hvγ : dist x p / r ≤ γ := (div_le_iff₀ hr).mpr hp'
  have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
  have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hb : b T (dist x p / r) = 1 := b_eq_one (by linarith [T.σ_pos])
  have hz : ∀ s ≠ x, insertUnit T r z x s * b T (dist s p / r) = 0 ∧
      insertUnit T r z x s * (1 + g s) * a T (dist s p / r) = 0 := by
    intro s hs
    by_cases hc : dist x s < 50 * T.R * r
    · simp [insertUnit, hs, hc]
    · have hd : 2 * T.R ≤ dist s p / r := by
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle x p s
        rw [dist_comm p s] at ht
        linarith
      simp [a_eq_zero hd, b_eq_zero (show 2 * T.σ ≤ dist s p / r by linarith [T.σ_le, T.R_ge])]
  have hbsum : (∑ s, insertUnit T r z x s * b T (dist s p / r)) = 1 := by
    rw [sum_eq_single x]
    · simp [insertUnit_self, hb]
    · intro s _ hs; exact (hz s hs).1
    · simp
  have hasum : (∑ s, insertUnit T r z x s * (1 + g s) * a T (dist s p / r)) =
      (1 + g x) * a T (dist x p / r) := by
    rw [sum_eq_single x]
    · simp [insertUnit_self]
    · intro s _ hs; exact (hz s hs).2
    · simp
  rw [integrand, hbsum, hasum]
  simp only [sub_self, mul_zero, zero_add]
  have ha : a T (dist x p / r) ≤ (dist x p / r) ^ 2 / T.σ ^ 2 := by
    rw [a, ite_eq_left (show dist x p / r ≤ T.R by linarith [T.R_ge, T.σ_le])]
    exact min_le_left _ _
  have hmul : 256 * ((1 + g x) * a T (dist x p / r)) ≤
      512 * ((dist x p / r) ^ 2 / T.σ ^ 2) := by
    have hg1 := (hg x).2
    have ha0 := a_nonneg T (dist x p / r)
    nlinarith [mul_nonneg (sub_nonneg.mpr hg1) ha0]
  apply hmul.trans
  have hprod : (dist x p / r) ^ 2 ≤ γ * (dist x p / r) := by nlinarith
  have hdpos : 0 < T.σ ^ 2 := sq_pos_of_pos T.σ_pos
  have := div_le_div_of_nonneg_right hprod hdpos.le
  calc _ ≤ 512 * (γ * (dist x p / r) / T.σ ^ 2) := mul_le_mul_of_nonneg_left this (by norm_num)
       _ = _ := by ring

lemma nearWeight_deficit {T : Template} {r γ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hμ : ∀ p, 0 ≤ μ p)
    (hg : ∀ p, g p ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0) :
    (1 - nearWeight T r z x) * mass μ (ball x (γ * r)) ≤
      512 * γ / T.σ ^ 2 * innerMoment μ x γ r +
      514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) := by
  let w := insertUnit T r z x
  have hw := insertUnit_feasible hr hz x
  have hmin' := hmin hw
  change r * (∑ p, μ p * integrand T r g z p) ≤ r * (∑ p, μ p * integrand T r g w p) at hmin'
  have hcost : 0 ≤ ∑ p, μ p * (integrand T r g w p - integrand T r g z p) := by
    simp only [mul_sub, sum_sub_distrib]
    exact sub_nonneg.mpr ((mul_le_mul_iff_right₀ hr).mp hmin')
  have innerOuter : ball x (γ * r) ⊆ ball x (100 * T.R * r) := by
    intro p hp
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hp' := (mem_filter.mp hp).2
    have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
    have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    linarith
  have hpoint : ∀ p, μ p * (integrand T r g w p - integrand T r g z p) ≤
      (if p ∈ ball x (γ * r) then μ p * (512 * γ / T.σ ^ 2 * (dist x p / r) -
        (1 - nearWeight T r z x)) else 0) +
      (if p ∈ ball x (100 * T.R * r) \ ball x (γ * r) then 514 * μ p else 0) := by
    intro p
    by_cases hp : p ∈ ball x (γ * r)
    · have hout : p ∉ ball x (100 * T.R * r) \ ball x (γ * r) := by simp [hp]
      rw [ite_eq_left hp, ite_eq_right hout, add_zero]
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      have hnew := insertUnit_integrand_inner hr hγ hg hp (z := z)
      have hold := old_integrand_inner_lower hr hγ hz hg hmiddle hp
      dsimp [w]
      linarith
    · rw [ite_eq_right hp, zero_add]
      by_cases hout : p ∈ ball x (100 * T.R * r)
      · rw [ite_eq_left (mem_sdiff.mpr ⟨hout, hp⟩)]
        have hnew := (integrand_bounds hw hg p).2
        have hold := (integrand_bounds hz hg p).1
        nlinarith [mul_le_mul_of_nonneg_left (show integrand T r g w p - integrand T r g z p ≤ 514 by linarith) (hμ p)]
      · rw [ite_eq_right (by simp [hout])]
        have he := insertUnit_integrand_outside (g := g) (z := z) hr
          (show 100 * T.R * r ≤ dist x p from le_of_lt (by simpa [ball] using hout))
        dsimp [w]
        rw [he, sub_self, mul_zero]
  have hsum := sum_le_sum fun p (_ : p ∈ (Finset.univ : Finset Y)) => hpoint p
  rw [sum_add_distrib] at hsum
  simp only [← sum_filter] at hsum
  have he1 : (∑ p ∈ univ.filter (fun p => p ∈ ball x (γ * r)),
      μ p * (512 * γ / T.σ ^ 2 * (dist x p / r) - (1 - nearWeight T r z x))) =
      512 * γ / T.σ ^ 2 * innerMoment μ x γ r -
        (1 - nearWeight T r z x) * mass μ (ball x (γ * r)) := by
    simp only [filter_mem_eq_inter, Finset.univ_inter, innerMoment, mass]
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  have he2 : (∑ p ∈ univ.filter (fun p => p ∈ ball x (100 * T.R * r) \ ball x (γ * r)), 514 * μ p) =
      514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) := by
    simp only [filter_mem_eq_inter, Finset.univ_inter, mass, mul_sum]
  rw [he1, he2] at hsum
  linarith

lemma nearWeight_large {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) ≤
      δ * mass μ (ball x (γ * r))) : 3 / 4 ≤ nearWeight T r z x := by
  have hdef := nearWeight_deficit hr hγ hμ hg hz hmin hmiddle (x := x)
  have hmoment := innerMoment_le hr hμ (x := x) (γ := γ)
  have hc0 : 0 ≤ 512 * γ / T.σ ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
  have hσ2 : 0 < T.σ ^ 2 := sq_pos_of_pos T.σ_pos
  have hc : (512 * γ / T.σ ^ 2) * γ ≤ 1 / 8 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hσ2).mpr
    have hprod := mul_le_mul hγ hγ hγ0 (show 0 ≤ T.σ / 64 by linarith [T.σ_pos])
    nlinarith
  have hterm : 512 * γ / T.σ ^ 2 * innerMoment μ x γ r ≤
      (1 / 8) * mass μ (ball x (γ * r)) := by
    calc _ ≤ (512 * γ / T.σ ^ 2) * (γ * mass μ (ball x (γ * r))) :=
           mul_le_mul_of_nonneg_left hmoment hc0
         _ = ((512 * γ / T.σ ^ 2) * γ) * mass μ (ball x (γ * r)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hc hM.le
  have hshell : 514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) ≤
      (1 / 8) * mass μ (ball x (γ * r)) := by
    have := mul_le_mul_of_nonneg_right hδ hM.le
    linarith
  nlinarith

lemma near_sites_unique {T : Template} {r : ℝ} {z : Y → ℝ} {x s t : Y}
    (hr : 0 < r) (hz : Feasible T r z)
    (hs : s ∈ nearBall x (T.σ * r / 4)) (ht : t ∈ nearBall x (T.σ * r / 4))
    (hspos : 0 < z s) (htpos : 0 < z t) : s = t := by
  by_contra hne
  have hs' := (mem_filter.mp hs).2
  have ht' := (mem_filter.mp ht).2
  have hd : dist s t < 5 * T.σ * r := by
    have htri := dist_triangle s x t
    rw [dist_comm s x] at htri
    nlinarith [mul_pos T.σ_pos hr]
  have he := hz.2.2 s t hne hd
  have := mul_pos hspos htpos
  linarith

lemma near_site_of_large {T : Template} {r : ℝ} {z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hlarge : 3 / 4 ≤ nearWeight T r z x) :
    ∃ s, s ∈ nearBall x (T.σ * r / 4) ∧ 3 / 4 ≤ z s ∧
      nearWeight T r z x = z s ∧
      ∀ t, t ∈ nearBall x (T.σ * r / 4) → 0 < z t → t = s := by
  have hpos : ∃ s ∈ nearBall x (T.σ * r / 4), 0 < z s := by
    apply exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (g := z)
    simpa only [sum_const_zero, nearWeight] using (show 0 < nearWeight T r z x by linarith)
  obtain ⟨s, hs, hspos⟩ := hpos
  have hun : ∀ t, t ∈ nearBall x (T.σ * r / 4) → 0 < z t → t = s :=
    fun t ht htpos => near_sites_unique hr hz ht hs htpos hspos
  have he : nearWeight T r z x = z s := by
    unfold nearWeight
    apply sum_eq_single s
    · intro t ht hne
      have hnot : ¬ 0 < z t := fun htpos => hne (hun t ht htpos)
      exact le_antisymm (le_of_not_gt hnot) (hz.1 t)
    · exact fun h => (h hs).elim
  exact ⟨s, hs, by rwa [← he], he, hun⟩

/-- Unit-site pilot-local conclusions and the shell-ratio estimate. -/

lemma near_site {T : Template} {r γ δ : ℝ} {μ g : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) ≤
      δ * mass μ (ball x (γ * r))) :
    ∃ s, dist s x < T.σ * r / 4 ∧ 3 / 4 ≤ minimizer T r μ g s ∧
      (1 - minimizer T r μ g s) * mass μ (ball x (γ * r)) ≤
        512 * γ / T.σ ^ 2 * innerMoment μ x γ r +
        514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) := by
  have hsubset : ball x (γ * r) ⊆ ball x (100 * T.R * r) := by
    intro p hp
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hp' := (mem_filter.mp hp).2
    have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
    have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
    linarith
  have hmass : mass μ (ball x (100 * T.R * r)) ≤ (1 + δ) * mass μ (ball x (γ * r)) := by
    have he := sum_sdiff (f := μ) hsubset
    change mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) +
      mass μ (ball x (γ * r)) = mass μ (ball x (100 * T.R * r)) at he
    nlinarith
  have hz := (minimizer_spec T r μ g).1
  have hmin := (minimizer_spec T r μ g).2
  have hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 →
      minimizer T r μ g s = 0 := by
    intro s hsl hsh
    exact no_middle_site hr hγ hδ hμ hg hz hmin hsl hsh hM hmass
  have hlarge := nearWeight_large hr hγ0 hγ hδ hμ hg hz hmin hmiddle hM hconc
  obtain ⟨s, hs, hsz, he, _⟩ := near_site_of_large hr hz hlarge
  refine ⟨s, ?_, hsz, ?_⟩
  · simpa only [dist_comm s x] using (mem_filter.mp hs).2
  · rw [← he]
    exact nearWeight_deficit hr hγ hμ hg hz hmin hmiddle

/-! Relocation at a concentrated request and local optimality,
including the dimension-free capacity repair competitor. -/
lemma clamp_abs {u v : ℝ} :
    |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
  calc _ ≤ max |(0 : ℝ) - 0| |min 1 u - min 1 v| := abs_max_sub_max_le_max _ _ _ _
       _ = |min 1 u - min 1 v| := by simp
       _ ≤ max |(1 : ℝ) - 1| |u - v| := abs_min_sub_min_le_max _ _ _ _
       _ = _ := by simp

lemma b_lipschitz (T : Template) (u v : ℝ) :
    |b T u - b T v| ≤ |u - v| / T.σ := by
  have h := clamp_abs (u := 2 - u / T.σ) (v := 2 - v / T.σ)
  have he : (2 - u / T.σ) - (2 - v / T.σ) = -(u - v) / T.σ := by ring
  simpa only [b, he, abs_div, abs_neg, abs_of_pos T.σ_pos] using h

lemma G_lipschitz (T : Template) (u v : ℝ) :
    |G T u - G T v| ≤ |u - v| / (10 * T.R) := by
  have h := clamp_abs (u := u / (10 * T.R) - 1) (v := v / (10 * T.R) - 1)
  have he : (u / (10 * T.R) - 1) - (v / (10 * T.R) - 1) = (u - v) / (10 * T.R) := by ring
  simpa only [G, he, abs_div, abs_of_pos (show 0 < 10 * T.R by linarith [T.R_ge])] using h

lemma a_min_rep {T : Template} {v : ℝ} (hv : 0 ≤ v) :
    a T v = min ((min 1 (v / T.σ)) ^ 2) (max 0 (2 - v / T.R)) := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hσR : T.σ ≤ T.R := by linarith [T.σ_le, T.R_ge]
  have hvσ : 0 ≤ v / T.σ := div_nonneg hv T.σ_pos.le
  by_cases hvR : v ≤ T.R
  · have htail : 1 ≤ max 0 (2 - v / T.R) := le_trans (by
      have := (div_le_one hR).mpr hvR; linarith) (le_max_right _ _)
    have hc : (min 1 (v / T.σ)) ^ 2 ≤ 1 := by
      have hlo : 0 ≤ min 1 (v / T.σ) := le_min zero_le_one hvσ
      have hhi : min 1 (v / T.σ) ≤ 1 := min_le_left _ _
      nlinarith
    rw [min_eq_left (le_trans hc htail), a, ite_eq_left hvR]
    by_cases h : v / T.σ ≤ 1
    · have hs : v ^ 2 / T.σ ^ 2 ≤ 1 := by
        rw [← div_pow]; nlinarith
      rw [min_eq_left hs, min_eq_right h, div_pow]
    · have hs : 1 ≤ v ^ 2 / T.σ ^ 2 := by
        rw [← div_pow]; nlinarith
      simp [min_eq_right hs, min_eq_left (le_of_not_ge h)]
  · have hvσ1 : 1 ≤ v / T.σ := (le_div_iff₀ T.σ_pos).mpr (by linarith)
    rw [min_eq_left hvσ1, one_pow]
    have htail : max 0 (2 - v / T.R) ≤ 1 := by
      apply max_le zero_le_one
      have := (one_lt_div hR).mpr (lt_of_not_ge hvR)
      linarith
    rw [min_eq_right htail, a, ite_eq_right hvR]
    by_cases h : v ≤ 2 * T.R
    · rw [ite_eq_left h, max_eq_right]
      have := (div_le_iff₀ hR).mpr h
      linarith
    · rw [ite_eq_right h, max_eq_left]
      have : 2 ≤ v / T.R := (le_div_iff₀ hR).mpr (le_of_not_ge h)
      linarith

lemma a_lipschitz {T : Template} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |a T u - a T v| ≤ 2 / T.σ * |u - v| := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hu' : 0 ≤ min 1 (u / T.σ) := le_min zero_le_one (div_nonneg hu T.σ_pos.le)
  have hv' : 0 ≤ min 1 (v / T.σ) := le_min zero_le_one (div_nonneg hv T.σ_pos.le)
  have hs : |min 1 (u / T.σ) + min 1 (v / T.σ)| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg hu' hv')]
    linarith [min_le_left (1 : ℝ) (u / T.σ), min_le_left (1 : ℝ) (v / T.σ)]
  have hd : |min 1 (u / T.σ) - min 1 (v / T.σ)| ≤ |u-v| / T.σ := by
    have := abs_min_sub_min_le_max (1 : ℝ) (u/T.σ) 1 (v/T.σ)
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (u / T.σ - v / T.σ))] at this
    simpa only [← sub_div, abs_div, abs_of_pos T.σ_pos] using this
  have hsq : |(min 1 (u / T.σ)) ^ 2 - (min 1 (v / T.σ)) ^ 2| ≤
      2 / T.σ * |u-v| := by
    have he : (min 1 (u / T.σ)) ^ 2 - (min 1 (v / T.σ)) ^ 2 =
        (min 1 (u / T.σ) - min 1 (v / T.σ)) *
        (min 1 (u / T.σ) + min 1 (v / T.σ)) := by ring
    rw [he, abs_mul]
    calc _ ≤ (|u-v| / T.σ) * 2 :=
           mul_le_mul hd hs (abs_nonneg _) (div_nonneg (abs_nonneg _) T.σ_pos.le)
         _ = _ := by ring
  have ht : |max 0 (2 - u / T.R) - max 0 (2 - v / T.R)| ≤ 2 / T.σ * |u-v| := by
    have hm := abs_max_sub_max_le_max (0 : ℝ) (2-u/T.R) 0 (2-v/T.R)
    have he : (2-u/T.R)-(2-v/T.R) = -(u-v)/T.R := by ring
    simp only [sub_self, abs_zero, he,
      abs_div, abs_neg, abs_of_pos hR] at hm
    rw [max_eq_right (div_nonneg (abs_nonneg _) hR.le)] at hm
    calc _ ≤ |u-v| / T.R := hm
         _ ≤ 2 / T.σ * |u-v| := by
           have hc : 1 / T.R ≤ 2 / T.σ := (div_le_div_iff₀ hR T.σ_pos).mpr (by
             linarith [T.σ_le, T.R_ge])
           have := mul_le_mul_of_nonneg_right hc (abs_nonneg (u-v))
           simpa only [one_div_mul_eq_div] using this
  rw [a_min_rep hu, a_min_rep hv]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hsq ht)

omit [Fintype Y] in
lemma scaled_dist_lipschitz {r : ℝ} (hr : 0 < r) (s x p : Y) :
    |dist s p / r - dist x p / r| ≤ dist s x / r := by
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le

omit [MetricSpace Y] in
lemma finite_sum_split (f : Y → ℝ) (s : Y) :
    (∑ i, f i) = f s + ∑ i, if i = s then 0 else f i := by
  calc _ = ∑ i, ((if i = s then f s else 0) + (if i = s then 0 else f i)) := by
         apply sum_congr rfl; intro i _; by_cases h : i = s <;> simp [h]
       _ = _ := by rw [sum_add_distrib]; simp

lemma clip_reduction {z G q : ℝ} (hG : 0 ≤ G) (hq : 0 ≤ q) :
    max (max (z-q) 0 - G) 0 = max (max (z-G) 0 - q) 0 := by
  by_cases hzq : z ≤ q
  · have h1 : max (z-q) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (z-G) 0 ≤ q := max_le (by linarith) hq
    rw [h1, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith : 0 ≤ z-q)]
    by_cases hzG : z ≤ G
    · rw [max_eq_right (by linarith : z-G ≤ 0), max_eq_right (by linarith),
        max_eq_right (by linarith)]
    · rw [max_eq_left (by linarith : 0 ≤ z-G)]
      congr 1; ring

def relocate (T : Template) (r : ℝ) (z : Y → ℝ) (s x : Y) : Y → ℝ := fun i =>
  if i = x then z s else if i = s then 0 else
    if dist x i < 50 * T.R * r then max (z i - (dist s x / r) / (10*T.R)) 0 else z i

omit [Fintype Y] in
lemma relocate_at {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y} (hne : s ≠ x) :
    relocate T r z s x x = z s ∧ relocate T r z s x s = 0 := by
  simp [relocate, hne]

lemma relocate_le {T : Template} {r : ℝ} {z : Y → ℝ} {s x i : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hi : i ≠ x) :
    0 ≤ relocate T r z s x i ∧ relocate T r z s x i ≤ z i := by
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  unfold relocate
  rw [ite_eq_right hi]
  split_ifs <;> first | exact ⟨hz.1 i, le_rfl⟩ | exact ⟨le_rfl, hz.1 i⟩ |
    exact ⟨le_max_right _ _, max_le (by linarith) (hz.1 i)⟩

lemma near_site_others_vanish {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hs : dist s x < T.σ*r/4)
    (hspos : 0 < z s)
    (hmiddle : ∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i = 0) :
    ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0 := by
  intro i hi hix
  by_cases hl : T.σ*r/4 ≤ dist i x
  · exact hmiddle i hl hix
  · by_contra hzi
    have hipos : 0 < z i := lt_of_le_of_ne (hz.1 i) (Ne.symm hzi)
    have his : i = s := near_sites_unique (x := x) (s := i) (t := s) hr hz
      (by apply mem_filter.mpr; exact ⟨mem_univ _, by simpa [dist_comm] using lt_of_not_ge hl⟩)
      (by apply mem_filter.mpr; exact ⟨mem_univ _, by simpa [dist_comm] using hs⟩)
      hipos hspos
    exact hi his

lemma relocate_feasible {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    Feasible T r (relocate T r z s x) := by
  have hRr : 0 < T.R*r := mul_pos (by linarith [T.R_ge]) hr
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; positivity)
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  have hn : ∀ i, 0 ≤ relocate T r z s x i := by
    intro i; by_cases hi : i=x
    · subst i; exact (relocate_at hne).1 ▸ hz.1 s
    · exact (relocate_le hr hz hi).1
  refine ⟨hn, ?_, ?_⟩
  · intro p
    let A := max (z s - G T (dist s p/r)) 0
    let A' := max (z s - G T (dist x p/r)) 0
    let β : Y → ℝ := fun i => if i=s then 0 else max (z i-G T (dist i p/r)) 0
    let β' : Y → ℝ := fun i => if i=x then 0 else max (relocate T r z s x i-G T (dist i p/r)) 0
    have hcap : A + ∑ i, β i ≤ 1 := by
      have hc := hz.2.1 p
      rw [finite_sum_split _ s] at hc
      exact hc
    have he : (∑ i, max (relocate T r z s x i - G T (dist i p/r)) 0) = A' + ∑ i, β' i := by
      rw [finite_sum_split _ x, (relocate_at hne).1]
    rw [he]
    have hβ : ∀ i, 0 ≤ β i := by intro i; exact ite_nonneg le_rfl (le_max_right _ _)
    have hb' : ∀ i, β' i ≤ β i := by
      intro i
      by_cases hix : i=x
      · subst i; exact le_trans (by simp [β']) (hβ x)
      · by_cases his : i=s
        · subst i; simp only [β', ite_eq_right hix, β, ite_eq_left rfl, (relocate_at hne).2]
          exact max_le (by linarith [G_nonneg T (dist s p/r)]) le_rfl
        · simp only [β', ite_eq_right hix, β, ite_eq_right his]
          exact max_le_max (sub_le_sub_right (relocate_le hr hz hix).2 _) le_rfl
    by_cases hAA : A' ≤ A
    · exact (add_le_add hAA (sum_le_sum (fun i _ => hb' i))).trans hcap
    · have hAp : 0 < A' := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hAA)
      have hxp : dist x p < 20*T.R*r := by
        by_contra hh
        have hG : G T (dist x p/r) = 1 := G_eq_one ((le_div_iff₀ hr).mpr (le_of_not_gt hh))
        have hz1 := coordinate_le_one hz s
        have : A' = 0 := by dsimp [A']; rw [hG, max_eq_right (by linarith)]
        linarith
      have hchange : A'-A ≤ (dist s x/r)/(10*T.R) := by
        have h1 := abs_max_sub_max_le_abs (z s-G T (dist x p/r)) (z s-G T (dist s p/r)) 0
        have heq : (z s-G T (dist x p/r))-(z s-G T (dist s p/r)) =
            G T (dist s p/r)-G T (dist x p/r) := by ring
        rw [heq] at h1
        exact (le_abs_self _).trans (h1.trans ((G_lipschitz T _ _).trans
          (div_le_div_of_nonneg_right (scaled_dist_lipschitz hr s x p)
            (by linarith [T.R_ge]))))
      have hrepair : ∀ i, β' i ≤ max (β i - (dist s x/r)/(10*T.R)) 0 := by
        intro i
        by_cases hix : i=x
        · simp only [β', ite_eq_left hix]; exact le_max_right _ _
        · by_cases his : i=s
          · subst i
            have hzero : β' s = 0 := le_antisymm (by simpa [β] using hb' s)
              (by simp only [β', ite_eq_right hix]; exact le_max_right _ _)
            rw [hzero]; exact le_max_right _ _
          · by_cases hi : dist x i < 50*T.R*r
            · simp only [β', ite_eq_right hix, β, ite_eq_right his, relocate, ite_eq_left hi]
              rw [clip_reduction (G_nonneg T _) hq]
            · have hβzero : β i = 0 := by
                have hip : 20*T.R*r ≤ dist i p := by
                  have ht := dist_triangle x p i
                  rw [dist_comm p i] at ht
                  linarith
                have hG : G T (dist i p/r) = 1 := G_eq_one ((le_div_iff₀ hr).mpr hip)
                simp only [β, ite_eq_right his, hG]
                exact max_eq_right (by linarith [coordinate_le_one hz i])
              exact (hb' i).trans (by rw [hβzero]; exact le_max_right _ _)
      have hAone : A' ≤ 1 := max_le (by
        have := coordinate_le_one hz s
        linarith [G_nonneg T (dist x p/r)]) zero_le_one
      exact (add_le_add (le_refl A') (sum_le_sum (fun i _ => hrepair i))).trans
        (capacity_repair hq hβ hcap hAone hchange)
  · intro i j hij hd
    have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
    have hbig : 5*T.σ*r ≤ T.R*r/2 := by
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    by_cases hix : i=x
    · subst i
      by_cases hjs : j=s
      · subst j; rw [(relocate_at hne).2, mul_zero]
      · have hzj := hother j hjs (by rw [dist_comm j x]; linarith)
        have hjx : j ≠ x := Ne.symm hij
        have hjzero : relocate T r z s x j = 0 := le_antisymm
          (by simpa only [hzj] using (relocate_le hr hz hjx).2) (hn j)
        rw [hjzero, mul_zero]
    · by_cases hjx : j=x
      · subst j
        by_cases his : i=s
        · subst i; rw [(relocate_at hne).2, zero_mul]
        · have hzi := hother i his (by linarith)
          have hizero : relocate T r z s x i = 0 := le_antisymm
            (by simpa only [hzi] using (relocate_le hr hz hix).2) (hn i)
          rw [hizero, zero_mul]
      · have hmul := mul_le_mul (relocate_le (s := s) hr hz hix).2 (relocate_le (s := s) hr hz hjx).2 (hn j) (hz.1 i)
        rw [hz.2.2 i j hij hd] at hmul
        exact le_antisymm hmul (mul_nonneg (hn i) (hn j))

lemma b_sum_single {T : Template} {r γ : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hs : dist s x < T.σ*r/4)
    (hp : dist x p ≤ γ*r)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (∑ i, z i * b T (dist i p/r)) = z s := by
  have hsr : 0 < T.σ*r := mul_pos T.σ_pos hr
  have hγr : γ*r ≤ T.σ*r/64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; linarith)
  have hb_one : b T (dist s p/r) = 1 := b_eq_one hsp
  rw [← mul_one (z s), ← hb_one]
  apply sum_eq_single s
  · intro i _ his
    by_cases hi : dist i x ≤ T.R*r/2
    · rw [hother i his hi, zero_mul]
    · have hip : 2*T.σ ≤ dist i p/r := by
        apply (le_div_iff₀ hr).mpr
        have htri := dist_triangle i p x
        rw [dist_comm p x] at htri
        have hRr := mul_le_mul_of_nonneg_right T.R_ge hr.le
        have hσr := mul_le_of_le_one_left hr.le T.σ_le
        linarith
      rw [b_eq_zero hip, mul_zero]
  · simp

lemma sum_relocate_le {T : Template} {r : ℝ} {z f : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i, relocate T r z s x i * f i) ≤ (∑ i, z i*f i) - z s*f s + z s*f x := by
  calc _ ≤ ∑ i, (z i*f i - (if i=s then z s*f s else 0) + (if i=x then z s*f x else 0)) := by
         apply sum_le_sum
         intro i _
         by_cases hix : i=x
         · subst i; simp [Ne.symm hne, hzx, (relocate_at hne).1]
         · by_cases his : i=s
           · subst i; simp [hne, (relocate_at hne).2]
           · simp only [ite_eq_right his, ite_eq_right hix, sub_zero, add_zero]
             exact mul_le_mul_of_nonneg_right (relocate_le hr hz hix).2 (hf i)
       _ = _ := by rw [sum_add_distrib, sum_sub_distrib]; simp

lemma moved_square_gain {L γ w u v gs gx : ℝ}
    (hL : 0 ≤ L) (hγL : L*γ ≤ 1) (hw : 0 ≤ w) (_ : 0 ≤ u)
    (hv : 0 ≤ v) (hvγ : v ≤ γ) (hwu : w ≤ u+v) (hvu : v ≤ u+w)
    (hgs : gs ∈ Set.Icc 0 1) (hgg : |gs-gx| ≤ L*w) :
    w^2-5*w*v ≤ (1+gs)*u^2-(1+gx)*v^2 := by
  have hquad : w^2-2*w*v+v^2 ≤ u^2 := by
    have hp := mul_nonneg (show 0 ≤ u-w+v by linarith) (show 0 ≤ u+w-v by linarith)
    nlinarith
  have hq := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 1+gs by linarith [hgs.1])
  have hgg' : -(L*w) ≤ gs-gx := (abs_le.mp hgg).1
  have hgm := mul_le_mul_of_nonneg_right hgg' (sq_nonneg v)
  have hvL : L*v ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hvγ hL) hγL
  have herr := mul_le_mul_of_nonneg_right hvL (mul_nonneg hw hv)
  have hgsw := mul_nonneg hgs.1 (sq_nonneg w)
  have hgsv := mul_le_mul_of_nonneg_right hgs.2 (mul_nonneg hw hv)
  nlinarith

lemma a_eq_square {T : Template} {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ T.σ) :
    a T v = v^2/T.σ^2 := by
  have hvR : v ≤ T.R := le_trans hv (by linarith [T.σ_le, T.R_ge])
  rw [a, ite_eq_left hvR, min_eq_left]
  apply (div_le_one (sq_pos_of_pos T.σ_pos)).mpr
  nlinarith [T.σ_pos]

lemma relocate_inner_gain {T : Template} {r γ : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hne : s ≠ x) (hs : dist s x < T.σ*r/4)
    (hp : dist x p ≤ γ*r)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (256*z s/T.σ^2) * ((dist s x/r)^2-5*(dist s x/r)*(dist x p/r)) ≤
      integrand T r g z p - integrand T r g (relocate T r z s x) p := by
  have hγr : γ*r ≤ T.σ*r/64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hσr : 0 < T.σ*r := mul_pos T.σ_pos hr
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; linarith)
  have hxp : dist x p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by linarith)
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; nlinarith [T.R_ge])
  have hnewother : ∀ i, i ≠ x → dist i x ≤ T.R*r/2 → relocate T r z s x i = 0 := by
    intro i hix hi
    by_cases his : i=s
    · subst i; exact (relocate_at hne).2
    · exact le_antisymm (by simpa only [hother i his hi] using (relocate_le hr hz hix).2)
        (relocate_le hr hz hix).1
  have hb := b_sum_single hr hγ hs hp hother
  have hb' := b_sum_single hr hγ (s := x) (by simp; linarith) hp hnewother
  rw [(relocate_at hne).1] at hb'
  have hsum := sum_relocate_le hr hz hne hzX (f := fun i => (1+g i)*a T (dist i p/r))
    (fun i => mul_nonneg (by linarith [(hg i).1]) (a_nonneg _ _))
  have hquad := moved_square_gain T.L_nonneg hγL (div_nonneg dist_nonneg hr.le)
    (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)
    ((div_le_iff₀ hr).mpr hp)
    (show dist s x/r ≤ dist s p/r + dist x p/r by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hr.le
      have := dist_triangle s p x; simpa only [dist_comm p x] using this)
    (show dist x p/r ≤ dist s p/r + dist s x/r by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hr.le
      have := dist_triangle x s p; simpa only [dist_comm x s, add_comm] using this)
    (hg s) (hglip s x)
  have hquad' := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 256*z s/T.σ^2 by exact div_nonneg (mul_nonneg (by norm_num) (hz.1 s)) (sq_nonneg _))
  rw [a_eq_square (div_nonneg dist_nonneg hr.le) hsp,
    a_eq_square (div_nonneg dist_nonneg hr.le) hxp] at hsum
  unfold integrand
  rw [hb, hb']
  have heq : (256*z s/T.σ^2)*((1+g s)*(dist s p/r)^2-(1+g x)*(dist x p/r)^2) =
      256*(z s*(1+g s)*((dist s p/r)^2/T.σ^2)-z s*(1+g x)*((dist x p/r)^2/T.σ^2)) := by ring
  rw [heq] at hquad'
  simp only [mul_assoc] at hsum hquad' ⊢
  linarith only [hquad', hsum]

omit [MetricSpace Y] in
lemma sum_unique_le {f : Y → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hf : ∀ i, 0 ≤ f i) (hfq : ∀ i, f i ≤ q)
    (hun : ∀ i j, 0 < f i → 0 < f j → i=j) : (∑ i, f i) ≤ q := by
  by_cases h : ∃ i, 0 < f i
  · obtain ⟨i, hi⟩ := h
    have he : (∑ j, f j) = f i := by
      apply sum_eq_single i
      · intro j _ hji
        exact le_antisymm (le_of_not_gt (fun hj => hji (hun j i hj hi))) (hf j)
      · simp
    rw [he]; exact hfq i
  · push Not at h
    have : ∀ i, f i = 0 := fun i => le_antisymm (h i) (hf i)
    simpa only [this, sum_const_zero] using hq

omit [Fintype Y] in
lemma relocate_decrease_le {T : Template} {r : ℝ} {z : Y → ℝ} {s x i : Y}
    (hr : 0 < r) (hix : i ≠ x) (his : i ≠ s) :
    z i-relocate T r z s x i ≤ (dist s x/r)/(10*T.R) := by
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  unfold relocate
  rw [ite_eq_right hix, ite_eq_right his]
  split_ifs
  · linarith [le_max_left (z i-(dist s x/r)/(10*T.R)) 0]
  · simpa only [sub_self] using hq

lemma relocate_residual_loss {T : Template} {r : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0) :
    (∑ i, z i*b T (dist i p/r)) - (∑ i, relocate T r z s x i*b T (dist i p/r)) ≤
      z s*(dist s x/r)/T.σ + (dist s x/r)/(10*T.R) := by
  let f : Y → ℝ := fun i => if i=s ∨ i=x then 0 else
    (z i-relocate T r z s x i)*b T (dist i p/r)
  have hf : ∀ i, 0 ≤ f i := by
    intro i; dsimp [f]; split_ifs with hi
    · rfl
    · exact mul_nonneg (sub_nonneg.mpr (relocate_le hr hz (not_or.mp hi).2).2) (b_nonneg _ _)
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  have hbound : ∀ i, f i ≤ (dist s x/r)/(10*T.R) := by
    intro i; dsimp [f]; split_ifs with hi
    · exact hq
    · have hx := (not_or.mp hi).2
      have hs := (not_or.mp hi).1
      calc _ ≤ ((dist s x/r)/(10*T.R))*1 := mul_le_mul
             (relocate_decrease_le hr hx hs) (b_le_one _ _) (b_nonneg _ _) hq
           _ = _ := mul_one _
  have hsupport : ∀ i, 0 < f i → 0 < z i ∧ 0 < b T (dist i p/r) := by
    intro i hi
    dsimp [f] at hi
    split_ifs at hi with hix
    · exact (lt_irrefl _ hi).elim
    · have hdiff : 0 < z i-relocate T r z s x i :=
        pos_of_mul_pos_left hi (b_nonneg _ _)
      have hb : 0 < b T (dist i p/r) := pos_of_mul_pos_right hi hdiff.le
      exact ⟨by linarith [(relocate_le (s := s) hr hz (not_or.mp hix).2).1], hb⟩
  have hsum : (∑ i, f i) ≤ (dist s x/r)/(10*T.R) :=
    sum_unique_le hq hf hbound (fun i j hi hj => positive_b_support_disjoint hr hz
      (hsupport i hi).1 (hsupport j hj).1 (hsupport i hi).2 (hsupport j hj).2)
  have he : (∑ i, z i*b T (dist i p/r)) - (∑ i, relocate T r z s x i*b T (dist i p/r)) =
      z s*b T (dist s p/r) - z s*b T (dist x p/r) + ∑ i, f i := by
    rw [← sum_sub_distrib]
    have hpw : ∀ i, z i*b T (dist i p/r) - relocate T r z s x i*b T (dist i p/r) =
        (if i=s then z s*b T (dist s p/r) else 0) -
          (if i=x then z s*b T (dist x p/r) else 0) + f i := by
      intro i
      by_cases his : i=s
      · subst i; simp [f, hne, (relocate_at hne).2]
      · by_cases hix : i=x
        · subst i; simp [f, Ne.symm hne, hzx, (relocate_at hne).1]
        · simp only [f, his, hix, false_or, ite_false, sub_zero, zero_add]
          ring
    simp only [hpw, sum_add_distrib, sum_sub_distrib]
    simp
  have hb : b T (dist s p/r)-b T (dist x p/r) ≤ (dist s x/r)/T.σ :=
    (le_abs_self _).trans ((b_lipschitz T _ _).trans
      (div_le_div_of_nonneg_right (scaled_dist_lipschitz hr s x p) T.σ_pos.le))
  have hbm := mul_le_mul_of_nonneg_left hb (hz.1 s)
  rw [he]
  calc _ = z s*(b T (dist s p/r)-b T (dist x p/r)) + ∑ i, f i := by ring
       _ ≤ z s*((dist s x/r)/T.σ) + (dist s x/r)/(10*T.R) := add_le_add hbm hsum
       _ = _ := by ring

omit [Fintype Y] in
lemma moved_surcharge_loss {T : Template} {r : ℝ} {g : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) :
    (1+g x)*a T (dist x p/r)-(1+g s)*a T (dist s p/r) ≤
      (4/T.σ+T.L)*(dist s x/r) := by
  have ha : |a T (dist x p/r)-a T (dist s p/r)| ≤ (2/T.σ)*(dist s x/r) := by
    have h1 := a_lipschitz (T := T) (u := dist x p/r) (v := dist s p/r) (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)
    apply h1.trans
    have h2 := scaled_dist_lipschitz hr x s p
    rw [dist_comm x s] at h2
    exact mul_le_mul_of_nonneg_left h2 (div_nonneg (by norm_num) T.σ_pos.le)
  have hg' : g x-g s ≤ T.L*(dist s x/r) := by
    have := (le_abs_self (g x-g s)).trans (hglip x s)
    simpa only [dist_comm x s] using this
  have hleft := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist x p/r)-a T (dist s p/r)))
    (show 0 ≤ 1+g x by linarith [(hg x).1])
  have hm := mul_le_mul (show 1+g x ≤ 2 by linarith [(hg x).2]) ha (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ 2)
  have hright : (g x-g s)*a T (dist s p/r) ≤ T.L*(dist s x/r) := by
    calc _ ≤ (T.L*(dist s x/r))*1 := mul_le_mul hg' (a_le_one _ _) (a_nonneg _ _)
           (mul_nonneg T.L_nonneg (div_nonneg dist_nonneg hr.le))
         _ = _ := mul_one _
  calc _ = (1+g x)*(a T (dist x p/r)-a T (dist s p/r)) + (g x-g s)*a T (dist s p/r) := by ring
       _ ≤ 2*((2/T.σ)*(dist s x/r)) + T.L*(dist s x/r) := add_le_add (hleft.trans hm) hright
       _ = _ := by ring

lemma relocate_shell_loss {T : Template} {r : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0) :
    integrand T r g (relocate T r z s x) p - integrand T r g z p ≤
      (z s*(1026/T.σ+256*T.L)+2/(10*T.R))*(dist s x/r) := by
  have hb := relocate_residual_loss (p := p) hr hz hne hzx
  have hb0 : 0 ≤ z s*(dist s x/r)/T.σ + (dist s x/r)/(10*T.R) := by
    apply add_nonneg
    · exact div_nonneg (mul_nonneg (hz.1 s) (div_nonneg dist_nonneg hr.le)) T.σ_pos.le
    · exact div_nonneg (div_nonneg dist_nonneg hr.le) (by linarith [T.R_ge])
  have hres := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+g p by linarith [(hg p).1])
  have hres2 := mul_le_mul_of_nonneg_right (show 1+g p ≤ 2 by linarith [(hg p).2]) hb0
  have hsum := sum_relocate_le hr hz hne hzx (f := fun i => (1+g i)*a T (dist i p/r))
    (fun i => mul_nonneg (by linarith [(hg i).1]) (a_nonneg _ _))
  have hm := mul_le_mul_of_nonneg_left (moved_surcharge_loss (s := s) (x := x) (p := p) hr hg hglip) (hz.1 s)
  have hsumdiff : (∑ i, relocate T r z s x i * ((1+g i)*a T (dist i p/r))) -
      (∑ i, z i*((1+g i)*a T (dist i p/r))) ≤ z s*((4/T.σ+T.L)*(dist s x/r)) := by
    linarith only [hsum, hm]
  unfold integrand
  simp only [mul_assoc]
  calc _ = (1+g p)*((∑ i, z i*b T (dist i p/r))-(∑ i, relocate T r z s x i*b T (dist i p/r))) +
      256*((∑ i, relocate T r z s x i*((1+g i)*a T (dist i p/r)))-(∑ i, z i*((1+g i)*a T (dist i p/r)))) := by ring
       _ ≤ 2*(z s*(dist s x/r)/T.σ+(dist s x/r)/(10*T.R)) +
        256*(z s*((4/T.σ+T.L)*(dist s x/r))) :=
          add_le_add (hres.trans hres2) (mul_le_mul_of_nonneg_left hsumdiff (by norm_num))
       _ = _ := by ring

lemma relocate_integrand_outside {T : Template} {r : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hs : dist s x < T.σ*r/4) (hp : 100*T.R*r ≤ dist x p) :
    integrand T r g (relocate T r z s x) p = integrand T r g z p := by
  have hab : ∀ i, relocate T r z s x i ≠ z i →
      a T (dist i p/r) = 0 ∧ b T (dist i p/r) = 0 := by
    intro i hi
    have hxi : dist x i ≤ 50*T.R*r := by
      by_cases hix : i=x
      · subst i; simp only [dist_self]; nlinarith [T.R_ge]
      · by_cases his : i=s
        · subst i
          rw [dist_comm x s]
          have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
          have hRr := mul_le_mul_of_nonneg_right T.R_ge hr.le
          linarith
        · by_contra hh
          exact hi (by simp [relocate, hix, his, not_lt.mpr (le_of_not_ge hh)])
    have hd : 2*T.R ≤ dist i p/r := by
      apply (le_div_iff₀ hr).mpr
      have htri := dist_triangle x i p
      have hRr : 0 ≤ T.R*r := mul_nonneg (by linarith [T.R_ge]) hr.le
      linarith
    exact ⟨a_eq_zero hd, b_eq_zero (by linarith [T.σ_le, T.R_ge])⟩
  unfold integrand
  congr 2
  · congr 1; apply sum_congr rfl; intro i _
    by_cases hi : relocate T r z s x i = z i
    · rw [hi]
    · simp [(hab i hi).2]
  · apply sum_congr rfl; intro i _
    by_cases hi : relocate T r z s x i = z i
    · rw [hi]
    · simp [(hab i hi).1]

lemma relocation_coefficient_bound (T : Template) {z : ℝ} (hz : 3/4 ≤ z) :
    z*(1026/T.σ+256*T.L)+2/(10*T.R) ≤ (256*z/T.σ^2)*(5+T.L) := by
  have hz0 : 0 ≤ z := by linarith
  have hσ2 : 0 < T.σ^2 := sq_pos_of_pos T.σ_pos
  have hσ21 : T.σ^2 ≤ 1 := by nlinarith [T.σ_pos, T.σ_le]
  have hq : 2/(10*T.R) ≤ 1 := (div_le_one (by linarith [T.R_ge])).mpr (by linarith [T.R_ge])
  have hp : 1026*T.σ+256*T.L*T.σ^2 ≤ 1026+256*T.L := by
    have := mul_le_mul_of_nonneg_left hσ21 (show 0 ≤ 256*T.L by nlinarith [T.L_nonneg])
    linarith [T.σ_le]
  have hpz := mul_le_mul_of_nonneg_left hp hz0
  have hqσ := mul_le_mul hq hσ21 hσ2.le zero_le_one
  have he : (z*(1026/T.σ+256*T.L)+2/(10*T.R))*T.σ^2 =
      z*(1026*T.σ+256*T.L*T.σ^2)+(2/(10*T.R))*T.σ^2 := by
    field_simp [T.σ_pos.ne']
  have hs : (z*(1026/T.σ+256*T.L)+2/(10*T.R))*T.σ^2 ≤ 256*z*(5+T.L) := by
    rw [he]; nlinarith
  have hf := (le_div_iff₀ hσ2).mpr hs
  calc _ ≤ 256*z*(5+T.L)/T.σ^2 := hf
       _ = _ := by ring

lemma relocate_displacement {T : Template} {r γ : ℝ} {μ g z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hs : dist s x < T.σ*r/4) (hweight : 3/4 ≤ z s)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (dist s x/r)*mass μ (ball x (γ*r)) ≤
      (5+T.L)*(mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r) := by
  have hmoment : 0 ≤ innerMoment μ x γ r :=
    sum_nonneg (fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le))
  have hshell : 0 ≤ mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := sum_nonneg (fun p _ => hμ p)
  by_cases hne : s=x
  · subst s; simp only [dist_self, zero_div, zero_mul]
    exact mul_nonneg (by linarith [T.L_nonneg]) (add_nonneg hshell hmoment)
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; nlinarith [T.R_ge])
  let w : ℝ := dist s x/r
  let A : ℝ := 256*z s/T.σ^2
  let K : ℝ := z s*(1026/T.σ+256*T.L)+2/(10*T.R)
  have hw : 0 < w := div_pos (dist_pos.mpr hne) hr
  have hA : 0 < A := div_pos (by nlinarith) (sq_pos_of_pos T.σ_pos)
  have hK : K ≤ A*(5+T.L) := relocation_coefficient_bound T hweight
  have hf := relocate_feasible hr hz hne hother
  have hm := hmin hf
  change r*(∑ p, μ p*integrand T r g z p) ≤
    r*(∑ p, μ p*integrand T r g (relocate T r z s x) p) at hm
  have hcost : 0 ≤ ∑ p, μ p*(integrand T r g (relocate T r z s x) p-integrand T r g z p) := by
    simp only [mul_sub, sum_sub_distrib]
    exact sub_nonneg.mpr ((mul_le_mul_iff_right₀ hr).mp hm)
  have hpoint : ∀ p, μ p*(integrand T r g (relocate T r z s x) p-integrand T r g z p) ≤
      (if p ∈ ball x (γ*r) then μ p * (-A*(w^2-5*w*(dist x p/r))) else 0) +
      (if p ∈ ball x (100*T.R*r) \ ball x (γ*r) then μ p*K*w else 0) := by
    intro p
    by_cases hp : p ∈ ball x (γ*r)
    · rw [ite_eq_left hp, ite_eq_right (by simp [hp]), add_zero]
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      have hgain := relocate_inner_gain hr hγ hγL hg hglip hz hne hs (mem_filter.mp hp).2 hother
      dsimp [w, A]; linarith
    · rw [ite_eq_right hp, zero_add]
      by_cases hout : p ∈ ball x (100*T.R*r)
      · rw [ite_eq_left (mem_sdiff.mpr ⟨hout, hp⟩)]
        have h := mul_le_mul_of_nonneg_left (relocate_shell_loss (p := p) hr hg hglip hz hne hzX) (hμ p)
        simpa only [mul_assoc] using h
      · rw [ite_eq_right (by simp [hout])]
        have he := relocate_integrand_outside (g := g) (z := z) hr hs
          (show 100*T.R*r ≤ dist x p from le_of_lt (by simpa [ball] using hout))
        rw [he, sub_self, mul_zero]
  have hsum := sum_le_sum fun p (_ : p ∈ (univ : Finset Y)) => hpoint p
  rw [sum_add_distrib] at hsum
  simp only [← sum_filter, filter_mem_eq_inter, Finset.univ_inter] at hsum
  have he1 : (∑ p ∈ ball x (γ*r), μ p*(-A*(w^2-5*w*(dist x p/r)))) =
      5*A*w*innerMoment μ x γ r - A*w^2*mass μ (ball x (γ*r)) := by
    unfold innerMoment mass
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro p _; ring
  have he2 : (∑ p ∈ ball x (100*T.R*r) \ ball x (γ*r), μ p*K*w) =
      K*w*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by
    unfold mass; rw [mul_sum]; apply sum_congr rfl; intro p _; ring
  rw [he1, he2] at hsum
  have hgain : (A*w)*(w*mass μ (ball x (γ*r))-5*innerMoment μ x γ r) ≤
      K*w*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by nlinarith only [hcost, hsum]
  have hK' := mul_le_mul_of_nonneg_right hK (mul_nonneg hw.le hshell)
  have hgain' : (A*w)*(w*mass μ (ball x (γ*r))-5*innerMoment μ x γ r) ≤
      (A*w)*((5+T.L)*mass μ (ball x (100*T.R*r) \ ball x (γ*r))) := by
    nlinarith only [hgain, hK']
  have hlast := (mul_le_mul_iff_right₀ (mul_pos hA hw)).mp hgain'
  change w*mass μ (ball x (γ*r)) ≤ _
  nlinarith [mul_nonneg T.L_nonneg hmoment]

lemma b_sum_near {T : Template} {r : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hs : dist s x < T.σ*r/4) (hp : dist x p < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (∑ i, z i*b T (dist i p/r)) = z s := by
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; have := mul_pos T.σ_pos hr; linarith)
  conv_rhs => rw [← mul_one (z s), ← b_eq_one hsp]
  apply sum_eq_single s
  · intro i _ his
    by_cases hi : dist i x ≤ T.R*r/2
    · rw [hother i his hi, zero_mul]
    · have hip : 2*T.σ ≤ dist i p/r := by
        apply (le_div_iff₀ hr).mpr
        have htri := dist_triangle i p x
        rw [dist_comm p x] at htri
        have := mul_le_mul_of_nonneg_right T.R_ge hr.le
        have := mul_le_of_le_one_left hr.le T.σ_le
        linarith
      rw [b_eq_zero hip, mul_zero]
  · simp

lemma surcharge_diff_by_capacity {T : Template} {r : ℝ} {g z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hxy : dist x y < T.σ*r/8) :
    z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) ≤
      (4/T.σ)*(dist x y/r)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (4/T.σ)*(dist x y/r) :=
    mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le) (div_nonneg dist_nonneg hr.le)
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |a T (dist i x/r)-a T (dist i y/r)| ≤ (2/T.σ)*(dist x y/r) := by
      apply (a_lipschitz (T := T) (u := dist i x/r) (v := dist i y/r)
        (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) T.σ_pos.le)
      have h := scaled_dist_lipschitz hr x y i
      simpa only [dist_comm i x, dist_comm i y] using h
    have h1 := mul_le_mul (show 1+g i ≤ 2 by linarith [(hg i).2]) hd (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist i x/r)-a T (dist i y/r)))
      (show 0 ≤ 1+g i by linarith [(hg i).1])
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hz.1 i)
    calc _ = z i*((1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by ring
         _ ≤ z i*(2*((2/T.σ)*(dist x y/r))) := h3
         _ = _ := by ring
  · have hix : 2*T.R ≤ dist i x/r := by linarith
    have hiy : 2*T.R ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      nlinarith
    rw [a_eq_zero hix, a_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

lemma near_square_loss {T : Template} {r : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8) :
    z s*(1+g s)*(a T (dist s x/r)-a T (dist s y/r)) ≤
      (4/T.σ^2)*(dist s x/r)*(dist x y/r) := by
  have hw : 0 ≤ dist s x/r := div_nonneg dist_nonneg hr.le
  have hv : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hsx : dist s x/r ≤ T.σ := (div_le_iff₀ hr).mpr (by nlinarith [mul_pos T.σ_pos hr])
  have hsy : dist s y/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x y; have := mul_pos T.σ_pos hr; linarith)
  have htri : dist s x/r-dist s y/r ≤ dist x y/r := by
    have ht := div_le_div_of_nonneg_right (dist_triangle s y x) hr.le
    rw [dist_comm y x, add_div] at ht
    linarith
  have hq : (dist s x/r)^2-(dist s y/r)^2 ≤ 2*(dist s x/r)*(dist x y/r) := by
    have := mul_le_mul_of_nonneg_left htri hw
    nlinarith [sq_nonneg (dist s x/r-dist s y/r)]
  have hcoef : z s*(1+g s) ≤ 2 := by
    have := mul_le_mul (coordinate_le_one hz s) (show 1+g s ≤ 2 by linarith [(hg s).2])
      (show 0 ≤ 1+g s by linarith [(hg s).1]) zero_le_one
    simpa using this
  have hcoef0 : 0 ≤ z s*(1+g s) := mul_nonneg (hz.1 s) (by linarith [(hg s).1])
  have h1 := mul_le_mul_of_nonneg_left hq hcoef0
  have h2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2*(dist s x/r)*(dist x y/r) by positivity)
  rw [a_eq_square hw hsx, a_eq_square (div_nonneg dist_nonneg hr.le) hsy]
  calc _ = (z s*(1+g s)*((dist s x/r)^2-(dist s y/r)^2))/T.σ^2 := by ring
       _ ≤ (2*(2*(dist s x/r)*(dist x y/r)))/T.σ^2 :=
         div_le_div_of_nonneg_right (h1.trans h2) (sq_nonneg _)
       _ = _ := by ring

lemma near_integrand_slope {T : Template} {r : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    integrand T r g z x-integrand T r g z y ≤
      ((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*(dist x y/r) := by
  have hbx := b_sum_near hr hs (p := x) (by simp; exact mul_pos T.σ_pos hr) hother
  have hby := b_sum_near hr hs hxy hother
  have hsG : G T (dist s x/r) = 0 := G_eq_zero ((div_le_iff₀ hr).mpr (by
    have := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have := mul_le_of_le_one_left hr.le T.σ_le
    linarith))
  have hcap : (∑ i ∈ univ.erase s, max (z i-G T (dist i x/r)) 0) ≤ 1-z s := by
    have h := hz.2.1 x
    rw [← sum_erase_add _ _ (mem_univ s), hsG, sub_zero, max_eq_left (hz.1 s)] at h
    linarith
  have hsum := sum_le_sum (s := univ.erase s) fun i _ =>
    surcharge_diff_by_capacity (i := i) hr hg hz hxy
  rw [← mul_sum] at hsum
  have hcap' := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ (4/T.σ)*(dist x y/r) from mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le)
      (div_nonneg dist_nonneg hr.le))
  have hsum' := hsum.trans hcap'
  have hnear := near_square_loss hr hg hz hs hxy
  have hres := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hglip x y))
    (sub_nonneg.mpr (coordinate_le_one hz s))
  have htotal : (∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) ≤
      (4/T.σ)*(dist x y/r)*(1-z s)+(4/T.σ^2)*(dist s x/r)*(dist x y/r) := by
    rw [← sum_erase_add _ _ (mem_univ s)]
    exact add_le_add hsum' hnear
  have he : (∑ i, z i*(1+g i)*a T (dist i x/r)) -
      (∑ i, z i*(1+g i)*a T (dist i y/r)) =
      ∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
  unfold integrand
  rw [hbx, hby]
  calc _ = (g x-g y)*(1-z s)+256*((∑ i, z i*(1+g i)*a T (dist i x/r)) -
      (∑ i, z i*(1+g i)*a T (dist i y/r))) := by ring
       _ = (g x-g y)*(1-z s)+256*(∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by rw [he]
       _ ≤ (T.L*(dist x y/r))*(1-z s)+256*((4/T.σ)*(dist x y/r)*(1-z s)+
         (4/T.σ^2)*(dist s x/r)*(dist x y/r)) :=
          add_le_add hres (mul_le_mul_of_nonneg_left htotal (by norm_num))
       _ = _ := by ring

/-- Exact constant displayed in (6.10), with no dependence on the metric size. -/
def localConstant (T : Template) : ℝ :=
  (T.L+1024/T.σ)*(514+8/T.σ)+1024*(5+T.L)/T.σ^2

lemma localConstant_nonneg (T : Template) : 0 ≤ localConstant T := by
  unfold localConstant
  have hσ := T.σ_pos; have hL := T.L_nonneg
  positivity

lemma near_slope_mass {T : Template} {r M S J γ : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hM : 0 ≤ M) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hγ : γ ≤ T.σ/64) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0)
    (hdef : (1-z s)*M ≤ (512*γ/T.σ^2)*J+514*S)
    (hmove : (dist s x/r)*M ≤ (5+T.L)*(S+J)) :
    max (integrand T r g z x-integrand T r g z y) 0 * M ≤
      localConstant T*(S+J)*(dist x y/r) := by
  have hσ := T.σ_pos
  have hcoef : 512*γ/T.σ^2 ≤ 8/T.σ := by
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    calc 512*γ ≤ 8*T.σ := by linarith
         _ = (8/T.σ)*T.σ^2 := by field_simp
  have hdef' : (1-z s)*M ≤ (514+8/T.σ)*(S+J) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef hJ
    have h2 : 0 ≤ (8/T.σ)*S := mul_nonneg (div_nonneg (by norm_num) hσ.le) hS
    nlinarith only [hdef, h1, h2, hJ]
  have h1 := mul_le_mul_of_nonneg_left hdef'
    (show 0 ≤ T.L+1024/T.σ from add_nonneg T.L_nonneg (div_nonneg (by norm_num) hσ.le))
  have h2 := mul_le_mul_of_nonneg_left hmove
    (show 0 ≤ 1024/T.σ^2 from div_nonneg (by norm_num) (sq_nonneg _))
  have hsum : ((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*M ≤
      localConstant T*(S+J) := by
    unfold localConstant
    calc _ = (T.L+1024/T.σ)*((1-z s)*M)+(1024/T.σ^2)*((dist s x/r)*M) := by ring
         _ ≤ (T.L+1024/T.σ)*((514+8/T.σ)*(S+J))+(1024/T.σ^2)*((5+T.L)*(S+J)) := add_le_add h1 h2
         _ = _ := by ring
  have hv : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hslope := mul_le_mul_of_nonneg_right (near_integrand_slope hr hg hglip hz hs hxy hother) hM
  have hlast := mul_le_mul_of_nonneg_right hsum hv
  have hab : (integrand T r g z x-integrand T r g z y)*M ≤
      localConstant T*(S+J)*(dist x y/r) := by
    calc _ ≤ (((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*(dist x y/r))*M := hslope
         _ = (((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*M)*(dist x y/r) := by ring
         _ ≤ _ := hlast
  rw [max_mul_of_nonneg _ _ hM]
  apply max_le hab
  simpa only [zero_mul] using mul_nonneg (mul_nonneg (localConstant_nonneg T) (add_nonneg hS hJ)) hv

/-- The full local-optimality theorem, derived from the actual compact
minimizer, deletion, insertion and relocation competitors. -/
theorem local_structure {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (100*T.R*r) \ ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r))) :
    (∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i=0) ∧
    ∃ s, dist s x < T.σ*r/4 ∧ 3/4 ≤ z s ∧
      (∀ i, dist i x < T.σ*r/4 → 0 < z i → i=s) ∧
      (1-z s)*mass μ (ball x (γ*r)) ≤ 512*γ/T.σ^2*innerMoment μ x γ r +
        514*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) ∧
      (dist s x/r)*mass μ (ball x (γ*r)) ≤ (5+T.L)*
        (mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r) ∧
      ∀ y, dist x y < T.σ*r/8 →
        max (integrand T r g z x-integrand T r g z y) 0 * mass μ (ball x (γ*r)) ≤
          localConstant T*(mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r)*(dist x y/r) := by
  have hsubset : ball x (γ*r) ⊆ ball x (100*T.R*r) := by
    intro p hp
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hp' := (mem_filter.mp hp).2
    have := mul_le_mul_of_nonneg_right hγ hr.le
    have := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have := mul_le_of_le_one_left hr.le T.σ_le
    nlinarith
  have hmass : mass μ (ball x (100*T.R*r)) ≤ (1+δ)*mass μ (ball x (γ*r)) := by
    have he := sum_sdiff (f := μ) hsubset
    change mass μ (ball x (100*T.R*r) \ ball x (γ*r)) + mass μ (ball x (γ*r)) =
      mass μ (ball x (100*T.R*r)) at he
    nlinarith
  have hmiddle : ∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i=0 :=
    fun i hl hh => no_middle_site hr hγ hδ hμ hg hz hmin hl hh hM hmass
  obtain ⟨s, hs, hsz, he, hun⟩ := near_site_of_large hr hz
    (nearWeight_large hr hγ0 hγ hδ hμ hg hz hmin hmiddle hM hconc)
  have hs' : dist s x < T.σ*r/4 := by simpa only [dist_comm s x] using (mem_filter.mp hs).2
  have hother := near_site_others_vanish hr hz hs' (show 0 < z s by linarith) hmiddle
  have hdef : (1-z s)*mass μ (ball x (γ*r)) ≤ 512*γ/T.σ^2*innerMoment μ x γ r +
      514*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by
    rw [← he]; exact nearWeight_deficit hr hγ hμ hg hz hmin hmiddle
  have hmove := relocate_displacement hr hγ hγL hμ hg hglip hz hmin hs' hsz hother
  refine ⟨hmiddle, s, hs', hsz, ?_, hdef, hmove, ?_⟩
  · intro i hi hip
    exact hun i (mem_filter.mpr ⟨mem_univ _, by simpa only [dist_comm x i] using hi⟩) hip
  · intro y hy
    exact near_slope_mass hr hM.le (sum_nonneg fun p _ => hμ p)
      (sum_nonneg fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le))
      hγ hg hglip hz hs' hy hother hdef hmove

lemma surcharge_global_by_capacity {T : Template} {r : ℝ} {g z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hxy : dist x y ≤ r) :
    z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) ≤
      (4/T.σ)*(dist x y/r)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (4/T.σ)*(dist x y/r) :=
    mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le) (div_nonneg dist_nonneg hr.le)
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |a T (dist i x/r)-a T (dist i y/r)| ≤ (2/T.σ)*(dist x y/r) := by
      apply (a_lipschitz (T := T) (u := dist i x/r) (v := dist i y/r)
        (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) T.σ_pos.le)
      have h := scaled_dist_lipschitz hr x y i
      simpa only [dist_comm i x, dist_comm i y] using h
    have h1 := mul_le_mul (show 1+g i ≤ 2 by linarith [(hg i).2]) hd (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist i x/r)-a T (dist i y/r)))
      (show 0 ≤ 1+g i by linarith [(hg i).1])
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hz.1 i)
    calc _ = z i*((1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by ring
         _ ≤ z i*(2*((2/T.σ)*(dist x y/r))) := h3
         _ = _ := by ring
  · have hix : 2*T.R ≤ dist i x/r := by linarith [T.R_ge]
    have hiy : 2*T.R ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      nlinarith
    rw [a_eq_zero hix, a_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

lemma b_global_by_capacity {T : Template} {r : ℝ} {z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hxy : dist x y ≤ r) :
    z i*(b T (dist i y/r)-b T (dist i x/r)) ≤
      ((dist x y/r)/T.σ)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (dist x y/r)/T.σ := div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |b T (dist i y/r)-b T (dist i x/r)| ≤ (dist x y/r)/T.σ := by
      apply (b_lipschitz T _ _).trans
      apply div_le_div_of_nonneg_right _ T.σ_pos.le
      have h := scaled_dist_lipschitz hr y x i
      simpa only [dist_comm i x, dist_comm i y, dist_comm y x] using h
    have h := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd) (hz.1 i)
    simpa only [mul_comm] using h
  · have hix : 2*T.σ ≤ dist i x/r := by linarith [T.R_ge, T.σ_le]
    have hiy : 2*T.σ ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      have := mul_le_of_le_one_left hr.le T.σ_le
      nlinarith
    rw [b_eq_zero hix, b_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

def globalConstant (T : Template) : ℝ := T.L+1026/T.σ

lemma globalConstant_ge (T : Template) : 1026 ≤ globalConstant T := by
  unfold globalConstant
  have : (1026:ℝ) ≤ 1026/T.σ := (le_div_iff₀ T.σ_pos).mpr (by nlinarith [T.σ_le])
  linarith [T.L_nonneg]

lemma integrand_diff_le {T : Template} {r : ℝ} {g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) (hz : Feasible T r z) :
    integrand T r g z x-integrand T r g z y ≤ globalConstant T*(dist x y/r) := by
  by_cases hxy : dist x y ≤ r
  · have ha := sum_le_sum (s := (univ : Finset Y)) fun i _ => surcharge_global_by_capacity (i := i) hr hg hz hxy
    rw [← mul_sum] at ha
    have ha' := ha.trans (mul_le_mul_of_nonneg_left (hz.2.1 x)
      (show 0 ≤ (4/T.σ)*(dist x y/r) from mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le)
        (div_nonneg dist_nonneg hr.le)))
    rw [mul_one] at ha'
    have hb := sum_le_sum (s := (univ : Finset Y)) fun i _ => b_global_by_capacity (i := i) hr hz hxy
    rw [← mul_sum] at hb
    have hb' := hb.trans (mul_le_mul_of_nonneg_left (hz.2.1 x)
      (div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le))
    rw [mul_one] at hb'
    have hby0 : 0 ≤ ∑ i, z i*b T (dist i y/r) := sum_nonneg fun i _ => mul_nonneg (hz.1 i) (b_nonneg _ _)
    have hby1 := sum_b_le_one hz y
    have hres1 : (g x-g y)*(1-∑ i, z i*b T (dist i y/r)) ≤ T.L*(dist x y/r) := by
      calc _ ≤ (T.L*(dist x y/r))*1 := mul_le_mul ((le_abs_self _).trans (hglip x y))
            (by linarith) (by linarith) (mul_nonneg T.L_nonneg (div_nonneg dist_nonneg hr.le))
           _ = _ := mul_one _
    have hres2 : (1+g x)*(∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) ≤ 2*((dist x y/r)/T.σ) := by
      calc _ ≤ (1+g x)*((dist x y/r)/T.σ) := mul_le_mul_of_nonneg_left hb' (by linarith [(hg x).1])
           _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [(hg x).2])
             (div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le)
    have heb : (∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) =
        (∑ i, z i*b T (dist i y/r))-(∑ i, z i*b T (dist i x/r)) := by
      simp only [mul_sub, sum_sub_distrib]
    have hea : (∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) =
        (∑ i, z i*(1+g i)*a T (dist i x/r))-(∑ i, z i*(1+g i)*a T (dist i y/r)) := by
      simp only [mul_sub, sum_sub_distrib]
    unfold integrand globalConstant
    calc _ = (g x-g y)*(1-∑ i, z i*b T (dist i y/r)) +
        (1+g x)*(∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) +
        256*(∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by rw [heb, hea]; ring
         _ ≤ T.L*(dist x y/r)+2*((dist x y/r)/T.σ)+256*((4/T.σ)*(dist x y/r)) :=
           add_le_add (add_le_add hres1 hres2) (mul_le_mul_of_nonneg_left ha' (by norm_num))
         _ = _ := by ring
  · have hv : 1 ≤ dist x y/r := (le_div_iff₀ hr).mpr (by linarith)
    have hg0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
    have h := mul_le_mul_of_nonneg_left hv hg0
    linarith [(integrand_bounds hz hg x).2, (integrand_bounds hz hg y).1, globalConstant_ge T]

theorem integrand_lipschitz {T : Template} {r : ℝ} {g z : Y → ℝ}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) (hz : Feasible T r z) (x y : Y) :
    |integrand T r g z x-integrand T r g z y| ≤ globalConstant T*(dist x y/r) := by
  apply abs_le.mpr
  constructor
  · have := integrand_diff_le (x := y) (y := x) hr hg hglip hz
    rw [dist_comm y x] at this
    linarith
  · exact integrand_diff_le hr hg hglip hz

end KServer.Pilot


/-! Exact scale summations for pilot drift and the partition budget.
No policy or drift estimate is assumed. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace KServer.ScaleMass

lemma capped_log {u : ℝ} (hu : 0 ≤ u) : min 1 u ≤ Real.log (1+u)/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ h2).mpr
  by_cases h : u ≤ 1
  · rw [min_eq_right h]
    have hc := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show (2:ℝ) ∈ Set.Ioi 0 by norm_num)
      (show 0 ≤ 1-u by linarith) hu (show 1-u+u=1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
    convert hc using 1
    congr 1
    ring
  · rw [min_eq_left (le_of_not_ge h), one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)

/-- A p-step telescoping sum has only p boundary differences. The function is
allowed to be extended by the upper endpoint. -/
lemma shifted_sum_le (f : ℕ → ℝ) (a b : ℝ) (hf : ∀ i, f i ∈ Set.Icc a b)
    (n p : ℕ) : ∑ i ∈ range n, (f (i+p)-f i) ≤ p*(b-a) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have he : (∑ i ∈ range n, (f (i+(p+1))-f i)) =
        (∑ i ∈ range n, (f (i+p)-f i)) + (f (n+p)-f p) := by
      have ht := sum_range_sub (fun i => f (i+p)) n
      simp only [zero_add, Nat.add_assoc, Nat.add_comm 1 p] at ht
      calc _ = (∑ i ∈ range n, (f (i+p)-f i)) +
          (∑ i ∈ range n, (f (i+(p+1))-f (i+p))) := by
            rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
           _ = _ := by rw [ht]
    rw [he, Nat.cast_add, Nat.cast_one]
    nlinarith [(hf (n+p)).2, (hf p).1]

lemma shell_log_sum {n p : ℕ} {m A : ℕ → ℝ} {k : ℝ}
    (hk : 0 < k) (hm : ∀ i, m i ∈ Set.Icc (1/2) k)
    (hA : ∀ i < n, m i ≤ A i ∧ A i ≤ m (i+p)) :
    ∑ i ∈ range n, min 1 ((A i-m i)/m i) ≤
      (p:ℝ)/Real.log 2 * Real.log (2*k) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : ∀ i, 0 < m i := fun i => lt_of_lt_of_le (by norm_num) (hm i).1
  have hstep : ∀ i ∈ range n, min 1 ((A i-m i)/m i) ≤
      (Real.log (m (i+p))-Real.log (m i))/Real.log 2 := by
    intro i hi
    have hai := hA i (mem_range.mp hi)
    have h := capped_log (div_nonneg (sub_nonneg.mpr hai.1) (hm0 i).le)
    have he : 1+(A i-m i)/m i = A i/m i := by field_simp [(hm0 i).ne']; ring
    rw [he, Real.log_div (ne_of_gt ((hm0 i).trans_le hai.1)) (hm0 i).ne'] at h
    exact h.trans (div_le_div_of_nonneg_right
      (sub_le_sub_right (Real.log_le_log ((hm0 i).trans_le hai.1) hai.2) _) h2.le)
  have ht := shifted_sum_le (fun i => Real.log (m i)) (Real.log (1/2)) (Real.log k)
    (fun i => ⟨Real.log_le_log (by norm_num) (hm i).1, Real.log_le_log (hm0 i) (hm i).2⟩) n p
  have he : Real.log k-Real.log (1/2) = Real.log (2*k) := by
    rw [← Real.log_div hk.ne' (by norm_num)]; congr 1; ring
  calc _ ≤ ∑ i ∈ range n, (Real.log (m (i+p))-Real.log (m i))/Real.log 2 := sum_le_sum hstep
       _ = (∑ i ∈ range n, (Real.log (m (i+p))-Real.log (m i)))/Real.log 2 := by rw [sum_div]
       _ ≤ ((p:ℝ)*(Real.log k-Real.log (1/2)))/Real.log 2 := div_le_div_of_nonneg_right ht h2.le
       _ = _ := by rw [he]; ring

/-- Relative new mass is controlled by the logarithmic increase. -/
lemma relative_increment_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/b ≤ Real.log b-Real.log a := by
  have hb := ha.trans_le hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  convert h using 1
  field_simp

lemma relative_increment_sum {m : ℕ → ℝ} {n : ℕ}
    (hm : ∀ i ≤ n, 0 < m i) (hmono : Monotone m) :
    1 + ∑ i ∈ range n, (m (i+1)-m i)/m (i+1) ≤
      1 + Real.log (m n/m 0) := by
  have hs := sum_le_sum (s := range n) (fun i hi =>
    relative_increment_le_log (hm i (by have := mem_range.mp hi; omega)) (hmono (by omega : i ≤ i+1)))
  rw [show (∑ i ∈ range n, (Real.log (m (i+1))-Real.log (m i))) =
    Real.log (m n)-Real.log (m 0) from sum_range_sub (fun i => Real.log (m i)) n] at hs
  rw [Real.log_div (hm n le_rfl).ne' (hm 0 (by omega)).ne']
  linarith

lemma geometric_sum_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (n : ℕ) :
    ∑ i ∈ range n, q^i ≤ 2 := by
  have hsum : 0 ≤ ∑ i ∈ range n, q^i := sum_nonneg fun i _ => pow_nonneg hq0 i
  have he := geom_sum_mul q n
  have hp := pow_nonneg hq0 n
  nlinarith

/-- Geometric radius sums, including every initial atom and any finite cutoff. -/
lemma geometric_weighted_sum {n : ℕ} {r : ℕ → ℝ} (hr : ∀ i < n, 0 ≤ r i)
    (hstep : ∀ i, i+1 < n → 2*r i ≤ r (i+1)) :
    ∑ i ∈ range n, r i ≤ if n=0 then 0 else 2*r (n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    by_cases hn : n=0
    · subst n; simp; linarith [hr 0 (by omega)]
    · have ht := ih (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
      rw [ite_eq_right hn] at ht
      have hd := hstep (n-1) (by omega)
      have he : n-1+1=n := by omega
      rw [he] at hd
      linarith


def convolution (q : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1), q^(j-i)*a i

lemma convolution_nonneg {q : ℝ} {a : ℕ → ℝ} (hq : 0 ≤ q)
    (ha : ∀ i, 0 ≤ a i) (j : ℕ) : 0 ≤ convolution q a j :=
  sum_nonneg fun i _ => mul_nonneg (pow_nonneg hq _) (ha i)

lemma convolution_succ (q : ℝ) (a : ℕ → ℝ) (j : ℕ) :
    convolution q a (j+1) = q*convolution q a j+a (j+1) := by
  unfold convolution
  rw [sum_range_succ, mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  have he : j+1-i=(j-i)+1 := by have := mem_range.mp hi; omega
  rw [he, pow_succ]; ring

lemma convolution_sum_aux {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    (∑ j ∈ range (n+1), convolution q a j)+convolution q a n ≤
      2*∑ i ∈ range (n+1), a i := by
  induction n with
  | zero => simp [convolution]; ring_nf; exact le_rfl
  | succ n ih =>
    rw [sum_range_succ, convolution_succ, sum_range_succ (f := a)]
    have hn := convolution_nonneg hq0 ha n
    have h := mul_le_mul_of_nonneg_right hq hn
    nlinarith

lemma convolution_sum_le {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    ∑ j ∈ range n, convolution q a j ≤ 2*∑ i ∈ range n, a i := by
  cases n with
  | zero => simp
  | succ n => linarith [convolution_sum_aux hq0 hq ha n, convolution_nonneg hq0 ha n]

/-- The first relative increment includes the entire first ball. -/
def increment (m : ℕ → ℝ) (i : ℕ) : ℝ := if i=0 then m 0 else m i-m (i-1)

lemma increment_nonneg {m : ℕ → ℝ} (hm0 : 0 ≤ m 0) (hm : Monotone m) (i : ℕ) :
    0 ≤ increment m i := by
  unfold increment; split_ifs with h
  · exact hm0
  · exact sub_nonneg.mpr (hm (Nat.sub_le _ _))

lemma increment_sum_le {m : ℕ → ℝ} (hm0 : 0 < m 0) (hm : Monotone m) (n : ℕ) :
    ∑ i ∈ range (n+1), increment m i/m i ≤ 1+Real.log (m n/m 0) := by
  rw [sum_range_succ']
  simp only [increment, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, div_self hm0.ne']
  have h := relative_increment_sum (m := m) (n := n)
    (fun i _ => hm0.trans_le (hm (Nat.zero_le i))) hm
  linarith

/-- Exact Fubini/geometric moment estimate, encoded as a finite convolution.
The hypotheses here are the ball-layer pointwise estimate and monotone masses;
no estimate to be proved is hidden among them. -/
lemma moment_sum_le {m t : ℕ → ℝ} {q γ k : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hγ : 0 ≤ γ) (hk : 1/2 ≤ k)
    (hm0 : 1/2 ≤ m 0) (hm : Monotone m) (hmk : ∀ i < n, m i ≤ k)
    (ht : ∀ j < n, t j ≤ γ*∑ i ∈ range (j+1), q^(j-i)*increment m i/m j) :
    ∑ j ∈ range n, t j ≤ 2*γ*(1+Real.log (2*k)) := by
  have hmp : ∀ i, 0 < m i := fun i => (show (0:ℝ)<1/2 by norm_num).trans_le
    (hm0.trans (hm (Nat.zero_le i)))
  have hd : ∀ i, 0 ≤ increment m i := increment_nonneg (hmp 0).le hm
  have ha : ∀ i, 0 ≤ increment m i/m i := fun i => div_nonneg (hd i) (hmp i).le
  have hrow : ∀ j ∈ range n, t j ≤ γ*convolution q (fun i => increment m i/m i) j := by
    intro j hj
    apply (ht j (mem_range.mp hj)).trans
    apply mul_le_mul_of_nonneg_left _ hγ
    unfold convolution
    apply sum_le_sum
    intro i hi
    have hij : i ≤ j := by have := mem_range.mp hi; omega
    calc _ ≤ q^(j-i)*increment m i/m i :=
            div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hq0 _) (hd i)) (hmp i) (hm hij)
         _ = _ := by ring
  have htotal : (∑ j ∈ range n, t j) ≤ γ*(2*∑ i ∈ range n, increment m i/m i) := by
    calc _ ≤ ∑ j ∈ range n, γ*convolution q (fun i => increment m i/m i) j := sum_le_sum hrow
         _ = γ*(∑ j ∈ range n, convolution q (fun i => increment m i/m i) j) := by rw [mul_sum]
         _ ≤ _ := mul_le_mul_of_nonneg_left (convolution_sum_le hq0 hq ha n) hγ
  by_cases hn : n=0
  · subst n
    simp only [sum_range_zero]
    have hl : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
    positivity
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hrel := increment_sum_le (hmp 0) hm N
    have hlog : Real.log (m N/m 0) ≤ Real.log (2*k) := by
      apply Real.log_le_log (div_pos (hmp N) (hmp 0))
      apply (div_le_iff₀ (hmp 0)).mpr
      have hk' := hmk N (by omega)
      nlinarith
    have hmcoef : 0 ≤ 2*γ := by positivity
    calc _ ≤ γ*(2*∑ i ∈ range (N+1), increment m i/m i) := htotal
         _ = (2*γ)*(∑ i ∈ range (N+1), increment m i/m i) := by ring
         _ ≤ (2*γ)*(1+Real.log (2*k)) := mul_le_mul_of_nonneg_left (hrel.trans (by linarith)) hmcoef

end KServer.ScaleMass

namespace KServer.Pilot
open Finset
variable {Y : Type*} [Fintype Y] [MetricSpace Y]

/-- The coarse consecutive range, written in increasing order for moment summation. -/
def radius (r₀ τ : ℝ) (j : ℕ) : ℝ := r₀*τ^j

lemma radius_pos {r₀ τ : ℝ} (hr : 0 < r₀) (hτ : 0 < τ) (j : ℕ) :
    0 < radius r₀ τ j := mul_pos hr (pow_pos hτ j)

lemma radius_succ (r₀ τ : ℝ) (j : ℕ) : radius r₀ τ (j+1)=τ*radius r₀ τ j := by
  unfold radius; rw [pow_succ]; ring

lemma radius_add (r₀ τ : ℝ) (i j : ℕ) : radius r₀ τ (i+j)=radius r₀ τ i*τ^j := by
  unfold radius; rw [pow_add]; ring

lemma radius_mono {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) : Monotone (radius r₀ τ) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [radius_succ]
  have hj : 0 ≤ radius r₀ τ j := mul_nonneg hr (pow_nonneg (by linarith) _)
  nlinarith

lemma ball_mono {x : Y} {r s : ℝ} (h : r ≤ s) : ball x r ⊆ ball x s := by
  intro y hy
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.trans h⟩

omit [Fintype Y] [MetricSpace Y] in
lemma mass_mono {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y) {A B : Finset Y} (h : A ⊆ B) :
    mass μ A ≤ mass μ B := sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hμ i)

omit [Fintype Y] [MetricSpace Y] in
lemma mass_nonneg {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y) (A : Finset Y) :
    0 ≤ mass μ A := sum_nonneg fun i _ => hμ i

def innerMass (μ : Y → ℝ) (x : Y) (γ r₀ τ : ℝ) (j : ℕ) : ℝ :=
  mass μ (ball x (γ*radius r₀ τ j))

lemma innerMass_mono {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) :
    Monotone (innerMass μ x γ r₀ τ) := by
  intro i j hij
  exact mass_mono hμ (ball_mono (mul_le_mul_of_nonneg_left (radius_mono hr hτ hij) hγ))

lemma innerMoment_step {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 1 ≤ τ) (j : ℕ) :
    innerMoment μ x γ (radius r₀ τ (j+1)) ≤
      τ⁻¹*innerMoment μ x γ (radius r₀ τ j) +
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) := by
  classical
  have hτ0 : 0 < τ := by linarith
  have hro := radius_pos hr hτ0 j
  have hrn := radius_pos hr hτ0 (j+1)
  let A := ball x (γ*radius r₀ τ j)
  let B := ball x (γ*radius r₀ τ (j+1))
  have hAB : A ⊆ B := ball_mono (mul_le_mul_of_nonneg_left (radius_mono hr.le hτ (by omega)) hγ)
  have he : innerMoment μ x γ (radius r₀ τ (j+1)) =
      (∑ p ∈ A, μ p*(dist x p/radius r₀ τ (j+1)))+
      (∑ p ∈ B\A, μ p*(dist x p/radius r₀ τ (j+1))) := by
    change (∑ p ∈ B, μ p*(dist x p/radius r₀ τ (j+1))) = _
    have hh := sum_sdiff (f := fun p => μ p*(dist x p/radius r₀ τ (j+1))) hAB
    linarith
  have hold : (∑ p ∈ A, μ p*(dist x p/radius r₀ τ (j+1))) =
      τ⁻¹*innerMoment μ x γ (radius r₀ τ j) := by
    unfold innerMoment
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    rw [radius_succ]
    field_simp
  have hnew : (∑ p ∈ B\A, μ p*(dist x p/radius r₀ τ (j+1))) ≤ γ*mass μ (B\A) := by
    unfold mass; rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hd := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hv : dist x p/radius r₀ τ (j+1) ≤ γ := (div_le_iff₀ hrn).mpr hd
    nlinarith [mul_le_mul_of_nonneg_left hv (hμ p)]
  have hm := sum_sdiff (f := μ) hAB
  change mass μ (B\A)+mass μ A=mass μ B at hm
  change _ ≤ _ + γ*(mass μ B-mass μ A)
  rw [he, hold]
  nlinarith

lemma innerMoment_convolution {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 1 ≤ τ) (j : ℕ) :
    innerMoment μ x γ (radius r₀ τ j) ≤
      γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j := by
  classical
  have hτ0 : 0 < τ := by linarith
  induction j with
  | zero =>
    simpa [ScaleMass.convolution, ScaleMass.increment, innerMass] using
      innerMoment_le (radius_pos hr hτ0 0) hμ (x := x) (γ := γ)
  | succ j ih =>
    calc _ ≤ τ⁻¹*innerMoment μ x γ (radius r₀ τ j)+
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) := innerMoment_step hμ hγ hr hτ j
         _ ≤ τ⁻¹*(γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j)+
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) :=
          add_le_add (mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr hτ0.le)) le_rfl
         _ = _ := by rw [ScaleMass.convolution_succ]; simp [ScaleMass.increment]; ring

/-- The moment sum for actual closed metric balls, not an interface
assuming the ball-layer estimate. It includes atoms in the first ball. -/
theorem innerMoment_scale_sum {μ : Y → ℝ} {x : Y} {γ r₀ τ k : ℝ} (n : ℕ)
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 2 ≤ τ)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y = k) :
    ∑ j ∈ range n, innerMoment μ x γ (radius r₀ τ j)/innerMass μ x γ r₀ τ j ≤
      2*γ*(1+Real.log (2*k)) := by
  have hτ0 : 0 < τ := by linarith
  have hmm := innerMass_mono (x := x) hμ hγ hr.le (show 1 ≤ τ by linarith)
  have hmp : ∀ i, 0 < innerMass μ x γ r₀ τ i := fun i =>
    (show (0:ℝ)<1/2 by norm_num).trans_le (hm0.trans (hmm (Nat.zero_le i)))
  have hmk : ∀ i, innerMass μ x γ r₀ τ i ≤ k := by
    intro i
    rw [← hk]
    exact mass_mono hμ (subset_univ _)
  apply ScaleMass.moment_sum_le (inv_nonneg.mpr hτ0.le)
    (show τ⁻¹ ≤ 1/2 by rw [inv_eq_one_div]; apply (div_le_iff₀ hτ0).mpr; linarith) hγ (hm0.trans (hmk 0)) hm0 hmm (fun i _ => hmk i)
  intro j _
  have h := div_le_div_of_nonneg_right
    (innerMoment_convolution (x := x) hμ hγ hr (show 1 ≤ τ by linarith) j) (hmp j).le
  calc _ ≤ (γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j)/
      innerMass μ x γ r₀ τ j := h
       _ = _ := by unfold ScaleMass.convolution; rw [mul_div_assoc, sum_div]

/-- Shell summation for the exact closed balls. Missing coarser masses are
assigned total mass k in the telescope. -/
theorem shell_scale_sum {μ : Y → ℝ} {x : Y} {γ D r₀ τ k : ℝ} (n p : ℕ)
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 2 ≤ τ)
    (hD : γ ≤ D) (hp : D ≤ γ*τ^p)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y = k) :
    ∑ j ∈ range n, min 1 (mass μ (ball x (D*radius r₀ τ j)\
      ball x (γ*radius r₀ τ j))/innerMass μ x γ r₀ τ j) ≤
      (p:ℝ)/Real.log 2*Real.log (2*k) := by
  classical
  have hτ0 : 0 < τ := by linarith
  have hmm := innerMass_mono (x := x) hμ hγ hr.le (show 1 ≤ τ by linarith)
  have hmk : ∀ i, innerMass μ x γ r₀ τ i ≤ k := by
    intro i; rw [← hk]; exact mass_mono hμ (subset_univ _)
  have hml : ∀ i, 1/2 ≤ innerMass μ x γ r₀ τ i := fun i => hm0.trans (hmm (Nat.zero_le i))
  have hk0 : 0 < k := (show (0:ℝ)<1/2 by norm_num).trans_le (hm0.trans (hmk 0))
  let m : ℕ → ℝ := fun i => if i<n then innerMass μ x γ r₀ τ i else k
  let A : ℕ → ℝ := fun i => mass μ (ball x (D*radius r₀ τ i))
  have hm : ∀ i, m i ∈ Set.Icc (1/2) k := by
    intro i; dsimp [m]; split_ifs
    · exact ⟨hml i, hmk i⟩
    · exact ⟨hm0.trans (hmk 0), le_rfl⟩
  have hAB : ∀ i, ball x (γ*radius r₀ τ i) ⊆ ball x (D*radius r₀ τ i) :=
    fun i => ball_mono (mul_le_mul_of_nonneg_right hD (radius_pos hr hτ0 i).le)
  have hA : ∀ i < n, m i ≤ A i ∧ A i ≤ m (i+p) := by
    intro i hi
    dsimp [m, A]
    rw [ite_eq_left hi]
    refine ⟨mass_mono hμ (hAB i), ?_⟩
    split_ifs with hj
    · apply mass_mono hμ
      apply ball_mono
      rw [radius_add]
      nlinarith [mul_le_mul_of_nonneg_right hp (radius_pos hr hτ0 i).le]
    · rw [← hk]; exact mass_mono hμ (subset_univ _)
  have h := ScaleMass.shell_log_sum hk0 hm hA
  convert h using 1
  apply sum_congr rfl
  intro i hi
  dsimp [m, A]
  rw [ite_eq_left (mem_range.mp hi)]
  have he := sum_sdiff (f := μ) (hAB i)
  change mass μ (ball x (D*radius r₀ τ i)\ball x (γ*radius r₀ τ i))+
    innerMass μ x γ r₀ τ i = mass μ (ball x (D*radius r₀ τ i)) at he
  have hed : mass μ (ball x (D*radius r₀ τ i)\ball x (γ*radius r₀ τ i)) =
      mass μ (ball x (D*radius r₀ τ i))-innerMass μ x γ r₀ τ i := by linarith
  rw [hed]

lemma radius_geometric {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) (j : ℕ) :
    2*radius r₀ τ j ≤ radius r₀ τ (j+1) := by
  rw [radius_succ]
  exact mul_le_mul_of_nonneg_right hτ (mul_nonneg hr (pow_nonneg (by linarith) _))

/-- Every truncated initial segment of a geometric radius sequence costs at
most twice the cutoff; there is no number-of-scales factor. -/
lemma radius_truncated_sum {r₀ τ R : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) (hR : 0 ≤ R) (n : ℕ) :
    ∑ j ∈ range n, (if radius r₀ τ j ≤ R then radius r₀ τ j else 0) ≤ 2*R := by
  have hr0 : ∀ i, 0 ≤ radius r₀ τ i := fun i => mul_nonneg hr (pow_nonneg (by linarith) _)
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    by_cases hn : radius r₀ τ n ≤ R
    · calc _ ≤ ∑ j ∈ range (n+1), radius r₀ τ j := by
            apply sum_le_sum; intro j _; split_ifs <;> simp [hr0 j]
           _ ≤ 2*radius r₀ τ n := by
            simpa using ScaleMass.geometric_weighted_sum (n := n+1) (r := radius r₀ τ)
              (fun i _ => hr0 i) (fun i _ => radius_geometric hr hτ i)
           _ ≤ _ := by linarith
    · rw [sum_range_succ, ite_eq_right hn, add_zero]; exact ih


def moveMeasure (μ ν : Y → ℝ) (x : Y) (y : Y) : ℝ := μ y-ν y+if y=x then 1 else 0

def moveCost (ν : Y → ℝ) (x : Y) : ℝ := ∑ y, ν y*dist x y

omit [Fintype Y] [MetricSpace Y] in
lemma moveMeasure_nonneg {μ ν : Y → ℝ} {x : Y} (hνμ : ∀ y, ν y ≤ μ y) :
    ∀ y, 0 ≤ moveMeasure μ ν x y := by
  intro y; unfold moveMeasure
  split_ifs <;> linarith [hνμ y]

lemma moveCost_nonneg {ν : Y → ℝ} {x : Y} (hν : ∀ y, 0 ≤ ν y) : 0 ≤ moveCost ν x :=
  sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg

omit [MetricSpace Y] in
lemma moveMeasure_integral {μ ν F : Y → ℝ} {x : Y} (hν1 : ∑ y, ν y=1) :
    (∑ y, moveMeasure μ ν x y*F y)-(∑ y, μ y*F y) =
      ∑ y, ν y*(F x-F y) := by
  classical
  simp only [moveMeasure, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_sub]
  have hδ : (∑ y, (if y=x then (1:ℝ) else 0)*F y) = F x := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hδ, ← sum_mul, hν1, one_mul]
  ring

lemma candidate_drift {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hν1 : ∑ y, ν y=1) :
    potential T r (moveMeasure μ ν x) g-potential T r μ g ≤
      r*∑ y, ν y*(integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) := by
  have h := potential_le (μ := moveMeasure μ ν x) (g := g) (minimizer_spec T r μ g).1
  have he := moveMeasure_integral (F := integrand T r g (minimizer T r μ g)) (x := x) (μ := μ) hν1
  unfold objective at h
  change potential T r (moveMeasure μ ν x) g ≤ _ at h
  change _-r*(∑ y, μ y*integrand T r g (minimizer T r μ g) y) ≤ _
  calc _ ≤ r*(∑ y, moveMeasure μ ν x y*integrand T r g (minimizer T r μ g) y)-
      r*(∑ y, μ y*integrand T r g (minimizer T r μ g) y) := sub_le_sub_right h _
       _ = _ := by rw [← mul_sub, he]

lemma positive_drift_candidate {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hr : 0 ≤ r) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1) :
    max (potential T r (moveMeasure μ ν x) g-potential T r μ g) 0 ≤
      ∑ y, ν y*(r*max (integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) 0) := by
  apply max_le
  · calc _ ≤ r*∑ y, ν y*(integrand T r g (minimizer T r μ g) x-
          integrand T r g (minimizer T r μ g) y) := candidate_drift hν1
         _ ≤ r*∑ y, ν y*max (integrand T r g (minimizer T r μ g) x-
          integrand T r g (minimizer T r μ g) y) 0 := by
          apply mul_le_mul_of_nonneg_left _ hr
          exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hν y)
         _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro y _; ring
  · exact sum_nonneg fun y _ => mul_nonneg (hν y) (mul_nonneg hr (le_max_right _ _))

lemma positive_integrand_global {T : Template} {r : ℝ} {z g : Y → ℝ}
    (hr : 0 < r) (hg : ∀ y, g y ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) (hz : Feasible T r z) (x y : Y) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤ globalConstant T*dist x y := by
  have hd := integrand_diff_le (x := x) (y := y) hr hg hglip hz
  have hc0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hb : max (integrand T r g z x-integrand T r g z y) 0 ≤ globalConstant T*(dist x y/r) :=
    max_le hd (mul_nonneg hc0 (div_nonneg dist_nonneg hr.le))
  calc _ ≤ r*(globalConstant T*(dist x y/r)) := mul_le_mul_of_nonneg_left hb hr.le
       _ = _ := by field_simp

lemma positive_integrand_bounded {T : Template} {r : ℝ} {z g : Y → ℝ}
    (hr : 0 ≤ r) (hg : ∀ y, g y ∈ Set.Icc 0 1) (hz : Feasible T r z) (x y : Y) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤ 514*r := by
  have hb : max (integrand T r g z x-integrand T r g z y) 0 ≤ 514 :=
    max_le (by linarith [(integrand_bounds hz hg x).2, (integrand_bounds hz hg y).1]) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

lemma positive_integrand_local {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (100*T.R*r)\ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r)))
    (hxy : dist x y < T.σ*r/8) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤
      localConstant T*((mass μ (ball x (100*T.R*r)\ball x (γ*r))+innerMoment μ x γ r)/
        mass μ (ball x (γ*r)))*dist x y := by
  classical
  obtain ⟨_, s, hs, hsw, hun, hdef, hdisp, hsl⟩ :=
    local_structure hr hγ0 hγ hγL hδ hμ hg hglip hz hmin hM hconc
  have h := hsl y hxy
  apply (mul_le_mul_iff_left₀ hM).mp
  calc _ = r*(max (integrand T r g z x-integrand T r g z y) 0*mass μ (ball x (γ*r))) := by ring
       _ ≤ r*(localConstant T*(mass μ (ball x (100*T.R*r)\ball x (γ*r))+
          innerMoment μ x γ r)*(dist x y/r)) := mul_le_mul_of_nonneg_left h hr.le
       _ = _ := by
          have hM' : mass μ (ball x (r*γ)) ≠ 0 := by simpa [mul_comm] using hM.ne'
          field_simp [hr.ne', hM.ne', hM']


lemma mover_innerMass_half {μ ν : Y → ℝ} {x : Y} {γ r : ℝ}
    (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y) (hν1 : ∑ y, ν y=1)
    (hγ : 0 < γ) (hr : 0 < r) (he : 2*moveCost ν x ≤ γ*r) :
    1/2 ≤ mass μ (ball x (γ*r)) := by
  classical
  have hpoint : ∀ y, (γ*r)*ν y ≤ (if y ∈ ball x (γ*r) then (γ*r)*μ y else 0)+ν y*dist x y := by
    intro y
    by_cases hy : y ∈ ball x (γ*r)
    · rw [ite_eq_left hy]
      have := mul_le_mul_of_nonneg_left (hνμ y) (mul_pos hγ hr).le
      linarith [mul_nonneg (hν y) (dist_nonneg (x := x) (y := y))]
    · rw [ite_eq_right hy, zero_add]
      have hd : γ*r ≤ dist x y := le_of_lt (by simpa [ball] using hy)
      nlinarith [mul_le_mul_of_nonneg_left hd (hν y)]
  have hs := sum_le_sum (s := univ) fun y _ => hpoint y
  rw [← mul_sum, hν1, mul_one, sum_add_distrib, ← sum_filter] at hs
  simp only [filter_mem_eq_inter, Finset.univ_inter] at hs
  rw [← mul_sum] at hs
  change γ*r ≤ (γ*r)*mass μ (ball x (γ*r))+moveCost ν x at hs
  have hp := mul_pos hγ hr
  nlinarith

def shellRatio (μ : Y → ℝ) (x : Y) (γ D r : ℝ) : ℝ :=
  mass μ (ball x (D*r)\ball x (γ*r))/mass μ (ball x (γ*r))

def momentRatio (μ : Y → ℝ) (x : Y) (γ r : ℝ) : ℝ :=
  innerMoment μ x γ r/mass μ (ball x (γ*r))

lemma shellRatio_nonneg {μ : Y → ℝ} {x : Y} {γ D r : ℝ} (hμ : ∀ y, 0 ≤ μ y) :
    0 ≤ shellRatio μ x γ D r := div_nonneg (mass_nonneg hμ _) (mass_nonneg hμ _)

lemma momentRatio_nonneg {μ : Y → ℝ} {x : Y} {γ r : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hr : 0 ≤ r) : 0 ≤ momentRatio μ x γ r :=
  div_nonneg (sum_nonneg fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr)) (mass_nonneg hμ _)

def slopeBudget (T : Template) (δ h t : ℝ) : ℝ :=
  (globalConstant T/δ+localConstant T)*min 1 h+localConstant T*t

lemma slopeBudget_nonneg (T : Template) {δ h t : ℝ} (hδ : 0 ≤ δ) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    0 ≤ slopeBudget T δ h t := by
  unfold slopeBudget
  have hg0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  exact add_nonneg (mul_nonneg (add_nonneg (div_nonneg hg0 hδ) (localConstant_nonneg T))
    (le_min zero_le_one hh)) (mul_nonneg (localConstant_nonneg T) ht)

/-- A single estimate covers good and bad coarse radii. The exceptional far
point term is geometric and will be summed before integration. -/
lemma positive_integrand_coarse {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r))) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤
      slopeBudget T δ (shellRatio μ x γ (100*T.R) r) (momentRatio μ x γ r)*dist x y +
        (if r ≤ 8*dist x y/T.σ then 514*r else 0) := by
  classical
  let h := shellRatio μ x γ (100*T.R) r
  let t := momentRatio μ x γ r
  have hh : 0 ≤ h := shellRatio_nonneg hμ
  have ht : 0 ≤ t := momentRatio_nonneg hμ hr.le
  have hF : 0 ≤ (if r ≤ 8*dist x y/T.σ then 514*r else 0) := by split_ifs <;> positivity
  have hB : 0 ≤ slopeBudget T δ h t := slopeBudget_nonneg T hδ0.le hh ht
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  by_cases hgood : h ≤ δ
  · have h1 : h ≤ 1 := by linarith
    have hcoeff : localConstant T*(h+t) ≤ slopeBudget T δ h t := by
      unfold slopeBudget; rw [min_eq_right h1]
      have := mul_nonneg (div_nonneg hG hδ0.le) hh
      nlinarith
    by_cases hnear : dist x y < T.σ*r/8
    · have hconc : mass μ (ball x (100*T.R*r)\ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r)) := by
        exact (div_le_iff₀ hM).mp hgood
      have hl := positive_integrand_local hr hγ0 hγ hγL hδ hμ hg hglip hz hmin hM hconc hnear
      have he : (mass μ (ball x (100*T.R*r)\ball x (γ*r))+innerMoment μ x γ r)/
          mass μ (ball x (γ*r)) = h+t := by
        dsimp [h, t, shellRatio, momentRatio]; rw [add_div]
      rw [he] at hl
      exact hl.trans (le_trans (mul_le_mul_of_nonneg_right hcoeff dist_nonneg) (le_add_of_nonneg_right hF))
    · have hfar : r ≤ 8*dist x y/T.σ := (le_div_iff₀ T.σ_pos).mpr (by linarith)
      rw [ite_eq_left hfar]
      exact (positive_integrand_bounded hr.le hg hz x y).trans
        (le_add_of_nonneg_left (mul_nonneg hB dist_nonneg))
  · have hc : δ ≤ min 1 h := le_min (by linarith) (le_of_lt (lt_of_not_ge hgood))
    have hcoef : globalConstant T ≤ slopeBudget T δ h t := by
      have hbound := mul_le_mul_of_nonneg_left hc (div_nonneg hG hδ0.le)
      have he : (globalConstant T/δ)*δ=globalConstant T := by field_simp
      rw [he] at hbound
      have hmore := mul_nonneg (localConstant_nonneg T) (le_min zero_le_one hh)
      have hmoment := mul_nonneg (localConstant_nonneg T) ht
      unfold slopeBudget
      nlinarith
    exact (positive_integrand_global hr hg hglip hz x y).trans
      (le_trans (mul_le_mul_of_nonneg_right hcoef dist_nonneg) (le_add_of_nonneg_right hF))


def coarseBudget (T : Template) (γ δ k : ℝ) (p : ℕ) : ℝ :=
  (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
    localConstant T*(2*γ*(1+Real.log (2*k)))+8224/T.σ

lemma coarse_drift_sum {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ) (hγ : γ ≤ T.σ/64)
    (hγL : T.L*γ ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*τ^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤ coarseBudget T γ δ k p*moveCost ν x := by
  classical
  let B : ℕ → ℝ := fun j => slopeBudget T δ
    (shellRatio μ x γ (100*T.R) (radius r₀ τ j)) (momentRatio μ x γ (radius r₀ τ j))
  have hτ0 : 0 < τ := by linarith
  have hD : γ ≤ 100*T.R := by linarith [T.R_ge, T.σ_le]
  have hM : ∀ j, 0 < mass μ (ball x (γ*radius r₀ τ j)) := fun j =>
    (show (0:ℝ)<1/2 by norm_num).trans_le
      (hm0.trans (innerMass_mono (x := x) hμ hγ0.le hr.le (by linarith) (Nat.zero_le j)))
  have hB : ∑ j ∈ range n, B j ≤
      (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
        localConstant T*(2*γ*(1+Real.log (2*k))) := by
    simp only [B, slopeBudget, sum_add_distrib, ← mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (shell_scale_sum (x := x) n p hμ hγ0.le hr hτ hD hpow hm0 hk)
      (add_nonneg (div_nonneg (by linarith [globalConstant_ge T]) hδ0.le) (localConstant_nonneg T)))
      (mul_le_mul_of_nonneg_left (innerMoment_scale_sum (x := x) n hμ hγ0.le hr hτ hm0 hk)
        (localConstant_nonneg T))
  have hFar : ∀ y, ∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0) ≤
      (8224/T.σ)*dist x y := by
    intro y
    have he : (∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) =
        514*∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then radius r₀ τ j else 0) := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; split_ifs <;> ring
    rw [he]
    calc _ ≤ 514*(2*(8*dist x y/T.σ)) := mul_le_mul_of_nonneg_left
            (radius_truncated_sum hr.le hτ (div_nonneg (mul_nonneg (by norm_num) dist_nonneg) T.σ_pos.le) n) (by norm_num)
         _ = _ := by ring
  calc _ ≤ ∑ j ∈ range n, ∑ y, ν y*(B j*dist x y+
      (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) := by
        apply sum_le_sum; intro j hj
        have hjn := mem_range.mp hj
        apply (positive_drift_candidate (radius_pos hr hτ0 j).le hν hν1).trans
        apply sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left _ (hν y)
        exact positive_integrand_coarse (radius_pos hr hτ0 j) hγ0.le hγ hγL hδ0 hδ hμ
          (hg j hjn) (hgLip j hjn) (minimizer_spec T (radius r₀ τ j) μ (g j)).1
          (minimizer_spec T (radius r₀ τ j) μ (g j)).2 (hM j)
       _ = ∑ y, ν y*((∑ j ∈ range n, B j)*dist x y+
          ∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) := by
        rw [sum_comm]; apply sum_congr rfl; intro y _
        rw [← mul_sum, sum_add_distrib, sum_mul]
       _ ≤ ∑ y, ν y*(coarseBudget T γ δ k p*dist x y) := by
        apply sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left _ (hν y)
        calc _ ≤ ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
            localConstant T*(2*γ*(1+Real.log (2*k))))*dist x y+(8224/T.σ)*dist x y :=
              add_le_add (mul_le_mul_of_nonneg_right hB dist_nonneg) (hFar y)
             _ = _ := by unfold coarseBudget; ring
       _ = _ := by unfold moveCost; rw [mul_sum]; apply sum_congr rfl; intro y _; ring

lemma radius_shift (r₀ τ : ℝ) (m j : ℕ) : radius r₀ τ (m+j)=radius (radius r₀ τ m) τ j := by
  simp only [radius, pow_add]; ring

lemma positive_drift_bounded {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hr : 0 ≤ r) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1)
    (hg : ∀ y, g y ∈ Set.Icc 0 1) :
    max (potential T r (moveMeasure μ ν x) g-potential T r μ g) 0 ≤ 514*r := by
  calc _ ≤ ∑ y, ν y*(r*max (integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) 0) := positive_drift_candidate hr hν hν1
       _ ≤ ∑ y, ν y*(514*r) := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (positive_integrand_bounded hr hg (minimizer_spec T r μ g).1 x y) (hν y)
       _ = _ := by rw [← sum_mul, hν1, one_mul]

/-- Full positive drift sum, with the actual minimizer at each scale. The
ascending order is just a reversal of the finite geometric scale list. -/
theorem drift_sum {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ) (hγ : γ ≤ T.σ/64)
    (hγL : T.L*γ ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*τ^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y)
    (hν1 : ∑ y, ν y=1) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤
        (2056/γ+coarseBudget T γ δ k p)*moveCost ν x := by
  classical
  let e := moveCost ν x
  have he : 0 ≤ e := moveCost_nonneg hν
  have hτ0 : 0 < τ := by linarith
  let hE : ∃ m, m=n ∨ 2*e ≤ γ*radius r₀ τ m := ⟨n, Or.inl rfl⟩
  let m := Nat.find hE
  have hmn : m ≤ n := Nat.find_min' hE (Or.inl rfl)
  have hsmall : ∀ j < m, radius r₀ τ j ≤ 2*e/γ := by
    intro j hj
    have h := Nat.find_min hE hj
    have hn : ¬ 2*e ≤ γ*radius r₀ τ j := fun he => h (Or.inr he)
    apply (le_div_iff₀ hγ0).mpr
    linarith
  let Δ := fun j => max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0
  have hfine : ∑ j ∈ range m, Δ j ≤ (2056/γ)*e := by
    calc _ ≤ 514*∑ j ∈ range m, (if radius r₀ τ j ≤ 2*e/γ then radius r₀ τ j else 0) := by
          rw [mul_sum]; apply sum_le_sum; intro j hj
          rw [ite_eq_left (hsmall j (mem_range.mp hj))]
          exact positive_drift_bounded (radius_pos hr hτ0 j).le hν hν1
            (hg j ((mem_range.mp hj).trans_le hmn))
         _ ≤ 514*(2*(2*e/γ)) := mul_le_mul_of_nonneg_left
            (radius_truncated_sum hr.le hτ (div_nonneg (by linarith) hγ0.le) m) (by norm_num)
         _ = _ := by ring
  have hcoarse : ∑ j ∈ range (n-m), Δ (m+j) ≤ coarseBudget T γ δ k p*e := by
    by_cases hm : m=n
    · rw [hm, Nat.sub_self]
      simp only [range_zero, sum_empty]
      have hkhalf : 1/2 ≤ k := by
        have h := sum_le_sum (s := univ) fun y _ => hνμ y
        rw [hν1, hk] at h
        linarith
      have hlog : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
      have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
      have hC := localConstant_nonneg T
      have hσ := T.σ_pos
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact mul_nonneg (by unfold coarseBudget; positivity) he
    · have hecut : 2*e ≤ γ*radius r₀ τ m := (Nat.find_spec hE).resolve_left hm
      have hmass : 1/2 ≤ innerMass μ x γ (radius r₀ τ m) τ 0 := by
        simpa [innerMass, radius] using mover_innerMass_half hν hνμ hν1 hγ0 (radius_pos hr hτ0 m) hecut
      have h := coarse_drift_sum (x := x) (fun j => g (m+j)) (n-m) p (radius_pos hr hτ0 m)
        hτ hγ0 hγ hγL hδ0 hδ hpow hμ hν hν1 hmass hk
        (fun j hj => hg (m+j) (by omega))
        (fun j hj => by simpa [radius_shift] using hgLip (m+j) (by omega))
      simpa [Δ, e, radius_shift] using h
  have hnm : n=m+(n-m) := by omega
  change ∑ j ∈ range n, Δ j ≤ _
  conv_lhs => rw [hnm, sum_range_add]
  calc _ ≤ (2056/γ)*e+coarseBudget T γ δ k p*e := add_le_add hfine hcoarse
       _ = _ := by ring


def driftConstant (T : Template) (γ δ : ℝ) (p : ℕ) : ℝ :=
  2056/γ + 8224/T.σ + 2*globalConstant T*p/(δ*Real.log 2)+
    2*localConstant T*((p:ℝ)/Real.log 2+2*γ)

lemma driftConstant_nonneg (T : Template) {γ δ : ℝ} (p : ℕ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) :
    0 ≤ driftConstant T γ δ p := by
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hC := localConstant_nonneg T
  have hσ := T.σ_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold driftConstant
  positivity

lemma log_k_bound {k : ℝ} (hk : 1 ≤ k) :
    0 ≤ Real.log (k+1) ∧ 1+Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by
  have hk0 : 0 < k := by linarith
  have hl := Real.log_nonneg (show 1 ≤ k+1 by linarith)
  have hlog := Real.log_le_log hk0 (show k ≤ k+1 by linarith)
  have hl2 := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hk0.ne']
  exact ⟨hl, by linarith⟩

lemma driftBudget_le {T : Template} {γ δ k : ℝ} (p : ℕ)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hk : 1 ≤ k) :
    2056/γ+coarseBudget T γ δ k p ≤ driftConstant T γ δ p*(1+Real.log (k+1)) := by
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hC := localConstant_nonneg T
  have hσ := T.σ_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := log_k_bound hk
  have hbase : 2056/γ+8224/T.σ ≤ (2056/γ+8224/T.σ)*(1+Real.log (k+1)) := by
    have he : 0 ≤ 2056/γ+8224/T.σ := by positivity
    nlinarith [mul_nonneg he hlog.1]
  have hs : (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k)) ≤
      ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2))*(2*(1+Real.log (k+1))) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith [hlog.2]) (by positivity)
  have ht : localConstant T*(2*γ*(1+Real.log (2*k))) ≤
      (localConstant T*(2*γ))*(2*(1+Real.log (k+1))) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog.2 (by positivity)
  unfold coarseBudget driftConstant
  calc _ ≤ (2056/γ+8224/T.σ)*(1+Real.log (k+1))+
      ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2))*(2*(1+Real.log (k+1)))+
        (localConstant T*(2*γ))*(2*(1+Real.log (k+1))) := by linarith
       _ = _ := by ring

/-- Section06's drift inequality with the stated dimension-free constant.
The sole scale parameter p only needs the displayed fixed geometric offset. -/
theorem pilot_drift {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y)
    (hν1 : ∑ y, ν y=1) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤
        driftConstant T γ δ p*(1+Real.log (k+1))*moveCost ν x := by
  have hk1 : 1 ≤ k := by
    have h := sum_le_sum (s := univ) fun y _ => hνμ y
    rwa [hν1, hk] at h
  have hγL : T.L*γ ≤ 1 := by
    have h := (le_div_iff₀ (show 0<1+T.L by linarith [T.L_nonneg])).mp (le_min_iff.mp hγ).2
    nlinarith
  have hpow' : 100*T.R ≤ γ*τ^p := hpow.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) hτ p) hγ0.le)
  exact (drift_sum g n p hr hτ hγ0 (le_min_iff.mp hγ).1 hγL hδ0 hδ hpow'
    hμ hν hνμ hν1 hk hg hgLip).trans (mul_le_mul_of_nonneg_right
      (driftBudget_le p hγ0.le hδ0.le hk1) (moveCost_nonneg hν))

/-- A finite weighted average obeys the filtering inequality directly by
comparing all posterior minima to the single old minimizer. This is the exact
concavity argument, without an assumed filtering/policy interface. -/
lemma potential_average {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (_ : ∑ ω, w ω=1) (T : Template) (r : ℝ) (g : Y → ℝ) (μ : Ω → Y → ℝ) :
    ∑ ω, w ω*potential T r (μ ω) g ≤
      potential T r (fun y => ∑ ω, w ω*μ ω y) g := by
  let z := minimizer T r (fun y => ∑ ω, w ω*μ ω y) g
  have hz := (minimizer_spec T r (fun y => ∑ ω, w ω*μ ω y) g).1
  calc _ ≤ ∑ ω, w ω*objective T r (μ ω) g z :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (potential_le hz) (hw ω)
       _ = objective T r (fun y => ∑ ω, w ω*μ ω y) g z := by
        unfold objective
        simp only [sum_mul, mul_sum, mul_left_comm (w _ ) r]
        rw [sum_comm]
        apply sum_congr rfl; intro y _
        apply sum_congr rfl; intro ω _; ring
       _ = _ := rfl

end KServer.Pilot

end
end

end OAI
