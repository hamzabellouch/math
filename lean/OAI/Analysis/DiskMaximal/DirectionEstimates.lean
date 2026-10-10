import OAI.Analysis.DiskMaximal.DirectionLaws

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DirectionNeighbors
open DyadicHats Finset

/-- The complete fixed grid window. No spatial observation enters the choices. -/
def window (d : ℕ) (q : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (q.1-d) (q.1+d)).product (Finset.Icc (q.2-d) (q.2+d))

lemma self_mem_window (d : ℕ) (q : ℤ × ℤ) : q ∈ window d q := by
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
    Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

lemma mem_window_iff {r : ℝ} (hr : 0 < r) (d : ℕ) (q z : ℤ × ℤ) :
    z ∈ window d q ↔ boxNorm (point r z-point r q) ≤ (d:ℝ)*r := by
  have hh (a b : ℤ) : |r*a-r*b| ≤ (d:ℝ)*r ↔ b-(d:ℤ) ≤ a ∧ a ≤ b+d := by
    rw [← mul_sub,abs_mul,abs_of_pos hr,mul_comm (d:ℝ) r,mul_le_mul_iff_right₀ hr]
    have hc : |(a:ℝ)-(b:ℝ)| ≤ (d:ℝ) ↔ |a-b| ≤ (d:ℤ) := by
      exact_mod_cast Iff.rfl
    rw [hc,abs_le]
    omega
  change (_ ∈ ((Finset.Icc _ _) ×ˢ (Finset.Icc _ _))) ↔ max _ _ ≤ _
  rw [Finset.mem_product,Finset.mem_Icc,Finset.mem_Icc,max_le_iff]
  exact (hh _ _).symm.and (hh _ _).symm

private lemma max_exists (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) :
    ∃ z ∈ window d q, ∀ z' ∈ window d q, f z' ≤ f z :=
  Finset.exists_max_image (window d q) f ⟨q,self_mem_window d q⟩

def maxVertex (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) : ℤ × ℤ :=
  Classical.choose (max_exists f d q)
lemma maxVertex_mem (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) :
    maxVertex f d q ∈ window d q := (Classical.choose_spec (max_exists f d q)).1
lemma le_maxVertex (f : ℤ × ℤ → ℝ) (d : ℕ) (q : ℤ × ℤ) {z : ℤ × ℤ}
    (hz : z ∈ window d q) : f z ≤ f (maxVertex f d q) :=
  (Classical.choose_spec (max_exists f d q)).2 z hz

def chosen (h : ℂ → ℂ) (r : ℝ) : ℤ × ℤ → ℤ × ℤ := maxVertex (scalarMass h r) 300

def theta (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℂ :=
  IntrinsicMarks.direction 1 (vectorMass h r q)
def Theta (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) : ℂ := theta h r (chosen h r z)

def worstVertex (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℤ × ℤ :=
  maxVertex (fun z => ‖Theta h r z-theta h r q‖^2) 200 q

def energy (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ℝ :=
  ‖Theta h r (worstVertex h r q)-theta h r q‖^2

lemma norm_theta (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : ‖theta h r q‖ = 1 :=
  IntrinsicMarks.norm_direction (by norm_num) _
lemma energy_nonneg (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : 0 ≤ energy h r q := sq_nonneg _
lemma energy_le_four (h : ℂ → ℂ) (r : ℝ) (q : ℤ × ℤ) : energy h r q ≤ 4 := by
  have hn := norm_sub_le (Theta h r (worstVertex h r q)) (theta h r q)
  simp only [Theta,norm_theta] at hn
  change ‖theta h r (chosen h r (worstVertex h r q))-theta h r q‖^2 ≤ 4
  nlinarith [norm_nonneg (theta h r (chosen h r (worstVertex h r q))-theta h r q)]

lemma energy_controls {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q z : ℤ × ℤ)
    (hz : boxNorm (point r z-point r q) ≤ 200*r) :
    ‖Theta h r z-theta h r q‖^2 ≤ energy h r q := by
  apply le_maxVertex (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  exact (mem_window_iff hr 200 q z).mpr (by simpa using hz)

lemma worstVertex_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    boxNorm (point r (worstVertex h r q)-point r q) ≤ 200*r := by
  have hm := maxVertex_mem (fun z => ‖Theta h r z-theta h r q‖^2) 200 q
  simpa only [worstVertex,Nat.cast_ofNat] using (mem_window_iff hr 200 q _).mp hm

lemma chosen_near {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (z : ℤ × ℤ) :
    boxNorm (point r (chosen h r z)-point r z) ≤ 300*r := by
  simpa only [chosen,Nat.cast_ofNat] using
    (mem_window_iff hr 300 z _).mp (maxVertex_mem (scalarMass h r) 300 z)

/-- The actual chosen neighbor supplies at least the root's mass and is within
500 fine-grid units, precisely the inputs spent by the coarse triangle defect. -/
lemma worst_chosen_spec {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ) :
    scalarMass h r q ≤ scalarMass h r (chosen h r (worstVertex h r q)) ∧
    boxNorm (point r (chosen h r (worstVertex h r q))-point r q) ≤ 500*r := by
  let z := worstVertex h r q
  have hz : boxNorm (point r z-point r q) ≤ 200*r := worstVertex_near hr h q
  have hz' : boxNorm (point r q-point r z) ≤ 300*r := by
    rw [boxNorm_sub_comm]
    linarith
  have ha := le_maxVertex (scalarMass h r) 300 z ((mem_window_iff hr 300 z q).mpr (by simpa using hz'))
  have hw := chosen_near hr h z
  have ht := boxNorm_add_le (point r (chosen h r z)-point r z) (point r z-point r q)
  rw [sub_add_sub_cancel] at ht
  exact ⟨ha,by linarith⟩

end DirectionNeighbors

namespace DirectionNeighbors
open DyadicHats

lemma vectorMass_mem_grid {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    {q : ℤ × ℤ} (hq : vectorMass h r q ≠ 0) : q ∈ indexBox N := by
  by_contra hn
  apply hq
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : h y=0
  · simp only [hy,smul_zero,Pi.zero_apply]
  · have hh : hat r q y=0 := by
      by_contra hz
      exact hn (mem_indexBox_of_le hr hN (hs y hy) hz)
    simp only [hh,zero_smul,Pi.zero_apply]

/-- The literal triangle defect over twelve positive refinements. -/
def coarseDefect (N : ℕ) (h : ℂ → ℂ) (r : ℝ) (d : ℕ) (p : Grid N) : ℝ :=
  (∑ q : Grid N, coeff N d p q*scalarMass h r q)-scalarMass h (scale r d) p

lemma direction_refine {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    scalarMass h (scale r d) p • theta h (scale r d) p =
      ∑ q : Grid N, (coeff N d p q*scalarMass h r q) • theta h r q := by
  rw [show scalarMass h (scale r d) p • theta h (scale r d) p =
    vectorMass h (scale r d) p from IntrinsicMarks.mass_direction 1 _]
  rw [vectorMass_coeff hr hR hN hh hs]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_smul]
  congr 1
  exact (IntrinsicMarks.mass_direction 1 _).symm

lemma coarseDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (d : ℕ) (p : Grid N) :
    0 ≤ coarseDefect N h r d p := by
  have he := VectorRefinement.quadratic_defect (coeff N d p) (fun q : Grid N => scalarMass h r q)
    (fun q : Grid N => theta h r q) (theta h (scale r d) p) (scalarMass h (scale r d) p)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _) (direction_refine hr hR hN hh hs d p)
  rw [coarseDefect,he]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (coeff_nonneg _ _ _ _) (norm_nonneg _)) (sq_nonneg _)

lemma coarseDefect_sum (N : ℕ) (h : ℂ → ℂ) (r : ℝ) (d : ℕ) :
    (∑ p : Grid N, coarseDefect N h r d p) =
      (∑ q : Grid N, scalarMass h r q)-(∑ p : Grid N, scalarMass h (scale r d) p) := by
  simp only [coarseDefect,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,coeff_column,one_mul]

def parent (N : ℕ) (q : Grid N) : Grid N := ⟨nearParent q,nearParent_mem q.property⟩

/-- The actual maximally differing neighbor spends true vector cancellation,
not an independently postulated directional budget. -/
lemma neighbor_charge {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (q : Grid N) :
    scalarMass h r q*energy h r q ≤ 48*coarseDefect N h r 12 (parent N q) := by
  by_cases hq : scalarMass h r q=0
  · rw [hq,zero_mul]
    exact mul_nonneg (by norm_num) (coarseDefect_nonneg hr hR hN hh hs 12 _)
  have hqpos : 0 < scalarMass h r q := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
  let z := chosen h r (worstVertex h r q)
  have hz := worst_chosen_spec hr h q
  have hzpos : 0 < scalarMass h r z := hqpos.trans_le hz.1
  have hzmem : z ∈ indexBox N := vectorMass_mem_grid hr hN hs (norm_ne_zero_iff.mp (ne_of_gt hzpos))
  let s : Grid N := ⟨z,hzmem⟩
  have hweights := nearParent_hat_lower hr q z hz.2
  have hwq : 1/4 ≤ coeff N 12 (parent N q) q := by
    rw [coeff_eq_hat hr]
    exact hweights.1
  have hws : 9/64 ≤ coeff N 12 (parent N q) s := by
    rw [coeff_eq_hat hr]
    exact hweights.2
  have he := VectorRefinement.pair_defect_bound (coeff N 12 (parent N q))
    (fun p : Grid N => scalarMass h r p) (fun p : Grid N => theta h r p)
    (theta h (scale r 12) (parent N q)) (scalarMass h (scale r 12) (parent N q))
    (fun p => coeff_nonneg N 12 _ p) (fun _ => norm_nonneg _)
    (norm_theta _ _ _) (fun _ => norm_theta _ _ _)
    (direction_refine hr hR hN hh hs 12 _) hwq hws hz.1
  change scalarMass h r q*‖theta h r z-theta h r q‖^2 ≤ _
  rw [norm_sub_rev]
  exact he

lemma parent_fiber_card (N : ℕ) (p : Grid N) :
    (Finset.univ.filter (fun q : Grid N => parent N q=p)).card ≤ 4097^2 := by
  let F := Finset.univ.filter (fun q : Grid N => parent N q=p)
  let e : Grid N ↪ ℤ × ℤ := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : F.map e ⊆ (indexBox N).filter (fun q => nearParent q=p.val) := by
    intro q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨s.property,congrArg Subtype.val (Finset.mem_filter.mp hs).2⟩
  calc
    _ = (F.map e).card := (Finset.card_map e).symm
    _ ≤ ((indexBox N).filter (fun q => nearParent q=p.val)).card := Finset.card_le_card hm
    _ ≤ 4097^2 := nearParent_fiber_card _ _

lemma parent_sum_bound (N : ℕ) (a : Grid N → ℝ) (ha : ∀ p, 0 ≤ a p) :
    (∑ q : Grid N, a (parent N q)) ≤ (4097:ℝ)^2*∑ p : Grid N, a p := by
  rw [← Finset.sum_fiberwise Finset.univ (parent N) (fun q => a (parent N q)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q => parent N q=p), a p := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = ((Finset.univ.filter (fun q => parent N q=p)).card:ℝ)*a p := by simp
    _ ≤ (4097:ℝ)^2*a p := by
      apply mul_le_mul_of_nonneg_right _ (ha p)
      exact_mod_cast parent_fiber_card N p

/-- Uniform one-scale neighbor energy bound by the actual twelve-scale mass drop. -/
theorem level_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, scalarMass h r q*energy h r q) ≤
      (48*(4097:ℝ)^2)*((∑ q : Grid N, scalarMass h r q)-
        ∑ p : Grid N, scalarMass h (scale r 12) p) := by
  have h1 := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Grid N))) =>
    neighbor_charge hr hR hN hh hs q)
  have h2 := parent_sum_bound N (coarseDefect N h r 12)
    (fun p => coarseDefect_nonneg hr hR hN hh hs 12 p)
  rw [← Finset.mul_sum] at h1
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 48))
  rw [coarseDefect_sum] at h3
  simpa only [mul_assoc] using h3

end DirectionNeighbors

namespace DirectionNeighbors
open DyadicHats
lemma scale_scale (r : ℝ) (k d : ℕ) : scale (scale r k) d = scale r (k+d) := by
  simp only [scale,pow_add]
  ring

lemma shifted_mass_bound (A : ℕ → ℝ) {V : ℝ} (h0 : ∀ k, 0 ≤ A k)
    (hV : ∀ k, A k ≤ V) (m d : ℕ) :
    (∑ k ∈ Finset.range m, (A k-A (k+d))) ≤ d*V := by
  have he : (∑ k ∈ Finset.range m, A k)+(∑ k ∈ Finset.range d, A (k+m)) =
      (∑ k ∈ Finset.range d, A k)+(∑ k ∈ Finset.range m, A (k+d)) := by
    calc
      _ = ∑ k ∈ Finset.range (m+d), A k := by
        simpa only [Nat.add_comm] using (Finset.sum_range_add A m d).symm
      _ = ∑ k ∈ Finset.range (d+m), A k := by rw [Nat.add_comm m d]
      _ = _ := by simpa only [Nat.add_comm] using Finset.sum_range_add A d m
  have hprefix : (∑ k ∈ Finset.range d, A k) ≤ d*V := by
    calc
      _ ≤ ∑ _k ∈ Finset.range d, V := Finset.sum_le_sum (fun k _ => hV k)
      _ = _ := by simp
  have htail : 0 ≤ ∑ k ∈ Finset.range d, A (k+m) := Finset.sum_nonneg (fun k _ => h0 _)
  rw [Finset.sum_sub_distrib]
  linarith

theorem neighbor_energy_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∑ q : Grid N,
      scalarMass h (scale r k) q*energy h (scale r k) q) ≤
      (576*(4097:ℝ)^2)*(∫ y, ‖h y‖) := by
  let A := fun k => ∑ q : Grid N, scalarMass h (scale r k) q
  have he (k : ℕ) :
      (∑ q : Grid N, scalarMass h (scale r k) q*energy h (scale r k) q) ≤
        (48*(4097:ℝ)^2)*(A k-A (k+12)) := by
    simpa only [scale_scale] using level_energy_budget (scale_pos hr k) hR
      (scale_index_bound hr hR hN k) hh hs
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range m) => he k)
  rw [← Finset.mul_sum] at hsum
  have hA0 (k : ℕ) : 0 ≤ A k := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hAV (k : ℕ) : A k ≤ ∫ y, ‖h y‖ := sum_scalarMass_grid_le hh _
  have hb := shifted_mass_bound A hA0 hAV m 12
  have hf := hsum.trans (mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 48*(4097:ℝ)^2))
  norm_num at hf ⊢
  nlinarith only [hf]
end DirectionNeighbors

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace ConeCoordinates

def axis (n : ℂ) (s : ℝ) : ℂ := (Real.sqrt 3/2) • n + (s/2) • (Complex.I*n)
def coordinate (n : ℂ) (s : ℝ) : ℂ →L[ℝ] ℝ :=
  (1 / Real.sqrt 3) • innerSL ℝ n + s • innerSL ℝ (Complex.I*n)

lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt3_sq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
lemma sqrt3_bounds : 3/2 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 := by
  have := sqrt3_sq
  have := sqrt3_pos
  constructor <;> nlinarith
lemma inner_re (n z : ℂ) : inner ℝ n z = (star n*z).re := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re]
  ring
lemma inner_im (n z : ℂ) : inner ℝ (Complex.I*n) z = (star n*z).im := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.mul_re, Complex.mul_im]
  ring
lemma mul_star_of_unit {n : ℂ} (hn : ‖n‖ = 1) : n * star n = 1 := by
  simpa [Complex.normSq_eq_norm_sq, hn] using Complex.mul_conj n
lemma coordinate_apply (n z : ℂ) (s : ℝ) :
    coordinate n s z = (star n*z).re / Real.sqrt 3 + s*(star n*z).im := by
  change (1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z = _
  rw [inner_re,inner_im]
  ring
lemma expansion {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) = z := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos
  have hz : n*(star n*z) = z := by rw [← mul_assoc,mul_star_of_unit hn,one_mul]
  have he : coordinate n 1 z • axis n 1 + coordinate n (-1) z • axis n (-1) =
      n*(star n*z) := by
    apply Complex.ext <;> simp [axis,coordinate_apply,Complex.mul_re,Complex.mul_im] <;> field_simp <;> ring
  exact he.trans hz
lemma axis_norm {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    ‖axis n s‖ = 1 := by
  have he : axis n s = (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I)*n := by
    apply Complex.ext <;> simp [axis,Complex.mul_re,Complex.mul_im]; ring
  rw [he,norm_mul,hn,mul_one]
  have hsq := sqrt3_sq
  have h : Complex.normSq (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I) = 1 := by
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith
  have hn0 := norm_nonneg (↑(Real.sqrt 3/2)+(↑s/2)*Complex.I : ℂ)
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith
lemma inner_axis (n z : ℂ) (s : ℝ) :
    inner ℝ (axis n s) z = Real.sqrt 3/2 * inner ℝ n z + s/2*inner ℝ (Complex.I*n) z := by
  simp only [axis,inner_add_left,real_inner_smul_left]
lemma coordinate_norm_le {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : |s| ≤ 1) (z : ℂ) :
    |coordinate n s z| ≤ 2 * ‖z‖ := by
  have ha : |inner ℝ n z| ≤ ‖z‖ := by simpa [hn] using abs_real_inner_le_norm n z
  have hb : |inner ℝ (Complex.I*n) z| ≤ ‖z‖ := by
    simpa [norm_mul,hn] using abs_real_inner_le_norm (Complex.I*n) z
  have hr : 1 / Real.sqrt 3 ≤ 1 := by rw [div_le_one sqrt3_pos]; linarith [sqrt3_bounds]
  have hnon : 0 ≤ 1 / Real.sqrt 3 := (div_pos (by norm_num) sqrt3_pos).le
  calc
    |coordinate n s z| ≤ (1/Real.sqrt 3)*|inner ℝ n z| + |s| *|inner ℝ (Complex.I*n) z| := by
      change |(1/Real.sqrt 3)*inner ℝ n z + s*inner ℝ (Complex.I*n) z| ≤ _
      simpa only [abs_mul,abs_of_nonneg hnon] using
        abs_add_le ((1/Real.sqrt 3)*inner ℝ n z) (s*inner ℝ (Complex.I*n) z)
    _ ≤ 1*‖z‖+1*‖z‖ := add_le_add (mul_le_mul hr ha (abs_nonneg _) (by norm_num))
      (mul_le_mul hs hb (abs_nonneg _) (by norm_num))
    _ = 2*‖z‖ := by ring

/-- Closed sector between the literal two palette axes. -/
def Good (n z : ℂ) : Prop := 0 ≤ coordinate n 1 z ∧ 0 ≤ coordinate n (-1) z

lemma good_of_close {n z : ℂ} (hn : ‖n‖ = 1) (hclose : ‖z-n‖ ≤ 1/10) : Good n z := by
  have ha : |inner ℝ n (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm n (z-n)
    simp only [hn,one_mul] at h
    exact h.trans hclose
  have hb : |inner ℝ (Complex.I*n) (z-n)| ≤ 1/10 := by
    have h := abs_real_inner_le_norm (Complex.I*n) (z-n)
    simp only [norm_mul,Complex.norm_I,hn,one_mul] at h
    exact h.trans hclose
  have hin : inner ℝ n n = 1 := by simp [hn]
  have hip : inner ℝ (Complex.I*n) n = 0 := by
    rw [inner_im,show star n*n = 1 by simpa [mul_comm] using mul_star_of_unit hn]
    simp
  simp only [inner_sub_right,hin,hip,sub_zero] at ha hb
  have hab := (abs_le.mp ha).1
  have hbb := abs_le.mp hb
  have hs := sqrt3_bounds
  have ha' : 1/10 ≤ inner ℝ n z / Real.sqrt 3 := by
    apply (le_div_iff₀ sqrt3_pos).2
    nlinarith
  change 0 ≤ (1/Real.sqrt 3)*inner ℝ n z + 1*inner ℝ (Complex.I*n) z ∧
    0 ≤ (1/Real.sqrt 3)*inner ℝ n z + (-1)*inner ℝ (Complex.I*n) z
  have hei : (1/Real.sqrt 3)*inner ℝ n z = inner ℝ n z / Real.sqrt 3 := by ring
  rw [hei]
  constructor <;> nlinarith

lemma inner_quarter_self {n : ℂ} (hn : ‖n‖ = 1) : inner ℝ (Complex.I*n) n = 0 := by
  rw [inner_im,show star n*n = 1 by simpa [mul_comm] using mul_star_of_unit hn]
  simp
lemma axes_inner {n : ℂ} (hn : ‖n‖ = 1) : inner ℝ (axis n 1) (axis n (-1)) = 1/2 := by
  rw [inner_axis]
  simp only [axis,inner_add_right,real_inner_smul_right]
  have hnn : inner ℝ n n = 1 := by simp [hn]
  have hnp : inner ℝ n (Complex.I*n) = 0 := by rw [real_inner_comm]; exact inner_quarter_self hn
  have hpn := inner_quarter_self hn
  have hpp : inner ℝ (Complex.I*n) (Complex.I*n) = 1 := by simp [hn]
  rw [hnn,hnp,hpn,hpp]
  nlinarith [sqrt3_sq]
lemma norm_le_coords {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    ‖z‖ ≤ |inner ℝ n z|+|inner ℝ (Complex.I*n) z| := by
  have hnorm : ‖star n*z‖ = ‖z‖ := by simp [hn]
  rw [inner_re,inner_im,← hnorm]
  exact Complex.norm_le_abs_re_add_abs_im _

theorem cone_algebra {n : ℂ} (hn : ‖n‖ = 1) (z : ℂ) :
    ‖z‖ ≤ 12*(inner ℝ n z + max 0 (-inner ℝ (axis n 1) z) +
      max 0 (-inner ℝ (axis n (-1)) z)) := by
  let a := inner ℝ n z
  let b := inner ℝ (Complex.I*n) z
  let u := max 0 (-inner ℝ (axis n 1) z)
  let v := max 0 (-inner ℝ (axis n (-1)) z)
  have hu0 : 0 ≤ u := le_max_left _ _
  have hv0 : 0 ≤ v := le_max_left _ _
  have hu : -(Real.sqrt 3/2*a+1/2*b) ≤ u := by simpa only [u,v,a,b,inner_axis] using le_max_right 0 (-inner ℝ (axis n 1) z)
  have hv : -(Real.sqrt 3/2*a+(-1)/2*b) ≤ v := by simpa only [u,v,a,b,inner_axis] using le_max_right 0 (-inner ℝ (axis n (-1)) z)
  have hs := sqrt3_bounds
  have ha : |a| ≤ 2*(a+u+v) := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      have hmul := mul_le_mul_of_nonpos_right hs.1 (le_of_not_ge h)
      nlinarith
  have hb : |b| ≤ 2*(u+v)+2*|a| := by
    have haa : Real.sqrt 3*a ≤ 2*|a| :=
      (mul_le_mul_of_nonneg_left (le_abs_self a) sqrt3_pos.le).trans
        (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg a))
    apply abs_le.2
    constructor <;> linarith
  have hz := norm_le_coords hn z
  change ‖z‖ ≤ 12*(a+u+v)
  change ‖z‖ ≤ |a|+|b| at hz
  have := neg_le_abs a
  linarith

/-- A finite fixed palette, all members genuinely on the unit circle. -/
structure Palette where
  labels : Finset ℂ
  unit : ∀ n ∈ labels, ‖n‖ = 1
  cover : ∀ z : ℂ, ‖z‖ = 1 → ∃ n ∈ labels, ‖z-n‖ < 1/2000

lemma exists_palette : Nonempty Palette := by
  classical
  let S := Metric.sphere (0 : ℂ) 1
  have hc : IsCompact S := isCompact_sphere 0 1
  obtain ⟨t,hts,htfin,ht⟩ := hc.elim_finite_subcover_image (fun n (_ : n ∈ S) => Metric.isOpen_ball (x := n) (ε := (1/2000:ℝ))) (by
      intro z hz
      exact Set.mem_iUnion₂.2 ⟨z,hz,by simp⟩)
  refine ⟨⟨htfin.toFinset,?_,?_⟩⟩
  · intro n hn
    simpa [S,Metric.mem_sphere,dist_zero_right] using hts (htfin.mem_toFinset.mp hn)
  · intro z hz
    have hzS : z ∈ S := by simpa [S,Metric.mem_sphere,dist_zero_right] using hz
    obtain ⟨n,hn,hzn⟩ := Set.mem_iUnion₂.mp (ht hzS)
    exact ⟨n,htfin.mem_toFinset.mpr hn,by simpa [Metric.mem_ball,dist_eq_norm] using hzn⟩

def fixedPalette : Palette := Classical.choice exists_palette

def quantize (z : ℂ) (hz : ‖z‖ = 1) : {n : ℂ // n ∈ fixedPalette.labels} :=
  ⟨Classical.choose (fixedPalette.cover z hz), (Classical.choose_spec (fixedPalette.cover z hz)).1⟩
lemma quantize_close (z : ℂ) (hz : ‖z‖ = 1) : ‖z-(quantize z hz : ℂ)‖ < 1/2000 :=
  (Classical.choose_spec (fixedPalette.cover z hz)).2

end ConeCoordinates

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset

def tree {N : ℕ} (v : Grid N → ℂ) : ℕ → ℝ → Grid N → Tree (Grid N) ℂ
  | 0,b,p => .leaf (b • v p)
  | k+1,b,p => .branch (fun q => tree v k (b*step p q) q)

lemma vector_tree {N : ℕ} (v : Grid N → ℂ) (k : ℕ) (b : ℝ) (p : Grid N) :
    vector (tree v k b p) = b • ∑ q : Grid N, coeff N k p q • v q := by
  induction k generalizing b p with
  | zero => simp [tree,vector,coeff]
  | succ k ih =>
    simp only [tree,vector,ih,coeff,smul_sum,sum_smul,smul_smul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro a ha
    congr 1
    ring

lemma terminalMass_tree {N : ℕ} (v : Grid N → ℂ) (k : ℕ) {b : ℝ} (hb : 0 ≤ b) (p : Grid N) :
    terminalMass (tree v k b p) = b * ∑ q : Grid N, coeff N k p q * ‖v q‖ := by
  induction k generalizing b p with
  | zero => simp [tree,terminalMass,coeff,Real.norm_eq_abs,abs_of_nonneg hb]
  | succ k ih =>
    simp only [tree,terminalMass]
    simp_rw [ih (mul_nonneg hb (step_nonneg _ _)),coeff,mul_sum,sum_mul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro q hq
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    ring

lemma sum_terminalMass {N : ℕ} (v : Grid N → ℂ) (k : ℕ) :
    (∑ p : Grid N, terminalMass (tree v k 1 p)) = ∑ q : Grid N, ‖v q‖ := by
  simp_rw [terminalMass_tree v k (by norm_num : (0:ℝ) ≤ 1),one_mul]
  rw [Finset.sum_comm]
  simp_rw [← sum_mul,coeff_column,one_mul]

lemma vector_actual {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (b : ℝ) (p : Grid N) :
    vector (tree (fun q : Grid N => vectorMass h r q) k b p) =
      b • vectorMass h (scale r k) p := by
  rw [vector_tree,← vectorMass_coeff hr hR hN hh hs]

/-- The actual finite dyadic vector forest satisfies the intrinsic mark budget.
The roots, terminal masses and every intermediate vector are their true hat
integrals; no abstract mark budget is supplied as a hypothesis. -/
theorem mark_budget {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    (∑ p : Grid N, costWithRoot (1:ℂ) δ
      (tree (fun q : Grid N => vectorMass h r q) k 1 p)) ≤
        (1+2/δ^2)*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ p : Grid N, (1+2/δ^2)*terminalMass
      (tree (fun q : Grid N => vectorMass h r q) k 1 p) :=
        sum_le_sum (fun _ _ => costWithRoot_le (by simp) hδ _)
    _ = (1+2/δ^2)*(∑ q : Grid N, scalarMass h r q) := by
      rw [← mul_sum,sum_terminalMass]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_scalarMass_grid_le hh r) (by positivity)

end ActualMarkTrees

end
end

end OAI
