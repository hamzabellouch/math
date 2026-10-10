import OAI.Analysis.SignedDisk.DyadicHats3

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

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

namespace ScalarCancellation
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
lemma roots_nonneg_of_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι)
    (hm : 0 ≤ ∫ x, refined w f k q x ∂μ) : ∀ x, 0 ≤ roots μ w f k q x := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.2.2.1 hm
  | succ k =>
    have hi := integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s))
    have hs := root_spec hi
    have he := roots_mass w hf (k+1) q
    change (∫ x, root μ _ x ∂μ) = _ at he
    rw [hs.2.1] at he
    exact hs.2.2.2.2.1 (by rw [he]; exact hm)
end ScalarCancellation

namespace ConeScalar
open ConeCoordinates DyadicHats IntrinsicMarks

lemma scalar_integrable {h : ℂ → ℂ} (hh : Integrable h) (c : ℂ →L[ℝ] ℝ) :
    Integrable (fun x => c (h x)) := c.integrable_comp hh
lemma scalar_support {h : ℂ → ℂ} {R : ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (c : ℂ →L[ℝ] ℝ) : ∀ y, c (h y) ≠ 0 → ‖y‖ ≤ R := by
  intro y hy
  exact hs y (fun h => hy (by simp [h]))
lemma scalar_mass {h : ℂ → ℂ} (hh : Integrable h) (c : ℂ →L[ℝ] ℝ) (r : ℝ) (q : ℤ × ℤ) :
    (∫ y, hat r q y*c (h y)) = c (vectorMass h r q) := by
  have he := c.integral_comp_comm (integrable_hat_smul hh r q)
  simpa only [map_smul,smul_eq_mul,vectorMass] using he

lemma coordinate_mass_nonneg {n v : ℂ}
    (hg : Good n (direction 1 v)) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    0 ≤ coordinate n s v := by
  have he := congrArg (coordinate n s) (mass_direction (1:ℂ) v)
  rw [map_smul,smul_eq_mul] at he
  rw [← he]
  exact mul_nonneg (norm_nonneg _) (hs.elim (fun h => h ▸ hg.1) (fun h => h ▸ hg.2))

lemma good_root_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ}
    (hg : Good n (direction 1 (vectorMass h (scale r k) q))) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (y : ℂ) :
      0 ≤ densityRoot N r (fun x => coordinate n s (h x)) k q y := by
  apply ScalarCancellation.roots_nonneg_of_mass (weights N)
    (pieces_integrable (scalar_integrable hh _) r) k q _ y
  simp_rw [refined_eq_density hr hR hN (scalar_support hsupp _),scalar_mass hh]
  exact coordinate_mass_nonneg hg hs

lemma root_mass_norm {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) =
      |coordinate n s (vectorMass h (scale r k) q)| := by
  simp only [norm_smul,axis_norm hn hs,Real.norm_eq_abs,mul_one]
  rw [densityRoot_abs_mass hr hR hN (scalar_integrable hh _) (scalar_support hsupp _),scalar_mass hh]

lemma root_vector_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (q : Grid N) (n : ℂ) (s : ℝ) :
    Integrable (fun y => densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s) :=
  (densityRoot_integrable (scalar_integrable hh _) r k q).smul_const _

lemma root_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (∫ y, ‖densityRoot N r (fun x => coordinate n s (h x)) k q y • axis n s‖) ≤
      2*scalarMass h (scale r k) q := by
  rw [root_mass_norm hr hR hN hh hsupp k q hn hs]
  apply coordinate_norm_le hn
  exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith)

lemma pair_cone {n : ℂ} (hn : ‖n‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (1/2:ℝ)*‖a • axis n 1+b • axis n (-1)‖ ≤ inner ℝ (axis n s)
      (a • axis n 1+b • axis n (-1)) := by
  have hnorm : ‖a • axis n 1+b • axis n (-1)‖ ≤ a+b := by
    convert norm_add_le (a • axis n 1) (b • axis n (-1)) using 1
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,
      axis_norm hn (by norm_num : (1:ℝ)^2=1),axis_norm hn (by norm_num : (-1:ℝ)^2=1),mul_one]
  have hp : inner ℝ (axis n 1) (axis n 1) = 1 := by simp [axis_norm hn (by norm_num : (1:ℝ)^2=1)]
  have hm : inner ℝ (axis n (-1)) (axis n (-1)) = 1 := by simp [axis_norm hn (by norm_num : (-1:ℝ)^2=1)]
  have hpm := axes_inner hn
  have hmp : inner ℝ (axis n (-1)) (axis n 1) = 1/2 := by rw [real_inner_comm]; exact hpm
  rcases hs with rfl | rfl <;> simp only [inner_add_right,real_inner_smul_right,hp,hm,hpm,hmp] <;> linarith

end ConeScalar

end SignedDisk

end

end OAI
