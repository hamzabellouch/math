import OAI.Analysis.DiskMaximal.DirectionEstimates

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
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

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

namespace AffineDensities

def rescale (p : ℂ) (r : ℝ) (h : ℂ → ℂ) (X : ℂ) : ℂ := r • h (p+r • X)

lemma integrable_rescale {h : ℂ → ℂ} (hh : Integrable h) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    Integrable (rescale p r h) := ((hh.comp_add_left p).comp_smul hr).smul r

lemma integral_affine (h : ℂ → ℂ) (p : ℂ) (r : ℝ) :
    (∫ X : ℂ, h (p+r • X)) = (r^2)⁻¹ • ∫ y, h y := by
  have he := Measure.integral_comp_smul volume (fun y : ℂ => h (p+y)) r
  simpa only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)),
    integral_add_left_eq_self] using he

lemma integral_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ X, rescale p r h X) = r⁻¹ • ∫ y, h y := by
  simp only [rescale,integral_smul,integral_affine,smul_smul]
  congr 1
  field_simp

lemma mass_rescale (h : ℂ → ℂ) (p : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ X, ‖rescale p r h X‖) = r⁻¹*(∫ y, ‖h y‖) := by
  simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le,integral_const_mul]
  have he := Measure.integral_comp_smul volume (fun y : ℂ => ‖h (p+y)‖) r
  simp only [Complex.finrank_real_complex,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] at he
  rw [he, integral_add_left_eq_self (fun y : ℂ => ‖h y‖)]
  field_simp

lemma rescale_support {h : ℂ → ℂ} {p z : ℂ} {r t : ℝ} (hr : 0 < r)
    (hs : ∀ y, h y ≠ 0 → ‖y-z‖ ≤ t) (X : ℂ) (hX : rescale p r h X ≠ 0) :
    ‖X-r⁻¹ • (z-p)‖ ≤ t/r := by
  have hh : h (p+r • X) ≠ 0 := fun h => hX (by change r • _ = 0; rw [h,smul_zero])
  have hi := hs (p+r • X) hh
  have he : p+r • X-z = r • (X-r⁻¹ • (z-p)) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le] at hi
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hi)

end AffineDensities

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

lemma error_support {N : ℕ} {h : ℂ → ℝ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (j : ℕ) (q : Grid N) (y : ℂ) (hy : densityError N r h j q y ≠ 0) :
    ‖y-point (scale r j) q‖ ≤ 2*scale r j := by
  have hn : hat (scale r j) q y ≠ 0 := fun hn => hy ((density_support hr hh j q y hn).2)
  simpa only [Metric.mem_closedBall,dist_eq_norm] using support_hat_subset (scale_pos hr j) q hn

lemma scale_le {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) : scale r j ≤ scale r k := by
  apply mul_le_mul_of_nonneg_right _ hr.le
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj

def errorPiece {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N) (n : ℂ) (s : ℝ) : ErrorPiece 2 where
  density := rescale p (scale r k)
    (fun y => densityError N r (fun x => coordinate n s (h x)) j q y • axis n s)
  integrable := integrable_rescale
    ((densityError_integrable (scalar_integrable hh _) r j q).smul_const _) p (scale_pos hr k).ne'
  size := scale r j / scale r k
  size_pos := div_pos (scale_pos hr j) (scale_pos hr k)
  size_le_one := (div_le_one (scale_pos hr k)).mpr (scale_le hr hj)
  center := (scale r k)⁻¹ • (point (scale r j) q-p)
  zero_mass := by
    intro _
    rw [integral_rescale _ _ (scale_pos hr k).ne',integral_smul_const,
      densityError_zero_mass (scalar_integrable hh _),zero_smul,smul_zero]
  support := by
    intro _
    apply ae_of_all
    intro X hX
    have hs : ∀ y, densityError N r (fun x => coordinate n s (h x)) j q y • axis n s ≠ 0 →
        ‖y-point (scale r j) q‖ ≤ 2*scale r j := by
      intro y hy
      apply error_support (scalar_integrable hh _) hr j q y
      exact fun h => hy (by rw [h,zero_smul])
    simpa only [mul_div_assoc] using rescale_support (scale_pos hr k) hs X hX

lemma errorPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k j : ℕ) (hj : j ≤ k) (p : ℂ) (q : Grid N)
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s^2 = 1) :
    (errorPiece hh hr k j hj p q n s).mass ≤ (scale r k)⁻¹*
      (2*densityDefect N r (fun x => coordinate n s (h x)) j q) := by
  change (∫ X, ‖rescale _ _ _ X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simp only [norm_smul,axis_norm hn hs,mul_one,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (densityError_cost hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) j q)
    (inv_nonneg.mpr (scale_pos hr k).le)

end PricePieces

namespace LocalCancellation

/-- Multiplication of an error density by a nonnegative path coefficient.
Zero coefficients are retained as genuine zero-density pieces. -/
def ErrorPiece.weight {Cs : ℝ} (b : ErrorPiece Cs) (w : ℝ) : ErrorPiece Cs where
  density := fun y => w • b.density y
  integrable := b.integrable.smul w
  size := b.size
  size_pos := b.size_pos
  size_le_one := b.size_le_one
  center := b.center
  zero_mass := by intro hs; rw [integral_smul,b.zero_mass hs,smul_zero]
  support := by
    intro hs
    filter_upwards [b.support hs] with y hy h
    exact hy (fun hz => h (by rw [hz,smul_zero]))

lemma ErrorPiece.mass_weight {Cs : ℝ} (b : ErrorPiece Cs) {w : ℝ} (hw : 0 ≤ w) :
    (b.weight w).mass = w*b.mass := by
  simp only [ErrorPiece.mass,ErrorPiece.weight,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw,
    integral_const_mul]

/-- An unrestricted integrable root term is a legitimate size-one piece. -/
def unitPiece (h : ℂ → ℂ) (hh : Integrable h) (Cs : ℝ) : ErrorPiece Cs where
  density := h
  integrable := hh
  size := 1
  size_pos := zero_lt_one
  size_le_one := le_rfl
  center := 0
  zero_mass := by intro hs; exact (lt_irrefl (1:ℝ) hs).elim
  support := by intro hs; exact (lt_irrefl (1:ℝ) hs).elim

lemma cone_sum {ι : Type*} {e : ℂ} {κ : ℝ} (hκ : 0 ≤ κ) (s : Finset ι) (v : ι → ℂ)
    (hv : ∀ i ∈ s, κ*‖v i‖ ≤ inner ℝ e (v i)) :
    κ*‖∑ i ∈ s, v i‖ ≤ inner ℝ e (∑ i ∈ s, v i) := by
  calc
    _ ≤ κ*∑ i ∈ s, ‖v i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hκ
    _ = ∑ i ∈ s, κ*‖v i‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, inner ℝ e (v i) := Finset.sum_le_sum hv
    _ = _ := (inner_sum _ _ _).symm

end LocalCancellation

namespace PricePieces
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities

/-- The vector root comprises the two actual signed scalar surviving roots. -/
def rootVector (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (q : Grid N) (n : ℂ) (y : ℂ) : ℂ :=
  densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1+
    densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)

def errorVector (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (j : ℕ) (q : Grid N) (n : ℂ) (y : ℂ) : ℂ :=
  densityError N r (fun x => coordinate n 1 (h x)) j q y • axis n 1+
    densityError N r (fun x => coordinate n (-1) (h x)) j q y • axis n (-1)

lemma vector_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) (y : ℂ) :
    hat (scale r k) q y • h y = rootVector N r h k q n y+
      ∑ j ∈ Finset.range (k+1), ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y := by
  have hp := density_decomposition hr hR hN (scalar_support hsupp (coordinate n 1)) k q y
  have hm := density_decomposition hr hR hN (scalar_support hsupp (coordinate n (-1))) k q y
  have hx := congrArg (fun z : ℂ => hat (scale r k) q y • z) (expansion hn (h y))
  rw [smul_add,smul_smul,smul_smul,hp,hm,add_smul,add_smul] at hx
  simp only [rootVector,errorVector,smul_add,smul_smul,Finset.sum_add_distrib]
  rw [← hx]
  simp only [Finset.sum_smul]
  abel

lemma rootVector_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (q : Grid N) (n : ℂ) : Integrable (rootVector N r h k q n) :=
  (root_vector_integrable hh r k q n 1).add (root_vector_integrable hh r k q n (-1))

lemma rootVector_cone {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1)
    (hg : Good n (IntrinsicMarks.direction 1 (vectorMass h (scale r k) q)))
    {s : ℝ} (hs : s = 1 ∨ s = -1) (y : ℂ) :
    (1/2:ℝ)*‖rootVector N r h k q n y‖ ≤ inner ℝ (axis n s) (rootVector N r h k q n y) :=
  pair_cone hn (good_root_nonneg hr hR hN hh hsupp k q hg (Or.inl rfl) y)
    (good_root_nonneg hr hR hN hh hsupp k q hg (Or.inr rfl) y) hs

lemma rootVector_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootVector N r h k q n y‖) ≤ 4*scalarMass h (scale r k) q := by
  calc
    _ ≤ (∫ y, ‖densityRoot N r (fun x => coordinate n 1 (h x)) k q y • axis n 1‖)+
      (∫ y, ‖densityRoot N r (fun x => coordinate n (-1) (h x)) k q y • axis n (-1)‖) :=
      by
        rw [← integral_add (root_vector_integrable hh r k q n 1).norm
          (root_vector_integrable hh r k q n (-1)).norm]
        exact integral_mono (rootVector_integrable hh r k q n).norm
          ((root_vector_integrable hh r k q n 1).norm.add
            (root_vector_integrable hh r k q n (-1)).norm) (fun y => norm_add_le _ _)
    _ ≤ 2*scalarMass h (scale r k) q+2*scalarMass h (scale r k) q :=
      add_le_add (root_bound hr hR hN hh hsupp k q hn (by norm_num))
        (root_bound hr hR hN hh hsupp k q hn (by norm_num))
    _ = _ := by ring

end PricePieces

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset

def rho : ℝ := (1/2:ℝ)^(1/100:ℝ)
lemma rho_pos : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
lemma rho_lt_one : rho < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

lemma scale_ratio {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    scale r j / scale r k = (1/2:ℝ)^(k-j) := by
  dsimp [scale]
  rw [mul_div_mul_right _ _ hr.ne']
  have hk : k = j+(k-j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk,pow_add]
  simp only [div_pow,one_pow]
  field_simp

lemma scale_discount {r : ℝ} (hr : 0 < r) {j k : ℕ} (hj : j ≤ k) :
    (scale r j / scale r k)^(1/100:ℝ) = rho^(k-j) := by
  rw [scale_ratio hr hj]
  unfold rho
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),mul_comm ((k-j:ℕ):ℝ),
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

/-- A common root price sums the two exact coordinate defects for every
member of one fixed finite palette; it does not depend on the active label. -/
def rootPrice (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (q : Grid N) : ℝ :=
  ∑ n ∈ fixedPalette.labels,
    (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
      scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q)

lemma scalarPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ scalarPrice N r h rho k q := by
  apply sum_nonneg
  intro j _
  apply mul_nonneg (pow_nonneg rho_pos.le _)
  exact sum_nonneg (fun s _ => mul_nonneg (coeff_nonneg N (k-j) q s)
    (densityDefect_nonneg hr hR hN hh hsupp j s))

lemma rootPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ rootPrice N r h k q := by
  apply sum_nonneg
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

lemma coordinate_total_le {h : ℂ → ℂ} (hh : Integrable h) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) : (∫ x, |coordinate n s (h x)|) ≤ 2*(∫ x, ‖h x‖) := by
  rw [← integral_const_mul]
  exact integral_mono (scalar_integrable hh _).abs (hh.norm.const_mul 2)
    (fun x => coordinate_norm_le hn hs _)

lemma coordinate_price_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {n : ℂ} (hn : ‖n‖ = 1)
    {s : ℝ} (hs : |s| ≤ 1) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N,
      scalarPrice N r (fun x => coordinate n s (h x)) rho k q) ≤
        (1-rho)⁻¹*(∫ x, ‖h x‖) := by
  apply (scalarPrice_budget hr hR hN (scalar_integrable hh _) (scalar_support hsupp _)
    rho_pos.le rho_lt_one m).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith [rho_lt_one]))
  have he := coordinate_total_le hh hn hs
  linarith

/-- The genuine all-label root price has a uniform total budget, including
the terminal scalar splits at the finest scale. -/
theorem rootPrice_budget {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ k ∈ range (m+1), ∑ q : Grid N, rootPrice N r h k q) ≤
      (2*(fixedPalette.labels.card:ℝ)*(1-rho)⁻¹)*(∫ x, ‖h x‖) := by
  unfold rootPrice
  simp_rw [Finset.sum_comm (s := univ) (t := fixedPalette.labels)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _n ∈ fixedPalette.labels, 2*((1-rho)⁻¹*(∫ x, ‖h x‖)) := by
      apply sum_le_sum
      intro n hn
      simp_rw [sum_add_distrib]
      have hp := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(1:ℝ)| ≤ 1) m
      have hm := coordinate_price_budget hr hR hN hh hsupp (fixedPalette.unit n hn)
        (by norm_num : |(-1:ℝ)| ≤ 1) m
      linarith
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end CommonPrices

end

end OAI
