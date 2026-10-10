import Mathlib
import OAI.Combinatorics.StripMass.DeficitBounds

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
section DeterminantBounds
open scoped BigOperators
open Set MeasureTheory Matrix
def boundedCauchyMatrix {N : ℕ} (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => boundedCauchy (x i) (y j)

 theorem basisDet_eq (N : ℕ) (x : Fin N → ℝ) :
    basisDet N x = (∏ i, omega (x i)) * (Matrix.vandermonde x).det := by
  have hscale := Matrix.det_mul_row (fun j => omega (x j)) (Matrix.vandermonde x).transpose
  have hm : (Matrix.of fun i j : Fin N => momentBasis i.val (x j)) =
      Matrix.of (fun i j : Fin N => omega (x j) * (Matrix.vandermonde x).transpose i j) := by
    ext i j
    exact mul_comm _ _
  unfold basisDet
  rw [hm, hscale, Matrix.det_transpose]

 theorem boundedCauchyMatrix_det (N : ℕ) (x y : Fin N → ℝ) :
    (boundedCauchyMatrix x y).det = (∏ i, x i) * (cauchyMatrix x y).det := by
  have hm : boundedCauchyMatrix x y = Matrix.of (fun i j => x i * cauchyMatrix x y i j) := by
    ext i j
    simp [boundedCauchyMatrix, boundedCauchy, cauchyMatrix, div_eq_mul_inv]
  rw [hm, Matrix.det_mul_column]

 theorem basis_cauchy_basis_eq (N : ℕ) (x y : Fin N → ℝ) :
    basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y =
      ((∏ i, omega (x i)) * (∏ i, x i) * (∏ i, omega (y i))) * cauchyAlternant x y := by
  rw [basisDet_eq, basisDet_eq, boundedCauchyMatrix_det]
  unfold cauchyAlternant
  ring

 theorem basis_cauchy_basis_nonneg (N : ℕ) (x y : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    0 ≤ basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y := by
  rw [basis_cauchy_basis_eq]
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => omega_nonneg _))
      (Finset.prod_nonneg (fun i _ => (hx i).le))) (Finset.prod_nonneg (fun i _ => omega_nonneg _))
  · exact cauchyAlternant_nonneg x y hx hy

 theorem basis_cauchy_basis_pos {N : ℕ} {x y : Fin N → ℝ}
    (hx : x ∈ orderedDomain N) (hy : y ∈ orderedDomain N) :
    0 < basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y := by
  rw [basis_cauchy_basis_eq]
  apply mul_pos
  · exact mul_pos (mul_pos (Finset.prod_pos (fun i _ => omega_pos (hx.2 i)))
      (Finset.prod_pos (fun i _ => (hx.2 i).1))) (Finset.prod_pos (fun i _ => omega_pos (hy.2 i)))
  · exact cauchyAlternant_pos x y hx.1 hy.1 (fun i => (hx.2 i).1) (fun i => (hy.2 i).1)

 theorem product_restrict_cube (N : ℕ) :
    Measure.pi (fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1)) =
    volume.restrict (univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1)) := by
  rw [volume_pi, Measure.restrict_pi_pi]

 theorem integral_pos_on_cube {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hi : Integrable f (Measure.pi fun _ => volume.restrict (Ioo (0 : ℝ) 1)))
    (hn : ∀ x, (∀ i, x i ∈ Ioo 0 1) → 0 ≤ f x)
    (hp : ∀ x ∈ orderedDomain N, 0 < f x) :
    0 < ∫ x, f x ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [product_restrict_cube] at hi ⊢
  have hc : MeasurableSet (univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hnn : 0 ≤ᵐ[volume.restrict (univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem hc] with x hx
    exact hn x (fun i => hx i (mem_univ _))
  apply (integral_pos_iff_support_of_nonneg_ae hnn hi).2
  have hs : orderedDomain N ⊆ Function.support f := fun x hx => (hp x hx).ne'
  have hsub : orderedDomain N ⊆ univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1) :=
    fun x hx i _ => hx.2 i
  calc
    0 < volume (orderedDomain N) :=
      (isOpen_orderedDomain N).measure_pos volume (orderedDomain_nonempty N)
    _ = (volume.restrict (univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1)) (orderedDomain N) := by
      rw [Measure.restrict_apply (isOpen_orderedDomain N).measurableSet, inter_eq_left.2 hsub]
    _ ≤ _ := measure_mono hs

 

theorem integral_cauchy_basis (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    (∫ y : Fin N → ℝ, (boundedCauchyMatrix x y).det * basisDet N y
      ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1))) =
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * transformedDet N x := by
  have h := integral_det_mul_det (fun i y => boundedCauchy (x i) y)
    (fun i : Fin N => momentBasis i.val)
    (fun i j => integrableOn_boundedCauchy_basis j.val (hx i))
  have hm : (Matrix.of fun i j : Fin N =>
      ∫ y in Ioo (0 : ℝ) 1, boundedCauchy (x i) y * momentBasis j.val y) =
      (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).transpose := rfl
  change _ = _ * (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).det
  simpa only [hm, Matrix.det_transpose, boundedCauchyMatrix, basisDet] using h

theorem integrable_cauchy_basis (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    Integrable (fun y => (boundedCauchyMatrix x y).det * basisDet N y)
      (Measure.pi fun _ => volume.restrict (Ioo (0 : ℝ) 1)) :=
  integrable_det_mul_det (fun i y => boundedCauchy (x i) y)
    (fun i : Fin N => momentBasis i.val)
    (fun i j => integrableOn_boundedCauchy_basis j.val (hx i))

theorem basis_transformed_nonneg (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ basisDet N x * transformedDet N x := by
  have hi : 0 ≤ ∫ y : Fin N → ℝ,
      basisDet N x * ((boundedCauchyMatrix x y).det * basisDet N y)
      ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply integral_nonneg_of_ae
    rw [product_restrict_cube]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin N => measurableSet_Ioo)] with y hy
    simpa only [mul_assoc, Pi.zero_apply] using basis_cauchy_basis_nonneg N x y hx
      (fun i => (hy i (mem_univ _)).1)
  rw [integral_const_mul, integral_cauchy_basis N x hx] at hi
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by positivity
  nlinarith

theorem basis_transformed_pos {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ orderedDomain N) :
    0 < basisDet N x * transformedDet N x := by
  have hi := integral_pos_on_cube
    ((integrable_cauchy_basis N x (fun i => (hx.2 i).1)).const_mul (basisDet N x))
    (fun y hy => by
      simpa only [mul_assoc] using basis_cauchy_basis_nonneg N x y
        (fun i => (hx.2 i).1) (fun i => (hy i).1))
    (fun y hy => by simpa only [mul_assoc] using basis_cauchy_basis_pos hx hy)
  rw [integral_const_mul, integral_cauchy_basis N x (fun i => (hx.2 i).1)] at hi
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by positivity
  nlinarith

 

theorem det_momentMatrix_pos (N : ℕ) : 0 < (momentMatrix N).det := by
  have hi := integral_pos_on_cube
    (integrable_det_mul_det (fun i : Fin N => momentBasis i.val)
      (fun i : Fin N => transformedBasis i.val)
      (fun i j => integrableOn_basis_transformedBasis i.val j.val))
    (fun x hx => basis_transformed_nonneg N x (fun i => (hx i).1))
    (fun _ hx => basis_transformed_pos hx)
  rw [integral_det_mul_det (fun i : Fin N => momentBasis i.val)
    (fun i : Fin N => transformedBasis i.val)
    (fun i j => integrableOn_basis_transformedBasis i.val j.val)] at hi
  change 0 < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * (momentMatrix N).det at hi
  exact (mul_pos_iff_of_pos_left (by positivity)).1 hi

 

def cauchyDefect (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) (x : ℝ) : ℝ :=
  D₀ - ∑ k, v k * transformedBasis k.val x

def CauchyMomentProblem (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N D₀ v x = 0

theorem cauchyDefect_moment (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) (j : Fin N) :
    (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N D₀ v x) =
      D₀ * (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x) - (momentMatrix N *ᵥ v) j := by
  have heq : (fun x => momentBasis j.val x * cauchyDefect N D₀ v x) =
      fun x => D₀ * momentBasis j.val x -
        ∑ k : Fin N, v k * (momentBasis j.val x * transformedBasis k.val x) := by
    funext x
    simp only [cauchyDefect, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      ring
  rw [heq, integral_sub ((integrableOn_momentBasis j.val).const_mul D₀)
    (integrable_finsetSum _ fun k _ => (integrableOn_basis_transformedBasis j.val k.val).const_mul (v k)),
    integral_const_mul, integral_finsetSum]
  · simp only [integral_const_mul, Matrix.mulVec, dotProduct, momentMatrix, Matrix.of_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  · intro k _
    exact (integrableOn_basis_transformedBasis j.val k.val).const_mul (v k)

theorem cauchyMomentProblem_iff (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) :
    CauchyMomentProblem N D₀ v ↔
      momentMatrix N *ᵥ v = fun j => D₀ * ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x := by
  simp only [CauchyMomentProblem, cauchyDefect_moment, sub_eq_zero]
  exact ⟨fun h => funext fun j => (h j).symm, fun h j => (congrFun h j).symm⟩

 

theorem existsUnique_cauchyMomentProblem (N : ℕ) (D₀ : ℝ) :
    ∃! v : Fin N → ℝ, CauchyMomentProblem N D₀ v := by
  have hu : IsUnit (momentMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_momentMatrix_pos N).ne')
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hu)
    (fun j => D₀ * ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x)
  refine ⟨v, (cauchyMomentProblem_iff _ _ _).2 hv, ?_⟩
  intro w hw
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu)
    (((cauchyMomentProblem_iff _ _ _).1 hw).trans hv.symm)

 

theorem cauchyMomentProblem_zero {N : ℕ} {v : Fin N → ℝ}
    (hv : CauchyMomentProblem N 0 v) : v = 0 := by
  have hu : IsUnit (momentMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_momentMatrix_pos N).ne')
  apply (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [Matrix.mulVec_zero]
  exact ((cauchyMomentProblem_iff _ _ _).1 hv).trans (by ext j; simp)

end DeterminantBounds

 

open Set MeasureTheory Filter
open scoped Topology

def quarticDen (r t : ℝ) : ℝ := t ^ 4 + 2 * t ^ 2 + r ^ 2
def quarticBase (r t : ℝ) : ℝ := (t ^ 2 + r) / quarticDen r t
def quarticWeighted (r t : ℝ) : ℝ := 2 * (t ^ 2 + r ^ 2) / quarticDen r t
def straightener (r t : ℝ) : ℝ := t - r / t

theorem quarticDen_pos {r t : ℝ} (hr : 0 < r) : 0 < quarticDen r t := by
  unfold quarticDen
  positivity

theorem straightener_deriv {r t : ℝ} (ht : 0 < t) :
    HasDerivAt (straightener r) (1 + r / t ^ 2) t := by
  exact ((hasDerivAt_id t).sub ((hasDerivAt_const t r).div
    (hasDerivAt_id t) ht.ne')).congr_deriv (by simp; ring)

theorem straightener_inj {r : ℝ} (hr : 0 < r) :
    InjOn (straightener r) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  dsimp [straightener]
  have hdiv : r / y < r / x := (div_lt_div_iff_of_pos_left hr hy hx).2 hxy
  linarith

theorem straightener_image {r : ℝ} (hr : 0 < r) :
    straightener r '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro u
  let s := Real.sqrt (u ^ 2 + 4 * r)
  have hs : s ^ 2 = u ^ 2 + 4 * r := Real.sq_sqrt (by positivity)
  have hsn : 0 ≤ s := Real.sqrt_nonneg _
  have hsu : -u < s := by nlinarith
  have ht : 0 < (u + s) / 2 := by linarith
  refine ⟨(u + s) / 2, ht, ?_⟩
  dsimp [straightener]
  field_simp [show u + s ≠ 0 by linarith]
  nlinarith

theorem scaled_cauchy {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (a ^ 2 + x ^ 2)⁻¹) ∧
      (∫ x : ℝ, (a ^ 2 + x ^ 2)⁻¹) = Real.pi / a := by
  have heq : (fun x : ℝ => (a ^ 2 + x ^ 2)⁻¹) =
      fun x => (a ^ 2)⁻¹ * (1 + (x / a) ^ 2)⁻¹ := by
    funext x
    field_simp
  rw [heq]
  constructor
  · exact (integrable_inv_one_add_sq.comp_div ha.ne').const_mul _
  · rw [integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) a, integral_univ_inv_one_add_sq,
      abs_of_pos ha, smul_eq_mul]
    field_simp

theorem quartic_base_integral {r : ℝ} (hr : 0 < r) :
    IntegrableOn (quarticBase r) (Ioi 0) ∧
      (∫ t in Ioi 0, quarticBase r t) = Real.pi / Real.sqrt (2 + 2 * r) := by
  let a := Real.sqrt (2 + 2 * r)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha2 : a ^ 2 = 2 + 2 * r := Real.sq_sqrt (by linarith)
  have heq : EqOn (fun t => |1 + r / t ^ 2| •
      (a ^ 2 + (straightener r t) ^ 2)⁻¹) (quarticBase r) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [abs_of_pos (by positivity : 0 < 1 + r / t ^ 2), smul_eq_mul, ha2]
    dsimp [straightener, quarticBase, quarticDen]
    field_simp [show t ≠ 0 from ne_of_gt ht]
    ring_nf
    field_simp
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (straightener_deriv ht).hasDerivWithinAt)
    (straightener_inj hr) (fun u => (a ^ 2 + u ^ 2)⁻¹)
  rw [straightener_image hr, integrableOn_univ] at hi
  refine ⟨(hi.1 (scaled_cauchy ha).1).congr_fun heq measurableSet_Ioi, ?_⟩
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (straightener_deriv ht).hasDerivWithinAt)
    (straightener_inj hr) (fun u => (a ^ 2 + u ^ 2)⁻¹)
  rw [straightener_image hr, Measure.restrict_univ, (scaled_cauchy ha).2] at h
  exact (setIntegral_congr_fun measurableSet_Ioi heq).symm.trans h.symm

theorem integral_reciprocal {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    (∫ t in Ioi 0, (r / t ^ 2) * g (r / t)) = ∫ t in Ioi 0, g t := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t => r / t)
      (-r / t ^ 2) (Ioi 0) t := by
    intro t ht
    exact (((hasDerivAt_const t r).div (hasDerivAt_id t) ht.ne').congr_deriv
      (by simp)).hasDerivWithinAt
  have hinj : InjOn (fun t => r / t) (Ioi 0) := by
    intro x hx y hy h
    have h' := (div_eq_div_iff hx.ne' hy.ne').1 h
    nlinarith
  have himage : (fun t => r / t) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hr hu
    · intro ht
      refine ⟨r / t, div_pos hr ht, ?_⟩
      field_simp
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
  rw [himage] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [abs_of_neg (by exact div_neg_of_neg_of_pos (neg_neg_of_pos hr) (sq_pos_of_pos ht)),
    neg_div, neg_neg, smul_eq_mul]

theorem quartic_weighted_integral {r : ℝ} (hr : 0 < r) :
    IntegrableOn (quarticWeighted r) (Ioi 0) ∧
      (∫ t in Ioi 0, quarticWeighted r t) =
        Real.pi * (1 + r) / Real.sqrt (2 + 2 * r) := by
  have hbase := quartic_base_integral hr
  have hint : IntegrableOn (quarticWeighted r) (Ioi 0) := by
    apply (hbase.1.const_mul (2 * (1 + r))).mono'
    · apply Measurable.aestronglyMeasurable
      unfold quarticWeighted quarticDen
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hd := quarticDen_pos (t := t) hr
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold quarticWeighted; positivity)]
      unfold quarticWeighted quarticBase
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hd]
      nlinarith [sq_nonneg t]
  have heq : EqOn (fun t => quarticWeighted r t +
      (r / t ^ 2) * quarticWeighted r (r / t))
      (fun t => (2 * (1 + r)) * quarticBase r t) (Ioi 0) := by
    intro t ht
    dsimp [quarticWeighted, quarticBase, quarticDen]
    field_simp [show t ≠ 0 from ne_of_gt ht]
    ring
  have hi2 : IntegrableOn (fun t => (r / t ^ 2) * quarticWeighted r (r / t)) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((hbase.1.const_mul (2 * (1 + r))).sub hint) _ measurableSet_Ioi
    intro t ht
    have h := heq ht
    dsimp only at h
    dsimp only [Pi.sub_apply]
    linarith
  have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioi heq
  rw [integral_add hint hi2, integral_const_mul, integral_reciprocal hr,
    hbase.2] at h
  refine ⟨hint, ?_⟩
  linear_combination h / 2

def uniformDen (t : ℝ) : ℝ := 2 * t ^ 4 + 4 * t ^ 2 + 1
def uniformizer (t : ℝ) : ℝ := 1 / uniformDen t

theorem uniformDen_pos (t : ℝ) : 0 < uniformDen t := by
  unfold uniformDen
  positivity

theorem uniformizer_mem {t : ℝ} (ht : 0 < t) : uniformizer t ∈ Ioo 0 1 := by
  refine ⟨one_div_pos.2 (uniformDen_pos t), ?_⟩
  unfold uniformizer
  rw [div_lt_one (uniformDen_pos t)]
  unfold uniformDen
  have : 0 < t ^ 2 := sq_pos_of_pos ht
  nlinarith [sq_nonneg (t ^ 2)]

theorem uniformizer_deriv (t : ℝ) :
    HasDerivAt uniformizer (-8 * t * (t ^ 2 + 1) / (uniformDen t) ^ 2) t := by
  have hd : HasDerivAt uniformDen (8 * t * (t ^ 2 + 1)) t := by
    exact (((((hasDerivAt_id t).pow 4).const_mul (2 : ℝ)).add
      (((hasDerivAt_id t).pow 2).const_mul (4 : ℝ))).add_const 1).congr_deriv (by simp only [id_eq]; ring)
  have heq : uniformizer = uniformDen⁻¹ := by funext t; simp [uniformizer]
  rw [heq]
  exact (hd.inv (uniformDen_pos t).ne').congr_deriv (by ring)

theorem uniformizer_inj : InjOn uniformizer (Ioi 0) := by
  apply StrictAntiOn.injOn
  intro x hx y hy hxy
  unfold uniformizer
  apply one_div_lt_one_div_of_lt (uniformDen_pos x)
  unfold uniformDen
  gcongr <;> exact le_of_lt hx

theorem omega_uniformizer {t : ℝ} (ht : 0 < t) : omega (uniformizer t) = t / 2 := by
  have hinner : (1 + uniformizer t) / (2 * uniformizer t) = (t ^ 2 + 1) ^ 2 := by
    unfold uniformizer uniformDen
    field_simp
    ring
  unfold omega
  rw [hinner, Real.sqrt_sq (by positivity : 0 ≤ t ^ 2 + 1)]
  simp only [add_sub_cancel_right, Real.sqrt_sq ht.le]
  ring

theorem uniformizer_image : uniformizer '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact uniformizer_mem ht
  · intro hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    let w := Real.sqrt ((1 + x) / (2 * x))
    have hw2 : w ^ 2 = (1 + x) / (2 * x) := Real.sq_sqrt (by positivity)
    have hw : 1 < w := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2
      rw [one_pow, lt_div_iff₀ (by positivity : 0 < 2 * x)]
      linarith [hx.1, hx.2]
    let t := Real.sqrt (w - 1)
    have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
    have ht2 : t ^ 2 = w - 1 := Real.sq_sqrt (by linarith)
    refine ⟨t, ht, ?_⟩
    unfold uniformizer
    apply (div_eq_iff (uniformDen_pos t).ne').2
    have hd : uniformDen t = 2 * w ^ 2 - 1 := by
      unfold uniformDen
      calc
        _ = 2 * (t ^ 2) ^ 2 + 4 * t ^ 2 + 1 := by ring
        _ = _ := by rw [ht2]; ring
    rw [hd, hw2]
    field_simp [hx0.ne']
    ring

end
end CriticalStrip

end OAI
