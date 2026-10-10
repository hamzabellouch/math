import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators Matrix.Norms.L2Operator

namespace CAT0Fillings

lemma inverse_quadratic_le {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (α : Fin k → ℝ) (hG : G.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hα : ∀ v, |α ⬝ᵥ v| ≤ K * Real.sqrt (v ⬝ᵥ G.mulVec v)) :
    α ⬝ᵥ G⁻¹.mulVec α ≤ K^2 := by
  have hi : G.mulVec (G⁻¹.mulVec α) = α := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
      Matrix.one_mulVec]
  have hq : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  have hh := hα (G⁻¹.mulVec α)
  rw [hi,dotProduct_comm (G⁻¹.mulVec α),abs_of_nonneg hq] at hh
  have hs := Real.sq_sqrt hq
  have hb : Real.sqrt (α ⬝ᵥ G⁻¹.mulVec α) ≤ K := by
    by_contra! hn
    have hp := mul_pos (lt_of_le_of_lt hK hn) (sub_pos.mpr hn)
    nlinarith
  nlinarith [Real.sqrt_nonneg (α ⬝ᵥ G⁻¹.mulVec α)]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

local instance : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _
local instance : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

noncomputable def covector (i : ℕ) (u : X → ℝ) (z : Euc k) : Fin k → ℝ :=
  differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z)

noncomputable def normSq (i : ℕ) (u : X → ℝ) (z : Euc k) : ℝ :=
  q.covector i u z ⬝ᵥ (q.gram i z)⁻¹.mulVec (q.covector i u z)

noncomputable def duNorm (i : ℕ) (u : X → ℝ) (z : Euc k) : ℝ :=
  Real.sqrt (q.normSq i u z)

lemma measurable_gram (i : ℕ) : Measurable (q.gram i) := by
  have hh : Measurable (fun z a b => q.gram i z a b) :=
    measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
      measurable_polarizationMatrix (q.field i)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (q.measurable i) a b
  have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
    BorelSpace.measurable_eq.symm
  change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) _
  rw [heq]
  exact hh

lemma aestronglyMeasurable_covector (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.covector i u)
      (volume.restrict (q.chart i).domain) := by
  obtain ⟨L,U,hL,_⟩ := (q.chart i).bilipschitz
  obtain ⟨R,hR,heR⟩ := ((q.chart i).scalar_lipschitzOn hL hu).extend_real
  have hm : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro j
    simp only [differentialRow]
    fun_prop
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume (q.chart i).borel hR heR] with z hz
  simp only [covector,hz]

lemma aestronglyMeasurable_normSq (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.normSq i u)
      (volume.restrict (q.chart i).domain) := by
  have hc : Continuous (fun r : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
      r.1 ⬝ᵥ r.2.mulVec r.1) := by fun_prop
  exact hc.comp_aestronglyMeasurable ((q.aestronglyMeasurable_covector i hu).prodMk
    (measurable_matrix_inverse _ (q.measurable_gram i)).aestronglyMeasurable)

lemma aestronglyMeasurable_duNorm (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.duNorm i u)
      (volume.restrict (q.chart i).domain) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (q.aestronglyMeasurable_normSq i hu)

lemma ae_normSq_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.normSq i u z ∧ q.normSq i u z ≤ (K : ℝ)^2 := by
  obtain ⟨L,U,hL,_⟩ := (q.chart i).bilipschitz
  have hb := MetricDifferentiation.ae_scalarOn_derivative_bound volume (q.chart i).borel hL
    ((q.differential i).mono fun z hz => hz.1) hu
  filter_upwards [q.differential i,hb] with z hz hbz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  refine ⟨hG.inv.posSemidef.dotProduct_mulVec_nonneg _,?_⟩
  apply inverse_quadratic_le _ _ hG K.coe_nonneg
  intro v
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let w : Euc k := WithLp.toLp 2 v
  have hr : b.repr w = v := by ext j; simp [b,w]
  have hquad : v ⬝ᵥ (q.gram i z).mulVec v = (q.field i z w)^2 := by
    simpa only [gram,hr] using polarizationMatrix_quadratic b (q.field i z) hz.2.2 hz.2.1 w
  rw [hquad,Real.sqrt_sq (apply_nonneg (q.field i z) w)]
  have he : (q.chart i).scalar u = MetricDifferentiation.scalarOn (q.chart i).param u := by
    ext x
    rfl
  simpa only [covector,differentialRow_dot,he,w] using hbz w

lemma ae_duNorm_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.duNorm i u z ∧ q.duNorm i u z ≤ (K : ℝ) ∧
      q.duNorm i u z ^2 = q.normSq i u z := by
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left K.coe_nonneg).mpr hz.2, Real.sq_sqrt hz.1⟩

lemma integrable_gradient (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Integrable (fun z => q.density i z * q.duNorm i u z)
      (volume.restrict (q.chart i).domain) := by
  apply ((q.density_integrable i).mul_const (K : ℝ)).mono'
    ((q.density_integrable i).aestronglyMeasurable.mul (q.aestronglyMeasurable_duNorm i hu))
  filter_upwards [q.ae_duNorm_bounds i hu] with z hz
  have density_nonneg : 0 ≤ q.density i z :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg density_nonneg hz.1)]
  exact mul_le_mul_of_nonneg_left hz.2.1 density_nonneg

lemma integrable_energy (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Integrable (fun z => q.density i z * q.normSq i u z)
      (volume.restrict (q.chart i).domain) := by
  apply ((q.density_integrable i).mul_const ((K : ℝ)^2)).mono'
    ((q.density_integrable i).aestronglyMeasurable.mul (q.aestronglyMeasurable_normSq i hu))
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  have density_nonneg : 0 ≤ q.density i z :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg density_nonneg hz.1)]
  exact mul_le_mul_of_nonneg_left hz.2 density_nonneg

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators MatrixOrder

namespace CAT0Fillings

lemma abs_det_le_prod_dual_norm {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    |L.det| ≤ (∏ i, Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i))) * Real.sqrt P.det := by
  let Q := CFC.sqrt P⁻¹
  have hQsym : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P⁻¹).posSemidef.isHermitian).eq
  have hQdet : Q.det = (Real.sqrt P.det)⁻¹ := by
    have hh := hP.inv.posSemidef.det_sqrt
    simpa only [Q,RCLike.sqrt_real,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
      Real.sqrt_inv] using hh
  have hJ : 0 < Real.sqrt P.det := Real.sqrt_pos.mpr hP.det_pos
  have hrow (i : Fin n) : (L * Q) i = Q.mulVec (L i) := by
    ext j
    change (∑ t, L i t * Q t j) = ∑ t, Q j t * L i t
    apply Finset.sum_congr rfl
    intro t ht
    have hs : Q t j = Q j t := congrFun (congrFun hQsym j) t
    rw [hs,mul_comm]
  have hnorm (i : Fin n) :
      ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i)) := by
    have hn : ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖^2 =
        L i ⬝ᵥ P⁻¹.mulVec (L i) := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hrow]
      exact (dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef (L i)).symm
    rw [←hn,Real.sqrt_sq (norm_nonneg _)]
  have heq : |L.det| = |(L*Q).det| * Real.sqrt P.det := by
    rw [Matrix.det_mul,abs_mul,hQdet,abs_of_pos (inv_pos.mpr hJ)]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hJ.le
  simpa only [hnorm] using abs_det_le_prod_row_norm (L*Q)

lemma abs_det_le_first_dual_norm {n : ℕ} (L P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef)
    (hL : ∀ i : Fin n, Real.sqrt (L i.succ ⬝ᵥ P⁻¹.mulVec (L i.succ)) ≤ 1) :
    |L.det| ≤ Real.sqrt (L 0 ⬝ᵥ P⁻¹.mulVec (L 0)) * Real.sqrt P.det := by
  apply (abs_det_le_prod_dual_norm L P hP).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [Fin.prod_univ_succ]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
    (Finset.prod_le_one₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => hL i))

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem ae_jacobian_le_duNorm (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      |(q.chart i).jacobian (Fin.cons u π) z| ≤
        q.duNorm i u z * Real.sqrt (q.gram i z).det := by
  have hp : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ∀ j, q.duNorm i ((Fin.cons u π : Fin (k+1) → X → ℝ) j) z ≤
        (Fin.cons (K : ℝ) (fun _ => (1 : ℝ)) : Fin (k+1) → ℝ) j := by
    rw [eventually_all]
    intro coordinate
    refine Fin.cases ?_ (fun tail => ?_) coordinate
    · exact (q.ae_duNorm_bounds i hu).mono fun _ bounds => bounds.2.1
    · exact (q.ae_duNorm_bounds i (hπ tail)).mono fun _ bounds => by simpa using bounds.2.1
  filter_upwards [q.differential i,hp] with z hz hpz
  apply abs_det_le_first_dual_norm _ _
    (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1)
  intro j
  exact hpz j.succ

end ChartGeometry
end CAT0Fillings
end

end OAI
