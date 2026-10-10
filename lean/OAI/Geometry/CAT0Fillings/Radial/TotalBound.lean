import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.ScalarBound
import OAI.Geometry.CAT0Fillings.Radial.ScalarDerivative
import OAI.Geometry.CAT0Fillings.Radial.SpatialBound
import OAI.Geometry.CAT0Fillings.Radial.TotalDeterminant

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

theorem abs_det_le_sqrt_det_of_posSemidef_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  let e := Fintype.equivFin ι
  have hh := abs_det_le_sqrt_det_of_posSemidef (reindex e e L) (reindex e e P)
    (hP.submatrix e.symm)
  rw [det_reindex_self,det_reindex_self] at hh
  apply hh
  intro i v
  have hb := h (e.symm i) (v ∘ e)
  convert hb using 1
  · change |(L (e.symm i) ∘ e.symm) ⬝ᵥ v| = _
    rw [comp_equiv_symm_dotProduct]
  · congr 1
    rw [Matrix.reindex_apply,Matrix.submatrix_mulVec_equiv]
    rw [dotProduct_comp_equiv_symm]
    simp only [Equiv.symm_symm]
end CAT0Fillings

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma metricTotalRadialForm_posSemidef
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosSemidef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    (metricTotalRadialForm G g r t α γ).PosSemidef := by
  have hQ : (G-vecMulVec α α).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub hG.isHermitian
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  exact totalRankOneForm_posSemidef _ _ _ (hQ.smul (sq_nonneg _))

omit [DecidableEq ι] in
lemma metricTotalRadialForm_quadratic
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) (v : Unit ⊕ ι → ℝ) :
    v ⬝ᵥ (metricTotalRadialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ (v ∘ Sum.inr))-t*r*(γ ⬝ᵥ (v ∘ Sum.inr))-r*g*v (Sum.inl ()))^2+
        (1-t*g)^2*((v ∘ Sum.inr) ⬝ᵥ G.mulVec (v ∘ Sum.inr)-
          (α ⬝ᵥ (v ∘ Sum.inr))^2) := by
  rw [metricTotalRadialForm,totalRankOneForm_quadratic,
    Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,dotProduct_sub,
    dotProduct_vecMulVec_self,sub_dotProduct,smul_dotProduct,smul_dotProduct]
  simp only [smul_eq_mul]
  ring

end CAT0Fillings

namespace CAT0Fillings
open Filter MeasureTheory Set Metric Matrix
open scoped Topology NNReal BigOperators

noncomputable def finiteDifferentialRow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) : ι → ℝ :=
  fun j => L (EuclideanSpace.single j 1)

lemma finiteDifferentialRow_dot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : ι → ℝ) :
    finiteDifferentialRow L ⬝ᵥ v = L (WithLp.toLp 2 v) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = WithLp.toLp 2 v := by
    convert b.sum_repr (WithLp.toLp 2 v) using 1
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,_root_.map_sum]
  simp only [finiteDifferentialRow,map_smul,smul_eq_mul,dotProduct,mul_comm]

noncomputable def spatialFunctional {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    EuclideanSpace ℝ (Unit ⊕ ι) →L[ℝ] ℝ :=
  ∑ j, a j • PiLp.proj 2 (fun _ : Unit ⊕ ι => ℝ) (Sum.inr j)

lemma spatialFunctional_toLp {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (v : Unit ⊕ ι → ℝ) :
    spatialFunctional a (WithLp.toLp 2 v) = a ⬝ᵥ (v ∘ Sum.inr) := by
  simp [spatialFunctional,dotProduct]

theorem total_radial_test_normalized_det_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [MetricSpace X]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set (EuclideanSpace ℝ (Unit ⊕ ι))} {x : EuclideanSpace ℝ (Unit ⊕ ι)}
    (hxs : x ∈ s)
    (hx : Tendsto (fun t => volume (s ∩ closedBall x t) / volume (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : EuclideanSpace ℝ (Unit ⊕ ι) → X) (o : X)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Unit ⊕ ι)))
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (hmetric : ∀ v : Unit ⊕ ι → ℝ, p (WithLp.toLp 2 v)^2 =
      (v ∘ Sum.inr) ⬝ᵥ G.mulVec (v ∘ Sum.inr))
    (g : EuclideanSpace ℝ (Unit ⊕ ι) → ℝ) (hg : 0 ≤ g x)
    (hscale : ∀ y ∈ s, 1-y (Sum.inl ())*g y ∈ Icc (0:ℝ) 1)
    (α γ : ι → ℝ)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) (spatialFunctional α) s x)
    (hγ : HasFDerivWithinAt g (spatialFunctional γ) s x)
    (F : (Unit ⊕ ι) → EuclideanSpace ℝ (Unit ⊕ ι) → ℝ)
    (L : (Unit ⊕ ι) → EuclideanSpace ℝ (Unit ⊕ ι) →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivWithinAt (F i) (L i) s x)
    (u : (Unit ⊕ ι) → X → ℝ) (hu : ∀ i, LipschitzWith 1 (u i))
    (hF : ∀ i y, y ∈ s → F i y = u i (seg o (f y) (1-y (Sum.inl ())*g y))) :
    |(Matrix.of fun i j => finiteDifferentialRow (L i) j).det| / Real.sqrt G.det ≤
      dist o (f x)*g x*(1-x (Sum.inl ())*g x)^Fintype.card ι *
        Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α) := by
  have hcontract (v : ι → ℝ) : (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v := by
    let w : Unit ⊕ ι → ℝ := Sum.elim (fun _ => 0) v
    have hr := scalar_derivative_bound_of_metric_differential volume hx hα hp
      (K := 1) (by
        intro y _
        simpa only [one_mul,dist_comm o] using abs_dist_sub_le (f y) (f x) o)
      (WithLp.toLp 2 w)
    have hh := (sq_le_sq₀ (abs_nonneg _) (apply_nonneg p _)).2 (by simpa using hr)
    simpa only [sq_abs,spatialFunctional_toLp,hmetric,w,Function.comp_def,Sum.elim_inr] using hh
  let P := metricTotalRadialForm G (g x) (dist o (f x)) (x (Sum.inl ())) α γ
  have hP : P.PosSemidef :=
    metricTotalRadialForm_posSemidef G _ _ _ α γ hG.posSemidef hcontract
  have ht : HasFDerivWithinAt (fun y : EuclideanSpace ℝ (Unit ⊕ ι) => y (Sum.inl ()))
      (PiLp.proj 2 (fun _ : Unit ⊕ ι => ℝ) (Sum.inl ())) s x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Unit ⊕ ι => ℝ) (Sum.inl ())).hasFDerivWithinAt
  have hd : |(Matrix.of fun i j => finiteDifferentialRow (L i) j).det| ≤ Real.sqrt P.det := by
    apply abs_det_le_sqrt_det_of_posSemidef_finite _ _ hP
    intro i v
    have hr := radial_scalar_derivative_sq_le volume seg hcomp hxs hx f o p hp hscale hα
      ((ht.mul hγ).const_sub 1) (hL i) (hu i) (hF i) (WithLp.toLp 2 v)
    have heq : (L i (WithLp.toLp 2 v))^2 ≤ v ⬝ᵥ P.mulVec v := by
      change _ ≤ v ⬝ᵥ (metricTotalRadialForm G (g x) (dist o (f x)) (x (Sum.inl ())) α γ).mulVec v
      rw [metricTotalRadialForm_quadratic]
      convert hr using 1
      simp only [spatialFunctional_toLp,hmetric,_root_.neg_apply,
        _root_.add_apply,_root_.smul_apply,smul_eq_mul,PiLp.proj_apply]
      ring
    change |finiteDifferentialRow (L i) ⬝ᵥ v| ≤ _
    rw [finiteDifferentialRow_dot]
    exact (Real.le_sqrt (abs_nonneg _) (hP.dotProduct_mulVec_nonneg v)).2 (by simpa using heq)
  have hdiv := div_le_div_of_nonneg_right hd (Real.sqrt_nonneg G.det)
  exact hdiv.trans_eq (metricTotalRadialForm_normalized_sqrt_det G (g x) (dist o (f x))
    (x (Sum.inl ())) α γ hG dist_nonneg hg (hscale x hxs).1)
end CAT0Fillings

end
end

end OAI
