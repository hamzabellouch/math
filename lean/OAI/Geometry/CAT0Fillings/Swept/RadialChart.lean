import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Extensions
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Prism.Chart
import OAI.Geometry.CAT0Fillings.Slicing.EuclideanSplit
import OAI.Geometry.CAT0Fillings.Radial.TestBound
import OAI.Geometry.CAT0Fillings.Radial.TotalBound

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace Prism
noncomputable def tail (k : ℕ) : Euc (k+1) →L[ℝ] Euc k :=
  (ContinuousLinearMap.snd ℝ ℝ (Euc k)).comp (split k).toContinuousLinearMap
@[simp] lemma tail_apply (k : ℕ) (v : Euc (k+1)) :
    tail k v = WithLp.toLp 2 (fun j => v j.succ) := rfl
@[simp] lemma tail_single_zero (k : ℕ) : tail k (EuclideanSpace.single 0 1) = 0 := by
  ext j; simp
@[simp] lemma tail_single_succ (k : ℕ) (j : Fin k) :
    tail k (EuclideanSpace.single j.succ 1) = EuclideanSpace.single j 1 := by
  ext l; simp

def zeroSumEquiv (k : ℕ) : Fin (k+1) ≃ Unit ⊕ Fin k where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := Fin.cases rfl (fun _ => rfl) i
  right_inv i := by rcases i with ⟨⟩ | i <;> rfl
@[simp] lemma zeroSumEquiv_symm_inl (k : ℕ) : (zeroSumEquiv k).symm (Sum.inl ()) = 0 := rfl
@[simp] lemma zeroSumEquiv_symm_inr (k : ℕ) (j : Fin k) :
    (zeroSumEquiv k).symm (Sum.inr j) = j.succ := rfl

noncomputable def radialForm {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (g r t : ℝ) (α γ : Fin k → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  reindex (zeroSumEquiv k).symm (zeroSumEquiv k).symm
    (metricTotalRadialForm G g r t α γ)

lemma radialForm_quadratic {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (g r t : ℝ) (α γ : Fin k → ℝ) (v : Fin (k+1) → ℝ) :
    v ⬝ᵥ (radialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ (fun j => v j.succ))-t*r*(γ ⬝ᵥ (fun j => v j.succ))-r*g*v 0)^2+
      (1-t*g)^2*((fun j => v j.succ) ⬝ᵥ G.mulVec (fun j => v j.succ)-
        (α ⬝ᵥ (fun j => v j.succ))^2) := by
  rw [radialForm,Matrix.reindex_apply,Matrix.submatrix_mulVec_equiv,
    dotProduct_comp_equiv_symm]
  simpa only [Equiv.symm_symm,Function.comp_def,zeroSumEquiv_symm_inl,
    zeroSumEquiv_symm_inr] using
    metricTotalRadialForm_quadratic G g r t α γ (v ∘ (zeroSumEquiv k).symm)
end Prism

theorem swept_radial_test_normalized_det_le
    {k : ℕ} {X : Type*} [MetricSpace X]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set (Euc (k+1))} {x : Euc (k+1)} (hxs : x ∈ s)
    (hx : Tendsto (fun t => volume (s ∩ closedBall x t) / volume (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : Euc (k+1) → X) (o : X) (p : Seminorm ℝ (Euc (k+1)))
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.PosDef)
    (hmetric : ∀ v : Fin (k+1) → ℝ, p (WithLp.toLp 2 v)^2 =
      (fun j => v j.succ) ⬝ᵥ G.mulVec (fun j => v j.succ))
    (g : Euc (k+1) → ℝ) (hg : 0 ≤ g x)
    (hscale : ∀ y ∈ s, 1-y 0*g y ∈ Icc (0:ℝ) 1)
    (α γ : Euc k →L[ℝ] ℝ)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) (α.comp (Prism.tail k)) s x)
    (hγ : HasFDerivWithinAt g (γ.comp (Prism.tail k)) s x)
    (F : Fin (k+1) → Euc (k+1) → ℝ)
    (L : Fin (k+1) → Euc (k+1) →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivWithinAt (F i) (L i) s x)
    (u : Fin (k+1) → X → ℝ) (hu : ∀ i, LipschitzWith 1 (u i))
    (hF : ∀ i y, y ∈ s → F i y = u i (seg o (f y) (1-y 0*g y))) :
    |(Matrix.of fun i j => differentialRow (L i) j).det| / Real.sqrt G.det ≤
      dist o (f x)*g x*(1-x 0*g x)^k *
        Real.sqrt (1-differentialRow α ⬝ᵥ G⁻¹.mulVec (differentialRow α)) := by
  have hcontract (v : Fin k → ℝ) :
      (differentialRow α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v := by
    let w : Fin (k+1) → ℝ := Matrix.vecCons 0 v
    have hr := scalar_derivative_bound_of_metric_differential volume hx hα hp
      (K := 1) (by
        intro y _
        simpa only [one_mul,dist_comm o] using abs_dist_sub_le (f y) (f x) o)
      (WithLp.toLp 2 w)
    have hh := (sq_le_sq₀ (abs_nonneg _) (apply_nonneg p _)).2 (by simpa using hr)
    simpa only [sq_abs,ContinuousLinearMap.comp_apply,Prism.tail_apply,w,
      Matrix.cons_val_succ,hmetric,differentialRow_dot] using hh
  let P := Prism.radialForm G (g x) (dist o (f x)) (x 0)
    (differentialRow α) (differentialRow γ)
  have hP : P.PosSemidef := (metricTotalRadialForm_posSemidef G _ _ _
    (differentialRow α) (differentialRow γ) hG.posSemidef hcontract).submatrix (Prism.zeroSumEquiv k)
  have ht : HasFDerivWithinAt (fun y : Euc (k+1) => y 0)
      (PiLp.proj 2 (fun _ : Fin (k+1) => ℝ) 0) s x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) 0).hasFDerivWithinAt
  have hd : |(Matrix.of fun i j => differentialRow (L i) j).det| ≤ Real.sqrt P.det := by
    apply abs_det_le_sqrt_det_of_posSemidef _ _ hP
    intro i v
    have hr := radial_scalar_derivative_sq_le volume seg hcomp hxs hx f o p hp hscale hα
      ((ht.mul hγ).const_sub 1) (hL i) (hu i) (hF i) (WithLp.toLp 2 v)
    have heq : (L i (WithLp.toLp 2 v))^2 ≤ v ⬝ᵥ P.mulVec v := by
      change _ ≤ v ⬝ᵥ (Prism.radialForm G (g x) (dist o (f x)) (x 0) _ _).mulVec v
      rw [Prism.radialForm_quadratic]
      convert hr using 1
      simp only [differentialRow_dot,ContinuousLinearMap.comp_apply,Prism.tail_apply,
        hmetric,_root_.neg_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,PiLp.proj_apply]
      ring
    change |differentialRow (L i) ⬝ᵥ v| ≤ _
    rw [differentialRow_dot]
    exact (Real.le_sqrt (abs_nonneg _) (hP.dotProduct_mulVec_nonneg v)).2 (by simpa using heq)
  have hdiv := div_le_div_of_nonneg_right hd (Real.sqrt_nonneg G.det)
  have hdet : P.det = (metricTotalRadialForm G (g x) (dist o (f x)) (x 0)
      (differentialRow α) (differentialRow γ)).det := det_reindex_self _ _
  rw [hdet] at hdiv
  exact hdiv.trans_eq (by
    simpa using (metricTotalRadialForm_normalized_sqrt_det G (g x)
      (dist o (f x)) (x 0) (differentialRow α) (differentialRow γ) hG dist_nonneg hg
      (hscale x hxs).1))

lemma metric_differential_pullback
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [PseudoMetricSpace X]
    (A : E →L[ℝ] F) {s : Set E} {t : Set F} {x : E}
    (hst : MapsTo A s t) (f : F → X) (p : Seminorm ℝ F)
    (hp : (fun y => dist (f y) (f (A x))-p (y-A x)) =o[𝓝[t] (A x)] (fun y => y-A x)) :
    (fun y => dist (f (A y)) (f (A x))-(p.comp A.toLinearMap) (y-x))
      =o[𝓝[s] x] (fun y => y-x) := by
  have ht : Tendsto A (𝓝[s] x) (𝓝[t] (A x)) :=
    A.continuous.continuousWithinAt.tendsto_nhdsWithin hst
  have hB : ((fun y => y-A x) ∘ A) =O[𝓝[s] x] (fun y => y-x) := by
    simpa only [Function.comp_def,map_sub] using (A.isBigO_sub (𝓝[s] x) x)
  have h := (hp.comp_tendsto ht).trans_isBigO hB
  convert h using 1; try rfl
  all_goals try { ext y; simp only [Function.comp_def,Seminorm.comp_apply,ContinuousLinearMap.coe_coe,map_sub] }
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma ae_prism_tail {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ}
    (C : IntegerChart X k) {P : Euc k → Prop}
    (h : ∀ᵐ z ∂volume.restrict C.domain, P z) :
    ∀ᵐ z ∂volume.restrict C.prism.domain, P (Prism.tail k z) := by
  have hh := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae h
  rw [Measure.prod_restrict] at hh
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).quasiMeasurePreserving.ae hh

lemma paramExtended_metric_differential {z : Euc k} (hz : z ∈ C.domain)
    {p : Seminorm ℝ (Euc k)}
    (hp : MetricDifferentiation.HasCenteredMetricDifferentialWithin C.domain C.param p ⟨z,hz⟩) :
    (fun y => dist (C.paramExtended y) (C.paramExtended z)-p (y-z))
      =o[𝓝[C.domain] z] (fun y => y-z) := by
  rw [nhdsWithin_eq_map_subtype_coe hz,Asymptotics.isLittleO_map]
  change (fun y : C.domain => dist (C.param y) (C.param ⟨z,hz⟩)-p ((y : Euc k)-z))
    =o[𝓝 (⟨z,hz⟩ : C.domain)] (fun y : C.domain => (y : Euc k)-z) at hp
  convert hp using 1
  · ext y
    simp only [Function.comp_apply,paramExtended,dite_eq_left y.property,dite_eq_left hz,Subtype.coe_eta]
  · rfl

lemma scalar_paramExtended_eqOn (b : X → ℝ) :
    EqOn (fun z => b (C.paramExtended z)) (C.scalar b) C.domain := by
  intro z hz; simp only [paramExtended,scalar,dite_eq_left hz]

noncomputable def sweptWeight (p : Euc k → Seminorm ℝ (Euc k))
    (o : X) (g : X → ℝ) (z : Euc k) : ℝ :=
  let G := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let α := differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
  (C.scalar (dist o) z)*C.scalar g z*Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α)*Real.sqrt G.det

lemma ae_swept_jacobian_bound
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ℝ × X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y, F (t,y) = seg o y (1-t*g y))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin (k+1) → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ z ∂volume.restrict C.prism.domain,
      |C.prism.jacobian (fun i => π i ∘ F) z| ≤ C.sweptWeight p o g (Prism.tail k z) := by
  have htests : ∀ᵐ z ∂volume.restrict C.prism.domain, ∀ i,
      DifferentiableWithinAt ℝ (C.prism.scalar (π i ∘ F)) C.prism.domain z :=
    ae_all_iff.mpr fun i => C.prism.ae_differentiableWithinAt_scalar ((hπ i).comp hF)
  filter_upwards [C.ae_prism_tail hp,ae_restrict_mem C.prism.borel,
    Besicovitch.ae_tendsto_measure_inter_div volume C.prism.domain,
    C.ae_prism_tail (C.ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o)),
    C.ae_prism_tail (C.ae_differentiableWithinAt_scalar hg),htests]
    with z hpz hzs hden hr hgz htests
  have hzt : z 0 ∈ Icc (0:ℝ) 1 := hzs.1
  have hzw : Prism.tail k z ∈ C.domain := hzs.2
  have hmap : MapsTo (Prism.tail k) C.prism.domain C.domain := fun _ hy => hy.2
  let w := Prism.tail k z
  let G := polarizationMatrix (p w) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hquad (v : Fin k → ℝ) : v ⬝ᵥ G.mulVec v = p w (WithLp.toLp 2 v)^2 := by
    have hrepr : (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr (WithLp.toLp 2 v) = v := by
      ext j; simp
    simpa only [hrepr] using polarizationMatrix_quadratic
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (p w) hpz.2.2 hpz.2.1 (WithLp.toLp 2 v)
  have hpe := metric_differential_pullback (Prism.tail k) hmap C.paramExtended (p w)
    (C.paramExtended_metric_differential hzw (hpz.1 hzw))
  have hR := (hr.hasFDerivWithinAt.congr (C.scalar_paramExtended_eqOn (dist o))
    (C.scalar_paramExtended_eqOn (dist o) hzw)).comp z (Prism.tail k).hasFDerivWithinAt hmap
  have hDg := (hgz.hasFDerivWithinAt.congr (C.scalar_paramExtended_eqOn g)
    (C.scalar_paramExtended_eqOn g hzw)).comp z (Prism.tail k).hasFDerivWithinAt hmap
  have hscale : ∀ y ∈ C.prism.domain, 1-y 0*g (C.paramExtended (Prism.tail k y)) ∈ Icc (0:ℝ) 1 := by
    intro y hy
    have ht : y 0 ∈ Icc (0:ℝ) 1 := hy.1
    have h0 := hg0 (C.paramExtended (Prism.tail k y))
    have h1 := hg1 (C.paramExtended (Prism.tail k y))
    constructor
    · exact sub_nonneg.mpr (((mul_le_mul_of_nonneg_right ht.2 h0).trans_eq (one_mul _)).trans h1)
    · exact sub_le_self _ (mul_nonneg ht.1 h0)
  have hh := swept_radial_test_normalized_det_le seg hcomp hzs hden
    (fun y => C.paramExtended (Prism.tail k y)) o ((p w).comp (Prism.tail k).toLinearMap) hpe
    G hG (by intro v; simpa only [Seminorm.comp_apply,ContinuousLinearMap.coe_coe,Prism.tail_apply] using (hquad (fun j => v j.succ)).symm)
    (fun y => g (C.paramExtended (Prism.tail k y))) (hg0 _) hscale
    (fderivWithin ℝ (C.scalar (dist o)) C.domain w)
    (fderivWithin ℝ (C.scalar g) C.domain w) hR hDg
    (fun i => C.prism.scalar (π i ∘ F))
    (fun i => fderivWithin ℝ (C.prism.scalar (π i ∘ F)) C.prism.domain z)
    (fun i => (htests i).hasFDerivWithinAt) π hπ (by
      intro i y hy
      rw [C.prism.scalar_eq hy]
      have hyt : y 0 ∈ Icc (0:ℝ) 1 := hy.1
      have hyw : Prism.tail k y ∈ C.domain := hy.2
      change π i (F (y 0,C.param ⟨Prism.tail k y,hyw⟩)) = _
      rw [hFeq (y 0) hyt]
      simp only [paramExtended,dite_eq_left hyw])
  have hs := (div_le_iff₀ (Real.sqrt_pos.2 hG.det_pos)).mp hh
  change |C.prism.jacobian (fun i => π i ∘ F) z| ≤ _ at hs
  have hlam := hscale z hzs
  have hpow : (1-z 0*g (C.paramExtended w))^k ≤ 1 := pow_le_one₀ hlam.1 hlam.2
  have hn : 0 ≤ dist o (C.paramExtended w)*g (C.paramExtended w) := mul_nonneg dist_nonneg (hg0 _)
  calc
    _ ≤ _ := hs
    _ ≤ dist o (C.paramExtended w)*g (C.paramExtended w)*
        Real.sqrt (1-differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain w) ⬝ᵥ
          G⁻¹.mulVec (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain w))) * Real.sqrt G.det := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hpow hn).trans_eq (mul_one _)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [sweptWeight,←C.scalar_paramExtended_eqOn (dist o) hzw,
        ←C.scalar_paramExtended_eqOn g hzw,w,G]
end IntegerChart
end CAT0Fillings
end

end OAI
