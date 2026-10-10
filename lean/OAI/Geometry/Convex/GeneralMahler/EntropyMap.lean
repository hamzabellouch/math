import OAI.Geometry.Convex.GeneralMahler.GainIndent
import OAI.Geometry.Convex.GeneralMahler.Scatter

namespace OAI
/-! Change of variables/Jensen for the projection scatter map. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Matrix Real
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma det_op (A:Mat m) : (op A).det=A.det := by
  change LinearMap.det (Matrix.toEuclideanLin A)=_
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

def logN0 := Real.log ((√(2*π))⁻¹)
omit [NeZero m] in
lemma logDensity (x:Rn m) : Real.log (nDensity x) = m*logN0- ‖x‖^2/2 := by
  unfold nDensity logN0; rw [Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_exp]; ring

omit [NeZero m] in
lemma i_N2 : Integrable (fun x:Rn m => ‖x‖^2) (normal m) :=
  (PolyBound.id.norm.pow _).gaussian_integrable ((continuous_norm.pow _).aestronglyMeasurable)
omit [NeZero m] in
lemma N2_area : (∫ x:Rn m,‖x‖^2 ∂normal m)=m := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have he (i:Fin m) (x:Rn m) : ⟪x,b i⟫=x i := by
    rw [real_inner_comm]
    exact (b.repr_apply_apply x i).symm
  have hh (i:Fin m) : (∫ x:Rn m, (x i)^2 ∂normal m)=1 := by
    let l := ProjField.coord i
    have hx (x:Rn m) : fderiv ℝ l x (b i)=1 := by
      rw [l.fderiv]
      change b i i = _
      simp [b]
    have h := normal_IBP_lipschitz l.lipschitzWith (b i)
    simp_rw [hx,he] at h
    simp only [smul_eq_mul,l,ProjField.coord_apply] at h
    simpa [pow_two] using h.symm
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp [hh]
  exact fun i _ => ((PolyBound.clm (ProjField.coord i)).pow _).gaussian_integrable
    (((ProjField.coord i).continuous.pow _).aestronglyMeasurable)

namespace Scatter
variable (q:Scatter m) (v:Rn m)
def cost := ∫ x,⟪v,q.t x⟫ ∂normal m
omit [NeZero m] in
lemma i_cost : Integrable (fun x=>⟪v,q.t x⟫) (normal m) :=
  (innerSL ℝ v).integrable_comp q.ti

theorem entropy (h:v∈interior (posDual q.cone:Set (Rn m))) (hq:q.B.det≠0) :
    -logN0+1/2 + logD q.B + (∫ x,logD (q.toEdge.Jedge x) ∂normal m) - q.cost v / m
      ≤ Real.log (chi q.cone v)/m := by
  let g (x:Rn m) := Real.exp (-⟪v,x⟫)
  let f (x:Rn m) := g (q.t x)*|(op (q.TJ x)).det|
  have hd := q.td
  let bad : Set (Rn m) := {x|¬ HasFDerivAt q.t (op (q.TJ x)) x}
  have Hb : volume bad = 0 := ae_iff.mp hd
  obtain ⟨u,hu,hm,hU⟩ := exists_measurable_superset_of_null Hb
  let S := uᶜ
  have hs : MeasurableSet S := hm.compl
  have he : ∀ x∈S,HasFDerivWithinAt q.t (op (q.TJ x)) S x := by
    intro x hx
    have h₁ : x∉bad := fun h' => hx (hu h')
    exact (not_not.mp h₁).hasFDerivWithinAt
  have hr : volume.restrict S=(volume:Measure (Rn m)) := restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; simpa [S] using hU)
  have hg := chi_integrable h
  have ht : q.t '' S ⊆ (q.cone:Set (Rn m)) := by rintro x ⟨y,hy,rfl⟩; exact q.t_in _
  have he' := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume:Measure (Rn m)) hs he q.t_injective.injOn g
  have hF : Integrable f := by
    have h := he'.mp (hg.mono_set ht)
    unfold IntegrableOn at h; rw [hr] at h
    convert h using 1
    ext x; change _*_= _*_ ; ring
  have H : (∫ x,f x) ≤ chi q.cone v := by
    have hi := integral_image_eq_integral_abs_det_fderiv_smul
      (volume:Measure (Rn m)) hs he q.t_injective.injOn g
    rw [hr] at hi
    calc
      _ = ∫ x in q.t '' S,g x := by rw [hi]; congr 1; ext x; change _*_=_*_; ring
      _ ≤ _ := setIntegral_mono_set hg (ae_of_all _ fun x=>Real.exp_nonneg _) (Filter.Eventually.of_forall ht)
  let K := fun x=>f x/(nDensity x)
  have hj (x:Rn m) : nDensity x • K x=f x := by
    unfold K
    rw [smul_eq_mul]
    field_simp [ne_of_gt (nDensity_pos _)]
  have hK : Integrable K (normal m) := normal_integrable_iff.mpr (by simp_rw [hj]; exact hF)
  have heK (x:Rn m) :
      |(op (q.TJ x)).det|=(q.toEdge.Jedge x).det*|q.B.det| := by
    rw [det_op,TJ,det_mul,abs_mul,abs_of_pos (q.toEdge.Jedge_pd x).det_pos]
  have hp (x:Rn m) : 0<K x := by
    unfold K f g; rw [heK]
    exact div_pos
      (mul_pos (Real.exp_pos _) (mul_pos (q.toEdge.Jedge_pd x).det_pos (abs_pos.mpr hq))) (nDensity_pos _)
  let c := ∫ x,K x ∂normal m
  have hc : 0 < c := by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(hp x).le) hK).mpr
    rw [show Function.support K=univ from eq_univ_of_forall fun x=>(hp x).ne',measure_univ]
    norm_num
  have hl : c≤chi q.cone v := by unfold c; rw [normal_integral]; simp_rw [hj]; exact H
  let a (x:Rn m) := (m:ℝ)*logD q.B + (m:ℝ)*logD (q.toEdge.Jedge x)
  let b (x:Rn m) := (m:ℝ)*logN0 - ‖x‖^2/2
  have Mm := ProjField.m_pos (m:=m)
  have ha (x:Rn m) : Real.log (K x) = a x-⟪v,q.t x⟫-b x := by
    unfold K f g
    rw [heK,Real.log_div,Real.log_mul,Real.log_exp,logDensity,Real.log_mul]
    · unfold a b logD; rw [Real.log_abs]; field_simp; ring
    all_goals
      have h₁ := (q.toEdge.Jedge_pd x).det_pos; have h₂ := abs_pos.mpr hq; have h₃ := nDensity_pos x; positivity
  have ia₁ := q.toEdge.gain_int.const_mul (m:ℝ)
  have ia : Integrable a (normal m) := (integrable_const _).add ia₁
  have ib : Integrable b (normal m) := (integrable_const _).sub (i_N2.div_const _)
  have iK : Integrable (fun x=>Real.log (K x)) (normal m) := by
    simp_rw [ha]
    exact (ia.sub (q.i_cost v)).sub ib
  have hh : (∫ x,Real.log (K x) ∂normal m) ≤ Real.log (chi q.cone v) := by
    apply le_trans _ (Real.log_le_log hc hl)
    let W (x:Rn m) := Real.log c+(K x / c-1)
    have hv := hK.div_const c
    have ih := hv.sub (integrable_const (1:ℝ))
    have he := integral_mono iK (show Integrable W (normal m) from
      (integrable_const _).add ih) (fun x=> ?_)
    · apply he.trans_eq
      unfold W
      rw [integral_add,integral_sub hv (integrable_const _),integral_div]
      · change (∫ x:Rn m,Real.log c ∂normal m)+(c/c-_) = _
        rw [div_self hc.ne']; simp
      all_goals first | exact integrable_const _ | exact ih
    · have h := Real.log_le_sub_one_of_pos (div_pos (hp x) hc)
      rw [Real.log_div (hp x).ne' hc.ne'] at h
      unfold W; linarith
  simp_rw [ha] at hh
  rw [integral_sub,integral_sub ia (q.i_cost v)] at hh
  · unfold a b at hh
    rw [integral_add (integrable_const _) ia₁,integral_sub,integral_const_mul, integral_div,N2_area] at hh
    · simp only [integral_const,probReal_univ,one_smul] at hh
      rw [integral_const_mul] at hh
      rw [le_div_iff₀ Mm]
      unfold cost
      field_simp
      nlinarith
    all_goals first | exact i_N2.div_const _ | exact integrable_const _
  · exact ia.sub (q.i_cost v)
  · exact ib

end Scatter
end GeneralMahler

end

end OAI
