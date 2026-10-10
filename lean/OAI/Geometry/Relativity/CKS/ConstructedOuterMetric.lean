import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.PhysicalFoliationConstraints
import OAI.Geometry.Relativity.CKS.PhysicalAccelerationNorm
import OAI.Geometry.Relativity.CKS.PhysicalLeafConnection
import OAI.Geometry.Relativity.CKS.SourcePhysicalFoliation
import OAI.Geometry.Relativity.CKS.CollarRadialFields
import OAI.Geometry.Relativity.CKS.OuterBounds
import OAI.Geometry.Relativity.CKS.OuterMetricComparison

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology Matrix

 def sphericalAngularMetric (x : CKSRealizedRound.Point) : CKSAngularGeometry.Mat :=
  Matrix.diagonal ![1, Real.sin (x 1)^2]

lemma sphericalAngularMetric_posDef {x : CKSRealizedRound.Point} (hs : Real.sin (x 1) ≠ 0) :
    (sphericalAngularMetric x).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i
  · norm_num
  · exact sq_pos_of_ne_zero hs

lemma outerMetric_foliation (F : CKSRealizedRound.Point → ℝ) (v : ℝ → ℝ) (x : CKSRealizedRound.Point) :
    CKSRealizedRound.outerMetric F v x =
      CKSAngularGeometry.foliationMetric (CKSRealizedRound.lapse F v x)
        (x 0 ^ 2 • sphericalAngularMetric x) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CKSRealizedRound.outerMetric, CKSRealizedRound.metric,
      CKSAngularGeometry.foliationMetric,CKSAngularGeometry.metricBlock,sphericalAngularMetric,
      Matrix.of_apply,Matrix.smul_apply]

theorem constructed_outer_metric_lower (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R, R₀ ≤ R → 0 < l R ∧ l R ≤ 1) ∧
      ∀ (R : ℝ) (x : CKSRealizedRound.Point), R₀ ≤ R → 3*R ≤ x 0 →
      Real.sin (x 1) ≠ 0 → ∀ w : Fin 3 → ℝ,
      l R * CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.metricBlock 1 0 (sphericalAngularMetric x)) w ≤
      CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.radialNormalize (x 0)
          (CKSRealizedRound.outerMetric (outerMass f₀ m R) (bendingV R) x)) w := by
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  let R₀ := max 12 (4*M)
  refine ⟨R₀,le_max_left _ _,CKSAngularGeometry.outerComparisonFactor M,
    CKSAngularGeometry.outerComparisonFactor_tendsto M,?_,?_⟩
  · intro R hR
    have hRp : 0<R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) ((le_max_left _ _).trans hR)
    exact ⟨CKSAngularGeometry.outerComparisonFactor_pos hM hRp,
      CKSAngularGeometry.outerComparisonFactor_le_one hM hRp⟩
  intro R x hR hr hs
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hMR : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0<R := by linarith
  have hrp : 0<x 0 := by linarith
  have hm := (hbound R hR12 x hr hs).1
  have hp := CKSAngularGeometry.outer_radicand_positive hrp hm (by linarith : 4*M ≤ x 0)
    (v := bendingV R (x 0))
  rw [outerMetric_foliation]
  exact CKSAngularGeometry.outer_metric_lower (by linarith) (by linarith) hM hm
    (bendingV_nonneg hRp hrp) (bendingV_le_radius hRp hrp) hp
    (sphericalAngularMetric_posDef hs)

end
end CKSSphericalChart

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set
def minkowski (x y : V) : ℝ := -x.1 * y.1 + inner ℝ x.2 y.2

def mass (e : ℝ) (p : E) : ℝ := Real.sqrt (e^2 - ‖p‖^2)

lemma energy_pos {e : ℝ} {p : E} (h : ‖p‖ < e) : 0 < e := (norm_nonneg p).trans_lt h
lemma mass_pos {e : ℝ} {p : E} (h : ‖p‖ < e) : 0 < mass e p := by
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg p, energy_pos h]
lemma mass_sq {e : ℝ} {p : E} (h : ‖p‖ < e) : mass e p ^2 = e^2 - ‖p‖^2 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg p, energy_pos h]
lemma inner_momentum {e m : ℝ} {p : E} (hm : m^2 = e^2 - ‖p‖^2) :
    inner ℝ p p = e^2-m^2 := by rw [real_inner_self_eq_norm_sq]; linarith

def boost (e m : ℝ) (p : E) (x : V) : V :=
  ((e*x.1 + inner ℝ p x.2)/m,
    x.2 + (x.1/m + inner ℝ p x.2/(m*(e+m))) • p)

lemma boost_minkowski {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (x y : V) :
    minkowski (boost e m p x) (boost e m p y) = minkowski x y := by
  simp only [minkowski, boost, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm x.2 p, inner_momentum hm]
  field_simp
  ring

lemma boost_neg_inverse {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (x : V) :
    boost e m (-p) (boost e m p x) = x := by
  apply Prod.ext
  · simp only [boost, inner_neg_left, inner_add_right, inner_smul_right,
      inner_momentum hm]
    field_simp
    ring
  · simp only [boost, inner_neg_left, inner_add_right, inner_smul_right,
      inner_momentum hm, smul_neg]
    have hc : x.1 / m + inner ℝ p x.2 / (m * (e + m)) -
        ((e * x.1 + inner ℝ p x.2) / m / m +
          -(inner ℝ p x.2 + (x.1 / m + inner ℝ p x.2 / (m * (e+m))) * (e^2-m^2)) / (m*(e+m))) = 0 := by
      field_simp
      ring
    calc
      _ = x.2 + (x.1 / m + inner ℝ p x.2 / (m * (e + m)) -
        ((e * x.1 + inner ℝ p x.2) / m / m +
          -(inner ℝ p x.2 + (x.1 / m + inner ℝ p x.2 / (m*(e+m))) * (e^2-m^2)) / (m*(e+m)))) • p := by module
      _ = x.2 := by rw [hc]; simp

lemma boost_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (boost e m p) := by
  have hi : ContDiff ℝ ∞ (fun x : V => inner ℝ p x.2) := ContDiff.inner ℝ contDiff_const contDiff_snd
  unfold boost
  exact (((contDiff_const.mul contDiff_fst).add hi).div_const m).prodMk
    (contDiff_snd.add (((contDiff_fst.div_const m).add
      (hi.div_const (m*(e+m)))).smul contDiff_const))

lemma boost_mass {e m : ℝ} {p : E} (hm0 : m ≠ 0) : boost e m p (m,0) = (e,p) := by
  simp [boost, hm0]

lemma sphere_norm (n : Sphere) : ‖(n : E)‖ = 1 := by simp

def denominator (e m : ℝ) (p : E) (n : E) : ℝ := (e + inner ℝ p n)/m

def boundarySpatial (e m : ℝ) (p : E) (n : E) : E :=
  n + (1/m + inner ℝ p n/(m*(e+m))) • p

lemma denominator_pos {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm : 0 < m) (n : Sphere) :
    0 < denominator e m p n := by
  apply div_pos _ hm
  have hi := neg_le_abs (inner ℝ p (n:E))
  have hb := (abs_real_inner_le_norm p (n:E))
  rw [sphere_norm] at hb
  nlinarith

lemma boundarySpatial_norm {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) :
    ‖boundarySpatial e m p n‖ = denominator e m p n := by
  have hd : e+m ≠ 0 := ne_of_gt (add_pos (energy_pos he) hm0)
  have h := boost_minkowski hm0.ne' hd hm ((1:ℝ),(n:E)) ((1:ℝ),(n:E))
  have hn := sphere_norm n
  change -((e*1 + inner ℝ p (n:E))/m) * ((e*1 + inner ℝ p (n:E))/m) +
    inner ℝ (boundarySpatial e m p n) (boundarySpatial e m p n) =
    -(1:ℝ)*1 + inner ℝ (n:E) (n:E) at h
  simp only [mul_one] at h
  change -(denominator e m p n) * (denominator e m p n) + _ = _ at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn] at h
  have hp := denominator_pos he hm0 n
  nlinarith [norm_nonneg (boundarySpatial e m p n)]

def boundary (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) : Sphere :=
  ⟨(denominator e (mass e p) p n)⁻¹ • boundarySpatial e (mass e p) p n, by
    have hm := mass_pos he
    have hp := denominator_pos he hm n
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp), boundarySpatial_norm he hm (mass_sq he), inv_mul_cancel₀ hp.ne']⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boostCLM (e m : ℝ) (p : E) : V →L[ℝ] V where
  toFun := boost e m p
  map_add' := by
    intro x y
    apply Prod.ext
    · simp only [boost, Prod.fst_add, Prod.snd_add, inner_add_right]; ring
    · simp only [boost, Prod.fst_add, Prod.snd_add, inner_add_right]
      module
  map_smul' := by
    intro c x
    apply Prod.ext
    · change (e*(c*x.1) + inner ℝ p (c • x.2))/m = c*((e*x.1 + inner ℝ p x.2)/m)
      rw [inner_smul_right]
      ring
    · change c • x.2 + ((c*x.1)/m + inner ℝ p (c • x.2)/(m*(e+m))) • p =
        c • (x.2 + (x.1/m + inner ℝ p x.2/(m*(e+m))) • p)
      rw [inner_smul_right]
      module
  cont := (boost_smooth e m p).continuous

@[simp] lemma boostCLM_apply (e m : ℝ) (p : E) (x : V) :
    boostCLM e m p x = boost e m p x := rfl

lemma mass_neg (e : ℝ) (p : E) : mass e (-p) = mass e p := by simp [mass]

lemma boost_neg_right_inverse {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (x : V) : boost e m p (boost e m (-p) x) = x := by
  simpa using boost_neg_inverse (p := -p) hm0 hd (by simpa using hm) x

def boostEquiv (e : ℝ) (p : E) (he : ‖p‖ < e) : V ≃L[ℝ] V where
  toLinearEquiv := {
    toLinearMap := (boostCLM e (mass e p) p).toLinearMap
    invFun := boost e (mass e p) (-p)
    left_inv := boost_neg_inverse (mass_pos he).ne'
      (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)
    right_inv := boost_neg_right_inverse (mass_pos he).ne'
      (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he) }
  continuous_toFun := (boost_smooth e (mass e p) p).continuous
  continuous_invFun := (boost_smooth e (mass e p) (-p)).continuous

def boundaryAmbient (e m : ℝ) (p : E) (n : E) : E :=
  (denominator e m p n)⁻¹ • boundarySpatial e m p n

lemma boundary_null (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boost e (mass e p) p (1,(n:E)) =
      denominator e (mass e p) p n • ((1:ℝ), (boundary e p he n : E)) := by
  have hd := (denominator_pos he (mass_pos he) n).ne'
  apply Prod.ext
  · simp [boost, denominator]
  · change boundarySpatial e (mass e p) p n =
      denominator e (mass e p) p n • ((denominator e (mass e p) p n)⁻¹ • _)
    simp [smul_smul, hd]

lemma boundary_inverse (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boundary e (-p) (by simpa using he) (boundary e p he n) = n := by
  let m := mass e p
  let D := denominator e m p n
  let n' := boundary e p he n
  have hD : D ≠ 0 := (denominator_pos he (mass_pos he) n).ne'
  have h := congrArg (boostCLM e m (-p)) (boundary_null e p he n)
  simp only [map_smul, boostCLM_apply] at h
  rw [boost_neg_inverse (mass_pos he).ne'
    (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)] at h
  change ((1:ℝ),(n:E)) = D • boost e m (-p) (1,(n':E)) at h
  have htime := congrArg Prod.fst h
  have hspace := congrArg Prod.snd h
  change (1:ℝ) = D * ((e*1 + inner ℝ (-p) (n':E))/m) at htime
  simp only [mul_one] at htime
  change (1:ℝ) = D * denominator e m (-p) n' at htime
  change (n:E) = D • boundarySpatial e m (-p) n' at hspace
  apply Subtype.ext
  change (denominator e (mass e (-p)) (-p) n')⁻¹ •
    boundarySpatial e (mass e (-p)) (-p) n' = (n:E)
  rw [mass_neg]
  have hc : (denominator e m (-p) n')⁻¹ = D := by
    apply inv_eq_of_mul_eq_one_right
    simpa [mul_comm] using htime.symm
  rw [hc]
  exact hspace.symm

lemma boundaryAmbient_smooth {e m : ℝ} {p : E} {n : E}
    (hd : denominator e m p n ≠ 0) : ContDiffAt ℝ ∞ (boundaryAmbient e m p) n := by
  have hi : ContDiff ℝ ∞ (fun n : E => inner ℝ p n) :=
    ContDiff.inner ℝ contDiff_const contDiff_id
  have hD : ContDiff ℝ ∞ (denominator e m p) :=
    (contDiff_const.add hi).div_const m
  have hS : ContDiff ℝ ∞ (boundarySpatial e m p) :=
    contDiff_id.add ((contDiff_const.add (hi.div_const (m*(e+m)))).smul contDiff_const)
  exact (hD.contDiffAt.inv hd).smul hS.contDiffAt

instance : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

lemma boundary_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (boundary e p he) := by
  have h : ContMDiff (𝓡 2) 𝓘(ℝ,E) ∞
      (fun n : Sphere => boundaryAmbient e (mass e p) p n) := by
    intro n
    exact (boundaryAmbient_smooth (denominator_pos he (mass_pos he) n).ne').comp_contMDiffAt
      (contMDiff_coe_sphere (E := E) (n := 2)).contMDiffAt
  exact h.codRestrict_sphere fun n => (boundary e p he n).property

def boundaryHomeomorph (e : ℝ) (p : E) (he : ‖p‖ < e) : Sphere ≃ₜ Sphere where
  toEquiv := {
    toFun := boundary e p he
    invFun := boundary e (-p) (by simpa using he)
    left_inv := boundary_inverse e p he
    right_inv := by intro n; simpa using boundary_inverse e (-p) (by simpa using he) n }
  continuous_toFun := (boundary_smooth e p he).continuous
  continuous_invFun := (boundary_smooth e (-p) (by simpa using he)).continuous

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperTime (x : E) : ℝ := Real.sqrt (1+‖x‖^2)
def hyperboloid (x : E) : V := (hyperTime x, x)
def hyperbolicMap (e m : ℝ) (p : E) (x : E) : E := (boost e m p (hyperboloid x)).2

lemma hyperTime_pos (x : E) : 0 < hyperTime x := Real.sqrt_pos.2 (by positivity)
lemma hyperTime_sq (x : E) : hyperTime x ^2 = 1+‖x‖^2 := Real.sq_sqrt (by positivity)
lemma norm_lt_hyperTime (x : E) : ‖x‖ < hyperTime x := by
  have := hyperTime_sq x
  have := hyperTime_pos x
  nlinarith [norm_nonneg x]
lemma hyperTime_smooth : ContDiff ℝ ∞ hyperTime :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)
lemma hyperboloid_smooth : ContDiff ℝ ∞ hyperboloid := hyperTime_smooth.prodMk contDiff_id
lemma hyperbolicMap_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (hyperbolicMap e m p) :=
  ((boost_smooth e m p).comp hyperboloid_smooth).snd

lemma boosted_time_pos {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm : 0 < m) (x : E) :
    0 < (boost e m p (hyperboloid x)).1 := by
  apply div_pos _ hm
  have hab := abs_real_inner_le_norm p x
  have hneg := neg_le_abs (inner ℝ p x)
  have hprod : ‖p‖ * ‖x‖ < e * hyperTime x := by
    calc
      _ ≤ ‖p‖ * hyperTime x := mul_le_mul_of_nonneg_left (norm_lt_hyperTime x).le (norm_nonneg p)
      _ < _ := mul_lt_mul_of_pos_right he (hyperTime_pos x)
  change 0 < e * hyperTime x + inner ℝ p x
  linarith

lemma hyperboloid_minkowski (x : E) : minkowski (hyperboloid x) (hyperboloid x) = -1 := by
  simp only [minkowski, hyperboloid, real_inner_self_eq_norm_sq]
  nlinarith [hyperTime_sq x]

theorem hyperboloid_boost {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (x : E) :
    hyperboloid (hyperbolicMap e m p x) = boost e m p (hyperboloid x) := by
  apply Prod.ext
  · have h := boost_minkowski hm0.ne' (add_pos (energy_pos he) hm0).ne' hm
      (hyperboloid x) (hyperboloid x)
    rw [hyperboloid_minkowski] at h
    change -(boost e m p (hyperboloid x)).1 * (boost e m p (hyperboloid x)).1 +
      inner ℝ (hyperbolicMap e m p x) (hyperbolicMap e m p x) = -1 at h
    rw [real_inner_self_eq_norm_sq] at h
    change hyperTime _ = _
    nlinarith [hyperTime_sq (hyperbolicMap e m p x),
      hyperTime_pos (hyperbolicMap e m p x), boosted_time_pos he hm0 x]
  · rfl

lemma hyperbolicMap_inverse (e : ℝ) (p : E) (he : ‖p‖ < e) (x : E) :
    hyperbolicMap e (mass e p) (-p) (hyperbolicMap e (mass e p) p x) = x := by
  change (boost e (mass e p) (-p) (hyperboloid (hyperbolicMap e (mass e p) p x))).2 = x
  rw [hyperboloid_boost he (mass_pos he) (mass_sq he),
    boost_neg_inverse (mass_pos he).ne' (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)]
  rfl

def hyperbolicHomeomorph (e : ℝ) (p : E) (he : ‖p‖ < e) : E ≃ₜ E where
  toEquiv := {
    toFun := hyperbolicMap e (mass e p) p
    invFun := hyperbolicMap e (mass e p) (-p)
    left_inv := hyperbolicMap_inverse e p he
    right_inv := by intro x; simpa [mass_neg] using hyperbolicMap_inverse e (-p) (by simpa using he) x }
  continuous_toFun := (hyperbolicMap_smooth e (mass e p) p).continuous
  continuous_invFun := (hyperbolicMap_smooth e (mass e p) (-p)).continuous

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

lemma hyperTime_derivative (x : E) :
    HasFDerivAt hyperTime ((hyperTime x)⁻¹ • innerSL ℝ x) x := by
  have h := (Real.hasDerivAt_sqrt (show 1+‖x‖^2 ≠ 0 by positivity)).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1)
  convert! h using 1
  ext Y
  simp [hyperTime, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma hyperboloid_derivative_pair (x Y Z : E) :
    minkowski (fderiv ℝ hyperboloid x Y) (fderiv ℝ hyperboloid x Z) = hyperbolicMetric x Y Z := by
  have hd := (hyperTime_derivative x).prodMk (hasFDerivAt_id x)
  change HasFDerivAt hyperboloid _ x at hd
  rw [hd.fderiv]
  simp only [minkowski, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul, hyperbolicMetric]
  rw [← hyperTime_sq]
  ring

theorem hyperbolicMap_isometry {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (x Y Z : E) :
    hyperbolicMetric (hyperbolicMap e m p x)
      (fderiv ℝ (hyperbolicMap e m p) x Y) (fderiv ℝ (hyperbolicMap e m p) x Z) =
        hyperbolicMetric x Y Z := by
  have heq : hyperboloid ∘ hyperbolicMap e m p = boostCLM e m p ∘ hyperboloid := by
    funext z; exact hyperboloid_boost he hm0 hm z
  have hh := congrArg (fun f : E → V => fderiv ℝ f x) heq
  rw [fderiv_comp x (hyperboloid_smooth.differentiable (by simp)).differentiableAt
      ((hyperbolicMap_smooth e m p).differentiable (by simp)).differentiableAt,
    fderiv_comp x (boostCLM e m p).differentiableAt
      (hyperboloid_smooth.differentiable (by simp)).differentiableAt,
    (boostCLM e m p).fderiv] at hh
  have hy := congrArg (fun L : E →L[ℝ] V => L Y) hh
  have hz := congrArg (fun L : E →L[ℝ] V => L Z) hh
  simp only [ContinuousLinearMap.comp_apply] at hy hz
  rw [← hyperboloid_derivative_pair, hy, hz]
  exact (boost_minkowski hm0.ne' (add_pos (energy_pos he) hm0).ne' hm _ _).trans
    (hyperboloid_derivative_pair x Y Z)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff

def timeDifferential (m : ℝ) (p : E) : E →L[ℝ] ℝ := m⁻¹ • innerSL ℝ p

def spaceDifferential (e m : ℝ) (p : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + ((m*(e+m))⁻¹ • innerSL ℝ p).smulRight p

@[simp] lemma timeDifferential_apply (m : ℝ) (p Y : E) :
    timeDifferential m p Y = inner ℝ p Y /m := by simp [timeDifferential, div_eq_mul_inv, mul_comm]
@[simp] lemma spaceDifferential_apply (e m : ℝ) (p Y : E) :
    spaceDifferential e m p Y = Y + (inner ℝ p Y/(m*(e+m))) • p := by
  simp [spaceDifferential, div_eq_mul_inv, mul_comm]

lemma denominator_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (denominator e m p) (timeDifferential m p) n := by
  convert! ((innerSL ℝ p).hasFDerivAt.const_add e).mul_const m⁻¹ using 1

lemma boundarySpatial_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (boundarySpatial e m p) (spaceDifferential e m p) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.mul_const (m*(e+m))⁻¹).const_add (1/m)).smul_const p) using 1

lemma boundaryAmbient_fderiv {e m : ℝ} {p n : E} (hd : denominator e m p n ≠ 0) (Y : E) :
    fderiv ℝ (boundaryAmbient e m p) n Y =
      (denominator e m p n)⁻¹ • spaceDifferential e m p Y -
        (timeDifferential m p Y / (denominator e m p n)^2) • boundarySpatial e m p n := by
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt n (denominator_derivative e m p n)
  have h := hi.smul (boundarySpatial_derivative e m p n)
  change HasFDerivAt (boundaryAmbient e m p) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  change _ = _
  simp only [smul_eq_mul, Function.comp_apply]
  module

lemma minkowski_null_tangent {e m : ℝ} {p n : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y : E) :
    -(denominator e m p n) * timeDifferential m p Y +
      inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) = inner ℝ n Y := by
  convert boost_minkowski hm0 hd hm ((1:ℝ),n) ((0:ℝ),Y) using 1 <;>
    simp [minkowski, boost, denominator, boundarySpatial]

lemma minkowski_tangent_tangent {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y Z : E) :
    -timeDifferential m p Y * timeDifferential m p Z +
      inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) = inner ℝ Y Z := by
  convert boost_minkowski hm0 hd hm ((0:ℝ),Y) ((0:ℝ),Z) using 1 <;>
    simp [minkowski, boost]

theorem boundary_conformal {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) (Y Z : E)
    (hY : inner ℝ (n:E) Y = 0) (hZ : inner ℝ (n:E) Z = 0) :
    inner ℝ (fderiv ℝ (boundaryAmbient e m p) n Y)
      (fderiv ℝ (boundaryAmbient e m p) n Z) =
        (denominator e m p n)⁻¹ ^2 * inner ℝ Y Z := by
  have hD := (denominator_pos he hm0 n).ne'
  have hd := (add_pos (energy_pos he) hm0).ne'
  have hy := minkowski_null_tangent hm0.ne' hd hm Y (n := (n:E))
  have hz := minkowski_null_tangent hm0.ne' hd hm Z (n := (n:E))
  have hyz := minkowski_tangent_tangent hm0.ne' hd hm Y Z
  rw [hY] at hy
  rw [hZ] at hz
  have hself : inner ℝ (boundarySpatial e m p n) (boundarySpatial e m p n) =
      (denominator e m p n)^2 := by
    rw [real_inner_self_eq_norm_sq, boundarySpatial_norm he hm0 hm]
  rw [boundaryAmbient_fderiv hD, boundaryAmbient_fderiv hD]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hself]
  rw [real_inner_comm (boundarySpatial e m p n) (spaceDifferential e m p Y)]
  have hy' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) =
      denominator e m p n * timeDifferential m p Y := by linarith
  have hz' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Z) =
      denominator e m p n * timeDifferential m p Z := by linarith
  have hyz' : inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) =
      inner ℝ Y Z + timeDifferential m p Y * timeDifferential m p Z := by linarith
  rw [hy', hz', hyz']
  field_simp [hD]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

def compactRoot (s : ℝ) : ℝ := Real.sqrt (1+s^2)
def compactSpatial (e m : ℝ) (p : E) (z : ℝ × E) : E :=
  z.2 + (compactRoot z.1/m + inner ℝ p z.2/(m*(e+m))) • p
def compactScale (e m : ℝ) (p : E) (z : ℝ × E) : ℝ := ‖compactSpatial e m p z‖
def spatialCorrection (m : ℝ) (p : E) (z : ℝ × E) : E :=
  (m*(compactRoot z.1+1))⁻¹ • p
def squareCorrection (e m : ℝ) (p : E) (z : ℝ × E) : ℝ :=
  (e^2 + 2*e*inner ℝ p z.2/(compactRoot z.1+1))/m^2 - 1
def radialCorrection (e m : ℝ) (p : E) (z : ℝ × E) : ℝ :=
  squareCorrection e m p z / (compactScale e m p z + denominator e m p z.2)
def angularCorrection (e m : ℝ) (p : E) (z : ℝ × E) : E :=
  (compactScale e m p z)⁻¹ • spatialCorrection m p z -
    (radialCorrection e m p z / (compactScale e m p z * denominator e m p z.2)) •
      boundarySpatial e m p z.2

lemma compactRoot_pos (s : ℝ) : 0 < compactRoot s := Real.sqrt_pos.2 (by positivity)
lemma compactRoot_add_one_pos (s : ℝ) : 0 < compactRoot s+1 := by linarith [compactRoot_pos s]
lemma compactRoot_sq (s : ℝ) : compactRoot s ^2 = 1+s^2 := Real.sq_sqrt (by positivity)
@[simp] lemma compactRoot_zero : compactRoot 0 = 1 := by simp [compactRoot]
lemma compactRoot_sub (s : ℝ) : compactRoot s - 1 = s^2/(compactRoot s+1) := by
  apply (eq_div_iff (compactRoot_add_one_pos s).ne').2
  nlinarith [compactRoot_sq s]
lemma compactRoot_smooth : ContDiff ℝ ∞ compactRoot :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => by positivity)

lemma compactSpatial_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (compactSpatial e m p) := by
  have hi := ContDiff.inner ℝ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => p)) contDiff_snd
  exact contDiff_snd.add ((((compactRoot_smooth.comp contDiff_fst).div_const m).add
    (hi.div_const (m*(e+m)))).smul contDiff_const)

@[simp] lemma compactSpatial_zero (e m : ℝ) (p n : E) :
    compactSpatial e m p (0,n) = boundarySpatial e m p n := by
  simp [compactSpatial, boundarySpatial]

lemma compactSpatial_expansion (e m : ℝ) (p : E) (s : ℝ) (n : E) :
    compactSpatial e m p (s,n) = boundarySpatial e m p n +
      s^2 • spatialCorrection m p (s,n) := by
  have h := compactRoot_sub s
  simp only [compactSpatial, boundarySpatial, spatialCorrection]
  have hs : compactRoot s/m = 1/m+s^2*(m*(compactRoot s+1))⁻¹ := by
    calc
      _ = (1+s^2/(compactRoot s+1))/m := by congr 1; linarith
      _ = _ := by simp only [mul_inv_rev]; ring
  rw [hs]
  module

lemma compactScale_sq {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (s : ℝ) (n : Sphere) :
    compactScale e m p (s,n)^2 = denominator e m p n ^2 +
      s^2 * squareCorrection e m p (s,n) := by
  have hd := (add_pos (energy_pos he) hm0).ne'
  have h := boost_minkowski hm0.ne' hd hm (compactRoot s,(n:E)) (compactRoot s,(n:E))
  change -((e*compactRoot s + inner ℝ p (n:E))/m) *
    ((e*compactRoot s + inner ℝ p (n:E))/m) +
    inner ℝ (compactSpatial e m p (s,n)) (compactSpatial e m p (s,n)) =
    -compactRoot s*compactRoot s + inner ℝ (n:E) (n:E) at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, sphere_norm] at h
  have hroot := compactRoot_sq s
  have hs := compactRoot_sub s
  change ‖compactSpatial e m p (s,n)‖^2 = _
  unfold denominator squareCorrection
  dsimp only
  have hr := (compactRoot_add_one_pos s).ne'
  have ha : ‖compactSpatial e m p (s,n)‖^2 =
      ((e*compactRoot s+inner ℝ p (n:E))/m)^2-s^2 := by nlinarith
  rw [ha, show s^2 = compactRoot s^2-1 by linarith]
  field_simp
  ring

lemma compactScale_expansion {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (s : ℝ) (n : Sphere) :
    compactScale e m p (s,n) = denominator e m p n +
      s^2 * radialCorrection e m p (s,n) := by
  have hs := compactScale_sq he hm0 hm s n
  have hp : 0 < compactScale e m p (s,n) + denominator e m p n :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) (denominator_pos he hm0 n)
  unfold radialCorrection
  dsimp only
  field_simp
  nlinarith

lemma compactAngle_expansion {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (s : ℝ) (n : Sphere)
    (hA : compactScale e m p (s,n) ≠ 0) :
    (compactScale e m p (s,n))⁻¹ • compactSpatial e m p (s,n) =
      boundaryAmbient e m p n + s^2 • angularCorrection e m p (s,n) := by
  have hD := (denominator_pos he hm0 n).ne'
  have heq := compactScale_expansion he hm0 hm s n
  rw [compactSpatial_expansion]
  unfold boundaryAmbient angularCorrection
  dsimp only
  have hc : (compactScale e m p (s,n))⁻¹ = (denominator e m p n)⁻¹ -
      s^2 * (radialCorrection e m p (s,n) /
        (compactScale e m p (s,n) * denominator e m p n)) := by
    field_simp
    nlinarith
  rw [smul_add]
  conv_lhs => lhs; rw [hc]
  module

lemma compactScale_smooth_at_zero {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) :
    ContDiffAt ℝ ∞ (compactScale e m p) (0,(n:E)) := by
  apply (compactSpatial_smooth e m p).contDiffAt.norm ℝ
  rw [compactSpatial_zero]
  exact norm_ne_zero_iff.mp (by rw [boundarySpatial_norm he hm0 hm]; exact (denominator_pos he hm0 n).ne')

lemma spatialCorrection_smooth (m : ℝ) (p : E) : ContDiff ℝ ∞ (spatialCorrection m p) := by
  have h : ContDiff ℝ ∞ (fun z : ℝ × E => (compactRoot z.1+1)⁻¹) :=
    ((compactRoot_smooth.comp contDiff_fst).add contDiff_const).inv
      (fun z => (compactRoot_add_one_pos z.1).ne')
  convert! (h.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => m⁻¹))).smul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => p)) using 1
  funext z
  simp [spatialCorrection, mul_inv_rev, mul_comm]

lemma squareCorrection_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (squareCorrection e m p) := by
  have hi := ContDiff.inner ℝ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => p)) contDiff_snd
  exact ((contDiff_const.add ((contDiff_const.mul hi).div
    ((compactRoot_smooth.comp contDiff_fst).add contDiff_const) (fun z => (compactRoot_add_one_pos z.1).ne'))).div_const _).sub contDiff_const

lemma radialCorrection_smooth_at_zero {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) :
    ContDiffAt ℝ ∞ (radialCorrection e m p) (0,(n:E)) := by
  have hD : ContDiff ℝ ∞ (fun z : ℝ × E => denominator e m p z.2) :=
    (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_snd)).div_const m
  apply (squareCorrection_smooth e m p).contDiffAt.div
    ((compactScale_smooth_at_zero he hm0 hm n).add hD.contDiffAt)
  change compactScale e m p (0,n) + denominator e m p n ≠ 0
  rw [compactScale, compactSpatial_zero, boundarySpatial_norm he hm0 hm]
  linarith [denominator_pos he hm0 n]

lemma angularCorrection_smooth_at_zero {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) :
    ContDiffAt ℝ ∞ (angularCorrection e m p) (0,(n:E)) := by
  have hA := compactScale_smooth_at_zero he hm0 hm n
  have ha : compactScale e m p (0,n) ≠ 0 := by
    rw [compactScale, compactSpatial_zero, boundarySpatial_norm he hm0 hm]
    exact (denominator_pos he hm0 n).ne'
  have hD : ContDiff ℝ ∞ (fun z : ℝ × E => denominator e m p z.2) :=
    (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_snd)).div_const m
  have hS : ContDiff ℝ ∞ (fun z : ℝ × E => boundarySpatial e m p z.2) := by
    convert! (compactSpatial_smooth e m p).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => (0:ℝ))).prodMk contDiff_snd) using 1
    funext z; simp
  exact ((hA.inv ha).smul (spatialCorrection_smooth m p).contDiffAt).sub
    (((radialCorrection_smooth_at_zero he hm0 hm n).div (hA.mul hD.contDiffAt)
      (mul_ne_zero ha (denominator_pos he hm0 n).ne')).smul hS.contDiffAt)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

def compactRegion (e m : ℝ) (p : E) : Set (ℝ × E) :=
  {z | 0 < denominator e m p z.2 ∧ 0 < compactScale e m p z}

def correctionPair (e m : ℝ) (p : E) (z : ℝ × E) : ℝ × E :=
  (radialCorrection e m p z, angularCorrection e m p z)

lemma denominator_joint_smooth (e m : ℝ) (p : E) :
    ContDiff ℝ ∞ (fun z : ℝ × E => denominator e m p z.2) :=
  (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_snd)).div_const m

lemma boundarySpatial_joint_smooth (e m : ℝ) (p : E) :
    ContDiff ℝ ∞ (fun z : ℝ × E => boundarySpatial e m p z.2) := by
  convert! (compactSpatial_smooth e m p).comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => (0:ℝ))).prodMk contDiff_snd) using 1
  funext z; simp

lemma compactRegion_open (e m : ℝ) (p : E) : IsOpen (compactRegion e m p) :=
  (isOpen_lt continuous_const (denominator_joint_smooth e m p).continuous).inter
    (isOpen_lt continuous_const (compactSpatial_smooth e m p).continuous.norm)

lemma compactScale_smooth_region (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactScale e m p) z :=
  (compactSpatial_smooth e m p).contDiffAt.norm ℝ (norm_ne_zero_iff.mp hz.2.ne')

lemma correctionPair_smooth_region (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (correctionPair e m p) z := by
  have hA := compactScale_smooth_region e m p hz
  have hD := (denominator_joint_smooth e m p).contDiffAt (x := z)
  have hR : ContDiffAt ℝ ∞ (radialCorrection e m p) z :=
    (squareCorrection_smooth e m p).contDiffAt.div (hA.add hD) (add_pos hz.2 hz.1).ne'
  exact hR.prodMk (((hA.inv hz.2.ne').smul (spatialCorrection_smooth m p).contDiffAt).sub
    ((hR.div (hA.mul hD) (mul_pos hz.2 hz.1).ne').smul (boundarySpatial_joint_smooth e m p).contDiffAt))

theorem exists_compact_collar {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| ≤ δ → ∀ n : Sphere,
      (s,(n:E)) ∈ compactRegion e m p := by
  let K : Set (ℝ × E) := ({0} : Set ℝ) ×ˢ Metric.sphere (0:E) 1
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_sphere (0:E) 1)
  have hsub : K ⊆ compactRegion e m p := by
    intro z hz
    rcases z with ⟨s,n⟩
    obtain ⟨rfl, hn⟩ := hz
    refine ⟨denominator_pos he hm0 ⟨n,hn⟩, ?_⟩
    change 0 < ‖compactSpatial e m p (0,n)‖
    rw [compactSpatial_zero, boundarySpatial_norm he hm0 hm ⟨n,hn⟩]
    exact denominator_pos he hm0 ⟨n,hn⟩
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open (compactRegion_open e m p) hsub
  refine ⟨δ,hδ,fun s hs n => hδK ?_⟩
  apply Metric.mem_cthickening_of_dist_le (s,(n:E)) (0,(n:E)) δ K
  · exact ⟨rfl,n.2⟩
  · simpa [Prod.dist_eq, Real.dist_eq] using hs

lemma correction_jets_continuous_region (e m : ℝ) (p : E) (j : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ j (correctionPair e m p)) (compactRegion e m p) := by
  intro z hz
  have h := correctionPair_smooth_region e m p hz
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  exact (h.continuousAt_iteratedFDeriv hj).continuousWithinAt

theorem coordinate_coefficients_all_orders {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ s : ℝ, |s| ≤ δ → ∀ n : Sphere,
      (s,(n:E)) ∈ compactRegion e m p) ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, |s| ≤ δ → ∀ n : Sphere,
        ‖iteratedFDeriv ℝ j (correctionPair e m p) (s,(n:E))‖ ≤ C := by
  obtain ⟨δ,hδ,hcol⟩ := exists_compact_collar he hm0 hm
  refine ⟨δ,hδ,hcol,fun j => ?_⟩
  let K : Set (ℝ × E) := Icc (-δ) δ ×ˢ Metric.sphere (0:E) 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere (0:E) 1)
  have hsub : K ⊆ compactRegion e m p := by
    intro z hz
    exact hcol z.1 (abs_le.mpr hz.1) ⟨z.2,hz.2⟩
  have hc := (correction_jets_continuous_region e m p j).mono hsub
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro s hs n
  have hmem : (s,(n:E)) ∈ K := ⟨abs_le.mp hs,n.2⟩
  exact (hC (s,(n:E)) hmem).trans (le_max_right 0 C)

lemma hyperTime_polar {ρ : ℝ} (hρ : 0 < ρ) (n : Sphere) :
    hyperTime (ρ • (n:E)) = ρ * compactRoot ρ⁻¹ := by
  have hsq : (ρ*compactRoot ρ⁻¹)^2 = 1+‖ρ • (n:E)‖^2 := by
    rw [mul_pow, compactRoot_sq, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, sphere_norm, mul_one]
    field_simp
    ring
  have hp : 0 < ρ * compactRoot ρ⁻¹ := mul_pos hρ (compactRoot_pos _)
  nlinarith [hyperTime_sq (ρ • (n:E)), hyperTime_pos (ρ • (n:E))]

lemma hyperbolicMap_polar {ρ : ℝ} (hρ : 0 < ρ) (e m : ℝ) (p : E) (n : Sphere) :
    hyperbolicMap e m p (ρ • (n:E)) = ρ • compactSpatial e m p (ρ⁻¹,(n:E)) := by
  unfold hyperbolicMap boost hyperboloid
  rw [hyperTime_polar hρ]
  simp only [compactSpatial, inner_smul_right]
  module

theorem actual_radius_expansion {e m ρ : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (hρ : 0 < ρ) (n : Sphere) :
    ‖hyperbolicMap e m p (ρ • (n:E))‖ =
      ρ * denominator e m p n + ρ⁻¹ * radialCorrection e m p (ρ⁻¹,(n:E)) := by
  rw [hyperbolicMap_polar hρ, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  change ρ * compactScale e m p (ρ⁻¹,(n:E)) = _
  rw [compactScale_expansion he hm0 hm]
  field_simp

theorem actual_angle_expansion {e m ρ : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (hρ : 0 < ρ) (n : Sphere)
    (hA : compactScale e m p (ρ⁻¹,(n:E)) ≠ 0) :
    ‖hyperbolicMap e m p (ρ • (n:E))‖⁻¹ • hyperbolicMap e m p (ρ • (n:E)) =
      boundaryAmbient e m p n + ρ⁻¹ ^2 • angularCorrection e m p (ρ⁻¹,(n:E)) := by
  rw [hyperbolicMap_polar hρ, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
    smul_smul, mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel₀ hρ.ne', mul_one]
  exact compactAngle_expansion he hm0 hm ρ⁻¹ n hA

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma multilinear_norm_of_components {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Point) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : Fin n → I, ‖M (fun i => basis (a i))‖ ≤ C) :
    ‖M‖ ≤ 3^n * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : M v = ∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i)) := by
    calc M v = M (fun i => ∑ k : I, v i k • basis k) := by
          congr 1; funext i; exact (sum_coordinate_basis _).symm
         _ = ∑ a : Fin n → I, M (fun i => v i (a i) • basis (a i)) := M.map_sum _
         _ = _ := by simp only [M.map_smul_univ, smul_eq_mul]
  rw [he]
  calc ‖∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i))‖
      ≤ ∑ a : Fin n → I, ‖(∏ i, v i (a i)) * M (fun i => basis (a i))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin n → I, (∏ i, ‖v i‖) * C := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, norm_prod]
      apply mul_le_mul
      · apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        intro i _
        exact norm_le_pi_norm (v i) (a i)
      · exact hb a
      · exact norm_nonneg _
      · positivity
    _ = 3^n * C * ∏ i, ‖v i‖ := by simp [mul_comm, mul_left_comm, mul_assoc]

lemma iteratedFDeriv_basis_ofFn (n : ℕ) (a : Fin n → I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ n f x) :
    iteratedFDeriv ℝ n f x (fun i => basis (a i)) = coordinateIter (List.ofFn a) f x := by
  induction n generalizing x with
  | zero => simp [coordinateIter]
  | succ n ih =>
    have hd := hf.differentiableAt_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) =ᶠ[𝓝 x]
        coordinateIter (List.ofFn (Fin.tail a)) f := by
      have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast Nat.le_succ n)
      filter_upwards [hfn.eventually (by simp)] with y hy
      exact ih (Fin.tail a) hy
    have hlist : List.ofFn a = a 0 :: List.ofFn (Fin.tail a) := by
      conv_lhs => rw [← Fin.cons_self_tail a]
      exact List.ofFn_cons _ _
    rw [hlist]
    change D (basis (a 0)) (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) x = _
    exact D_congr he _

lemma coordinateIter_le_iteratedFDeriv (l : List I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ l.length f x) :
    |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ := by
  have he := iteratedFDeriv_basis_ofFn l.length l.get hf
  rw [List.ofFn_get] at he
  rw [← he, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ l.length f x).le_opNorm (fun i => basis (l.get i))
  have hn (i : Fin l.length) : ‖basis (l.get i)‖ = 1 := by simp [basis, Pi.norm_single]
  simpa only [hn, Finset.prod_const_one, mul_one] using h

lemma source_scaledComponent_norm_derivative
    (j q n : ℕ) {B : ℝ} (hB : 0 ≤ B) (hn : n ≤ j)
    {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ j f (logRadiusChart x))
    (hb : ScaledComponentBound f j q B (logRadiusChart x)) :
    ‖iteratedFDeriv ℝ n (fun y => f (logRadiusChart y)) x‖ ≤
      3^n * (B / (Real.exp (x 0))^q) := by
  apply multilinear_norm_of_components _ (by positivity)
  intro a
  have hfn : ContDiffAt ℝ n f (logRadiusChart x) := hf.of_le (by exact_mod_cast hn)
  have hcomp := hfn.comp x (logRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  change ‖iteratedFDeriv ℝ n (f ∘ logRadiusChart) x (fun i => basis (a i))‖ ≤ _
  rw [iteratedFDeriv_basis_ofFn n a hcomp, Real.norm_eq_abs]
  simp only [Function.comp_def]
  rw [coordinateIter_pullback (f := f) (x := x) (List.ofFn a) (by simpa only [List.length_ofFn] using hfn)]
  have h := hb (List.ofFn a) (by simpa using hn)
  simpa only [logRadiusChart, ite_true] using h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def inverseLogRadiusChart (x : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i=0 then Real.exp (-x 0) else x i

def backwardFactor (a : I) (y : Point) : ℝ :=
  letI := pointDimension_neZero
  if a=0 then -y 0 else 1

def backwardScaledD (a : I) (f : Point → ℝ) (y : Point) : ℝ :=
  backwardFactor a y * D (basis a) f y

def backwardScaledIter (directions : List I) (function : Point → ℝ) : Point → ℝ :=
  directions.foldr backwardScaledD function

@[simp] lemma backwardScaledIter_nil (function : Point → ℝ) :
    backwardScaledIter [] function = function := by
  simp only [backwardScaledIter, List.foldr_nil]

@[simp] lemma backwardScaledIter_cons (direction : I) (directions : List I)
    (function : Point → ℝ) :
    backwardScaledIter (direction :: directions) function =
      backwardScaledD direction (backwardScaledIter directions function) := by
  simp only [backwardScaledIter, List.foldr_cons]

lemma inverseLogRadiusChart_smooth : ContDiff ℝ ∞ inverseLogRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=0 <;> simp only [inverseLogRadiusChart,hi,ite_true,ite_false] <;> fun_prop

lemma backwardFactor_smooth (a : I) : ContDiff ℝ ∞ (backwardFactor a) := by
  change ContDiff ℝ ∞ (fun y : Point => if a=0 then -y 0 else 1)
  split_ifs <;> fun_prop

def inverseChartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i=0 then (-Real.exp (-x 0)) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma inverseLogRadiusChart_hasFDerivAt (x : Point) :
    HasFDerivAt inverseLogRadiusChart (inverseChartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    have h := (Real.hasDerivAt_exp (-x 0)).comp_hasFDerivAt x
      ((ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt.neg)
    change HasFDerivAt (fun y : Point => Real.exp (-y 0))
      ((-Real.exp (-x 0)) • ContinuousLinearMap.proj 0) x
    convert h using 1 <;> ext y <;> simp
  · simp only [inverseLogRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma inverseChartDerivative_basis (a : I) (x : Point) :
    inverseChartDerivative x (basis a) = backwardFactor a (inverseLogRadiusChart x) • basis a := by
  ext i
  by_cases ha : a=0 <;> by_cases hi : i=0
  · subst a; subst i; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis]
  · subst a; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis,hi]
  · subst i; simp [inverseChartDerivative,backwardFactor,basis,ha,Ne.symm ha]
  · simp [inverseChartDerivative,backwardFactor,basis,ha,hi]

lemma D_inverse_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (inverseLogRadiusChart x)) :
    D (basis a) (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledD a f (inverseLogRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ inverseLogRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (inverseLogRadiusChart_hasFDerivAt x).differentiableAt,
    (inverseLogRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,inverseChartDerivative_basis,map_smul,
    smul_eq_mul,backwardScaledD,D]

lemma backwardScaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) :
    ContDiffAt ℝ m (backwardScaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,backwardScaledIter_nil] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((backwardFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by simp) (basis a))

lemma coordinateIter_inverse_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (inverseLogRadiusChart x)) :
    coordinateIter l (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledIter l f (inverseLogRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (inverseLogRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => backwardScaledIter l f (inverseLogRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (inverseLogRadiusChart x) := hf.of_le (by simp)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (inverseLogRadiusChart y) :=
        inverseLogRadiusChart_smooth.continuous.continuousAt.eventually (hf'.eventually (by simp))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (inverseLogRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (inverseLogRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_inverse_pullback a ((backwardScaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

theorem compactified_scalar_uniform_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤ C := by
  let Q : Point → (Fin n → I) → ℝ := fun z a => backwardScaledIter (List.ofFn a) f z
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro a
    exact (backwardScaledIter_contDiffAt (List.ofFn a) 0
      ((hf z hz).of_le (by simp))).continuousAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨3^n * max 0 C,by positivity,?_⟩
  intro x hx
  apply multilinear_norm_of_components _ (le_max_left _ _)
  intro a
  have hfn : ContDiffAt ℝ n f (inverseLogRadiusChart x) :=
    (hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    hfn.comp x (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  rw [iteratedFDeriv_basis_ofFn n a hcomp]
  rw [coordinateIter_inverse_pullback (f := f) (x := x) (List.ofFn a) (by simpa using hfn)]
  exact (norm_le_pi_norm (Q (inverseLogRadiusChart x)) a).trans ((hC _ hx).trans (le_max_right _ _))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem compactified_vector_uniform_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → Point} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤ C := by
  classical
  have hc (k : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x‖ ≤ C :=
    compactified_scalar_uniform_jets n hK (f := fun z => f z k)
      (fun z hz => (contDiffAt_pi.mp (hf z hz)) k)
  choose C hC hbound using hc
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro x hx
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    ((hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp x
      (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun k _ => hC k))
  intro v
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun k _ => hC k)) (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))).mpr
  intro k
  have he := (ContinuousLinearMap.proj k : Point →L[ℝ] ℝ).iteratedFDeriv_comp_left hcomp (i := n) le_rfl
  have hv : (iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x v) k =
      iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x v := by
    exact (congrArg (fun M => M v) he).symm
  rw [hv]
  exact ((iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y) k) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((hbound k x hx).trans
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ k))) (by positivity))

lemma linear_positive_jet_bound (L : Point →L[ℝ] Point) (n : ℕ) (hn : 1 ≤ n) (x : Point) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ ‖L‖ := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
      rw [he,iteratedFDeriv_succ_const]
      simp

def logAffineCompactMap (L : Point →L[ℝ] Point) (f : Point → Point) (x : Point) : Point :=
  L x + f (inverseLogRadiusChart x)

theorem logAffineCompactMap_uniform_jets (j : ℕ) (L : Point →L[ℝ] Point)
    {K : Set Point} (hK : IsCompact K) {f : Point → Point}
    (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ j →
        ‖iteratedFDeriv ℝ n (logAffineCompactMap L f) x‖ ≤ D^n := by
  classical
  choose C hC hbound using (fun n : Fin (j+1) => compactified_vector_uniform_jets n.val hK hf)
  let D : ℝ := 1 + ‖L‖ + ∑ n, C n
  have hs : 0 ≤ ∑ n, C n := Finset.sum_nonneg (fun n _ => hC n)
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg L]
  refine ⟨D,hD,?_⟩
  intro x hx n hn hnj
  have hfn : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    ((hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp x
      (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  change ‖iteratedFDeriv ℝ n ((L : Point → Point) + (fun y => f (inverseLogRadiusChart y))) x‖ ≤ _
  rw [iteratedFDeriv_add_apply L.contDiff.contDiffAt hfn]
  have hCn : C ⟨n,by omega⟩ ≤ ∑ i, C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _)
  calc ‖iteratedFDeriv ℝ n L x + iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖
      ≤ ‖iteratedFDeriv ℝ n L x‖ + ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ := norm_add_le _ _
    _ ≤ ‖L‖ + C ⟨n,by omega⟩ := add_le_add (linear_positive_jet_bound L n hn x) (hbound ⟨n,by omega⟩ x hx)
    _ ≤ D := by dsimp [D]; linarith
    _ ≤ D^n := by simpa only [pow_one] using pow_le_pow_right₀ hD hn

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice
open scoped ContDiff

def radialLinear : Point →L[ℝ] Point :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).smulRight (basis 0)

def compactPolar (φ : Angle → E) (z : Point) : ℝ × E :=
  (z 0, φ (angularProjection z))

def compactAngle (e m : ℝ) (p : E) (z : ℝ × E) : E :=
  (compactScale e m p z)⁻¹ • compactSpatial e m p z

def compactLorentzCoefficients (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (z : Point) : Point :=
  slice (Real.log (compactScale e m p (compactPolar φ z)))
    (ψ (compactAngle e m p (compactPolar φ z)))

def logLorentzChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) : Point → Point :=
  logAffineCompactMap radialLinear (compactLorentzCoefficients e m p φ ψ)

def lorentzPolarChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (y : Point) : Point :=
  let v := hyperbolicMap e m p (y 0 • φ (angularProjection y))
  slice ‖v‖ (ψ (‖v‖⁻¹ • v))

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma compactPolar_contDiffAt {φ : Angle → E} {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) : ContDiffAt ℝ ∞ (compactPolar φ) z :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.contDiffAt.prodMk
    (hφ.comp z angularProjection.contDiff.contDiffAt)

lemma compactAngle_contDiffAt (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactAngle e m p) z :=
  ((compactScale_smooth_region e m p hz).inv hz.2.ne').smul
    (compactSpatial_smooth e m p).contDiffAt

lemma compactLorentzCoefficients_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z := by
  have hp := compactPolar_contDiffAt hφ
  have hA := (compactScale_smooth_region e m p hz).comp z hp
  have ha := (compactAngle_contDiffAt e m p hz).comp z hp
  have hang := hψ.comp z ha
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [compactLorentzCoefficients,slice_zero,Function.comp_def] using hA.log hz.2.ne'
  · simpa only [compactLorentzCoefficients,slice_succ,Function.comp_def] using (contDiffAt_pi.mp hang) a

lemma logLorentzChart_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) :
    ContDiffAt ℝ ∞ (logLorentzChart e m p φ ψ) x :=
  radialLinear.contDiff.contDiffAt.add
    ((compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ).comp x
      inverseLogRadiusChart_smooth.contDiffAt)

theorem logLorentzChart_uniform_jets (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ j →
        ‖iteratedFDeriv ℝ n (logLorentzChart e m p φ ψ) x‖ ≤ D^n :=
  logAffineCompactMap_uniform_jets j radialLinear hK
    (fun z hz => compactLorentzCoefficients_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz))

@[simp] lemma angularProjection_inverseLogRadiusChart (x : Point) :
    angularProjection (inverseLogRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,inverseLogRadiusChart,Fin.succ_ne_zero]

@[simp] lemma angularProjection_logRadiusChart (x : Point) :
    angularProjection (logRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,logRadiusChart,Fin.succ_ne_zero]

lemma logLorentzChart_eq_slice (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (x : Point) :
    logLorentzChart e m p φ ψ x =
      slice (x 0 + Real.log (compactScale e m p (compactPolar φ (inverseLogRadiusChart x))))
        (ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logLorentzChart,logAffineCompactMap,radialLinear,basis,compactLorentzCoefficients]
  · simp [logLorentzChart,logAffineCompactMap,radialLinear,basis,compactLorentzCoefficients,
      Fin.succ_ne_zero]

lemma logLorentzChart_radial_exp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hA : 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart x))) :
    Real.exp ((logLorentzChart e m p φ ψ x) 0) =
      Real.exp (x 0) * compactScale e m p (compactPolar φ (inverseLogRadiusChart x)) := by
  rw [logLorentzChart_eq_slice,slice_zero,Real.exp_add,Real.exp_log hA]

lemma logRadiusChart_slice (r : ℝ) (a : Angle) :
    logRadiusChart (slice r a) = slice (Real.exp r) a := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

theorem lorentzPolarChart_logRadiusChart (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {x : Point}
    (hn : φ (angularProjection x) ∈ Metric.sphere (0 : E) 1)
    (hA : 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart x))) :
    lorentzPolarChart e m p φ ψ (logRadiusChart x) =
      logRadiusChart (logLorentzChart e m p φ ψ x) := by
  let ρ := Real.exp (x 0)
  let n : Sphere := ⟨φ (angularProjection x),hn⟩
  have hρ : 0 < ρ := Real.exp_pos _
  have he : compactPolar φ (inverseLogRadiusChart x) = (ρ⁻¹,(n:E)) := by
    simp [compactPolar,inverseLogRadiusChart,ρ,n,Real.exp_neg]
  have hv : hyperbolicMap e m p ((logRadiusChart x) 0 • φ (angularProjection (logRadiusChart x))) =
      ρ • compactSpatial e m p (compactPolar φ (inverseLogRadiusChart x)) := by
    simpa only [logRadiusChart,ite_true,angularProjection_logRadiusChart,he] using
      hyperbolicMap_polar hρ e m p n
  unfold lorentzPolarChart
  rw [hv,logLorentzChart_eq_slice,logRadiusChart_slice,Real.exp_add,Real.exp_log hA]
  dsimp only
  congr 1
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    rfl
  · congr 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ,smul_smul,mul_inv_rev]
    simp only [mul_assoc,inv_mul_cancel₀ hρ.ne',mul_one]
    rfl

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma local_norm_iteratedFDeriv_comp {f : Point → Point} {g : Point → ℝ}
    {n : ℕ} {x : Point} (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x)
    {C D : ℝ}
    (hC : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * C * D^n := by
  obtain ⟨t,htsub,htopen,hft⟩ := mem_nhds_iff.mp (hg.eventually (by simp))
  have ht : t ∈ 𝓝 (f x) := htopen.mem_nhds hft
  have he := (hf.eventually (by simp)).and (hf.continuousAt.preimage_mem_nhds ht)
  obtain ⟨s,hsub,hsopen,hxs⟩ := mem_nhds_iff.mp he
  have hgs : ContDiffOn ℝ n g t := fun y hy => (show ContDiffAt ℝ n g y from htsub hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hsub hy).1.contDiffWithinAt
  have hst : MapsTo f s t := fun y hy => (hsub hy).2
  have hCv (i : ℕ) (hi : i ≤ n) : ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv htopen.uniqueDiffOn
      (hg.of_le (by exact_mod_cast hi)) hft]
    exact hC i hi
  have hDv (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D^i := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hi)) hxs]
    exact hD i hi1 hi
  have h := norm_iteratedFDerivWithin_comp_le hgs hfs (by rfl) htopen.uniqueDiffOn
    hsopen.uniqueDiffOn hst hxs hCv hDv
  rwa [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn (hg.comp x hf) hxs] at h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem source_scaledComponent_pullback
    (j q : ℕ) {B D : ℝ} (hB : 0 ≤ B) (_hD0 : 1 ≤ D)
    {f : Point → ℝ} {F : Point → Point} {x : Point}
    (hf : ContDiffAt ℝ j f (logRadiusChart (F x)))
    (hF : ContDiffAt ℝ j F x)
    (hb : ScaledComponentBound f j q B (logRadiusChart (F x)))
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i F x‖ ≤ D^i) :
    ∀ l : List I, l.length ≤ j →
      |coordinateIter l (fun y => f (logRadiusChart (F y))) x| ≤
        (l.length.factorial : ℝ) * 3^l.length * D^l.length * B /
          (Real.exp ((F x) 0))^q

 := by
  intro l hl
  let g : Point → ℝ := fun y => f (logRadiusChart y)
  have hg : ContDiffAt ℝ j g (F x) := hf.comp (F x)
    (logRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
  have hgn : ContDiffAt ℝ l.length g (F x) := hg.of_le (by exact_mod_cast hl)
  have hFn : ContDiffAt ℝ l.length F x := hF.of_le (by exact_mod_cast hl)
  have hC (i : ℕ) (hi : i ≤ l.length) :
      ‖iteratedFDeriv ℝ i g (F x)‖ ≤ 3^l.length * (B / (Real.exp ((F x) 0))^q) := by
    exact (source_scaledComponent_norm_derivative j q i hB (hi.trans hl) hf hb).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hi) (by positivity))
  have h := local_norm_iteratedFDeriv_comp hgn hFn hC
    (fun i hi1 hi => hD i hi1 (hi.trans hl))
  have hh := coordinateIter_le_iteratedFDeriv l (hgn.comp x hFn)
  have he : (l.length.factorial : ℝ) *
      (3^l.length * (B / (Real.exp ((F x) 0))^q)) * D^l.length =
      (l.length.factorial : ℝ) * 3^l.length * D^l.length * B /
          (Real.exp ((F x) 0))^q := by ring
  rw [he] at h
  exact hh.trans h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_finite_remainder_pullback (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Point → ℝ) (B : ℝ), 0 ≤ B →
      ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ContDiffAt ℝ j f (logRadiusChart (logLorentzChart e m p φ ψ x)) →
      ScaledComponentBound f j q B (logRadiusChart (logLorentzChart e m p φ ψ x)) →
      ∀ l : List I, l.length ≤ j →
      |coordinateIter l (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x| ≤
        C * B / (Real.exp (x 0))^q := by
  classical
  let A : Point → ℝ := fun z => compactScale e m p (compactPolar φ z)
  have hA (z : Point) (hz : z ∈ K) : 0 < A z := (hreg z hz).2
  have hAs (z : Point) (hz : z ∈ K) : ContDiffAt ℝ ∞ A z :=
    (compactScale_smooth_region e m p (hreg z hz)).comp z (compactPolar_contDiffAt (hφ z hz))
  have hc : ContinuousOn (fun z => ((A z)^q)⁻¹) K := by
    intro z hz
    exact (((hAs z hz).pow q).inv (pow_ne_zero q (hA z hz).ne')).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨D,hD,hjets⟩ := logLorentzChart_uniform_jets e m p φ ψ j hK hφ hreg hψ
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  let N : ℝ := (j.factorial : ℝ)*3^j*D^j
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨N * max 0 M,mul_nonneg hN0 (le_max_left _ _),?_⟩
  intro f B hB x hx hf hb l hl
  have hFx : ContDiffAt ℝ j (logLorentzChart e m p φ ψ) x :=
    (logLorentzChart_contDiffAt e m p φ ψ (hφ _ hx) (hreg _ hx) (hψ _ hx)).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hscaled := source_scaledComponent_pullback j q hB hD hf hFx hb (hjets x hx) l hl
  have hfac : (l.length.factorial : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hl
  have hN : (l.length.factorial : ℝ)*3^l.length*D^l.length ≤ N :=
    mul_le_mul (mul_le_mul hfac (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hl)
      (by positivity) (by positivity)) (pow_le_pow_right₀ hD hl) (pow_nonneg hD0 _)
      (by positivity)
  have hAi0 : 0 ≤ ((A (inverseLogRadiusChart x))^q)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (hA _ hx).le _)
  have hAi : ((A (inverseLogRadiusChart x))^q)⁻¹ ≤ max 0 M := by
    have h := hM (inverseLogRadiusChart x) hx
    rw [Real.norm_eq_abs,abs_of_nonneg hAi0] at h
    exact h.trans (le_max_right _ _)
  have hcoef := mul_le_mul hN hAi hAi0 hN0
  have heq : (l.length.factorial : ℝ)*3^l.length*D^l.length*B /
        Real.exp ((logLorentzChart e m p φ ψ x) 0)^q =
      ((l.length.factorial : ℝ)*3^l.length*D^l.length) *
        ((A (inverseLogRadiusChart x))^q)⁻¹ * B / Real.exp (x 0)^q := by
    rw [logLorentzChart_radial_exp e m p φ ψ (hA _ hx)]
    dsimp [A]
    simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq] at hscaled
  exact hscaled.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hB) (by positivity))
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def LogJetBound (f : Point → ℝ) (j : ℕ) (q C : ℝ) (x : Point) : Prop :=
  ∀ n : ℕ, n ≤ j → ‖iteratedFDeriv ℝ n f x‖ ≤ C * radiusPower (-q) x

lemma local_norm_iteratedFDeriv_mul {f g : Point → ℝ} {n : ℕ} {x : Point}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨s,hs,hsopen,hxs⟩ := mem_nhds_iff.mp
    ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hs hy).1.contDiffWithinAt
  have hgs : ContDiffOn ℝ n g s := fun y hy => (hs hy).2.contDiffWithinAt
  have h := norm_iteratedFDerivWithin_mul_le hfs hgs hsopen.uniqueDiffOn hxs (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn (hf.mul hg) hxs] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hi')) hxs,
    iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hxs]

lemma LogJetBound.mul {f g : Point → ℝ} {x : Point} {j : ℕ} {q r C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x)
    (hb : LogJetBound f j q C x) (hc : LogJetBound g j r D x) :
    LogJetBound (fun y => f y * g y) j (q+r) (2^j*C*D) x := by
  intro n hn
  have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast hn)
  have hgn : ContDiffAt ℝ n g x := hg.of_le (by exact_mod_cast hn)
  calc
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      local_norm_iteratedFDeriv_mul hfn hgn
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
          (C * radiusPower (-q) x)*(D * radiusPower (-r) x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hn)) (by positivity))
        (hc (n-i) ((Nat.sub_le n i).trans hn)) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg hC (radiusPower_pos _ _).le))
    _ = 2^n*C*D * radiusPower (-(q+r)) x := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) = 2^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hsum]
      have he : radiusPower (-(q+r)) x = radiusPower (-q) x * radiusPower (-r) x := by
        simp only [radiusPower,neg_add,add_mul,Real.exp_add]
      rw [he]
      ring
    _ ≤ 2^j*C*D * radiusPower (-(q+r)) x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) hC) hD)
        (radiusPower_pos _ _).le

lemma LogJetBound.of_source {f : Point → ℝ} {x : Point} {j q : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ContDiffAt ℝ j f (logRadiusChart x))
    (hb : ScaledComponentBound f j q C (logRadiusChart x)) :
    LogJetBound (fun y => f (logRadiusChart y)) j q (3^j*C) x := by
  intro n hn
  have h := source_scaledComponent_norm_derivative j q n hC hn hf hb
  calc
    _ ≤ 3^n*(C / Real.exp (x 0)^q) := h
    _ ≤ 3^j*(C / Real.exp (x 0)^q) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn) (by positivity)
    _ = (3^j*C) * radiusPower (-(q:ℝ)) x := by rw [radiusPower_neg_nat]; ring

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def radialEigenvalue (t : ℝ) (directions : List I) : ℝ :=
  letI := pointDimension_neZero
  directions.foldr (fun direction product => (t*basis direction 0)*product) 1

@[simp] lemma radialEigenvalue_nil (exponent : ℝ) :
    radialEigenvalue exponent [] = 1 := by
  simp only [radialEigenvalue, List.foldr_nil]

@[simp] lemma radialEigenvalue_cons (exponent : ℝ) (direction : I)
    (directions : List I) :
    radialEigenvalue exponent (direction :: directions) =
      (exponent*basis direction 0)*radialEigenvalue exponent directions := by
  simp only [radialEigenvalue, List.foldr_cons]

lemma coordinateIter_radiusPower (t : ℝ) (l : List I) :
    coordinateIter l (radiusPower t) = fun x => radialEigenvalue t l * radiusPower t x := by
  induction l with
  | nil => simp [coordinateIter,radialEigenvalue]
  | cons a l ih =>
    funext x
    simp only [coordinateIter,ih]
    rw [D_const_mul (basis a) _ ((radiusPower_smooth t).contDiffAt.differentiableAt (by simp))]
    simp only [D_radiusPower,radialEigenvalue_cons]
    ring

lemma abs_radialEigenvalue (t : ℝ) (l : List I) :
    |radialEigenvalue t l| ≤ |t|^l.length := by
  induction l with
  | nil => simp [radialEigenvalue]
  | cons a l ih =>
    simp only [radialEigenvalue_cons,abs_mul,List.length_cons,pow_succ]
    calc |t| * |basis a 0| * |radialEigenvalue t l|
        ≤ (|t| *1) * |t|^l.length :=
          mul_le_mul (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg t)) ih
            (abs_nonneg _) (by positivity)
      _ = |t|^l.length * |t| := by ring

lemma radiusPower_logJet (j : ℕ) (q : ℝ) (x : Point) :
    LogJetBound (radiusPower (-q)) j q (3^j * (max 1 |q|)^j) x := by
  intro n hn
  have hc : 0 ≤ |q|^n * radiusPower (-q) x :=
    mul_nonneg (pow_nonneg (abs_nonneg q) _) (radiusPower_pos _ _).le
  have hb := multilinear_norm_of_components (iteratedFDeriv ℝ n (radiusPower (-q)) x) hc
    (fun a => by
      rw [iteratedFDeriv_basis_ofFn n a (radiusPower_diff (-q) n x),
        coordinateIter_radiusPower,Real.norm_eq_abs,abs_mul,
        abs_of_pos (radiusPower_pos (-q) x)]
      have he : |radialEigenvalue (-q) (List.ofFn a)| ≤ |q|^n := by
        simpa only [abs_neg,List.length_ofFn] using abs_radialEigenvalue (-q) (List.ofFn a)
      exact mul_le_mul_of_nonneg_right he (radiusPower_pos _ _).le)
  have hpow : |q|^n ≤ (max 1 |q|)^j :=
    (pow_le_pow_left₀ (abs_nonneg q) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hn)
  calc _ ≤ 3^n * (|q|^n * radiusPower (-q) x) := hb
    _ ≤ 3^j * ((max 1 |q|)^j * radiusPower (-q) x) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn)
        (mul_le_mul_of_nonneg_right hpow (radiusPower_pos _ _).le) hc (by positivity)
    _ = _ := by ring

lemma compactified_uniform_logJet (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      LogJetBound (fun y => f (inverseLogRadiusChart y)) j 0 C x := by
  classical
  choose C hC hb using (fun n : Fin (j+1) => compactified_scalar_uniform_jets n.val hK hf)
  refine ⟨∑ n, C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro x hx n hn
  have hc : C ⟨n,by omega⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ _)
  simpa [radiusPower] using (hb ⟨n,by omega⟩ x hx).trans hc

theorem weighted_compactified_logJet (j : ℕ) (q : ℝ)
    {K : Set Point} (hK : IsCompact K) {f : Point → ℝ}
    (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      LogJetBound (fun y => radiusPower (-q) y * f (inverseLogRadiusChart y)) j q C x := by
  obtain ⟨C,hC,hb⟩ := compactified_uniform_logJet j hK hf
  refine ⟨2^j*(3^j*(max 1 |q|)^j)*C,by positivity,?_⟩
  intro x hx
  have hs : ContDiffAt ℝ j (fun y => f (inverseLogRadiusChart y)) x :=
    ((hf _ hx).of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).comp x
      (inverseLogRadiusChart_smooth.contDiffAt.of_le
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
  simpa only [add_zero] using (LogJetBound.mul (by positivity) hC
    (radiusPower_diff (-q) j x) hs (radiusPower_logJet j q x) (hb x hx))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def boundaryProjection : Point →L[ℝ] Point :=
  ContinuousLinearMap.id ℝ Point -
    (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).smulRight (basis 0)

@[simp] lemma boundaryProjection_zero (z : Point) : boundaryProjection z 0 = 0 := by
  simp [boundaryProjection,basis]

lemma boundaryProjection_sub (z : Point) : z - boundaryProjection z = z 0 • basis 0 := by
  simp [boundaryProjection]

@[simp] lemma boundaryProjection_idem (z : Point) :
    boundaryProjection (boundaryProjection z) = boundaryProjection z := by
  simp [boundaryProjection, basis]

lemma norm_sub_boundaryProjection (z : Point) : ‖z - boundaryProjection z‖ = |z 0| := by
  rw [boundaryProjection_sub,norm_smul,Real.norm_eq_abs]
  simp [basis,Pi.norm_single]

lemma angular_D_vanishes_boundary {f : Point → ℝ}
    (hf : ∀ z : Point, z 0 = 0 → f z = 0) {z : Point} (hz : z 0 = 0)
    {a : I} (ha : a ≠ 0) : D (basis a) f z = 0 := by
  by_cases hd : DifferentiableAt ℝ f z
  · have he : (fun t : ℝ => f (z + t • basis a)) = fun _ => (0:ℝ) := by
      funext t
      apply hf
      simp [hz,basis,Ne.symm ha]
    have hline := hd.hasFDerivAt.hasLineDerivAt (basis a)
    change HasDerivAt (fun t : ℝ => f (z + t • basis a)) (D (basis a) f z) 0 at hline
    rw [he] at hline
    exact hline.unique (hasDerivAt_const 0 0)
  · simp [D,fderiv_zero_of_not_differentiableAt hd]

lemma backwardScaledIter_vanishes_boundary {f : Point → ℝ}
    (hf : ∀ z : Point, z 0 = 0 → f z = 0) (l : List I) :
    ∀ z : Point, z 0 = 0 → backwardScaledIter l f z = 0 := by
  induction l with
  | nil => exact hf
  | cons a l ih =>
    intro z hz
    by_cases ha : a=0
    · simp [backwardScaledIter_cons,backwardScaledD,backwardFactor,ha,hz]
    · simp [backwardScaledIter_cons,backwardScaledD,backwardFactor,ha,
        angular_D_vanishes_boundary ih hz ha]

lemma coefficient_difference_vanishes (f : Point → ℝ) :
    ∀ z : Point, z 0 = 0 → (f z - f (boundaryProjection z)) = 0 := by
  intro z hz
  have he : boundaryProjection z = z := by simp [boundaryProjection,hz]
  rw [he,sub_self]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

theorem compactified_vanishing_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z)
    (hv : ∀ z : Point, z 0 = 0 → f z = 0)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤
        C / Real.exp (x 0) := by
  let Q : Point → (Fin n → I) → (Point →L[ℝ] ℝ) :=
    fun z a => fderiv ℝ (backwardScaledIter (List.ofFn a) f) z
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro a
    exact (backwardScaledIter_contDiffAt (List.ofFn a) 1
      ((hf z hz).of_le (by simp))).continuousAt_fderiv
        (by norm_num)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨3^n * max 0 C,by positivity,?_⟩
  intro x hx
  let z := inverseLogRadiusChart x
  have hz : z ∈ K := hx
  have hbound (a : Fin n → I) :
      |backwardScaledIter (List.ofFn a) f z| ≤ max 0 C / Real.exp (x 0) := by
    have hd (w : Point) (hw : w ∈ segment ℝ (boundaryProjection z) z) :
        DifferentiableAt ℝ (backwardScaledIter (List.ofFn a) f) w :=
      (backwardScaledIter_contDiffAt (List.ofFn a) 1
        ((hf w (hsegment z hz hw)).of_le
          (by simp))).differentiableAt (by norm_num)
    have hb (w : Point) (hw : w ∈ segment ℝ (boundaryProjection z) z) :
        ‖fderiv ℝ (backwardScaledIter (List.ofFn a) f) w‖ ≤ max 0 C :=
      (norm_le_pi_norm (Q w) a).trans ((hC w (hsegment z hz hw)).trans (le_max_right _ _))
    have h := (convex_segment (boundaryProjection z) z).norm_image_sub_le_of_norm_fderiv_le
      hd hb (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [backwardScaledIter_vanishes_boundary hv _ _ (boundaryProjection_zero z),sub_zero,
      norm_sub_boundaryProjection,Real.norm_eq_abs] at h
    have he : |z 0| = (Real.exp (x 0))⁻¹ := by
      simp [z,inverseLogRadiusChart,Real.exp_neg]
    rw [he] at h
    simpa only [div_eq_mul_inv] using h
  have hfn : ContDiffAt ℝ n f z :=
    (hf z hz).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    hfn.comp x (inverseLogRadiusChart_smooth.contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  have hb := multilinear_norm_of_components (iteratedFDeriv ℝ n
      (fun y => f (inverseLogRadiusChart y)) x)
      (show 0 ≤ max 0 C / Real.exp (x 0) by positivity)
      (fun a => by
        rw [iteratedFDeriv_basis_ofFn n a hcomp,Real.norm_eq_abs]
        rw [coordinateIter_inverse_pullback (f := f) (x := x) (List.ofFn a)
          (by simpa using hfn)]
        exact hbound a)
  simpa only [mul_div_assoc] using hb

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

structure FiniteLogDecay (j : ℕ) (q : ℝ) (U : Set Point) (f : Point → ℝ) : Prop where
  regular : ∀ x ∈ U, ContDiffAt ℝ j f x
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, LogJetBound f j q C x

namespace FiniteLogDecay
variable {j : ℕ} {q r : ℝ} {U : Set Point} {f g : Point → ℝ}

lemma germ_congr (hf : FiniteLogDecay j q U f)
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] g) : FiniteLogDecay j q U g := by
  refine ⟨fun x hx => (hf.regular x hx).congr_of_eventuallyEq (he x hx).symm, ?_⟩
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,fun x hx n hn => ?_⟩
  rw [← ((he x hx).iteratedFDeriv ℝ n).eq_of_nhds]
  exact hb x hx n hn

lemma congr (hf : FiniteLogDecay j q U f) (he : f = g) : FiniteLogDecay j q U g := he ▸ hf

lemma add (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j q U g) :
    FiniteLogDecay j q U (fun x => f x + g x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  obtain ⟨D,hD,hc⟩ := hg.bound
  refine ⟨fun x hx => (hf.regular x hx).add (hg.regular x hx),
    C+D,add_nonneg hC hD,?_⟩
  intro x hx n hn
  rw [fun_iteratedFDeriv_add_apply ((hf.regular x hx).of_le (by exact_mod_cast hn))
    ((hg.regular x hx).of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans ((add_le_add (hb x hx n hn) (hc x hx n hn)).trans_eq
    (add_mul C D (radiusPower (-q) x)).symm)

lemma neg (hf : FiniteLogDecay j q U f) : FiniteLogDecay j q U (fun x => -f x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨fun x hx => (hf.regular x hx).neg,C,hC,?_⟩
  intro x hx n hn
  change ‖iteratedFDeriv ℝ n (-f) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply,norm_neg]
  exact hb x hx n hn

lemma sub (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j q U g) :
    FiniteLogDecay j q U (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma mul (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j r U g) :
    FiniteLogDecay j (q+r) U (fun x => f x*g x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  obtain ⟨D,hD,hc⟩ := hg.bound
  exact ⟨fun x hx => (hf.regular x hx).mul (hg.regular x hx),2^j*C*D,by positivity,
    fun x hx => LogJetBound.mul hC hD (hf.regular x hx) (hg.regular x hx) (hb x hx) (hc x hx)⟩

lemma weaken (hf : FiniteLogDecay j q U f) (h : r ≤ q)
    (hU : ∀ x ∈ U, 0 ≤ x 0) : FiniteLogDecay j r U f := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨hf.regular,C,hC,?_⟩
  intro x hx n hn
  refine (hb x hx n hn).trans (mul_le_mul_of_nonneg_left ?_ hC)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg h) (hU x hx)

lemma zero (j : ℕ) (q : ℝ) (U : Set Point) : FiniteLogDecay j q U (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffAt_const,0,le_refl _,?_⟩
  intro x hx n hn
  simp

lemma sum {ι : Type*} (s : Finset ι) (F : ι → Point → ℝ)
    (hF : ∀ i ∈ s, FiniteLogDecay j q U (F i)) :
    FiniteLogDecay j q U (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero j q U
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self _ _)).add (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)))

lemma radiusPower (j : ℕ) (q : ℝ) (U : Set Point) :
    FiniteLogDecay j q U (CKSMixedGeometry.radiusPower (-q)) :=
  ⟨fun x _ => radiusPower_diff (-q) j x,
    3^j*(max 1 |q|)^j,by positivity,fun x _ => radiusPower_logJet j q x⟩

lemma compactified (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j 0 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x)) := by
  refine ⟨fun x hx => ?_,compactified_uniform_logJet j hK hF⟩
  exact ((hF _ hx).comp x inverseLogRadiusChart_smooth.contDiffAt).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))

lemma vanishing (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hv : ∀ z : Point, z 0 = 0 → F z = 0)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j 1 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x)) := by
  classical
  have hs := compactified j hK hF
  choose C hC hb using (fun n : Fin (j+1) => compactified_vanishing_jets n.val hK hF hv hsegment)
  refine ⟨hs.regular,∑ n, C n,Finset.sum_nonneg (fun n _ => hC n),?_⟩
  intro x hx n hn
  have hc : C ⟨n,by omega⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ _)
  calc _ ≤ C ⟨n,by omega⟩ / Real.exp (x 0) := hb ⟨n,by omega⟩ x hx
    _ ≤ (∑ k, C k) / Real.exp (x 0) := div_le_div_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by simp [CKSMixedGeometry.radiusPower,Real.exp_neg,div_eq_mul_inv]

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff
namespace FiniteLogDecay

lemma mono {j : ℕ} {q : ℝ} {U V : Set Point} {f : Point → ℝ}
    (hf : FiniteLogDecay j q U f) (hV : V ⊆ U) : FiniteLogDecay j q V f := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  exact ⟨fun x hx => hf.regular x (hV hx),C,hC,fun x hx => hb x (hV hx)⟩

lemma compactified_difference (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j 1 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x) - F (boundaryProjection (inverseLogRadiusChart x))) := by
  apply vanishing j hK _ (coefficient_difference_vanishes F) hsegment
  intro z hz
  have hp : boundaryProjection z ∈ K := hsegment z hz (left_mem_segment ℝ _ _)
  exact (hF z hz).sub ((hF _ hp).comp z boundaryProjection.contDiff.contDiffAt)

lemma weighted_compactified (j : ℕ) (q : ℝ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j q (inverseLogRadiusChart ⁻¹' K)
      (fun x => CKSMixedGeometry.radiusPower (-q) x * F (inverseLogRadiusChart x)) := by
  simpa only [add_zero] using (radiusPower j q _).mul (compactified j hK hF)

lemma weighted_difference (j : ℕ) (q : ℝ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K) :
    FiniteLogDecay j (q+1) (inverseLogRadiusChart ⁻¹' K)
      (fun x => CKSMixedGeometry.radiusPower (-q) x * F (inverseLogRadiusChart x) -
        CKSMixedGeometry.radiusPower (-q) x * F (boundaryProjection (inverseLogRadiusChart x))) := by
  have h := (radiusPower j q _).mul (compactified_difference j hK hF hsegment)
  simpa only [mul_sub] using h

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_source_remainder_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    (U : Set Point) (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    {f : Point → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x ∈ U, ContDiffAt ℝ j f (logRadiusChart (logLorentzChart e m p φ ψ x)))
    (hb : ∀ x ∈ U, ScaledComponentBound f j q B (logRadiusChart (logLorentzChart e m p φ ψ x))) :
    FiniteLogDecay j q U (fun x => f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  have hs (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j
      (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x := by
    have hc := (logLorentzChart_contDiffAt e m p φ ψ (hφ _ (hU hx))
      (hreg _ (hU hx)) (hψ _ (hU hx))).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    exact (hf x hx).comp x ((logRadiusChart_smooth.contDiffAt.of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).comp x hc)
  obtain ⟨C,hC,hc⟩ := lorentz_finite_remainder_pullback e m p φ ψ j q hK hφ hreg hψ
  refine ⟨hs,3^j*C*B,by positivity,?_⟩
  intro x hx n hn
  have h := multilinear_norm_of_components (iteratedFDeriv ℝ n
      (fun y => f (logRadiusChart (logLorentzChart e m p φ ψ y))) x)
      (show 0 ≤ C*B/Real.exp (x 0)^q by positivity)
      (fun a => by rw [iteratedFDeriv_basis_ofFn n a ((hs x hx).of_le (by exact_mod_cast hn)),
        Real.norm_eq_abs]
                   exact hc f B hB x (hU hx) (hf x hx) (hb x hx) _ (by simpa using hn))
  calc _ ≤ 3^n*(C*B/Real.exp (x 0)^q) := h
    _ ≤ 3^j*(C*B/Real.exp (x 0)^q) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn) (by positivity)
    _ = _ := by rw [radiusPower_neg_nat]; ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma radiusPower_add (t u : ℝ) (x : Point) :
    radiusPower (t+u) x = radiusPower t x*radiusPower u x := by
  simp only [radiusPower,add_mul,Real.exp_add]

lemma logLorentzChart_radial_coeff (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (x : Point) : (logLorentzChart e m p φ ψ x) 0 =
      x 0 + compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x) 0 := by
  rw [logLorentzChart_eq_slice]
  simp only [slice_zero,compactLorentzCoefficients]

lemma logLorentzChart_angular_coeff (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (x : Point) : angularProjection (logLorentzChart e m p φ ψ x) =
      angularProjection (compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x)) := by
  rw [logLorentzChart_eq_slice]
  ext a
  simp [compactLorentzCoefficients,angularProjection]

lemma radiusPower_lorentz (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (t : ℝ)
    (x : Point) : radiusPower t (logLorentzChart e m p φ ψ x) = radiusPower t x *
      Real.exp (t*compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x) 0) := by
  simp only [radiusPower,logLorentzChart_radial_coeff,mul_add,Real.exp_add]

def compactLeadingCoefficient (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (q : ℝ) (M : Angle → ℝ) (z : Point) : ℝ :=
  Real.exp (-q*compactLorentzCoefficients e m p φ ψ z 0) *
    M (angularProjection (compactLorentzCoefficients e m p φ ψ z))

lemma ordinaryLeadingComponent_log_lorentz (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (M : Angle → ℝ) (x : Point) :
    ordinaryLeadingComponent q M (logRadiusChart (logLorentzChart e m p φ ψ x)) =
      radiusPower (-(q:ℝ)) (logLorentzChart e m p φ ψ x) *
        M (angularProjection (compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart x))) := by
  simp only [ordinaryLeadingComponent,logRadiusChart,ite_true,
    angularProjection_logRadiusChart,radiusPower_neg_nat,logLorentzChart_angular_coeff]

lemma weighted_ordinary_leading (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (w : ℝ) (M : Angle → ℝ) (x : Point) :
    radiusPower w (logLorentzChart e m p φ ψ x) *
      ordinaryLeadingComponent q M (logRadiusChart (logLorentzChart e m p φ ψ x)) =
      radiusPower (-(q-w)) x * compactLeadingCoefficient e m p φ ψ (q-w) M (inverseLogRadiusChart x) := by
  rw [ordinaryLeadingComponent_log_lorentz,← mul_assoc,← radiusPower_add]
  have he : w + -(q:ℝ) = -((q:ℝ)-w) := by ring
  rw [he,radiusPower_lorentz]
  exact mul_assoc _ _ _

lemma compactLeadingCoefficient_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (q : ℝ) {M : Angle → ℝ} {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    (hM : ContDiffAt ℝ ∞ M (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ContDiffAt ℝ ∞ (compactLeadingCoefficient e m p φ ψ q M) z := by
  have hc := compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ
  exact (contDiffAt_const.mul ((contDiffAt_pi.mp hc) 0)).exp.mul
    (hM.comp z (angularProjection.contDiff.contDiffAt.comp z hc))

lemma lorentz_radius_weight_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) (t : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    FiniteLogDecay j (-t) (inverseLogRadiusChart ⁻¹' K)
      (fun x => radiusPower t (logLorentzChart e m p φ ψ x)) := by
  have h := FiniteLogDecay.weighted_compactified j (-t) hK (fun z hz =>
    ((contDiffAt_const (c := t)).mul ((contDiffAt_pi.mp
      (compactLorentzCoefficients_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz))) 0)).exp)
  apply h.congr
  funext x
  rw [neg_neg,radiusPower_lorentz]

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma source_remainder_lorentz_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} (hf : SourceRemainderOn j q V f) :
    FiniteLogDecay j q U (fun x => f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact lorentz_source_remainder_decay e m p φ ψ j q hK hφ hreg hψ U hU hB
    (fun x hx => hf.regular _ (hV x hx)) (fun x hx => hb _ (hV x hx))

lemma weighted_source_remainder_lorentz_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q : ℕ) (w : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} (hf : SourceRemainderOn j q V f) :
    FiniteLogDecay j (q-w) U (fun x => radiusPower w (logLorentzChart e m p φ ψ x) *
      f (logRadiusChart (logLorentzChart e m p φ ψ x))) := by
  have hpow := (lorentz_radius_weight_decay e m p φ ψ j w hK hφ hreg hψ).mono hU
  have hr := source_remainder_lorentz_decay e m p φ ψ j q hK hφ hreg hψ hU hV hf
  convert hpow.mul hr using 1
  ring

lemma weighted_source_leading_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j q qlead : ℕ) (w : ℝ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z)))
    {U V : Set Point} (hU : U ⊆ inverseLogRadiusChart ⁻¹' K)
    (hV : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V)
    {f : Point → ℝ} {M : Angle → ℝ}
    (hf : SourceRemainderOn j q V (fun y => f y-ordinaryLeadingComponent qlead M y)) :
    FiniteLogDecay j (q-w) U (fun x => radiusPower w (logLorentzChart e m p φ ψ x) *
      f (logRadiusChart (logLorentzChart e m p φ ψ x)) -
        radiusPower (-(qlead-w)) x * compactLeadingCoefficient e m p φ ψ (qlead-w) M (inverseLogRadiusChart x)) := by
  have h := weighted_source_remainder_lorentz_decay e m p φ ψ j q w hK hφ hreg hψ hU hV hf
  apply h.congr
  funext x
  rw [mul_sub,weighted_ordinary_leading]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def squareRadialChart (z : Point) : Point := slice ((z 0)^2) (angularProjection z)

def squaredCompactSpatial (e m : ℝ) (p : E) (φ : Angle → E) (z : Point) : E :=
  φ (angularProjection z) +
    (Real.sqrt (1+z 0) / m + inner ℝ p (φ (angularProjection z)) / (m*(e+m))) • p

def squaredLorentzCoefficients (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (z : Point) : Point :=
  let v := squaredCompactSpatial e m p φ z
  slice (Real.log ‖v‖) (ψ (‖v‖⁻¹ • v))

lemma squareRadialChart_smooth : ContDiff ℝ ∞ squareRadialChart := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [squareRadialChart,slice_zero,ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.pow 2)
  · simpa only [squareRadialChart,slice_succ,ContinuousLinearMap.proj_apply,Function.comp_def] using
      (ContinuousLinearMap.proj a : Angle →L[ℝ] ℝ).contDiff.comp angularProjection.contDiff

@[simp] lemma angularProjection_squareRadialChart (z : Point) :
    angularProjection (squareRadialChart z) = angularProjection z := by
  ext a
  simp [squareRadialChart,angularProjection]

lemma squaredCompactSpatial_square (e m : ℝ) (p : E) (φ : Angle → E) (z : Point) :
    squaredCompactSpatial e m p φ (squareRadialChart z) =
      compactSpatial e m p (compactPolar φ z) := by
  simp [squaredCompactSpatial,squareRadialChart,compactSpatial,compactPolar,compactRoot,angularProjection]

lemma compactLorentzCoefficients_squared (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) (z : Point) :
    compactLorentzCoefficients e m p φ ψ z =
      squaredLorentzCoefficients e m p φ ψ (squareRadialChart z) := by
  simp [squaredLorentzCoefficients,squaredCompactSpatial_square,
    compactLorentzCoefficients,compactScale,compactAngle]

lemma squaredCompactSpatial_contDiffAt (e m : ℝ) (p : E) (φ : Angle → E)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) (hz : -1 < z 0) :
    ContDiffAt ℝ ∞ (squaredCompactSpatial e m p φ) z := by
  have hang := hφ.comp z angularProjection.contDiff.contDiffAt
  have hroot : ContDiffAt ℝ ∞ (fun w : Point => Real.sqrt (1+w 0)) z :=
    (contDiffAt_const.add (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.contDiffAt).sqrt
      (by change 1 + z 0 ≠ 0; linarith)
  exact hang.add (((hroot.div_const m).add
    ((ContDiffAt.inner ℝ (contDiffAt_const (c := p)) hang).div_const (m*(e+m)))).smul_const p)

lemma squaredLorentzCoefficients_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) (hz : -1 < z 0)
    (hv : squaredCompactSpatial e m p φ z ≠ 0)
    (hψ : ContDiffAt ℝ ∞ ψ (‖squaredCompactSpatial e m p φ z‖⁻¹ •
      squaredCompactSpatial e m p φ z)) :
    ContDiffAt ℝ ∞ (squaredLorentzCoefficients e m p φ ψ) z := by
  have h := squaredCompactSpatial_contDiffAt e m p φ hφ hz
  have hn := h.norm ℝ hv
  have ha := hψ.comp z ((hn.inv (norm_ne_zero_iff.mpr hv)).smul h)
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [squaredLorentzCoefficients,slice_zero] using hn.log (norm_ne_zero_iff.mpr hv)
  · simpa [squaredLorentzCoefficients,Function.comp_def,Pi.smul_apply,Pi.inv_apply] using (contDiffAt_pi.mp ha) a

lemma squaredLorentzCoefficients_regular (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ContDiffAt ℝ ∞ (squaredLorentzCoefficients e m p φ ψ) (squareRadialChart z) := by
  apply squaredLorentzCoefficients_contDiffAt
  · simpa only [angularProjection_squareRadialChart] using hφ
  · simp only [squareRadialChart,slice_zero]
    linarith [sq_nonneg (z 0)]
  · rw [squaredCompactSpatial_square]
    exact norm_ne_zero_iff.mp hz.2.ne'
  · simpa only [squaredCompactSpatial_square,compactScale,compactAngle] using hψ

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set
open scoped ContDiff Topology

def squareRadialDerivative (z : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun i => if i=0 then (2*z 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma squareRadialChart_hasFDerivAt (z : Point) :
    HasFDerivAt squareRadialChart (squareRadialDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [squareRadialChart,slice_zero,ite_true]
    change HasFDerivAt (fun w : Point => (w 0)^2)
      ((2*z 0) • (ContinuousLinearMap.proj (0 : I) : Point →L[ℝ] ℝ)) z
    have hd : HasFDerivAt (fun w : Point => w 0) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) z :=
      hasFDerivAt_apply (0 : I) z
    simpa only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat] using hd.pow 2
  · simp only [squareRadialChart,slice_succ,Fin.succ_ne_zero,ite_false]
    change HasFDerivAt (fun w : Point => w a.succ) (ContinuousLinearMap.proj a.succ) z
    exact hasFDerivAt_apply a.succ z

lemma squareRadialDerivative_zero (z : Point) :
    squareRadialDerivative z (basis 0) = (2*z 0) • basis 0 := by
  ext i
  by_cases hi : i=0
  · subst i; simp [squareRadialDerivative,basis]
  · simp [squareRadialDerivative,basis,hi]

lemma D_zero_square_pullback {f : Point → ℝ} {z : Point}
    (hf : DifferentiableAt ℝ f (squareRadialChart z)) :
    D (basis 0) (fun w => f (squareRadialChart w)) z =
      (2*z 0)*D (basis 0) f (squareRadialChart z) := by
  unfold D
  change fderiv ℝ (f ∘ squareRadialChart) z (basis 0) = _
  rw [fderiv_comp z hf (squareRadialChart_hasFDerivAt z).differentiableAt,
    (squareRadialChart_hasFDerivAt z).fderiv]
  simp only [ContinuousLinearMap.comp_apply,squareRadialDerivative_zero,
    map_smul,smul_eq_mul]

def lorentzLogJac (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (a i : I) (z : Point) : ℝ :=
  (if a=0 ∧ i=0 then 1 else 0) +
    backwardScaledD a (fun w => compactLorentzCoefficients e m p φ ψ w i) z

def lorentzRadialJacCorrection (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (i : I) (z : Point) : ℝ :=
  -2 * D (basis 0) (fun w => squaredLorentzCoefficients e m p φ ψ w i) (squareRadialChart z)

lemma lorentzLogJac_radial (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (i : I) :
    lorentzLogJac e m p φ ψ 0 i z =
      (if i=0 then 1 else 0) + (z 0)^2 * lorentzRadialJacCorrection e m p φ ψ i z := by
  have he : (fun w => compactLorentzCoefficients e m p φ ψ w i) =
      fun w => squaredLorentzCoefficients e m p φ ψ (squareRadialChart w) i := by
    funext w
    rw [compactLorentzCoefficients_squared]
  have hf := (contDiffAt_pi.mp (squaredLorentzCoefficients_regular e m p φ ψ hφ hz hψ)) i
  simp only [lorentzLogJac,backwardScaledD,backwardFactor,ite_true,true_and,he]
  rw [D_zero_square_pullback (hf.differentiableAt (by simp))]
  unfold lorentzRadialJacCorrection
  ring

lemma lorentzLogJac_contDiffAt (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (a i : I) :
    ContDiffAt ℝ ∞ (lorentzLogJac e m p φ ψ a i) z := by
  have hf := (contDiffAt_pi.mp (compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ)) i
  exact contDiffAt_const.add ((backwardFactor_smooth a).contDiffAt.mul
    (contDiffAt_D hf (by simp) (basis a)))

lemma lorentzRadialJacCorrection_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (i : I) :
    ContDiffAt ℝ ∞ (lorentzRadialJacCorrection e m p φ ψ i) z := by
  have hf := (contDiffAt_pi.mp (squaredLorentzCoefficients_regular e m p φ ψ hφ hz hψ)) i
  exact contDiffAt_const.mul
    ((contDiffAt_D hf (by simp) (basis 0)).comp z squareRadialChart_smooth.contDiffAt)

lemma D_logLorentzChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) (a i : I) :
    D (basis a) (fun y => logLorentzChart e m p φ ψ y i) x =
      lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x) := by
  let L : Point →L[ℝ] ℝ := (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).comp radialLinear
  have he : (fun y => logLorentzChart e m p φ ψ y i) =
      fun y => L y + compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart y) i := rfl
  have hf := (contDiffAt_pi.mp (compactLorentzCoefficients_contDiffAt e m p φ ψ hφ hz hψ)) i
  have hd : DifferentiableAt ℝ
      (fun y => compactLorentzCoefficients e m p φ ψ (inverseLogRadiusChart y) i) x :=
    (hf.comp x inverseLogRadiusChart_smooth.contDiffAt).differentiableAt (by simp)
  rw [he,D_add (basis a) L.differentiableAt hd,
    D_clm,D_inverse_pullback a (hf.differentiableAt (by simp))]
  unfold lorentzLogJac
  congr 1
  change (basis a 0) * basis 0 i = (if a = 0 ∧ i = 0 then 1 else 0)
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [basis]
  · subst a; simp [basis,hi]
  · subst i; simp [basis,ha,Ne.symm ha]
  · simp [basis,ha,Ne.symm ha,hi]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma lorentzLogJac_radial_of_differentiable (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (i : I) {z : Point} (hf : DifferentiableAt ℝ
      (fun w => squaredLorentzCoefficients e m p φ ψ w i) (squareRadialChart z)) :
    lorentzLogJac e m p φ ψ 0 i z =
      (if i=0 then 1 else 0) + (z 0)^2 * lorentzRadialJacCorrection e m p φ ψ i z := by
  have he : (fun w => compactLorentzCoefficients e m p φ ψ w i) =
      fun w => squaredLorentzCoefficients e m p φ ψ (squareRadialChart w) i := by
    funext w
    rw [compactLorentzCoefficients_squared]
  simp only [lorentzLogJac,backwardScaledD,backwardFactor,ite_true,true_and,he]
  rw [D_zero_square_pullback hf]
  unfold lorentzRadialJacCorrection
  ring

lemma lorentzLogJac_radial_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {z : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) (i : I) :
    lorentzLogJac e m p φ ψ 0 i =ᶠ[𝓝 z]
      (fun w => (if i=0 then 1 else 0) + (w 0)^2 * lorentzRadialJacCorrection e m p φ ψ i w) := by
  have hf := (contDiffAt_pi.mp (squaredLorentzCoefficients_regular e m p φ ψ hφ hz hψ)) i
  have hf1 : ContDiffAt ℝ 1 (fun w => squaredLorentzCoefficients e m p φ ψ w i)
      (squareRadialChart z) := hf.of_le (by simp)
  have hn := squareRadialChart_smooth.continuous.continuousAt.eventually
    (hf1.eventually (by simp))
  filter_upwards [hn] with w hw
  exact lorentzLogJac_radial_of_differentiable e m p φ ψ i (hw.differentiableAt (by simp))

lemma lorentzLogJac_radial_log_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point} (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x)))) (i : I) :
    (fun y => lorentzLogJac e m p φ ψ 0 i (inverseLogRadiusChart y)) =ᶠ[𝓝 x]
      (fun y => (if i=0 then 1 else 0) + radiusPower (-2) y *
        lorentzRadialJacCorrection e m p φ ψ i (inverseLogRadiusChart y)) := by
  have hn := inverseLogRadiusChart_smooth.continuous.continuousAt.eventually
    (lorentzLogJac_radial_germ e m p φ ψ hφ hz hψ i)
  filter_upwards [hn] with y hy
  rw [hy]
  have he : (inverseLogRadiusChart y 0)^2 = radiusPower (-2) y := by
    simp only [inverseLogRadiusChart,ite_true,radiusPower]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentz_jacobian_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hφ : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z))
    (hreg : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p)
    (hψ : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    (∀ a i, FiniteLogDecay j 0 (inverseLogRadiusChart ⁻¹' K)
      (fun x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x))) ∧
    (∀ i, FiniteLogDecay j 2 (inverseLogRadiusChart ⁻¹' K)
      (fun x => lorentzLogJac e m p φ ψ 0 i (inverseLogRadiusChart x) - (if i=0 then 1 else 0))) := by
  constructor
  · intro a i
    exact FiniteLogDecay.compactified j hK (fun z hz =>
      lorentzLogJac_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz) a i)
  · intro i
    have h := FiniteLogDecay.weighted_compactified j 2 hK (fun z hz =>
      lorentzRadialJacCorrection_contDiffAt e m p φ ψ (hφ z hz) (hreg z hz) (hψ z hz) i)
    apply h.germ_congr
    intro x hx
    filter_upwards [lorentzLogJac_radial_log_germ e m p φ ψ (hφ _ hx) (hreg _ hx) (hψ _ hx) i]
      with y hy
    rw [hy]
    ring

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def logTensorRate (i k : I) : ℝ :=
  if i=0 then (if k=0 then 3 else 2) else (if k=0 then 2 else 1)

def logJacRate (a i : I) : ℝ := if a=0 ∧ i≠0 then 2 else 0

def logCovariantPullback (J : I → I → Point → ℝ) (T : I → I → Point → ℝ)
    (a b : I) (x : Point) : ℝ := ∑ i, ∑ k, J a i x * J b k x * T i k x

lemma tensor_rate_inequality (a b i k : I) :
    logTensorRate a b ≤ logJacRate a i + logJacRate b k + logTensorRate i k := by
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    by_cases hi : i=0 <;> by_cases hk : k=0 <;>
      norm_num [logTensorRate,logJacRate,ha,hb,hi,hk]

theorem finite_log_tensor_pullback_rates (j : ℕ) {U : Set Point}
    (hU : ∀ x ∈ U, 0 ≤ x 0) {J T : I → I → Point → ℝ}
    (hJ : ∀ a i, FiniteLogDecay j (logJacRate a i) U (J a i))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k)) :
    ∀ a b, FiniteLogDecay j (logTensorRate a b) U (logCovariantPullback J T a b) := by
  intro a b
  apply FiniteLogDecay.sum
  intro i _
  apply FiniteLogDecay.sum
  intro k _
  exact (((hJ a i).mul (hJ b k)).mul (hT i k)).weaken (tensor_rate_inequality a b i k) hU

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def angularLeadingEntry (C : I → I → Point → ℝ) (i k : I) (z : Point) : ℝ :=
  if i≠0 ∧ k≠0 then C i k z else 0

def transformedAngularLeading (J C : I → I → Point → ℝ) (a b : I) (z : Point) : ℝ :=
  ∑ i, ∑ k, J a i z * J b k z * angularLeadingEntry C i k z

lemma angular_leading_term_decay (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J C T : I → I → Point → ℝ}
    (hJ : ∀ a i z, z ∈ K → ContDiffAt ℝ ∞ (J a i) z)
    (hC : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (C i k) z)
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : ∀ i k, i≠0 → k≠0 → FiniteLogDecay j 2 U
      (fun x => T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x)))
    (a b i k : I) :
    FiniteLogDecay j 2 U (fun x =>
      J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) * T i k x -
        radiusPower (-1) x * (J a i (boundaryProjection (inverseLogRadiusChart x)) *
          J b k (boundaryProjection (inverseLogRadiusChart x)) *
          angularLeadingEntry C i k (boundaryProjection (inverseLogRadiusChart x)))) := by
  have hJJ := ((FiniteLogDecay.compactified j hK (hJ a i)).mono hUK).mul
    ((FiniteLogDecay.compactified j hK (hJ b k)).mono hUK)
  by_cases hi : i=0
  · have hTi : FiniteLogDecay j 2 U (T i k) :=
      (hT i k).weaken (by simp [logTensorRate,hi]; split_ifs <;> norm_num) hU
    simpa only [zero_add,angularLeadingEntry,hi,ne_eq,not_true_eq_false,false_and,ite_false,
      mul_zero,sub_zero] using hJJ.mul hTi
  by_cases hk : k=0
  · have hTi : FiniteLogDecay j 2 U (T i k) :=
      (hT i k).weaken (by simp [logTensorRate,hi,hk]) hU
    simpa only [zero_add,angularLeadingEntry,hk,ne_eq,not_true_eq_false,and_false,ite_false,
      mul_zero,sub_zero] using hJJ.mul hTi
  have he : FiniteLogDecay j 2 U (fun x =>
      (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x)) *
        (T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x))) := by
    simpa only [zero_add] using hJJ.mul (hE i k hi hk)
  have hd := (FiniteLogDecay.weighted_difference j 1 hK
    (fun z hz => ((hJ a i z hz).mul (hJ b k z hz)).mul (hC i k hi hk z hz)) hsegment).mono hUK
  have hadd : FiniteLogDecay j 2 U (fun x =>
      (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x)) *
        (T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x)) +
      (radiusPower (-1) x * (J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) *
        C i k (inverseLogRadiusChart x)) - radiusPower (-1) x *
        (J a i (boundaryProjection (inverseLogRadiusChart x)) *
         J b k (boundaryProjection (inverseLogRadiusChart x)) * C i k (boundaryProjection (inverseLogRadiusChart x))))) :=
    he.add (by simpa only [show (1:ℝ)+1=2 by norm_num] using hd)
  apply hadd.congr
  funext x
  simp only [angularLeadingEntry,ne_eq,hi,hk,not_false_eq_true,true_and,ite_true]
  ring

theorem finite_log_tensor_angular_leading (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J C T : I → I → Point → ℝ}
    (hJ : ∀ a i z, z ∈ K → ContDiffAt ℝ ∞ (J a i) z)
    (hC : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (C i k) z)
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : ∀ i k, i≠0 → k≠0 → FiniteLogDecay j 2 U
      (fun x => T i k x - radiusPower (-1) x * C i k (inverseLogRadiusChart x))) :
    ∀ a b, FiniteLogDecay j 2 U (fun x =>
      logCovariantPullback (fun a i x => J a i (inverseLogRadiusChart x)) T a b x -
        radiusPower (-1) x * transformedAngularLeading J C a b (boundaryProjection (inverseLogRadiusChart x))) := by
  intro a b
  let F : I → I → Point → ℝ := fun i k x =>
    J a i (inverseLogRadiusChart x) * J b k (inverseLogRadiusChart x) * T i k x -
      radiusPower (-1) x * (J a i (boundaryProjection (inverseLogRadiusChart x)) *
        J b k (boundaryProjection (inverseLogRadiusChart x)) *
        angularLeadingEntry C i k (boundaryProjection (inverseLogRadiusChart x)))
  have h := FiniteLogDecay.sum Finset.univ (fun i x => ∑ k, F i k x)
    (fun i _ => FiniteLogDecay.sum Finset.univ (F i) (fun k _ =>
      angular_leading_term_decay j hK hsegment hUK hU hJ hC hT hE a b i k))
  apply h.congr
  funext x
  simp only [F,logCovariantPullback,transformedAngularLeading,Finset.sum_sub_distrib,Finset.mul_sum]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma radial_leading_00_decay (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J T C : Point → ℝ} (hC : ∀ z ∈ K, ContDiffAt ℝ ∞ C z)
    (hJ : FiniteLogDecay j 0 U J)
    (hδ : FiniteLogDecay j 2 U (fun x => J x-1))
    (hE : FiniteLogDecay j 4 U
      (fun x => T x - radiusPower (-3) x * C (inverseLogRadiusChart x))) :
    FiniteLogDecay j 4 U (fun x => J x*J x*T x -
      radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x))) := by
  have hsq : FiniteLogDecay j 2 U (fun x => J x*J x-1) := by
    have hmul : FiniteLogDecay j 2 U (fun x => (J x-1)*J x) := by
      simpa only [add_zero] using hδ.mul hJ
    apply (hmul.add hδ).congr
    funext x
    ring
  have hlead := (FiniteLogDecay.weighted_compactified j 3 hK hC).mono hUK
  have hrest : FiniteLogDecay j 4 U (fun x =>
      (J x*J x)*(T x-radiusPower (-3) x*C (inverseLogRadiusChart x))) := by
    simpa only [zero_add] using (hJ.mul hJ).mul hE
  have hsquare : FiniteLogDecay j 4 U (fun x =>
      (radiusPower (-3) x*C (inverseLogRadiusChart x))*(J x*J x-1)) :=
    (hlead.mul hsq).weaken (by norm_num) hU
  have hdiff : FiniteLogDecay j 4 U (fun x =>
      radiusPower (-3) x*C (inverseLogRadiusChart x) -
        radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x))) := by
    simpa only [show (3:ℝ)+1=4 by norm_num] using
      (FiniteLogDecay.weighted_difference j 3 hK hC hsegment).mono hUK
  apply ((hrest.add hsquare).add hdiff).congr
  funext x
  ring

lemma radial_off_diagonal_entry_decay (j : ℕ) {U : Set Point}
    (hU : ∀ x ∈ U, 0 ≤ x 0) {J T : I → I → Point → ℝ}
    (hJ : ∀ i, FiniteLogDecay j (logJacRate 0 i) U (J 0 i))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (i k : I) (hik : ¬(i=0 ∧ k=0)) :
    FiniteLogDecay j 4 U (fun x => J 0 i x*J 0 k x*T i k x) := by
  refine (((hJ i).mul (hJ k)).mul (hT i k)).weaken ?_ hU
  by_cases hi : i=0 <;> by_cases hk : k=0
  · exact False.elim (hik ⟨hi,hk⟩)
  · norm_num [logJacRate,logTensorRate,hi,hk]
  · norm_num [logJacRate,logTensorRate,hi,hk]
  · norm_num [logJacRate,logTensorRate,hi,hk]

theorem finite_log_tensor_radial_leading (j : ℕ) {K : Set Point} (hK : IsCompact K)
    (hsegment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K)
    {U : Set Point} (hUK : U ⊆ inverseLogRadiusChart ⁻¹' K) (hU : ∀ x ∈ U, 0 ≤ x 0)
    {J T : I → I → Point → ℝ} {C : Point → ℝ}
    (hC : ∀ z ∈ K, ContDiffAt ℝ ∞ C z)
    (hJ : ∀ i, FiniteLogDecay j (logJacRate 0 i) U (J 0 i))
    (hδ : FiniteLogDecay j 2 U (fun x => J 0 0 x-1))
    (hT : ∀ i k, FiniteLogDecay j (logTensorRate i k) U (T i k))
    (hE : FiniteLogDecay j 4 U (fun x => T 0 0 x -
      radiusPower (-3) x * C (inverseLogRadiusChart x))) :
    FiniteLogDecay j 4 U (fun x => logCovariantPullback J T 0 0 x -
      radiusPower (-3) x * C (boundaryProjection (inverseLogRadiusChart x))) := by
  classical
  have he (i k : I) : FiniteLogDecay j 4 U (fun x => J 0 i x*J 0 k x*T i k x -
      if i=0 ∧ k=0 then radiusPower (-3) x*C (boundaryProjection (inverseLogRadiusChart x)) else 0) := by
    by_cases hik : i=0 ∧ k=0
    · rcases hik with ⟨rfl,rfl⟩
      simpa only [and_self,ite_true] using radial_leading_00_decay j hK hsegment hUK hU hC
        (by simpa [logJacRate] using hJ 0) hδ hE
    · simpa only [hik,ite_false,sub_zero] using radial_off_diagonal_entry_decay j hU hJ hT i k hik
  have h := FiniteLogDecay.sum Finset.univ _ (fun i _ => FiniteLogDecay.sum Finset.univ _
    (fun k _ => he i k))
  apply h.congr
  funext x
  simp [logCovariantPullback,Finset.sum_sub_distrib,ite_and]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
open scoped ContDiff

def radialIndexWeight (i k : I) : ℝ := (if i=0 then 1 else 0)+(if k=0 then 1 else 0)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure LorentzChartDomain (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (K U V : Set Point) : Prop where
  compact : IsCompact K
  chart : ∀ z ∈ K, ContDiffAt ℝ ∞ φ (angularProjection z)
  region : ∀ z ∈ K, compactPolar φ z ∈ compactRegion e m p
  chartInv : ∀ z ∈ K, ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))
  segment : ∀ z ∈ K, segment ℝ (boundaryProjection z) z ⊆ K
  newRegion : U ⊆ inverseLogRadiusChart ⁻¹' K
  oldRegion : ∀ x ∈ U, logRadiusChart (logLorentzChart e m p φ ψ x) ∈ V
  largeRadius : ∀ x ∈ U, 0 ≤ x 0

def oldLogTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (i k : I) (x : Point) : ℝ :=
  radiusPower (radialIndexWeight i k) (logLorentzChart e m p φ ψ x) *
    A i k (logRadiusChart (logLorentzChart e m p φ ψ x))

def lorentzLogTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) : I → I → Point → ℝ :=
  logCovariantPullback (fun a i x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x))
    (oldLogTensor e m p φ ψ A)

def compactAngularCoefficient (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mg : I → I → Angle → ℝ) (i k : I) : Point → ℝ :=
  compactLeadingCoefficient e m p φ ψ 1 (mg i k)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma oldLogTensor_radial_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) :
    FiniteLogDecay j (qrad-2) U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) := by
  have h := weighted_source_leading_remainder e m p φ ψ j qrad 5 2
      hd.compact hd.chart hd.region hd.chartInv hd.newRegion hd.oldRegion hA.radial
  convert h using 1
  norm_num [oldLogTensor,radialIndexWeight]

lemma oldLogTensor_angular_remainder (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) (i k : I) (hi : i≠0) (hk : k≠0) :
    FiniteLogDecay j 2 U (fun x => oldLogTensor e m p φ ψ A i k x -
      radiusPower (-1) x * compactAngularCoefficient e m p φ ψ mg i k (inverseLogRadiusChart x)) := by
  simpa [oldLogTensor,radialIndexWeight,hi,hk,compactAngularCoefficient] using weighted_source_leading_remainder e m p φ ψ j 2 1 0
      hd.compact hd.chart hd.region hd.chartInv hd.newRegion hd.oldRegion (hA.angular i k hi hk)

lemma oldLogTensor_mixed_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg) (i k : I)
    (hik : (i=0 ∧ k≠0) ∨ (i≠0 ∧ k=0)) :
    FiniteLogDecay j 2 U (oldLogTensor e m p φ ψ A i k) := by
  have hw : radialIndexWeight i k = 1 := by
    rcases hik with ⟨hi,hk⟩ | ⟨hi,hk⟩ <;> simp [radialIndexWeight,hi,hk]
  have h := weighted_source_remainder_lorentz_decay e m p φ ψ j 3 1 hd.compact hd.chart
      hd.region hd.chartInv hd.newRegion hd.oldRegion (hA.mixed i k hik)
  change FiniteLogDecay j 2 U (fun x => radiusPower (radialIndexWeight i k)
    (logLorentzChart e m p φ ψ x) * A i k (logRadiusChart (logLorentzChart e m p φ ψ x)))
  convert h using 1 <;> norm_num [hw]

lemma lorentz_compact_radial_leading_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {mr : Angle → ℝ}
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ z ∈ K, ContDiffAt ℝ ∞ (compactLeadingCoefficient e m p φ ψ 3 mr) z := by
  intro z hz
  exact compactLeadingCoefficient_regular e m p φ ψ 3 (hd.chart z hz)
    (hd.region z hz) (hd.chartInv z hz) (hr z hz)

lemma lorentz_compact_angular_leading_regular (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {mg : I → I → Angle → ℝ}
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ i k, i≠0 → k≠0 → ∀ z ∈ K,
      ContDiffAt ℝ ∞ (compactAngularCoefficient e m p φ ψ mg i k) z := by
  intro i k hi hk z hz
  exact compactLeadingCoefficient_regular e m p φ ψ 1 (hd.chart z hz)
    (hd.region z hz) (hd.chartInv z hz) (hg i k hi hk z hz)

lemma oldLogTensor_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) (hq : 5 ≤ qrad) {K U V : Set Point}
    (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    ∀ i k, FiniteLogDecay j (logTensorRate i k) U (oldLogTensor e m p φ ψ A i k) := by
  intro i k
  by_cases hi : i=0 <;> by_cases hk : k=0
  · subst i; subst k
    have he : FiniteLogDecay j 3 U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
        radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) :=
      (oldLogTensor_radial_remainder e m p φ ψ j qrad hd hA).weaken
        (by exact_mod_cast (show (3:ℤ) ≤ (qrad:ℤ)-2 by omega)) hd.largeRadius
    have hl := (FiniteLogDecay.weighted_compactified j 3 hd.compact
      (lorentz_compact_radial_leading_regular e m p φ ψ hd hr)).mono hd.newRegion
    simpa only [logTensorRate,ite_true,sub_add_cancel] using he.add hl
  · simpa only [logTensorRate,hi,hk,ite_true,ite_false] using
      oldLogTensor_mixed_decay e m p φ ψ j qrad hd hA i k (Or.inl ⟨hi,hk⟩)
  · simpa only [logTensorRate,hi,hk,ite_true,ite_false] using
      oldLogTensor_mixed_decay e m p φ ψ j qrad hd hA i k (Or.inr ⟨hi,hk⟩)
  · have he := (oldLogTensor_angular_remainder e m p φ ψ j qrad hd hA i k hi hk).weaken
        (by norm_num : (1:ℝ) ≤ 2) hd.largeRadius
    have hl := (FiniteLogDecay.weighted_compactified j 1 hd.compact
      (lorentz_compact_angular_leading_regular e m p φ ψ hd hg i k hi hk)).mono hd.newRegion
    simpa only [logTensorRate,hi,hk,ite_false,sub_add_cancel] using he.add hl

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma lorentz_jacobian_sharp_decay (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V) :
    ∀ a i, FiniteLogDecay j (logJacRate a i) U
      (fun x => lorentzLogJac e m p φ ψ a i (inverseLogRadiusChart x)) := by
  obtain ⟨h0,h2⟩ := lorentz_jacobian_decay e m p φ ψ j hd.compact hd.chart hd.region hd.chartInv
  intro a i
  by_cases h : a=0 ∧ i≠0
  · rcases h with ⟨rfl,hi⟩
    simpa only [logJacRate,hi,ne_eq,not_false_eq_true,true_and,ite_true,ite_false,sub_zero] using
      (h2 i).mono hd.newRegion
  · simpa only [logJacRate,h,ite_false] using (h0 a i).mono hd.newRegion

theorem lorentz_CKS_finite_components (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j qrad : ℕ) (hq : 5 ≤ qrad) {K U V : Set Point}
    (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j qrad V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    (∀ a b, FiniteLogDecay j (logTensorRate a b) U (lorentzLogTensor e m p φ ψ A a b)) ∧
    (∀ a b, FiniteLogDecay j 2 U (fun x => lorentzLogTensor e m p φ ψ A a b x -
      radiusPower (-1) x * transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b (boundaryProjection (inverseLogRadiusChart x)))) ∧
    (6 ≤ qrad → FiniteLogDecay j 4 U (fun x => lorentzLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr
        (boundaryProjection (inverseLogRadiusChart x)))) := by
  have hT := oldLogTensor_decay e m p φ ψ j qrad hq hd hA hr hg
  have hJ := lorentz_jacobian_sharp_decay e m p φ ψ j hd
  refine ⟨finite_log_tensor_pullback_rates j hd.largeRadius hJ hT,?_,?_⟩
  · exact finite_log_tensor_angular_leading j hd.compact hd.segment hd.newRegion hd.largeRadius
      (fun a i z hz => lorentzLogJac_contDiffAt e m p φ ψ (hd.chart z hz)
        (hd.region z hz) (hd.chartInv z hz) a i)
      (lorentz_compact_angular_leading_regular e m p φ ψ hd hg) hT
      (oldLogTensor_angular_remainder e m p φ ψ j qrad hd hA)
  · intro hq6
    have hδ : FiniteLogDecay j 2 U
        (fun x => lorentzLogJac e m p φ ψ 0 0 (inverseLogRadiusChart x)-1) := by
      simpa only [ite_true] using ((lorentz_jacobian_decay e m p φ ψ j
        hd.compact hd.chart hd.region hd.chartInv).2 0).mono hd.newRegion
    have he : FiniteLogDecay j 4 U (fun x => oldLogTensor e m p φ ψ A 0 0 x -
        radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr (inverseLogRadiusChart x)) :=
      (oldLogTensor_radial_remainder e m p φ ψ j qrad hd hA).weaken
        (by exact_mod_cast (show (4:ℤ) ≤ (qrad:ℤ)-2 by omega)) hd.largeRadius
    exact finite_log_tensor_radial_leading j hd.compact hd.segment hd.newRegion hd.largeRadius
      (lorentz_compact_radial_leading_regular e m p φ ψ hd hr) (hJ 0) hδ hT he

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus CKSAngularSlice
open scoped ContDiff Topology

def radialLogChart (y : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i=0 then Real.log (y 0) else y i

@[simp] lemma radialLogChart_logRadiusChart (x : Point) :
    radialLogChart (logRadiusChart x) = x := by
  ext i
  by_cases hi : i=0 <;> simp [radialLogChart,logRadiusChart,hi]

lemma logRadiusChart_radialLogChart {y : Point} (hy : 0 < y 0) :
    logRadiusChart (radialLogChart y) = y := by
  ext i
  by_cases hi : i=0 <;> simp [radialLogChart,logRadiusChart,hi,Real.exp_log hy]

lemma radialLogChart_contDiffAt {y : Point} (hy : 0 < y 0) :
    ContDiffAt ℝ ∞ radialLogChart y := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · simp only [radialLogChart,hi,ite_true]
    exact (show ContDiffAt ℝ ∞ (fun z : Point => z 0) y by fun_prop).log (ne_of_gt hy)
  · simp only [radialLogChart,hi,ite_false]
    fun_prop

theorem FiniteLogDecay.to_source {j q : ℕ} {U : Set Point} {f : Point → ℝ}
    (hf : FiniteLogDecay j q U f) :
    SourceRemainderOn j q (logRadiusChart '' U) (fun y => f (radialLogChart y)) := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j
      (fun y => f (radialLogChart y)) (logRadiusChart x) := by
    have hl := (radialLogChart_contDiffAt (show 0 < (logRadiusChart x) 0 by
      simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    have hfx : ContDiffAt ℝ j f (radialLogChart (logRadiusChart x)) := by
      simpa only [radialLogChart_logRadiusChart] using hf.regular x hx
    exact hfx.comp _ hl
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  have he := coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))
  have hi : (fun z => f (radialLogChart (logRadiusChart z))) = f := by
    funext z
    rw [radialLogChart_logRadiusChart]
  rw [hi] at he
  rw [← he]
  calc |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

theorem FiniteLogDecay.source_of_log {j q : ℕ} {U : Set Point} {g : Point → ℝ}
    (hf : FiniteLogDecay j q U (fun x => g (logRadiusChart x))) :
    SourceRemainderOn j q (logRadiusChart '' U) g := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j g (logRadiusChart x) := by
    have h := hf.to_source.regular (logRadiusChart x) ⟨x,hx,rfl⟩
    have he : g =ᶠ[𝓝 (logRadiusChart x)]
        (fun y => g (logRadiusChart (radialLogChart y))) := by
      have hp : ∀ᶠ y in 𝓝 (logRadiusChart x), 0 < y 0 :=
        (isOpen_lt continuous_const (continuous_apply (0:I))).mem_nhds
          (by change 0 < (logRadiusChart x) 0
              simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))
      filter_upwards [hp] with y hy
      rw [logRadiusChart_radialLogChart hy]
    exact h.congr_of_eventuallyEq he
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  rw [← coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))]
  calc _ ≤ ‖iteratedFDeriv ℝ l.length (fun z => g (logRadiusChart z)) x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

def lorentzOrdinaryTensor (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (a b : I) (y : Point) : ℝ :=
  radiusPower (-radialIndexWeight a b) (radialLogChart y) *
    lorentzLogTensor e m p φ ψ A a b (radialLogChart y)

def lorentzRadialLeading (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mr : Angle → ℝ) (θ : Angle) : ℝ :=
  compactLeadingCoefficient e m p φ ψ 3 mr (slice 0 θ)

def lorentzAngularLeading (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (mg : I → I → Angle → ℝ) (a b : I) (θ : Angle) : ℝ :=
  transformedAngularLeading (lorentzLogJac e m p φ ψ)
    (compactAngularCoefficient e m p φ ψ mg) a b (slice 0 θ)

lemma boundary_inverseLogRadiusChart (x : Point) :
    boundaryProjection (inverseLogRadiusChart x) = slice 0 (angularProjection x) := by
  ext i
  fin_cases i <;> simp [boundaryProjection,inverseLogRadiusChart,angularProjection,slice,injection,basis] <;> rfl

lemma ordinaryLeadingComponent_log (q : ℕ) (M : Angle → ℝ) (x : Point) :
    ordinaryLeadingComponent q M (logRadiusChart x) =
      radiusPower (-(q:ℝ)) x * M (angularProjection x) := by
  simp [ordinaryLeadingComponent,logRadiusChart,angularProjection_logRadiusChart,radiusPower_neg_nat]

@[simp] lemma lorentzOrdinaryTensor_log (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (A : I → I → Point → ℝ) (a b : I) (x : Point) :
    lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) =
      radiusPower (-radialIndexWeight a b) x * lorentzLogTensor e m p φ ψ A a b x := by
  simp only [lorentzOrdinaryTensor,radialLogChart_logRadiusChart]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma lorentzOrdinaryTensor_mixed (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ}
    (hT : ∀ a b, FiniteLogDecay j (logTensorRate a b) U (lorentzLogTensor e m p φ ψ A a b))
    (a b : I) (hab : (a=0 ∧ b≠0) ∨ (a≠0 ∧ b=0)) :
    SourceRemainderOn j 3 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A a b) := by
  have hw : radialIndexWeight a b = 1 := by
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [radialIndexWeight,ha,hb]
  have hrate : logTensorRate a b = 2 := by
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [logTensorRate,ha,hb]
  have h := (FiniteLogDecay.radiusPower j 1 U).mul (hT a b)
  have hh : FiniteLogDecay j (3:ℕ) U
      (fun x => lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x)) := by
    simpa only [lorentzOrdinaryTensor_log,hw,hrate,show (1:ℝ)+2=3 by norm_num,Nat.cast_ofNat] using h
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_radial_rough (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ}
    (hT : FiniteLogDecay j 3 U (lorentzLogTensor e m p φ ψ A 0 0)) :
    SourceRemainderOn j 5 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A 0 0) := by
  have h := (FiniteLogDecay.radiusPower j 2 U).mul hT
  have hh : FiniteLogDecay j (5:ℕ) U
      (fun x => lorentzOrdinaryTensor e m p φ ψ A 0 0 (logRadiusChart x)) := by
    convert h using 1 <;> norm_num [lorentzOrdinaryTensor_log,radialIndexWeight]
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_radial_sharp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ} {mr : Angle → ℝ}
    (hT : FiniteLogDecay j 4 U (fun x => lorentzLogTensor e m p φ ψ A 0 0 x -
      radiusPower (-3) x * compactLeadingCoefficient e m p φ ψ 3 mr
        (boundaryProjection (inverseLogRadiusChart x)))) :
    SourceRemainderOn j 6 (logRadiusChart '' U) (fun y => lorentzOrdinaryTensor e m p φ ψ A 0 0 y -
      ordinaryLeadingComponent 5 (lorentzRadialLeading e m p φ ψ mr) y) := by
  have h : FiniteLogDecay j 6 U (fun x => radiusPower (-2) x *
      (lorentzLogTensor e m p φ ψ A 0 0 x - radiusPower (-3) x *
        compactLeadingCoefficient e m p φ ψ 3 mr (boundaryProjection (inverseLogRadiusChart x)))) := by
    simpa only [show (2:ℝ)+4=6 by norm_num] using (FiniteLogDecay.radiusPower j 2 U).mul hT
  have hh : FiniteLogDecay j (6:ℕ) U (fun x => lorentzOrdinaryTensor e m p φ ψ A 0 0 (logRadiusChart x) -
      ordinaryLeadingComponent 5 (lorentzRadialLeading e m p φ ψ mr) (logRadiusChart x)) := by
    apply h.congr
    funext x
    rw [lorentzOrdinaryTensor_log,ordinaryLeadingComponent_log]
    norm_num only [radialIndexWeight,ite_true]
    simp only [lorentzRadialLeading,boundary_inverseLogRadiusChart,mul_sub,← mul_assoc,← radiusPower_add]
    norm_num
  exact hh.source_of_log

lemma lorentzOrdinaryTensor_angular_sharp (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    (j : ℕ) {U : Set Point} {A : I → I → Point → ℝ} {mg : I → I → Angle → ℝ}
    (hT : ∀ a b, FiniteLogDecay j 2 U (fun x => lorentzLogTensor e m p φ ψ A a b x -
      radiusPower (-1) x * transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b (boundaryProjection (inverseLogRadiusChart x))))
    (a b : I) (ha : a≠0) (hb : b≠0) :
    SourceRemainderOn j 2 (logRadiusChart '' U) (fun y => lorentzOrdinaryTensor e m p φ ψ A a b y -
      ordinaryLeadingComponent 1 (lorentzAngularLeading e m p φ ψ mg a b) y) := by
  have hh : FiniteLogDecay j (2:ℕ) U (fun x => lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) -
      ordinaryLeadingComponent 1 (lorentzAngularLeading e m p φ ψ mg a b) (logRadiusChart x)) := by
    convert hT a b using 1
    funext x
    simp [lorentzOrdinaryTensor_log,ordinaryLeadingComponent_log,lorentzAngularLeading,
      radialIndexWeight,ha,hb,radiusPower,boundary_inverseLogRadiusChart]
  exact hh.source_of_log

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem lorentz_metric_CKS (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 V A mr mg)
    (hr : ∀ z ∈ K, ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ z)))
    (hg : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    SourceCKSComponents 3 6 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ A)
      (lorentzRadialLeading e m p φ ψ mr) (lorentzAngularLeading e m p φ ψ mg) := by
  obtain ⟨hT,hg',hr'⟩ := lorentz_CKS_finite_components e m p φ ψ 3 6 (by norm_num) hd hA hr hg
  exact ⟨lorentzOrdinaryTensor_radial_sharp e m p φ ψ 3 (hr' le_rfl),
    lorentzOrdinaryTensor_mixed e m p φ ψ 3 hT,
    lorentzOrdinaryTensor_angular_sharp e m p φ ψ 3 hg'⟩

theorem lorentz_second_CKS (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {K U V : Set Point} (hd : LorentzChartDomain e m p φ ψ K U V)
    {B : I → I → Point → ℝ} {mK : I → I → Angle → ℝ}
    (hB : SourceCKSComponents 2 5 V B (fun _ => 0) mK)
    (hK : ∀ i k, i≠0 → k≠0 → ∀ z ∈ K, ContDiffAt ℝ ∞ (mK i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ z))) :
    SourceCKSComponents 2 5 (logRadiusChart '' U) (lorentzOrdinaryTensor e m p φ ψ B)
      (fun _ => 0) (lorentzAngularLeading e m p φ ψ mK) := by
  obtain ⟨hT,hg',_⟩ := lorentz_CKS_finite_components e m p φ ψ 2 5 (by norm_num) hd hB
    (fun z hz => contDiffAt_const) hK
  refine ⟨?_,lorentzOrdinaryTensor_mixed e m p φ ψ 2 hT,
    lorentzOrdinaryTensor_angular_sharp e m p φ ψ 2 hg'⟩
  have hr : FiniteLogDecay 2 3 U (lorentzLogTensor e m p φ ψ B 0 0) := by
    simpa only [logTensorRate,ite_true] using hT 0 0
  simpa only [ordinaryLeadingComponent,mul_zero,sub_zero] using
    lorentzOrdinaryTensor_radial_rough e m p φ ψ 2 hr

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice

def coordinateTensorPullback (F : Point → Point) (A : I → I → Point → ℝ)
    (a b : I) (y : Point) : ℝ :=
  ∑ i, ∑ k, D (basis a) (fun z => F z i) y *
    D (basis b) (fun z => F z k) y * A i k (F y)

def ordinaryConjugate (F : Point → Point) (y : Point) : Point :=
  logRadiusChart (F (radialLogChart y))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma chartDerivative_apply (x v : Point) (i : I) :
    chartDerivative x v i = radialFactor i (logRadiusChart x) * v i := by
  by_cases hi : i=0 <;> simp [chartDerivative,radialFactor,logRadiusChart,hi]

lemma D_logRadius_comp {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (a i : I) :
    D (basis a) (fun z => logRadiusChart (F z) i) x =
      radialFactor i (logRadiusChart (F x)) * D (basis a) (fun z => F z i) x := by
  have hL := ((ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt.comp (F x)
    (logRadiusChart_hasFDerivAt (F x))).comp x hF.hasFDerivAt
  have hFi := ((ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt)
  change HasFDerivAt (fun z => logRadiusChart (F z) i) _ x at hL
  change HasFDerivAt (fun z => F z i) _ x at hFi
  unfold D
  rw [hL.fderiv,hFi.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,chartDerivative_apply]

lemma ordinaryConjugate_differentiableAt {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) :
    DifferentiableAt ℝ (ordinaryConjugate F) (logRadiusChart x) := by
  have hl := (radialLogChart_contDiffAt (show 0 < (logRadiusChart x) 0 by
    simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0))).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ F (radialLogChart (logRadiusChart x)) := by simpa using hF
  exact logRadiusChart_smooth.differentiable (by simp) |>.differentiableAt.comp _ (hf.comp _ hl)

lemma radialFactor_pos (a : I) (x : Point) : 0 < radialFactor a (logRadiusChart x) := by
  by_cases ha : a=0 <;> simp [radialFactor,logRadiusChart,ha,Real.exp_pos]

lemma D_ordinaryConjugate {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (a i : I) :
    D (basis a) (fun y => ordinaryConjugate F y i) (logRadiusChart x) =
      (radialFactor a (logRadiusChart x))⁻¹ *
        radialFactor i (logRadiusChart (F x)) * D (basis a) (fun z => F z i) x := by
  have hdi : DifferentiableAt ℝ (fun y => ordinaryConjugate F y i) (logRadiusChart x) := by
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).differentiableAt.comp _
      (ordinaryConjugate_differentiableAt hF)
  have he := D_pullback a hdi
  have heq : (fun z => ordinaryConjugate F (logRadiusChart z) i) =
      (fun z => logRadiusChart (F z) i) := by
    funext z
    simp only [ordinaryConjugate,radialLogChart_logRadiusChart]
  rw [heq,D_logRadius_comp hF] at he
  unfold scaledD at he
  have hne := (radialFactor_pos a x).ne'
  calc
    _ = (radialFactor a (logRadiusChart x))⁻¹ *
        (radialFactor a (logRadiusChart x) *
          D (basis a) (fun y => ordinaryConjugate F y i) (logRadiusChart x)) := by
            rw [←mul_assoc,inv_mul_cancel₀ hne,one_mul]
    _ = _ := by rw [←he]; ring

lemma radialFactor_pair (a b : I) (x : Point) :
    radialFactor a (logRadiusChart x) * radialFactor b (logRadiusChart x) =
      radiusPower (radialIndexWeight a b) x := by
  simp only [radialIndexWeight,radiusPower,add_mul,Real.exp_add]
  congr 1 <;> split_ifs <;> simp_all [radialFactor,logRadiusChart]

lemma radialFactor_inv_pair (a b : I) (x : Point) :
    (radialFactor a (logRadiusChart x))⁻¹ * (radialFactor b (logRadiusChart x))⁻¹ =
      radiusPower (-radialIndexWeight a b) x := by
  rw [←mul_inv,radialFactor_pair]
  simp only [radiusPower,neg_mul,Real.exp_neg]

theorem coordinateTensorPullback_log {F : Point → Point} {x : Point}
    (hF : DifferentiableAt ℝ F x) (A : I → I → Point → ℝ) (a b : I) :
    coordinateTensorPullback (ordinaryConjugate F) A a b (logRadiusChart x) =
      radiusPower (-radialIndexWeight a b) x *
        ∑ i, ∑ k, D (basis a) (fun z => F z i) x * D (basis b) (fun z => F z k) x *
          (radiusPower (radialIndexWeight i k) (F x) * A i k (logRadiusChart (F x))) := by
  simp only [coordinateTensorPullback]
  simp_rw [D_ordinaryConjugate hF]
  simp only [ordinaryConjugate,radialLogChart_logRadiusChart,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [←radialFactor_inv_pair,←radialFactor_pair]
  ring

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma coordinateTensorPullback_congr {F G : Point → Point} {y : Point}
    (hFG : F =ᶠ[𝓝 y] G) (A : I → I → Point → ℝ) (a b : I) :
    coordinateTensorPullback F A a b y = coordinateTensorPullback G A a b y := by
  have he (i : I) : (fun z => F z i) =ᶠ[𝓝 y] (fun z => G z i) :=
    hFG.mono (fun z hz => congrFun hz i)
  simp only [coordinateTensorPullback,D,(he _).fderiv_eq,hFG.eq_of_nhds]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma lorentzPolarChart_germ (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point}
    (hn : ∀ᶠ θ in 𝓝 (angularProjection x), φ θ ∈ Metric.sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p) :
    lorentzPolarChart e m p φ ψ =ᶠ[𝓝 (logRadiusChart x)]
      ordinaryConjugate (logLorentzChart e m p φ ψ) := by
  have hnr : ∀ᶠ z in 𝓝 x, φ (angularProjection z) ∈ Metric.sphere (0 : E) 1 :=
    angularProjection.continuous.continuousAt.eventually hn
  have hscale : ContinuousAt (fun z => compactScale e m p (compactPolar φ (inverseLogRadiusChart z))) x :=
    ((compactScale_smooth_region e m p hz).continuousAt.comp
      (compactPolar_contDiffAt hφ).continuousAt).comp inverseLogRadiusChart_smooth.continuous.continuousAt
  have hpos : ∀ᶠ z in 𝓝 x, 0 < compactScale e m p (compactPolar φ (inverseLogRadiusChart z)) :=
    hscale.eventually (Ioi_mem_nhds hz.2)
  have he : (fun z => lorentzPolarChart e m p φ ψ (logRadiusChart z)) =ᶠ[𝓝 x]
      (fun z => logRadiusChart (logLorentzChart e m p φ ψ z)) := by
    filter_upwards [hnr,hpos] with z hzn hzp
    exact lorentzPolarChart_logRadiusChart e m p φ ψ hzn hzp
  have hr : 0 < (logRadiusChart x) 0 := by
    simpa only [logRadiusChart,ite_true] using Real.exp_pos (x 0)
  have hlc : Tendsto radialLogChart (𝓝 (logRadiusChart x)) (𝓝 x) := by
    simpa only [ContinuousAt,radialLogChart_logRadiusChart] using (radialLogChart_contDiffAt hr).continuousAt
  have hy : ∀ᶠ y in 𝓝 (logRadiusChart x), 0 < y 0 :=
    (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).continuous.continuousAt.eventually
      (Ioi_mem_nhds hr)
  filter_upwards [he.comp_tendsto hlc,hy] with y hey hry
  simpa only [Function.comp_def,logRadiusChart_radialLogChart hry,ordinaryConjugate] using hey

theorem lorentzOrdinaryTensor_eq_pullback (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle)
    {x : Point}
    (hn : ∀ᶠ θ in 𝓝 (angularProjection x), φ θ ∈ Metric.sphere (0 : E) 1)
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection (inverseLogRadiusChart x)))
    (hz : compactPolar φ (inverseLogRadiusChart x) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (inverseLogRadiusChart x))))
    (A : I → I → Point → ℝ) (a b : I) :
    lorentzOrdinaryTensor e m p φ ψ A a b (logRadiusChart x) =
      coordinateTensorPullback (lorentzPolarChart e m p φ ψ) A a b (logRadiusChart x) := by
  rw [coordinateTensorPullback_congr (lorentzPolarChart_germ e m p φ ψ hn hφ hz),
    coordinateTensorPullback_log
      ((logLorentzChart_contDiffAt e m p φ ψ hφ hz hψ).differentiableAt (by simp)),
    lorentzOrdinaryTensor_log]
  simp only [D_logLorentzChart e m p φ ψ hφ hz hψ,lorentzLogTensor,logCovariantPullback,
    oldLogTensor]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

def boundaryChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (θ : Angle) : Angle :=
  ψ (boundaryAmbient e m p (φ θ))

def angularCoordinatePullback (Φ : Angle → Angle) (mg : I → I → Angle → ℝ)
    (a b : Fin 2) (θ : Angle) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 2,
    D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ *
    D (CKSAngularGeometry.basis b) (fun η => Φ η k) θ * mg i.succ k.succ (Φ θ)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

lemma compactPolar_slice (r : ℝ) (θ : Angle) (φ : Angle → E) :
    compactPolar φ (slice r θ) = (r,φ θ) := by
  simp [compactPolar,angularProjection_slice]

lemma compactScale_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactScale e m p (0,n) = denominator e m p n := by
  change ‖compactSpatial e m p (0,n)‖ = _
  rw [compactSpatial_zero]
  exact boundarySpatial_norm he hm0 hm ⟨n,hn⟩

lemma compactAngle_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactAngle e m p (0,n) = boundaryAmbient e m p n := by
  simp only [compactAngle,compactScale_boundary he hm0 hm hn,compactSpatial_zero,boundaryAmbient]

lemma compactRegion_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) : (0,n) ∈ compactRegion e m p := by
  refine ⟨denominator_pos he hm0 ⟨n,hn⟩,?_⟩
  rw [compactScale_boundary he hm0 hm hn]
  exact denominator_pos he hm0 ⟨n,hn⟩

lemma compactLorentzCoefficients_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLorentzCoefficients e m p φ ψ (slice 0 θ) =
      slice (Real.log (denominator e m p (φ θ))) (boundaryChart e m p φ ψ θ) := by
  simp only [compactLorentzCoefficients,compactPolar_slice,compactScale_boundary he hm0 hm hn,
    compactAngle_boundary he hm0 hm hn,boundaryChart]

lemma compactLeadingCoefficient_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (M : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLeadingCoefficient e m p φ ψ q M (slice 0 θ) =
      (denominator e m p (φ θ))⁻¹^q * M (boundaryChart e m p φ ψ θ) := by
  simp only [compactLeadingCoefficient,compactLorentzCoefficients_boundary he hm0 hm φ ψ hn,
    slice_zero,angularProjection_slice,neg_mul,Real.exp_neg,Real.exp_nat_mul,
    Real.exp_log (denominator_pos he hm0 ⟨φ θ,hn⟩),inv_pow]

theorem lorentzRadialLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mr : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    lorentzRadialLeading e m p φ ψ mr θ =
      (denominator e m p (φ θ))⁻¹^3 * mr (boundaryChart e m p φ ψ θ) :=
  compactLeadingCoefficient_boundary he hm0 hm φ ψ 3 mr hn

lemma lorentzLogJac_boundary_angular {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a i : Fin 2) :
    lorentzLogJac e m p φ ψ a.succ i.succ (slice 0 θ) =
      D (CKSAngularGeometry.basis a) (fun η => boundaryChart e m p φ ψ η i) θ := by
  have hn0 := hn.self_of_nhds
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) (slice 0 θ) := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [angularProjection_slice] using hφ
    · simpa only [compactPolar_slice] using compactRegion_boundary he hm0 hm hn0
    · simpa only [compactPolar_slice,compactAngle_boundary he hm0 hm hn0] using hψ
  have hci := ((contDiffAt_pi.mp hc) i.succ).differentiableAt (by simp)
  simp only [lorentzLogJac,Fin.succ_ne_zero,false_and,ite_false,zero_add,
    backwardScaledD,backwardFactor,one_mul]
  rw [←D_slice a 0 hci]
  apply D_congr
  filter_upwards [hn] with η hη
  simp only [compactLorentzCoefficients_boundary he hm0 hm φ ψ hη,slice_succ]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentzAngularLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mg : I → I → Angle → ℝ) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a b : Fin 2) :
    lorentzAngularLeading e m p φ ψ mg a.succ b.succ θ =
      (denominator e m p (φ θ))⁻¹ *
        angularCoordinatePullback (boundaryChart e m p φ ψ) mg a b θ := by
  simp only [lorentzAngularLeading,transformedAngularLeading,Fin.sum_univ_succ,
    angularLeadingEntry,ne_eq,not_true_eq_false,false_and,and_false,ite_false,
    mul_zero,Finset.sum_const_zero,zero_add,Fin.succ_ne_zero,not_false_eq_true,
    and_self,ite_true,compactAngularCoefficient]
  simp_rw [lorentzLogJac_boundary_angular he hm0 hm φ ψ hn hφ hψ]
  have hc (M : Angle → ℝ) :
      compactLeadingCoefficient e m p φ ψ 1 M (slice 0 θ) =
        (denominator e m p (φ θ))⁻¹ * M (boundaryChart e m p φ ψ θ) := by
    simpa only [Nat.cast_one,pow_one] using
      compactLeadingCoefficient_boundary he hm0 hm φ ψ 1 M hn.self_of_nhds
  simp_rw [hc]
  simp only [angularCoordinatePullback,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

lemma lorentzRadialLeading_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {mr : Angle → ℝ} {θ : Angle}
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hz : compactPolar φ (slice 0 θ) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (slice 0 θ))))
    (hr : ContDiffAt ℝ ∞ mr
      (angularProjection (compactLorentzCoefficients e m p φ ψ (slice 0 θ)))) :
    ContDiffAt ℝ ∞ (lorentzRadialLeading e m p φ ψ mr) θ := by
  have hp : ContDiffAt ℝ ∞ φ (angularProjection (slice 0 θ)) := by
    simpa only [angularProjection_slice] using hφ
  exact (compactLeadingCoefficient_regular e m p φ ψ 3 hp hz hψ hr).comp θ
    (slice_smooth 0).contDiffAt

lemma lorentzAngularLeading_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {mg : I → I → Angle → ℝ} {θ : Angle}
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hz : compactPolar φ (slice 0 θ) ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ (slice 0 θ))))
    (hg : ∀ i k, i≠0 → k≠0 → ContDiffAt ℝ ∞ (mg i k)
      (angularProjection (compactLorentzCoefficients e m p φ ψ (slice 0 θ)))) (a b : I) :
    ContDiffAt ℝ ∞ (lorentzAngularLeading e m p φ ψ mg a b) θ := by
  have hp : ContDiffAt ℝ ∞ φ (angularProjection (slice 0 θ)) := by
    simpa only [angularProjection_slice] using hφ
  have hJ i k := lorentzLogJac_contDiffAt e m p φ ψ hp hz hψ i k
  have hC (i k : I) : ContDiffAt ℝ ∞
      (fun z => angularLeadingEntry (compactAngularCoefficient e m p φ ψ mg) i k z) (slice 0 θ) := by
    simp only [angularLeadingEntry]
    split_ifs with hik
    · exact compactLeadingCoefficient_regular e m p φ ψ 1 hp hz hψ (hg i k hik.1 hik.2)
    · exact contDiffAt_const
  have ht : ContDiffAt ℝ ∞
      (transformedAngularLeading (lorentzLogJac e m p φ ψ)
        (compactAngularCoefficient e m p φ ψ mg) a b) (slice 0 θ) := by
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    exact ((hJ a i).mul (hJ b k)).mul (hC i k)
  exact ht.comp θ (slice_smooth 0).contDiffAt

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def angularLogTail (L : ℝ) (θ : Angle) (δ : ℝ) : Set Point :=
  {x | L ≤ x 0 ∧ angularProjection x ∈ Metric.ball θ δ}

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma boundaryProjection_closedBall {θ : Angle} {δ : ℝ} (hδ : 0 ≤ δ)
    {z : Point} (hz : z ∈ Metric.closedBall (slice 0 θ) δ) :
    boundaryProjection z ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [boundaryProjection_zero,slice_zero,dist_self]
    exact hδ
  · have hi := (dist_pi_le_iff hδ).1 hz a.succ
    simpa only [boundaryProjection,sub_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      basis,Pi.single_apply,Fin.succ_ne_zero,ite_false,mul_zero,sub_zero] using hi

lemma inverseLogRadius_mem_closedBall {θ : Angle} {δ : ℝ} (hδ : 0 < δ)
    {x : Point} (hr : Real.exp (-x 0) ≤ δ)
    (ha : angularProjection x ∈ Metric.closedBall θ δ) :
    inverseLogRadiusChart x ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ.le).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [inverseLogRadiusChart,ite_true,slice_zero,Real.dist_eq,sub_zero,
      abs_of_pos (Real.exp_pos _)] using hr
  · have hi := (dist_pi_le_iff hδ.le).1 ha a
    simpa only [inverseLogRadiusChart,Fin.succ_ne_zero,ite_false,slice_succ,
      angularProjection,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply] using hi

lemma eventually_full_log_tail {δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, L ≤ t →
      Real.exp (-t) ≤ δ ∧ R < Real.exp t*d := by
  have hs : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < δ :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hδ)
  have he : ∀ᶠ t : ℝ in atTop, R/d < Real.exp t :=
    Real.tendsto_exp_atTop.eventually (eventually_gt_atTop (R/d))
  obtain ⟨L,hL⟩ := eventually_atTop.1 ((eventually_ge_atTop (0:ℝ)).and (hs.and he))
  refine ⟨L,(hL L le_rfl).1,fun t ht => ?_⟩
  exact ⟨(hL t ht).2.1.le,(div_lt_iff₀ hd).mp (hL t ht).2.2⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

theorem exists_lorentzChartDomain_regular {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    {A W : Set Angle} {B : Set E}
    (hA : IsOpen A) (hθ : θ ∈ A) (hφ : ContDiffOn ℝ ∞ φ A)
    (hn : ∀ η ∈ A, φ η ∈ Metric.sphere (0:E) 1)
    (hB : IsOpen B) (hψ : ContDiffOn ℝ ∞ ψ B)
    (hb : boundaryAmbient e m p (φ θ) ∈ B)
    (hW : IsOpen W) (hw : boundaryChart e m p φ ψ θ ∈ W) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      LorentzChartDomain e m p φ ψ (Metric.closedBall (slice 0 θ) δ)
        (angularLogTail L θ (δ/2)) (angularRadialTail R W) ∧
      MapsTo angularProjection (Metric.closedBall (slice 0 θ) δ) A ∧
      MapsTo (fun z => angularProjection (compactLorentzCoefficients e m p φ ψ z))
        (Metric.closedBall (slice 0 θ) δ) W := by
  let z₀ : Point := slice 0 θ
  have hφ₀ := hφ.contDiffAt (hA.mem_nhds hθ)
  have hp : ContDiffAt ℝ ∞ (compactPolar φ) z₀ := by
    apply compactPolar_contDiffAt
    simpa only [z₀,angularProjection_slice] using hφ₀
  have hz₀ : compactPolar φ z₀ ∈ compactRegion e m p := by
    simpa only [z₀,compactPolar_slice] using compactRegion_boundary he hm0 hm (hn θ hθ)
  have hb₀ : compactAngle e m p (compactPolar φ z₀) ∈ B := by
    simpa only [z₀,compactPolar_slice,compactAngle_boundary he hm0 hm (hn θ hθ)] using hb
  have hψ₀ := hψ.contDiffAt (hB.mem_nhds hb₀)
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z₀ := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [z₀,angularProjection_slice] using hφ₀
    · exact hz₀
    · exact hψ₀
  have hw₀ : angularProjection (compactLorentzCoefficients e m p φ ψ z₀) ∈ W := by
    simpa only [z₀,compactLorentzCoefficients_boundary he hm0 hm φ ψ (hn θ hθ),
      angularProjection_slice] using hw
  let d : ℝ := denominator e m p (φ θ)/2
  have hd : 0 < d := half_pos (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have hds : d < compactScale e m p (compactPolar φ z₀) := by
    rw [show z₀ = slice 0 θ from rfl,compactPolar_slice,compactScale_boundary he hm0 hm (hn θ hθ)]
    exact half_lt_self (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have ha : ∀ᶠ z : Point in 𝓝 z₀, angularProjection z ∈ A :=
    angularProjection.continuous.continuousAt.preimage_mem_nhds
      (hA.mem_nhds (by simpa only [z₀,angularProjection_slice] using hθ))
  have hr : ∀ᶠ z : Point in 𝓝 z₀, compactPolar φ z ∈ compactRegion e m p :=
    hp.continuousAt.preimage_mem_nhds ((compactRegion_open e m p).mem_nhds hz₀)
  have hb' : ∀ᶠ z : Point in 𝓝 z₀, compactAngle e m p (compactPolar φ z) ∈ B :=
    ((compactAngle_contDiffAt e m p hz₀).comp z₀ hp).continuousAt.preimage_mem_nhds
      (hB.mem_nhds hb₀)
  have hw' : ∀ᶠ z : Point in 𝓝 z₀,
      angularProjection (compactLorentzCoefficients e m p φ ψ z) ∈ W :=
    (angularProjection.contDiff.contDiffAt.comp z₀ hc).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hw₀)
  have hs : ∀ᶠ z : Point in 𝓝 z₀, d < compactScale e m p (compactPolar φ z) :=
    ((compactScale_smooth_region e m p hz₀).comp z₀ hp).continuousAt
      (lt_mem_nhds hds)
  obtain ⟨ρ,hρ,hsub⟩ := Metric.mem_nhds_iff.1 (ha.and (hr.and (hb'.and (hw'.and hs))))
  let δ : ℝ := ρ/2
  have hδ : 0 < δ := half_pos hρ
  have hδρ : δ < ρ := half_lt_self hρ
  have hK z (hz : z ∈ Metric.closedBall z₀ δ) :=
    hsub (Metric.closedBall_subset_ball hδρ hz)
  obtain ⟨L,hL,hLt⟩ := eventually_full_log_tail (half_pos hδ) hd R
  have hnew {x : Point} (hx : x ∈ angularLogTail L θ (δ/2)) :
      inverseLogRadiusChart x ∈ Metric.closedBall z₀ δ := by
    apply inverseLogRadius_mem_closedBall hδ
    · exact ((hLt (x 0) hx.1).1).trans (half_le_self hδ.le)
    · exact ((Metric.mem_ball.mp hx.2).le).trans (half_le_self hδ.le)
  refine ⟨δ,hδ,L,hL,?_,fun z hz => (hK z hz).1,fun z hz => (hK z hz).2.2.2.1⟩
  refine ⟨isCompact_closedBall _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact hφ.contDiffAt (hA.mem_nhds (hK z hz).1)
  · intro z hz
    exact (hK z hz).2.1
  · intro z hz
    exact hψ.contDiffAt (hB.mem_nhds (hK z hz).2.2.1)
  · intro z hz
    exact (convex_closedBall z₀ δ).segment_subset (boundaryProjection_closedBall hδ.le hz) hz
  · intro x hx
    exact hnew hx
  · intro x hx
    have hk := hK _ (hnew hx)
    refine ⟨?_,?_⟩
    · change R < Real.exp ((logLorentzChart e m p φ ψ x) 0)
      rw [logLorentzChart_radial_exp e m p φ ψ hk.2.1.2]
      exact ((hLt (x 0) hx.1).2).trans_le
        (mul_le_mul_of_nonneg_left hk.2.2.2.2.le (Real.exp_pos _).le)
    · simpa only [angularProjection_logRadiusChart,logLorentzChart_angular_coeff] using hk.2.2.2.1
  · intro x hx
    exact hL.trans hx.1

theorem exists_lorentzChartDomain {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    {A W : Set Angle} {B : Set E}
    (hA : IsOpen A) (hθ : θ ∈ A) (hφ : ContDiffOn ℝ ∞ φ A)
    (hn : ∀ η ∈ A, φ η ∈ Metric.sphere (0:E) 1)
    (hB : IsOpen B) (hψ : ContDiffOn ℝ ∞ ψ B)
    (hb : boundaryAmbient e m p (φ θ) ∈ B)
    (hW : IsOpen W) (hw : boundaryChart e m p φ ψ θ ∈ W) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      LorentzChartDomain e m p φ ψ (Metric.closedBall (slice 0 θ) δ)
        (angularLogTail L θ (δ/2)) (angularRadialTail R W) := by
  obtain ⟨δ,hδ,L,hL,hd,_,_⟩ := exists_lorentzChartDomain_regular he hm0 hm φ ψ
    hA hθ hφ hn hB hψ hb hW hw R
  exact ⟨δ,hδ,L,hL,hd⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

namespace SmoothAngularPatch

end SmoothAngularPatch

theorem stereoDimension : Fact (Module.finrank ℝ E = 2+1) := ⟨by simp [E]⟩

attribute [local instance] stereoDimension

def stereoAngleEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] Angle :=
  EuclideanSpace.equiv (Fin 2) ℝ

def stereoOrthogonalEquiv (v : Sphere) : (ℝ ∙ (v:E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr

def stereoAngularChart (v : Sphere) : OpenPartialHomeomorph Sphere Angle :=
  (stereographic' 2 v).trans stereoAngleEquiv.toHomeomorph.toOpenPartialHomeomorph

def stereoAngularExtension (v : Sphere) (x : E) : Angle :=
  stereoAngleEquiv (stereoOrthogonalEquiv v (stereoToFun (v:E) x))

def stereoAmbientDomain (v : Sphere) : Set E :=
  letI := two_atLeastTwo
  letI : Inner ℝ E :=
    @InnerProductSpace.toInner ℝ E _
      (PiLp.seminormedAddCommGroup 2 (fun _ : Fin 3 => ℝ))
      (PiLp.innerProductSpace (fun _ : Fin 3 => ℝ))
  {x | inner ℝ (v:E) x ≠ 1}

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

@[simp] lemma stereoAngularChart_source (v : Sphere) :
    (stereoAngularChart v).source = {v}ᶜ := by
  simp [stereoAngularChart]

@[simp] lemma stereoAngularChart_target (v : Sphere) :
    (stereoAngularChart v).target = univ := by
  simp [stereoAngularChart]

lemma stereoAngularChart_param (v : Sphere) (θ : Angle) :
    ((stereoAngularChart v).symm θ : E) = stereoInvFunAux (v:E)
      ((stereoOrthogonalEquiv v).symm (stereoAngleEquiv.symm θ) : E) := rfl

lemma stereoAngularChart_param_smooth (v : Sphere) :
    ContDiff ℝ ∞ (fun θ => ((stereoAngularChart v).symm θ : E)) := by
  simp_rw [stereoAngularChart_param]
  exact contDiff_stereoInvFunAux.comp
    ((ℝ ∙ (v:E))ᗮ.subtypeL.contDiff.comp
      ((stereoOrthogonalEquiv v).symm.toContinuousLinearEquiv.contDiff.comp
        stereoAngleEquiv.symm.contDiff))

lemma stereoAmbientDomain_open (v : Sphere) : IsOpen (stereoAmbientDomain v) :=
  isOpen_ne_fun (innerSL ℝ (v:E)).continuous continuous_const

lemma stereoAngularExtension_smooth (v : Sphere) :
    ContDiffOn ℝ ∞ (stereoAngularExtension v) (stereoAmbientDomain v) := by
  exact stereoAngleEquiv.contDiff.comp_contDiffOn
    ((stereoOrthogonalEquiv v).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      contDiffOn_stereoToFun)

lemma stereoAngularChart_source_domain (v n : Sphere)
    (hn : n ∈ (stereoAngularChart v).source) : (n:E) ∈ stereoAmbientDomain v := by
  change inner ℝ (v:E) (n:E) ≠ 1
  intro h
  have he : v=n := (sphere_ext_iff v n).mpr h
  simp [stereoAngularChart_source,he] at hn

lemma stereoAngularExtension_eq (v n : Sphere) :
    stereoAngularExtension v n=stereoAngularChart v n := rfl

def stereoSmoothPatch (v : Sphere) : SmoothAngularPatch where
  chart := stereoAngularChart v
  param_smooth := (stereoAngularChart_param_smooth v).contDiffOn
  extension := stereoAngularExtension v
  domain := stereoAmbientDomain v
  isOpen_domain := stereoAmbientDomain_open v
  extension_smooth := stereoAngularExtension_smooth v
  source_domain := stereoAngularChart_source_domain v
  extension_eq := fun n _ => stereoAngularExtension_eq v n

theorem exists_smoothAngularPatch (n : Sphere) :
    ∃ P : SmoothAngularPatch, n ∈ P.chart.source := by
  refine ⟨stereoSmoothPatch (-n),?_⟩
  change n ∈ (stereoAngularChart (-n)).source
  simpa only [stereoAngularChart_source,mem_compl_iff,mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ n

namespace SmoothAngularPatch

lemma param_sphere (P : SmoothAngularPatch) (θ : Angle) :
    P.param θ ∈ Metric.sphere (0:E) 1 := (P.chart.symm θ).2

lemma param_norm (patch : SmoothAngularPatch) (angle : Angle) : ‖patch.param angle‖ = 1 :=
  (dist_zero_right (patch.param angle)).symm.trans (Metric.mem_sphere.mp (patch.param_sphere angle))

lemma param_contDiffAt (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    ContDiffAt ℝ ∞ P.param θ :=
  P.param_smooth.contDiffAt (P.chart.open_target.mem_nhds hθ)

lemma sphereRegion_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (P.sphereRegion W) :=
  P.chart.isOpen_inter_preimage hW

lemma param_chart (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source) :
    P.param (P.chart n)=(n:E) := congrArg Subtype.val (P.chart.left_inv hn)

end SmoothAngularPatch
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

structure BoostPatchEstimates (e : ℝ) (p : E) (Q : CKSTensorPatch)
    (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  radius_pos : 0 < R
  ball_pos : 0 < δ
  ball_target : Metric.ball θ δ ⊆ P.chart.target
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail R (Metric.ball θ δ))
    (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.metric)
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
  second_CKS : SourceCKSComponents 2 5 (angularRadialTail R (Metric.ball θ δ))
    (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.second)
    (fun _ => 0)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
  radial_smooth : ContDiffOn ℝ ∞
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr) (Metric.ball θ δ)
  angular_smooth : ∀ i k, ContDiffOn ℝ ∞
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg i k) (Metric.ball θ δ)
  second_smooth : ∀ i k, ContDiffOn ℝ ∞
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK i k) (Metric.ball θ δ)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def boostedDirection (e m : ℝ) (p : E) (φ : Angle → E) (y : Point) : E :=
  let v := hyperbolicMap e m p (y 0 • φ (angularProjection y))
  ‖v‖⁻¹ • v

structure GenuineBoostPatch (e : ℝ) (p : E) (he : ‖p‖ < e) (Q : CKSTensorPatch)
    (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  estimates : BoostPatchEstimates e p Q P θ δ R
  boundary_image : ∀ η ∈ Metric.ball θ δ,
    boundary e p he (P.chart.symm η) ∈ Q.patch.sphereRegion Q.region
  chart_image : ∀ y ∈ angularRadialTail R (Metric.ball θ δ),
    ∃ n : Sphere, n ∈ Q.patch.sphereRegion Q.region ∧
      (n:E)=boostedDirection e (mass e p) p P.param y
  genuine_tensor : ∀ y ∈ angularRadialTail R (Metric.ball θ δ),
    ∀ (A : I → I → Point → ℝ) (a b : I),
      lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension A a b y =
      coordinateTensorPullback (lorentzPolarChart e (mass e p) p P.param Q.patch.extension) A a b y
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice
attribute [local instance] real_continuousAdd

def spatialTensorPullback (F : E → E) (A : SpatialTensor) : SpatialTensor :=
  fun x => (A (F x)).bilinearComp (fderiv ℝ F x) (fderiv ℝ F x)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

structure SpatialBoostPatch (e : ℝ) (p : E) (he : ‖p‖ < e) (A B : SpatialTensor)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) (θ : Angle) (δ R : ℝ) : Prop where
  genuine : GenuineBoostPatch e p he Q P θ δ R
  old_tail : MapsTo (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
    (angularRadialTail R (Metric.ball θ δ)) (angularRadialTail Q.radius Q.region)
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail R (Metric.ball θ δ))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A))
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
  second_CKS : SourceCKSComponents 2 5 (angularRadialTail R (Metric.ball θ δ))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B))
    (fun _ => 0) (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceRemainderOn.mono {j q : ℕ} {U V : Set Point} {f : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hUV : U ⊆ V) : SourceRemainderOn j q U f := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact ⟨fun y hy => hf.regular y (hUV hy),B,hB,fun y hy => hb y (hUV hy)⟩

@[simp] lemma angularProjection_radialLogChart (y : Point) :
    angularProjection (radialLogChart y) = angularProjection y := by
  ext a
  simp [angularProjection,radialLogChart]

lemma slice_mem_closedBall {θ η : Angle} {δ : ℝ} (hδ : 0 ≤ δ)
    (hη : η ∈ Metric.closedBall θ δ) : slice 0 η ∈ Metric.closedBall (slice 0 θ) δ := by
  apply (dist_pi_le_iff hδ).2
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [slice_zero,dist_self] using hδ
  · simpa only [slice_succ] using (dist_pi_le_iff hδ).1 hη a

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceCKSComponents.mono {j q : ℕ} {U V : Set Point}
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j q V A mr mg) (hUV : U ⊆ V) :
    SourceCKSComponents j q U A mr mg :=
  ⟨hA.radial.mono hUV,fun i k hik => (hA.mixed i k hik).mono hUV,
    fun i k hi hk => (hA.angular i k hi hk).mono hUV⟩

lemma angularRadialTail_subset_log (L : ℝ) (θ : Angle) (δ : ℝ) :
    angularRadialTail (Real.exp L) (Metric.ball θ δ) ⊆ logRadiusChart '' angularLogTail L θ δ := by
  intro y hy
  have hp : 0 < y 0 := (Real.exp_pos L).trans hy.1
  refine ⟨radialLogChart y,⟨?_,?_⟩,logRadiusChart_radialLogChart hp⟩
  · change L ≤ Real.log (y 0)
    exact ((Real.lt_log_iff_exp_lt hp).2 hy.1).le
  · simpa only [angularProjection_radialLogChart] using hy.2

lemma BoostPatchEstimates.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {Q : CKSTensorPatch}
    {P : SmoothAngularPatch} {θ : Angle}
    (h : BoostPatchEstimates e p Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    BoostPatchEstimates e p Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.radius_pos.trans_le hR,h.ball_pos,h.ball_target,h.metric_CKS.mono hs,
    h.second_CKS.mono hs,h.radial_smooth,h.angular_smooth,h.second_smooth⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem exists_boostPatchEstimates {e : ℝ} {p : E} (he : ‖p‖ < e)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) {n : Sphere}
    (hn : n ∈ P.chart.source)
    (hQ : boundary e p he n ∈ Q.patch.sphereRegion Q.region) :
    ∃ δ R : ℝ, BoostPatchEstimates e p Q P (P.chart n) δ R := by
  let θ := P.chart n
  have hθ : θ ∈ P.chart.target := P.chart.map_source hn
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ Q.patch.domain := by
    rw [P.param_chart hn]
    exact Q.patch.source_domain _ hQ.1
  have hw : boundaryChart e (mass e p) p P.param Q.patch.extension θ ∈ Q.region := by
    change Q.patch.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.region
    rw [P.param_chart hn]
    rw [show boundaryAmbient e (mass e p) p (n:E) = (boundary e p he n : E) from rfl]
    rw [Q.patch.extension_eq _ hQ.1]
    exact hQ.2
  obtain ⟨δ,hδ,L,hL,hd,ha,ho⟩ := exists_lorentzChartDomain_regular he (mass_pos he) (mass_sq he)
    P.param Q.patch.extension P.chart.open_target hθ P.param_smooth
    (fun η hη => P.param_sphere η) Q.patch.isOpen_domain Q.patch.extension_smooth hb
    Q.open_region hw Q.radius
  have hs {η : Angle} (hη : η ∈ Metric.ball θ (δ/2)) :
      slice 0 η ∈ Metric.closedBall (slice 0 θ) δ := by
    apply slice_mem_closedBall hδ.le
    exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hη).le.trans (half_le_self hδ.le))
  have hm := lorentz_metric_CKS e (mass e p) p P.param Q.patch.extension hd Q.metric_CKS
    (fun z hz => Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho hz)))
    (fun i k hi hk z hz => (Q.mg_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  have hk := lorentz_second_CKS e (mass e p) p P.param Q.patch.extension hd Q.second_CKS
    (fun i k hi hk z hz => (Q.mK_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  refine ⟨δ/2,Real.exp L,⟨Real.exp_pos L,half_pos hδ,?_,
    hm.mono (angularRadialTail_subset_log L θ (δ/2)),
    hk.mono (angularRadialTail_subset_log L θ (δ/2)),?_,?_,?_⟩⟩
  · intro η hη
    simpa only [angularProjection_slice] using ha (hs hη)
  · intro η hη
    apply ContDiffAt.contDiffWithinAt
    apply lorentzRadialLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
    · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
    · exact hd.region _ (hs hη)
    · exact hd.chartInv _ (hs hη)
    · exact Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
  · intro i k η hη
    apply ContDiffAt.contDiffWithinAt
    apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
    · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
    · exact hd.region _ (hs hη)
    · exact hd.chartInv _ (hs hη)
    · intro a b ha hb
      exact (Q.mg_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
  · intro i k η hη
    apply ContDiffAt.contDiffWithinAt
    apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
    · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
    · exact hd.region _ (hs hη)
    · exact hd.chartInv _ (hs hη)
    · intro a b ha hb
      exact (Q.mK_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem exists_finite_boost_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ) (R : ℝ),
      0 < R ∧
      (∀ n ∈ s, BoostPatchEstimates e p (old (boundary e p he n)) (P n) ((P n).chart n) (δ n) R) ∧
      ∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n)) := by
  classical
  choose P hP using exists_smoothAngularPatch
  choose δ R hR using fun n => exists_boostPatchEstimates he
    (old (boundary e p he n)) (P n) (hP n) (hold (boundary e p he n))
  let U (n : Sphere) := (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n))
  have hU n : IsOpen (U n) := (P n).sphereRegion_open Metric.isOpen_ball
  have hn n : n ∈ U n := ⟨hP n,Metric.mem_ball_self (hR n).ball_pos⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (show univ ⊆ ⋃ n, U n from fun n _ => mem_iUnion.2 ⟨n,hn n⟩)
  have hsum : 0 ≤ ∑ n ∈ s, R n := Finset.sum_nonneg (fun n _ => (hR n).radius_pos.le)
  refine ⟨s,P,δ,1+∑ n ∈ s, R n,by linarith,?_,?_⟩
  · intro n hn
    apply (hR n).mono_radius
    have hle : R n ≤ ∑ m ∈ s, R m :=
      Finset.single_le_sum (fun m _ => (hR m).radius_pos.le) hn
    linarith
  · intro q
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hs (mem_univ q))
    obtain ⟨hns,hqn⟩ := mem_iUnion.mp hn
    exact ⟨n,hns,hqn⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
def angularJacobian (Φ : Angle → Angle) (θ : Angle) : AngularMatrix := fun a i =>
  D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma extension_param (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    P.extension (P.param θ)=θ := by
  rw [show P.param θ=(P.chart.symm θ:E) from rfl,
    P.extension_eq _ (P.chart.map_target hθ)]
  exact P.chart.right_inv hθ

lemma extension_contDiffAt_param (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : ContDiffAt ℝ ∞ P.extension (P.param θ) := by
  exact P.extension_smooth.contDiffAt (P.isOpen_domain.mem_nhds
    (P.source_domain _ (P.chart.map_target hθ)))

lemma param_fderiv_leftInverse (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) :
    (fderiv ℝ P.extension (P.param θ)).comp (fderiv ℝ P.param θ) =
      ContinuousLinearMap.id ℝ Angle := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hψ := (P.extension_contDiffAt_param hθ).differentiableAt (by simp)
  have hg : (fun η => P.extension (P.param η)) =ᶠ[𝓝 θ] id := by
    filter_upwards [P.chart.open_target.mem_nhds hθ] with η hη
    exact P.extension_param hη
  have ht := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (P.extension ∘ P.param) θ = fderiv ℝ id θ at ht
  rw [fderiv_comp θ hψ hφ,fderiv_id] at ht
  exact ht

lemma param_fderiv_injective (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : Function.Injective (fderiv ℝ P.param θ) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ P.extension (P.param θ)) hvw
  have hl := P.param_fderiv_leftInverse hθ
  have hv := congrArg (fun L : Angle →L[ℝ] Angle => L v) hl
  have hw := congrArg (fun L : Angle →L[ℝ] Angle => L w) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    hv.symm.trans (h.trans hw)

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

lemma roundMetric_posDef (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    (angularRoundMetric P.param θ).PosDef := by
  change (Matrix.gram ℝ (fun a => fderiv ℝ P.param θ (CKSAngularGeometry.basis a))).PosDef
  apply Matrix.posDef_gram_iff_linearIndependent.mpr
  have h := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map'
    (fderiv ℝ P.param θ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.param_fderiv_injective hθ))
  simpa only [Function.comp_def,Pi.basisFun_apply,CKSAngularGeometry.basis,
    ContinuousLinearMap.coe_coe] using h

end SmoothAngularPatch

lemma angular_vector_expansion (v : Angle) :
    ∑ a : Fin 2, v a • CKSAngularGeometry.basis a = v := by
  funext i
  fin_cases i <;> simp [CKSAngularGeometry.basis,Pi.single_apply]

lemma angularJacobian_apply {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a : Fin 2) :
    fderiv ℝ Φ θ (CKSAngularGeometry.basis a) =
      ∑ i : Fin 2, angularJacobian Φ θ a i • CKSAngularGeometry.basis i := by
  conv_lhs => rw [← angular_vector_expansion (fderiv ℝ Φ θ (CKSAngularGeometry.basis a))]
  congr 1; funext i
  congr 1
  simp only [angularJacobian,D,fderiv_apply hΦ,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped Topology ContDiff
lemma polarParam_contDiffAt (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) : ContDiffAt ℝ ∞ (polarParam P) y := by
  exact (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).contDiff.contDiffAt.smul
    ((P.param_contDiffAt hy).comp y angularProjection.contDiff.contDiffAt)
lemma polarParam_norm (P : SmoothAngularPatch) {y : Point} (hy : 0 ≤ y 0) :
    ‖polarParam P y‖ = y 0 := by
  have hn : ‖P.param (angularProjection y)‖=1 := P.param_norm (angularProjection y)
  simp only [polarParam,norm_smul,Real.norm_eq_abs,abs_of_nonneg hy,hn,mul_one]
lemma fderiv_coordinate_expansion {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (a : I) :
    fderiv ℝ F y (basis a) = ∑ i, D (basis a) (fun z => F z i) y • basis i := by
  conv_lhs => rw [← sum_coordinate_basis (fderiv ℝ F y (basis a))]
  congr 1; funext i
  congr 1
  simp only [D,fderiv_apply hF,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
lemma coordinateTensorPullback_polar {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (Q : SmoothAngularPatch) (A : SpatialTensor) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      A (polarParam Q (F y))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis a)))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis b))) := by
  rw [fderiv_coordinate_expansion hF a,fderiv_coordinate_expansion hF b]
  simp only [map_sum,map_smul,_root_.sum_apply,smul_apply,
    smul_eq_mul,Finset.mul_sum,coordinateTensorPullback,polarTensorComponents]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma polarTensor_covariance {F : Point → Point} {H : E → E} {y : Point}
    (P Q : SmoothAngularPatch) (A : SpatialTensor)
    (hF : DifferentiableAt ℝ F y)
    (hP : DifferentiableAt ℝ (polarParam P) y)
    (hQ : DifferentiableAt ℝ (polarParam Q) (F y))
    (hH : DifferentiableAt ℝ H (polarParam P y))
    (he : (polarParam Q ∘ F) =ᶠ[𝓝 y] (H ∘ polarParam P)) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      polarTensorComponents P (spatialTensorPullback H A) a b y := by
  have hp : polarParam Q (F y)=H (polarParam P y) := he.eq_of_nhds
  have hd := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp y hQ hF,fderiv_comp y hH hP] at hd
  have ha := congrArg (fun L : Point →L[ℝ] E => L (basis a)) hd
  have hb := congrArg (fun L : Point →L[ℝ] E => L (basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [coordinateTensorPullback_polar hF Q A a b,hp,ha,hb]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Set

lemma homeomorph_full_tail (H : E ≃ₜ E) (r : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, R < ‖x‖ → r < ‖H x‖ := by
  have hc : IsCompact (H ⁻¹' Metric.closedBall 0 r) :=
    H.isCompact_preimage.mpr (isCompact_closedBall 0 r)
  obtain ⟨C,hC⟩ := isBounded_iff_forall_norm_le.mp hc.isBounded
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  by_contra hn
  have hm : x ∈ H ⁻¹' Metric.closedBall 0 r := by
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using le_of_not_gt hn
  exact (not_le_of_gt hx) ((hC x hm).trans (le_max_right _ _))

theorem hyperbolic_boost_full_tails {e : ℝ} {p : E} (he : ‖p‖ < e) (r : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, R < ‖x‖ →
      r < ‖hyperbolicMap e (mass e p) p x‖ ∧
      r < ‖hyperbolicMap e (mass e p) (-p) x‖ := by
  obtain ⟨R₁,h₁,q₁⟩ := homeomorph_full_tail (hyperbolicHomeomorph e p he) r
  obtain ⟨R₂,h₂,q₂⟩ := homeomorph_full_tail (hyperbolicHomeomorph e p he).symm r
  refine ⟨max R₁ R₂,h₁.trans_le (le_max_left _ _),?_⟩
  intro x hx
  exact ⟨q₁ x (lt_of_le_of_lt (le_max_left _ _) hx),
    q₂ x (lt_of_le_of_lt (le_max_right _ _) hx)⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma angularRadialTail_open (R : ℝ) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (angularRadialTail R W) := by
  exact (isOpen_Ioi.preimage (continuous_apply 0)).inter
    (hW.preimage angularProjection.continuous)

lemma GenuineBoostPatch.spatial_nonzero {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    hyperbolicMap e (mass e p) p (polarParam P y) ≠ 0 := by
  obtain ⟨n,_,hn⟩ := h.chart_image y hy
  intro hz
  change (n:E) = ‖hyperbolicMap e (mass e p) p (polarParam P y)‖⁻¹ •
    hyperbolicMap e (mass e p) p (polarParam P y) at hn
  have hn0 : (n:E)=0 := by simpa only [hz,norm_zero,inv_zero,zero_smul] using hn
  exact (ne_zero_of_mem_unit_sphere n) hn0

lemma GenuineBoostPatch.polar_commutes {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    polarParam Q.patch (lorentzPolarChart e (mass e p) p P.param Q.patch.extension y) =
      hyperbolicMap e (mass e p) p (polarParam P y) := by
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  simp only [polarParam,lorentzPolarChart,slice_zero,angularProjection_slice]
  change ‖hyperbolicMap e (mass e p) p (polarParam P y)‖ •
    Q.patch.param (Q.patch.extension (boostedDirection e (mass e p) p P.param y)) = _
  rw [← heq,Q.patch.extension_eq n hn.1,Q.patch.param_chart hn.1,heq]
  change ‖hyperbolicMap e (mass e p) p (polarParam P y)‖ •
    (‖hyperbolicMap e (mass e p) p (polarParam P y)‖⁻¹ •
      hyperbolicMap e (mass e p) p (polarParam P y)) = _
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (h.spatial_nonzero hy)),one_smul]
  rfl

lemma GenuineBoostPatch.old_angle {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    angularProjection (lorentzPolarChart e (mass e p) p P.param Q.patch.extension y) ∈ Q.region := by
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  simp only [lorentzPolarChart,angularProjection_slice]
  change Q.patch.extension (boostedDirection e (mass e p) p P.param y) ∈ Q.region
  rw [← heq,Q.patch.extension_eq n hn.1]
  exact hn.2

lemma GenuineBoostPatch.chart_contDiffAt {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ)) :
    ContDiffAt ℝ ∞ (lorentzPolarChart e (mass e p) p P.param Q.patch.extension) y := by
  have hP := polarParam_contDiffAt P (h.estimates.ball_target hy.2)
  have hv := (hyperbolicMap_smooth e (mass e p) p).contDiffAt.comp y hP
  have hnorm := hv.norm ℝ (h.spatial_nonzero hy)
  have hnormalize := (hnorm.inv (norm_ne_zero_iff.mpr (h.spatial_nonzero hy))).smul hv
  obtain ⟨n,hn,heq⟩ := h.chart_image y hy
  have hdom : boostedDirection e (mass e p) p P.param y ∈ Q.patch.domain := by
    rw [← heq]; exact Q.patch.source_domain n hn.1
  have hangle := (Q.patch.extension_smooth.contDiffAt (Q.patch.isOpen_domain.mem_nhds hdom)).comp y hnormalize
  change ContDiffAt ℝ ∞ (fun z => slice _ _) y
  have hsingle : ContDiffAt ℝ ∞ (fun z => (Pi.single (0:I)
      ‖hyperbolicMap e (mass e p) p (polarParam P z)‖ : Point)) y := by
    apply contDiffAt_pi.mpr
    intro i
    by_cases hi : i=0
    · subst i; simp only [Pi.single_eq_same]; exact hnorm
    · simpa only [Pi.single_eq_of_ne hi] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point => (0:ℝ)) y)
  exact hsingle.add (injection.contDiff.contDiffAt.comp y hangle)

lemma GenuineBoostPatch.tensor_components {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R)
    {y : Point} (hy : y ∈ angularRadialTail R (Metric.ball θ δ))
    (A : SpatialTensor) (a b : I) :
    coordinateTensorPullback (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
      (polarTensorComponents Q.patch A) a b y =
    polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) a b y := by
  apply polarTensor_covariance P Q.patch A
  · exact (h.chart_contDiffAt hy).differentiableAt (by simp)
  · exact (polarParam_contDiffAt P (h.estimates.ball_target hy.2)).differentiableAt (by simp)
  · exact (polarParam_contDiffAt Q.patch (Q.region_target (h.old_angle hy))).differentiableAt (by simp)
  · exact (hyperbolicMap_smooth e (mass e p) p).differentiable (by simp) |>.differentiableAt
  · filter_upwards [(angularRadialTail_open R Metric.isOpen_ball).mem_nhds hy] with z hz
    exact h.polar_commutes hz
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped ContDiff Topology
lemma scaledIter_congr_germ {f g : Point → ℝ} {y : Point} (h : f =ᶠ[𝓝 y] g)
    (l : List I) : scaledIter l f =ᶠ[𝓝 y] scaledIter l g := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    filter_upwards [ih.fderiv (𝕜:=ℝ)] with z hz
    exact congrArg (fun L : Point →L[ℝ] ℝ => radialFactor a z * L (basis a)) hz
lemma SourceRemainderOn.congrOn {j q : ℕ} {V : Set Point} {f g : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hV : IsOpen V) (he : EqOn f g V) :
    SourceRemainderOn j q V g := by
  have hg {y} (hy : y ∈ V) : f =ᶠ[𝓝 y] g := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact he hz
  refine ⟨fun y hy => (hf.regular y hy).congr_of_eventuallyEq (hg hy).symm,?_⟩
  obtain ⟨B,hB,hb⟩ := hf.bound
  refine ⟨B,hB,?_⟩
  intro y hy l hl
  rw [← (scaledIter_congr_germ (hg hy) l).eq_of_nhds]
  exact hb y hy l hl
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set
lemma SourceCKSComponents.congrOn {j q : ℕ} {V : Set Point}
    {A B : I → I → Point → ℝ} {mr : Angle → ℝ}
    {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j q V A mr mg) (hV : IsOpen V)
    (he : ∀ i k, EqOn (A i k) (B i k) V) : SourceCKSComponents j q V B mr mg := by
  refine ⟨hA.radial.congrOn hV (fun y hy => by dsimp only; rw [he 0 0 hy]),?_,?_⟩
  · intro i k hik
    exact (hA.mixed i k hik).congrOn hV (he i k)
  · intro i k hi hk
    exact (hA.angular i k hi hk).congrOn hV (fun y hy => by dsimp only; rw [he i k hy])
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

theorem exists_lorentzChartDomain_image {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    {A W : Set Angle} {B : Set E}
    (hA : IsOpen A) (hθ : θ ∈ A) (hφ : ContDiffOn ℝ ∞ φ A)
    (hn : ∀ η ∈ A, φ η ∈ Metric.sphere (0:E) 1)
    (hB : IsOpen B) (hψ : ContDiffOn ℝ ∞ ψ B)
    (hb : boundaryAmbient e m p (φ θ) ∈ B)
    (hW : IsOpen W) (hw : boundaryChart e m p φ ψ θ ∈ W) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      LorentzChartDomain e m p φ ψ (Metric.closedBall (slice 0 θ) δ)
        (angularLogTail L θ (δ/2)) (angularRadialTail R W) ∧
      MapsTo angularProjection (Metric.closedBall (slice 0 θ) δ) A ∧
      MapsTo (fun z => angularProjection (compactLorentzCoefficients e m p φ ψ z))
        (Metric.closedBall (slice 0 θ) δ) W ∧
      MapsTo (fun z => compactAngle e m p (compactPolar φ z))
        (Metric.closedBall (slice 0 θ) δ) B := by
  let z₀ : Point := slice 0 θ
  have hφ₀ := hφ.contDiffAt (hA.mem_nhds hθ)
  have hp : ContDiffAt ℝ ∞ (compactPolar φ) z₀ := by
    apply compactPolar_contDiffAt
    simpa only [z₀,angularProjection_slice] using hφ₀
  have hz₀ : compactPolar φ z₀ ∈ compactRegion e m p := by
    simpa only [z₀,compactPolar_slice] using compactRegion_boundary he hm0 hm (hn θ hθ)
  have hb₀ : compactAngle e m p (compactPolar φ z₀) ∈ B := by
    simpa only [z₀,compactPolar_slice,compactAngle_boundary he hm0 hm (hn θ hθ)] using hb
  have hψ₀ := hψ.contDiffAt (hB.mem_nhds hb₀)
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z₀ := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [z₀,angularProjection_slice] using hφ₀
    · exact hz₀
    · exact hψ₀
  have hw₀ : angularProjection (compactLorentzCoefficients e m p φ ψ z₀) ∈ W := by
    simpa only [z₀,compactLorentzCoefficients_boundary he hm0 hm φ ψ (hn θ hθ),
      angularProjection_slice] using hw
  let d : ℝ := denominator e m p (φ θ)/2
  have hd : 0 < d := half_pos (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have hds : d < compactScale e m p (compactPolar φ z₀) := by
    rw [show z₀ = slice 0 θ from rfl,compactPolar_slice,compactScale_boundary he hm0 hm (hn θ hθ)]
    exact half_lt_self (denominator_pos he hm0 ⟨φ θ,hn θ hθ⟩)
  have ha : ∀ᶠ z : Point in 𝓝 z₀, angularProjection z ∈ A :=
    angularProjection.continuous.continuousAt.preimage_mem_nhds
      (hA.mem_nhds (by simpa only [z₀,angularProjection_slice] using hθ))
  have hr : ∀ᶠ z : Point in 𝓝 z₀, compactPolar φ z ∈ compactRegion e m p :=
    hp.continuousAt.preimage_mem_nhds ((compactRegion_open e m p).mem_nhds hz₀)
  have hb' : ∀ᶠ z : Point in 𝓝 z₀, compactAngle e m p (compactPolar φ z) ∈ B :=
    ((compactAngle_contDiffAt e m p hz₀).comp z₀ hp).continuousAt.preimage_mem_nhds
      (hB.mem_nhds hb₀)
  have hw' : ∀ᶠ z : Point in 𝓝 z₀,
      angularProjection (compactLorentzCoefficients e m p φ ψ z) ∈ W :=
    (angularProjection.contDiff.contDiffAt.comp z₀ hc).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hw₀)
  have hs : ∀ᶠ z : Point in 𝓝 z₀, d < compactScale e m p (compactPolar φ z) :=
    ((compactScale_smooth_region e m p hz₀).comp z₀ hp).continuousAt
      (lt_mem_nhds hds)
  obtain ⟨ρ,hρ,hsub⟩ := Metric.mem_nhds_iff.1 (ha.and (hr.and (hb'.and (hw'.and hs))))
  let δ : ℝ := ρ/2
  have hδ : 0 < δ := half_pos hρ
  have hδρ : δ < ρ := half_lt_self hρ
  have hK z (hz : z ∈ Metric.closedBall z₀ δ) :=
    hsub (Metric.closedBall_subset_ball hδρ hz)
  obtain ⟨L,hL,hLt⟩ := eventually_full_log_tail (half_pos hδ) hd R
  have hnew {x : Point} (hx : x ∈ angularLogTail L θ (δ/2)) :
      inverseLogRadiusChart x ∈ Metric.closedBall z₀ δ := by
    apply inverseLogRadius_mem_closedBall hδ
    · exact ((hLt (x 0) hx.1).1).trans (half_le_self hδ.le)
    · exact ((Metric.mem_ball.mp hx.2).le).trans (half_le_self hδ.le)
  refine ⟨δ,hδ,L,hL,?_,fun z hz => (hK z hz).1,fun z hz => (hK z hz).2.2.2.1,
    fun z hz => (hK z hz).2.2.1⟩
  refine ⟨isCompact_closedBall _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact hφ.contDiffAt (hA.mem_nhds (hK z hz).1)
  · intro z hz
    exact (hK z hz).2.1
  · intro z hz
    exact hψ.contDiffAt (hB.mem_nhds (hK z hz).2.2.1)
  · intro z hz
    exact (convex_closedBall z₀ δ).segment_subset (boundaryProjection_closedBall hδ.le hz) hz
  · intro x hx
    exact hnew hx
  · intro x hx
    have hk := hK _ (hnew hx)
    refine ⟨?_,?_⟩
    · change R < Real.exp ((logLorentzChart e m p φ ψ x) 0)
      rw [logLorentzChart_radial_exp e m p φ ψ hk.2.1.2]
      exact ((hLt (x 0) hx.1).2).trans_le
        (mul_le_mul_of_nonneg_left hk.2.2.2.2.le (Real.exp_pos _).le)
    · simpa only [angularProjection_logRadiusChart,logLorentzChart_angular_coeff] using hk.2.2.2.1
  · intro x hx
    exact hL.trans hx.1

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Topology ContDiff
lemma SmoothAngularPatch.exists_exact_domain (P : SmoothAngularPatch) :
    ∃ B : Set E, IsOpen B ∧ B ⊆ P.domain ∧
      ∀ n : Sphere, (n:E) ∈ B ↔ n ∈ P.chart.source := by
  obtain ⟨V,hV,hPV⟩ := isOpen_induced_iff.mp P.chart.open_source
  refine ⟨P.domain ∩ V,P.isOpen_domain.inter hV,inter_subset_left,?_⟩
  intro n
  have hv : (n:E) ∈ V ↔ n ∈ P.chart.source := by rw [← hPV]; rfl
  exact ⟨fun h => hv.mp h.2,fun h => ⟨P.source_domain n h,hv.mpr h⟩⟩

lemma compactAngle_sphere (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : compactAngle e m p z ∈ Metric.sphere (0:E) 1 := by
  simp only [Metric.mem_sphere,dist_zero_right,compactAngle,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hz.2)]
  exact inv_mul_cancel₀ hz.2.ne'

lemma boostedDirection_log (e m : ℝ) (p : E) (P : SmoothAngularPatch) {x : Point}
    (_hz : compactPolar P.param (inverseLogRadiusChart x) ∈ compactRegion e m p) :
    boostedDirection e m p P.param (logRadiusChart x) =
      compactAngle e m p (compactPolar P.param (inverseLogRadiusChart x)) := by
  have ht := hyperbolicMap_polar (e:=e) (m:=m) (p:=p) (Real.exp_pos (x 0))
    (P.chart.symm (angularProjection x))
  change hyperbolicMap e m p (Real.exp (x 0) • P.param (angularProjection x)) =
    Real.exp (x 0) • compactSpatial e m p
      ((Real.exp (x 0))⁻¹, P.param (angularProjection x)) at ht
  simp only [boostedDirection,angularProjection_logRadiusChart,show logRadiusChart x 0=Real.exp (x 0) from rfl]
  rw [ht,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos (x 0)),smul_smul,mul_inv_rev]
  simp only [mul_assoc,inv_mul_cancel₀ (Real.exp_ne_zero (x 0)),mul_one]
  change (compactScale e m p ((Real.exp (x 0))⁻¹,P.param (angularProjection x)))⁻¹ •
    compactSpatial e m p ((Real.exp (x 0))⁻¹,P.param (angularProjection x)) = _
  rw [← Real.exp_neg]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

theorem exists_genuineBoostPatch {e : ℝ} {p : E} (he : ‖p‖ < e)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) {n : Sphere}
    (hn : n ∈ P.chart.source)
    (hQ : boundary e p he n ∈ Q.patch.sphereRegion Q.region) :
    ∃ δ R : ℝ, GenuineBoostPatch e p he Q P (P.chart n) δ R := by
  let θ := P.chart n
  have hθ : θ ∈ P.chart.target := P.chart.map_source hn
  obtain ⟨B,hB,hQB,hBS⟩ := Q.patch.exists_exact_domain
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ B := by
    rw [P.param_chart hn]
    exact (hBS _).mpr hQ.1
  have hw : boundaryChart e (mass e p) p P.param Q.patch.extension θ ∈ Q.region := by
    change Q.patch.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.region
    rw [P.param_chart hn]
    rw [show boundaryAmbient e (mass e p) p (n:E) = (boundary e p he n : E) from rfl]
    rw [Q.patch.extension_eq _ hQ.1]
    exact hQ.2
  obtain ⟨δ,hδ,L,hL,hd,ha,ho,hi⟩ := exists_lorentzChartDomain_image he (mass_pos he) (mass_sq he)
    P.param Q.patch.extension P.chart.open_target hθ P.param_smooth
    (fun η hη => P.param_sphere η) hB (Q.patch.extension_smooth.mono hQB) hb
    Q.open_region hw Q.radius
  have hs {η : Angle} (hη : η ∈ Metric.ball θ (δ/2)) :
      slice 0 η ∈ Metric.closedBall (slice 0 θ) δ := by
    apply slice_mem_closedBall hδ.le
    exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hη).le.trans (half_le_self hδ.le))
  have hm := lorentz_metric_CKS e (mass e p) p P.param Q.patch.extension hd Q.metric_CKS
    (fun z hz => Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho hz)))
    (fun i k hi hk z hz => (Q.mg_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  have hk := lorentz_second_CKS e (mass e p) p P.param Q.patch.extension hd Q.second_CKS
    (fun i k hi hk z hz => (Q.mK_smooth i k hi hk).contDiffAt
      (Q.open_region.mem_nhds (ho hz)))
  have hest : BoostPatchEstimates e p Q P (P.chart n) (δ/2) (Real.exp L) := by
    refine ⟨Real.exp_pos L,half_pos hδ,?_,
      hm.mono (angularRadialTail_subset_log L θ (δ/2)),
      hk.mono (angularRadialTail_subset_log L θ (δ/2)),?_,?_,?_⟩
    · intro η hη
      simpa only [angularProjection_slice] using ha (hs hη)
    · intro η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzRadialLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · exact Q.mr_smooth.contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
    · intro i k η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · intro a b ha hb
        exact (Q.mg_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
    · intro i k η hη
      apply ContDiffAt.contDiffWithinAt
      apply lorentzAngularLeading_contDiffAt e (mass e p) p P.param Q.patch.extension
      · simpa only [angularProjection_slice] using hd.chart _ (hs hη)
      · exact hd.region _ (hs hη)
      · exact hd.chartInv _ (hs hη)
      · intro a b ha hb
        exact (Q.mK_smooth a b ha hb).contDiffAt (Q.open_region.mem_nhds (ho (hs hη)))
  refine ⟨δ/2,Real.exp L,⟨hest,?_,?_,?_⟩⟩
  · intro η hη
    have hsrc : boundary e p he (P.chart.symm η) ∈ Q.patch.chart.source := by
      apply (hBS _).mp
      have ht := hi (hs hη)
      change boundaryAmbient e (mass e p) p (P.param η) ∈ B
      simpa only [compactPolar_slice,compactAngle_boundary he (mass_pos he) (mass_sq he)
        (P.param_sphere η)] using ht
    refine ⟨hsrc,?_⟩
    have ht := ho (hs hη)
    change angularProjection (compactLorentzCoefficients e (mass e p) p P.param
      Q.patch.extension (slice 0 η)) ∈ Q.region at ht
    rw [compactLorentzCoefficients_boundary he (mass_pos he) (mass_sq he) P.param
      Q.patch.extension (P.param_sphere η),angularProjection_slice] at ht
    change Q.patch.chart (boundary e p he (P.chart.symm η)) ∈ Q.region
    rw [← Q.patch.extension_eq _ hsrc]
    exact ht
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := angularRadialTail_subset_log L θ (δ/2) hy
    have hz := hd.newRegion hx
    let n' : Sphere := ⟨compactAngle e (mass e p) p (compactPolar P.param (inverseLogRadiusChart x)),
      compactAngle_sphere e (mass e p) p (hd.region _ hz)⟩
    have hn' : n' ∈ Q.patch.chart.source := (hBS _).mp (hi hz)
    refine ⟨n',⟨hn',?_⟩,(boostedDirection_log e (mass e p) p P (hd.region _ hz)).symm⟩
    change Q.patch.chart n' ∈ Q.region
    rw [← Q.patch.extension_eq _ hn']
    simpa only [compactLorentzCoefficients,angularProjection_slice,n'] using ho hz
  · intro y hy A a b
    obtain ⟨x,hx,rfl⟩ := angularRadialTail_subset_log L θ (δ/2) hy
    have hz := hd.newRegion hx
    exact lorentzOrdinaryTensor_eq_pullback e (mass e p) p P.param Q.patch.extension
      (Filter.Eventually.of_forall P.param_sphere) (hd.chart _ hz) (hd.region _ hz) (hd.chartInv _ hz) A a b

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma GenuineBoostPatch.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    GenuineBoostPatch e p he Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.estimates.mono_radius hR,h.boundary_image,
    fun y hy => h.chart_image y (hs hy),fun y hy => h.genuine_tensor y (hs hy)⟩

theorem exists_finite_genuine_boost_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ) (R : ℝ),
      0 < R ∧
      (∀ n ∈ s, GenuineBoostPatch e p he (old (boundary e p he n)) (P n) ((P n).chart n) (δ n) R) ∧
      ∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n)) := by
  classical
  choose P hP using exists_smoothAngularPatch
  choose δ R hR using fun n => exists_genuineBoostPatch he
    (old (boundary e p he n)) (P n) (hP n) (hold (boundary e p he n))
  let U (n : Sphere) := (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n))
  have hU n : IsOpen (U n) := (P n).sphereRegion_open Metric.isOpen_ball
  have hn n : n ∈ U n := ⟨hP n,Metric.mem_ball_self (hR n).estimates.ball_pos⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (show univ ⊆ ⋃ n, U n from fun n _ => mem_iUnion.2 ⟨n,hn n⟩)
  have hsum : 0 ≤ ∑ n ∈ s, R n := Finset.sum_nonneg (fun n _ => (hR n).estimates.radius_pos.le)
  refine ⟨s,P,δ,1+∑ n ∈ s, R n,by linarith,?_,?_⟩
  · intro n hn
    apply (hR n).mono_radius
    have hle : R n ≤ ∑ m ∈ s, R m :=
      Finset.single_le_sum (fun m _ => (hR m).estimates.radius_pos.le) hn
    linarith
  · intro q
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hs (mem_univ q))
    obtain ⟨hns,hqn⟩ := mem_iUnion.mp hn
    exact ⟨n,hns,hqn⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology
lemma GenuineBoostPatch.toSpatial {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : GenuineBoostPatch e p he Q P θ δ R) (A B : SpatialTensor)
    (hr : Q.Realizes A B)
    (htail : MapsTo (lorentzPolarChart e (mass e p) p P.param Q.patch.extension)
      (angularRadialTail R (Metric.ball θ δ)) (angularRadialTail Q.radius Q.region)) :
    SpatialBoostPatch e p he A B Q P θ δ R := by
  have hm (a b : I) : EqOn
      (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.metric a b)
      (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) a b)
      (angularRadialTail R (Metric.ball θ δ)) := by
    intro y hy
    rw [h.genuine_tensor y hy]
    rw [← h.tensor_components hy A a b]
    unfold coordinateTensorPullback
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hr _ (htail hy) i k).1]
  have hk (a b : I) : EqOn
      (lorentzOrdinaryTensor e (mass e p) p P.param Q.patch.extension Q.second a b)
      (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) a b)
      (angularRadialTail R (Metric.ball θ δ)) := by
    intro y hy
    rw [h.genuine_tensor y hy]
    rw [← h.tensor_components hy B a b]
    unfold coordinateTensorPullback
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hr _ (htail hy) i k).2]
  exact ⟨h,htail,h.estimates.metric_CKS.congrOn (angularRadialTail_open R Metric.isOpen_ball) hm,
    h.estimates.second_CKS.congrOn (angularRadialTail_open R Metric.isOpen_ball) hk⟩

theorem exists_spatialBoostPatch {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (Q : CKSTensorPatch) (hr : Q.Realizes A B)
    (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source)
    (hQ : boundary e p he n ∈ Q.patch.sphereRegion Q.region) :
    ∃ δ R : ℝ, SpatialBoostPatch e p he A B Q P (P.chart n) δ R := by
  obtain ⟨δ,R,h⟩ := exists_genuineBoostPatch he Q P hn hQ
  obtain ⟨R₀,hR₀,hproper⟩ := hyperbolic_boost_full_tails he Q.radius
  have h' := h.mono_radius (le_max_left R R₀)
  refine ⟨δ,max R R₀,h'.toSpatial A B hr ?_⟩
  intro y hy
  refine ⟨?_,h'.old_angle hy⟩
  simp only [lorentzPolarChart,slice_zero]
  change Q.radius < ‖hyperbolicMap e (mass e p) p (polarParam P y)‖
  apply (hproper _ ?_).1
  rw [polarParam_norm P (h'.estimates.radius_pos.trans hy.1).le]
  exact lt_of_le_of_lt (le_max_right R R₀) hy.1

lemma SpatialBoostPatch.mono_radius {e R₁ R₂ δ : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle} {A B : SpatialTensor}
    (h : SpatialBoostPatch e p he A B Q P θ δ R₁) (hR : R₁ ≤ R₂) :
    SpatialBoostPatch e p he A B Q P θ δ R₂ := by
  have hs : angularRadialTail R₂ (Metric.ball θ δ) ⊆ angularRadialTail R₁ (Metric.ball θ δ) :=
    fun y hy => ⟨hR.trans_lt hy.1,hy.2⟩
  exact ⟨h.genuine.mono_radius hR,fun y hy => h.old_tail (hs hy),
    h.metric_CKS.mono hs,h.second_CKS.mono hs⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology
theorem exists_precompact_spatial_boost_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ) (R : ℝ),
      0 < R ∧
      (∀ n ∈ s, SpatialBoostPatch e p he A B (old (boundary e p he n)) (P n) ((P n).chart n) (2*δ n) R) ∧
      ∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n)) := by
  classical
  choose P hP using exists_smoothAngularPatch
  choose δ R hR using fun n => exists_spatialBoostPatch he A B
    (old (boundary e p he n)) (hreal _) (P n) (hP n) (hold (boundary e p he n))
  let U (n : Sphere) := (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n/2))
  have hU n : IsOpen (U n) := (P n).sphereRegion_open Metric.isOpen_ball
  have hn n : n ∈ U n := ⟨hP n,Metric.mem_ball_self (half_pos (hR n).genuine.estimates.ball_pos)⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (show univ ⊆ ⋃ n, U n from fun n _ => mem_iUnion.2 ⟨n,hn n⟩)
  have hsum : 0 ≤ ∑ n ∈ s, R n := Finset.sum_nonneg (fun n _ => (hR n).genuine.estimates.radius_pos.le)
  refine ⟨s,P,(fun n => δ n/2),1+∑ n ∈ s, R n,by linarith,?_,?_⟩
  · intro n hn
    have hh : 2 * (δ n / 2) = δ n := by ring
    rw [hh]
    apply (hR n).mono_radius
    have hle : R n ≤ ∑ m ∈ s, R m :=
      Finset.single_le_sum (fun m _ => (hR m).genuine.estimates.radius_pos.le) hn
    linarith
  · intro q
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hs (mem_univ q))
    obtain ⟨hns,hqn⟩ := mem_iUnion.mp hn
    exact ⟨n,hns,hqn⟩

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

def cksSourceFields (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) : SourceTensorFields where
  base := {
    sigma := σ
    mg := fun θ a b => mg a.succ b.succ θ
    mK := fun θ a b => mK a.succ b.succ θ
    mr := mr
    eg := fun y a b => A a.succ b.succ y-ordinaryLeadingComponent 1 (mg a.succ b.succ) y
    ek := fun y a b => B a.succ b.succ y-ordinaryLeadingComponent 1 (mK a.succ b.succ) y
    b := fun y a => A 0 a.succ y
    err := fun y => A 0 0 y-ordinaryLeadingComponent 5 mr y }
  kr := B 0 0
  kb := fun y a => B 0 a.succ y

def cksReference (σ : Angle → Mat) (y : Point) : AmbientMat :=
  metricBlock (1/(1+(y 0)^2)) 0 ((y 0)^2 • σ (angularProjection y))
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set
lemma ScaledComponentBound.mono {f : Point → ℝ} {j j' q : ℕ} {B C : ℝ} {y : Point}
    (h : ScaledComponentBound f j q B y) (hy : 0 ≤ y 0) (hj : j' ≤ j) (hBC : B ≤ C) :
    ScaledComponentBound f j' q C y := by
  intro l hl
  exact (h l (hl.trans hj)).trans (div_le_div_of_nonneg_right hBC (pow_nonneg hy q))
lemma finite_sourceRemainder_bound {ι : Type*} [Fintype ι] {j q : ℕ} {V : Set Point}
    (hV : ∀ y ∈ V, 0 ≤ y 0) {f : ι → Point → ℝ}
    (h : ∀ i, SourceRemainderOn j q V (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, y ∈ V → ScaledComponentBound (f i) j q C y := by
  classical
  choose B hB hb using fun i => (h i).bound
  refine ⟨∑ i, B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
  intro i y hy
  exact (hb i y hy).mono (hV y hy) le_rfl
    (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Set
open CKSAngularGeometry (metricBlock AmbientMat)

theorem cksSourceFields_bounds {V : Set Point} (hV : ∀ y ∈ V, 0 ≤ y 0)
    (σ : Angle → Mat) {A B : I → I → Point → ℝ} {mr : Angle → ℝ}
    {mg mK : I → I → Angle → ℝ}
    (hg : SourceCKSComponents 3 6 V A mr mg)
    (hk : SourceCKSComponents 2 5 V B (fun _ => 0) mK) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ V, (cksSourceFields σ A B mr mg mK).ComponentBounds C y := by
  obtain ⟨Ceg,heg,beg⟩ := finite_sourceRemainder_bound hV
    (fun ab : Fin 2 × Fin 2 => hg.angular ab.1.succ ab.2.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _))
  obtain ⟨Cek,hek,bek⟩ := finite_sourceRemainder_bound hV
    (fun ab : Fin 2 × Fin 2 => hk.angular ab.1.succ ab.2.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _))
  obtain ⟨Cbg,hbg,bbg⟩ := finite_sourceRemainder_bound hV
    (fun a : Fin 2 => hg.mixed 0 a.succ (Or.inl ⟨rfl,Fin.succ_ne_zero _⟩))
  obtain ⟨Cbk,hbk,bbk⟩ := finite_sourceRemainder_bound hV
    (fun a : Fin 2 => hk.mixed 0 a.succ (Or.inl ⟨rfl,Fin.succ_ne_zero _⟩))
  obtain ⟨Crg,hrg,brg⟩ := hg.radial.bound
  have hkr : SourceRemainderOn 2 5 V (B 0 0) := by
    simpa only [ordinaryLeadingComponent,mul_zero,sub_zero] using hk.radial
  obtain ⟨Crk,hrk,brk⟩ := hkr.bound
  let C := Ceg+Cek+Cbg+Cbk+Crg+Crk
  have h1 : Ceg ≤ C := by dsimp [C]; linarith
  have h2 : Cek ≤ C := by dsimp [C]; linarith
  have h3 : Cbg ≤ C := by dsimp [C]; linarith
  have h4 : Cbk ≤ C := by dsimp [C]; linarith
  have h5 : Crg ≤ C := by dsimp [C]; linarith
  have h6 : Crk ≤ C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro y hy
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · intro a b
    exact (beg (a,b) y hy).mono (hV y hy) le_rfl h1
  · intro a b
    exact (bek (a,b) y hy).mono (hV y hy) le_rfl h2
  · intro a
    exact (bbg a y hy).mono (hV y hy) le_rfl h3
  · exact (brg y hy).mono (hV y hy) (by decide) h5
  · exact (brk y hy).mono (hV y hy) le_rfl h6
  · intro a
    exact (bbk a y hy).mono (hV y hy) le_rfl h4
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def boostSourceFields (e : ℝ) (p : E) (A B : SpatialTensor)
    (Q : CKSTensorPatch) (P : SmoothAngularPatch) : SourceTensorFields :=
  cksSourceFields (angularRoundMetric P.param)
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) A))
    (polarTensorComponents P (spatialTensorPullback (hyperbolicMap e (mass e p) p) B))
    (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
    (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma D_translation_invariant (f : Point → ℝ) (a v : Point)
    (h : ∀ x, f (x+a)=f x) : ∀ x, D v f (x+a)=D v f x := by
  intro x
  unfold D
  rw [← fderiv_comp_add_right]
  congr 2
  exact funext h
lemma scalarJet_translation_invariant (f : Point → ℝ) (a : Point)
    (h : ∀ x, f (x+a)=f x) (x : Point) :
    actualScalarJet f (x+a)=actualScalarJet f x := by
  unfold actualScalarJet
  apply Prod.ext
  · exact h x
  · apply Prod.ext
    · funext i
      exact D_translation_invariant f a (basis i) h x
    · funext i j
      exact D_translation_invariant (D (basis j) f) a (basis i)
        (D_translation_invariant f a (basis j) h) x
lemma threeJet_translation_invariant (f : Point → ℝ) (a : Point)
    (h : ∀ x, f (x+a)=f x) (x : Point) :
    actualThreeJet f (x+a)=actualThreeJet f x := by
  unfold actualThreeJet
  apply Prod.ext
  · exact scalarJet_translation_invariant f a h x
  · funext i
    exact scalarJet_translation_invariant (D (basis i) f) a
      (D_translation_invariant f a (basis i) h) x
lemma angularLift_translate {F : Type*} (f : Angle → F) (ρ : ℝ) (x : Point) :
    angularLift f (x+ρ • basis 0)=angularLift f x := by
  simp [angularLift,map_add,map_smul,angularProjection_basis_zero]
lemma slice_add_radial (ρ : ℝ) (θ : Angle) : slice 0 θ+ρ • basis 0=slice ρ θ := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [slice,basis]
  · simp [slice,basis,Fin.succ_ne_zero]
lemma actualScalarJet_angularLift_slice (f : Angle → ℝ) (ρ : ℝ) (θ : Angle) :
    actualScalarJet (angularLift f) (slice ρ θ)=actualScalarJet (angularLift f) (slice 0 θ) := by
  rw [← slice_add_radial]
  exact scalarJet_translation_invariant _ _ (angularLift_translate f ρ) _
lemma actualThreeJet_angularLift_slice (f : Angle → ℝ) (ρ : ℝ) (θ : Angle) :
    actualThreeJet (angularLift f) (slice ρ θ)=actualThreeJet (angularLift f) (slice 0 θ) := by
  rw [← slice_add_radial]
  exact threeJet_translation_invariant _ _ (angularLift_translate f ρ) _
lemma matrixScalarJets_angularLift_slice (f : Angle → Mat) (ρ : ℝ) (θ : Angle) :
    matrixScalarJets (angularLift f) (slice ρ θ)=matrixScalarJets (angularLift f) (slice 0 θ) := by
  funext i j
  exact actualScalarJet_angularLift_slice (fun x => f x i j) ρ θ
lemma matrixThreeJets_angularLift_slice (f : Angle → Mat) (ρ : ℝ) (θ : Angle) :
    matrixThreeJets (angularLift f) (slice ρ θ)=matrixThreeJets (angularLift f) (slice 0 θ) := by
  funext i j
  exact actualThreeJet_angularLift_slice (fun x => f x i j) ρ θ
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice CKSCalculus
open scoped ContDiff Matrix.Norms.Elementwise
lemma angularProjection_slice_eq (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  funext a
  exact slice_succ r θ a
lemma actualScalarJet_continuousAt {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (actualScalarJet f) x := by
  apply ContinuousAt.prodMk hf.continuousAt
  apply ContinuousAt.prodMk
  · apply continuousAt_pi.mpr
    intro a
    exact (contDiffAt_D hf (m := 1) (by norm_num) (basis a)).continuousAt
  · apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    exact (contDiffAt_D (contDiffAt_D hf (m := 1) (by norm_num) (basis b))
      (m := 0) (by norm_num) (basis a)).continuousAt
lemma actualThreeJet_continuousAt {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContinuousAt (actualThreeJet f) x := by
  apply ContinuousAt.prodMk (actualScalarJet_continuousAt (hf.of_le (by norm_num)))
  apply continuousAt_pi.mpr
  intro a
  exact actualScalarJet_continuousAt (contDiffAt_D hf (by norm_num) (basis a))
lemma matrixScalarJets_continuousAt {f : Point → Mat} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (matrixScalarJets f) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  exact actualScalarJet_continuousAt (contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k)
lemma matrixThreeJets_continuousAt {f : Point → Mat} {x : Point} (hf : ContDiffAt ℝ 3 f x) :
    ContinuousAt (matrixThreeJets f) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  exact actualThreeJet_continuousAt (contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k)
lemma angular_threeJets_continuousOn {V W : Set Angle} (hV : IsOpen V) (hWV : W ⊆ V)
    {f : Angle → Mat} (hf : ContDiffOn ℝ 3 f V) :
    ContinuousOn (fun θ => matrixThreeJets (angularLift f) (slice 0 θ)) W := by
  intro θ hθ
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (matrixThreeJets_continuousAt ?_) (slice_smooth 0).continuous.continuousAt
  apply angularLift_diff
  rw [angularProjection_slice_eq]
  exact hf.contDiffAt (hV.mem_nhds (hWV hθ))
lemma angular_scalarJets_continuousOn {V W : Set Angle} (hV : IsOpen V) (hWV : W ⊆ V)
    {f : Angle → Mat} (hf : ContDiffOn ℝ 2 f V) :
    ContinuousOn (fun θ => matrixScalarJets (angularLift f) (slice 0 θ)) W := by
  intro θ hθ
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp (matrixScalarJets_continuousAt ?_) (slice_smooth 0).continuous.continuousAt
  apply angularLift_diff
  rw [angularProjection_slice_eq]
  exact hf.contDiffAt (hV.mem_nhds (hWV hθ))
theorem compact_angular_source_jets {W V : Set Angle} (hW : IsCompact W)
    (hV : IsOpen V) (hWV : W ⊆ V) (σ mg mK : Angle → Mat) (mr : Angle → ℝ)
    (hσ : ContDiffOn ℝ 3 σ V) (hmg : ContDiffOn ℝ 3 mg V)
    (hmK : ContDiffOn ℝ 2 mK V) (hmr : ContDiffOn ℝ 2 mr V)
    (hpos : ∀ θ ∈ V, (σ θ).PosDef) :
    ∃ K : Set MatrixThreeJet, IsCompact K ∧
      (∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ W, ∀ ρ : ℝ,
        matrixThreeJets (angularLift σ) (slice ρ θ) ∈ K ∧
        ‖matrixThreeJets (angularLift σ) (slice ρ θ)‖ ≤ B ∧
        ‖matrixThreeJets (angularLift mg) (slice ρ θ)‖ ≤ B ∧
        ‖matrixScalarJets (angularLift mK) (slice ρ θ)‖ ≤ B ∧
        ‖actualScalarJet (angularLift mr) (slice ρ θ)‖ ≤ B := by
  have hcσ := angular_threeJets_continuousOn hV hWV hσ
  have hcg := angular_threeJets_continuousOn hV hWV hmg
  have hck := angular_scalarJets_continuousOn hV hWV hmK
  have hcr : ContinuousOn (fun θ => actualScalarJet (angularLift mr) (slice 0 θ)) W := by
    intro θ hθ
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp (actualScalarJet_continuousAt ?_) (slice_smooth 0).continuous.continuousAt
    apply angularLift_diff
    rw [angularProjection_slice_eq]
    exact hmr.contDiffAt (hV.mem_nhds (hWV hθ))
  obtain ⟨bσ,hbσ⟩ := hW.exists_bound_of_continuousOn hcσ
  obtain ⟨bg,hbg⟩ := hW.exists_bound_of_continuousOn hcg
  obtain ⟨bk,hbk⟩ := hW.exists_bound_of_continuousOn hck
  obtain ⟨br,hbr⟩ := hW.exists_bound_of_continuousOn hcr
  let K := (fun θ => matrixThreeJets (angularLift σ) (slice 0 θ)) '' W
  refine ⟨K,hW.image_of_continuousOn hcσ,?_,max 0 (max bσ (max bg (max bk br))),le_max_left _ _,?_⟩
  · rintro q ⟨θ,hθ,rfl⟩
    simpa only [matrixThreeJets,actualThreeJet,actualScalarJet,angularLift,angularProjection_slice_eq] using hpos θ (hWV hθ)
  · intro θ hθ ρ
    simp only [matrixThreeJets_angularLift_slice,
      matrixScalarJets_angularLift_slice,actualScalarJet_angularLift_slice]
    refine ⟨⟨θ,hθ,rfl⟩,?_,?_,?_,?_⟩
    · exact (hbσ θ hθ).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hbg θ hθ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hbk θ hθ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    · exact (hbr θ hθ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise
lemma SmoothAngularPatch.roundMetric_contDiffAt (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : ContDiffAt ℝ ∞ (angularRoundMetric P.param) θ := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact ContDiffAt.inner ℝ
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open scoped Matrix.Norms.Elementwise
lemma SourceTensorFields.ComponentBounds.mono {f : SourceTensorFields} {B C : ℝ} {y : Point}
    (h : f.ComponentBounds B y) (hy : 0 ≤ y 0) (hBC : B ≤ C) : f.ComponentBounds C y := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · intro i k; exact (h.base.eg i k).mono hy le_rfl hBC
  · intro i k; exact (h.base.ek i k).mono hy le_rfl hBC
  · intro i; exact (h.base.b i).mono hy le_rfl hBC
  · exact h.base.err.mono hy le_rfl hBC
  · exact h.kr.mono hy le_rfl hBC
  · intro i; exact (h.kb i).mono hy le_rfl hBC
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise
theorem SpatialBoostPatch.uniform_collar_input {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : SpatialBoostPatch e p he A B Q P θ (2*δ) R) :
    ∃ K : Set MatrixThreeJet, IsCompact K ∧
      (∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Metric.closedBall θ δ, ∀ ρ : ℝ,
        matrixThreeJets (angularLift (boostSourceFields e p A B Q P).base.sigma) (slice ρ η) ∈ K ∧
        ‖matrixThreeJets (angularLift (boostSourceFields e p A B Q P).base.sigma) (slice ρ η)‖ ≤ C ∧
        ‖matrixThreeJets (angularLift (boostSourceFields e p A B Q P).base.mg) (slice ρ η)‖ ≤ C ∧
        ‖matrixScalarJets (angularLift (boostSourceFields e p A B Q P).base.mK) (slice ρ η)‖ ≤ C ∧
        ‖actualScalarJet (angularLift (boostSourceFields e p A B Q P).base.mr) (slice ρ η)‖ ≤ C ∧
        (R < Real.exp ρ → (boostSourceFields e p A B Q P).ComponentBounds C (logRadiusChart (slice ρ η))) := by
  let f := boostSourceFields e p A B Q P
  have hd : 0 < δ := by linarith [h.genuine.estimates.ball_pos]
  have hsub : Metric.closedBall θ δ ⊆ Metric.ball θ (2*δ) :=
    Metric.closedBall_subset_ball (by linarith)
  have hs : ContDiffOn ℝ 3 f.base.sigma (Metric.ball θ (2*δ)) := by
    intro η hη
    exact ((P.roundMetric_contDiffAt (h.genuine.estimates.ball_target hη)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffWithinAt
  have hg : ContDiffOn ℝ 3 f.base.mg (Metric.ball θ (2*δ)) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro k
    exact (h.genuine.estimates.angular_smooth i.succ k.succ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hk : ContDiffOn ℝ 2 f.base.mK (Metric.ball θ (2*δ)) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro k
    exact (h.genuine.estimates.second_smooth i.succ k.succ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hr : ContDiffOn ℝ 2 f.base.mr (Metric.ball θ (2*δ)) :=
    h.genuine.estimates.radial_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨K,hK,hpos,C,hC,hjets⟩ := compact_angular_source_jets
    (isCompact_closedBall θ δ) Metric.isOpen_ball hsub f.base.sigma f.base.mg f.base.mK f.base.mr
    hs hg hk hr (fun η hη => P.roundMetric_posDef (h.genuine.estimates.ball_target hη))
  obtain ⟨D,hD,hcomp⟩ := cksSourceFields_bounds
    (fun y (hy : y ∈ angularRadialTail R (Metric.ball θ (2*δ))) => (h.genuine.estimates.radius_pos.trans hy.1).le)
    (angularRoundMetric P.param) h.metric_CKS h.second_CKS
  refine ⟨K,hK,hpos,max C D,hC.trans (le_max_left _ _),?_⟩
  intro η hη ρ
  obtain ⟨hmem,h1,h2,h3,h4⟩ := hjets η hη ρ
  refine ⟨hmem,h1.trans (le_max_left _ _),h2.trans (le_max_left _ _),
    h3.trans (le_max_left _ _),h4.trans (le_max_left _ _),?_⟩
  intro hr
  apply (hcomp _ ?_).mono (by simpa only [logRadiusChart,ite_true,slice_zero] using (Real.exp_pos ρ).le) (le_max_right _ _)
  exact ⟨by simpa [logRadiusChart,slice_zero] using hr,by simpa only [angularProjection_logRadiusChart,angularProjection_slice] using hsub hη⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set CKSAngularSlice
open scoped Matrix.Norms.Elementwise

def SourceTensorFields.UniformCollarInput (f : SourceTensorFields)
    (K : Set MatrixThreeJet) (C R : ℝ) (W : Set Angle) : Prop :=
  ∀ η ∈ W, ∀ ρ : ℝ,
    matrixThreeJets (angularLift f.base.sigma) (slice ρ η) ∈ K ∧
    ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ η)‖ ≤ C ∧
    ‖matrixThreeJets (angularLift f.base.mg) (slice ρ η)‖ ≤ C ∧
    ‖matrixScalarJets (angularLift f.base.mK) (slice ρ η)‖ ≤ C ∧
    ‖actualScalarJet (angularLift f.base.mr) (slice ρ η)‖ ≤ C ∧
    (R < Real.exp ρ → f.ComponentBounds C (logRadiusChart (slice ρ η)))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped Matrix.Norms.Elementwise

theorem exists_uniform_boost_collar_atlas {e : ℝ} {p : E} (he : ‖p‖ < e)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hreal : ∀ n, (old n).Realizes A B) :
    ∃ (s : Finset Sphere) (P : Sphere → SmoothAngularPatch) (δ : Sphere → ℝ)
      (R : ℝ) (K : Set MatrixThreeJet) (C : ℝ),
      0 < R ∧ IsCompact K ∧
      (∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1)) ∧ 0 ≤ C ∧
      (∀ n ∈ s, SpatialBoostPatch e p he A B (old (boundary e p he n))
        (P n) ((P n).chart n) (2*δ n) R) ∧
      (∀ n ∈ s, (boostSourceFields e p A B (old (boundary e p he n)) (P n)).UniformCollarInput
        K C R (Metric.closedBall ((P n).chart n) (δ n))) ∧
      (∀ q : Sphere, ∃ n ∈ s, q ∈ (P n).sphereRegion (Metric.ball ((P n).chart n) (δ n))) := by
  classical
  obtain ⟨s,P,δ,R,hR,hpatch,hcover⟩ := exists_precompact_spatial_boost_atlas he A B old hold hreal
  let ι := {n : Sphere // n ∈ s}
  choose K hK hp C hC hb using fun i : ι => (hpatch i i.2).uniform_collar_input
  let U : Set MatrixThreeJet := ⋃ i : ι, K i
  let D : ℝ := ∑ i : ι, C i
  have hu : IsCompact U := isCompact_iUnion (fun i => hK i)
  have hpU : ∀ q ∈ U, Matrix.PosDef (fun i k => (q i k).1.1) := by
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    exact hp i q hi
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hC i)
  have hCD (i : ι) : C i ≤ D := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨s,P,δ,R,U,D,hR,hu,hpU,hD,hpatch,?_,hcover⟩
  intro n hn η hη ρ
  let i : ι := ⟨n,hn⟩
  obtain ⟨hmem,h1,h2,h3,h4,hcomp⟩ := hb i η hη ρ
  refine ⟨mem_iUnion.mpr ⟨i,hmem⟩,h1.trans (hCD i),h2.trans (hCD i),
    h3.trans (hCD i),h4.trans (hCD i),?_⟩
  intro hr
  exact (hcomp hr).mono
    (by simpa only [logRadiusChart,ite_true,slice_zero] using (Real.exp_pos ρ).le) (hCD i)
end
end CKSLorentz

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
abbrev Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ
def tensorPullback (f : E → F) (T : F → Bilinear F) (x : E) : Bilinear E :=
  (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)

def tensorLie (T : E → Bilinear E) (V : E → E) (x v w : E) : ℝ :=
  (fderiv ℝ T x (V x)) v w + T x (fderiv ℝ V x v) w + T x v (fderiv ℝ V x w)
end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma differentiableAt_flip {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → F →L[ℝ] G →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) : DifferentiableAt ℝ (fun y => (B y).flip) x := by
  have hf : DifferentiableAt ℝ (fun b : F →L[ℝ] G →L[ℝ] ℝ => b.flip) (B x) :=
    (ContinuousLinearMap.flipₗᵢ ℝ F G ℝ).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt
  exact DifferentiableAt.comp (𝕜 := ℝ) (F := F →L[ℝ] G →L[ℝ] ℝ)
    (G := G →L[ℝ] F →L[ℝ] ℝ) x hf hB
lemma differentiableAt_bilinearComp {B : E → Bilinear F} {A : E → E →L[ℝ] F} {x : E}
    (hB : DifferentiableAt ℝ B x) (hA : DifferentiableAt ℝ A x) :
    DifferentiableAt ℝ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  exact differentiableAt_flip ((differentiableAt_flip (hB.clm_comp hA)).clm_comp hA)
lemma fderiv_bilinear_apply {B : E → Bilinear F} {u v : E → F} {x : E}
    (hB : DifferentiableAt ℝ B x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (a : E) :
    fderiv ℝ (fun y => B y (u y) (v y)) x a =
      B x (fderiv ℝ u x a) (v x) + B x (u x) (fderiv ℝ v x a) +
        (fderiv ℝ B x a) (u x) (v x) := by
  rw [fderiv_clm_apply (hB.clm_apply hu) hv, fderiv_clm_apply hB hu]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring
lemma fderiv_bilinear_const {B : E → Bilinear F} {x : E}
    (hB : DifferentiableAt ℝ B x) (v w : F) (a : E) :
    fderiv ℝ (fun y => B y v w) x a = (fderiv ℝ B x a) v w := by
  simpa using fderiv_bilinear_apply hB
    (differentiableAt_const (c := v)) (differentiableAt_const (c := w)) a
lemma differentiableAt_tensorPullback {f : E → F} {T : F → Bilinear F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x)) :
    DifferentiableAt ℝ (tensorPullback f T) x := by
  exact differentiableAt_bilinearComp (hT.comp (G := Bilinear F) x (hf.differentiableAt (by norm_num)))
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [completeF : CompleteSpace F]
omit completeF in
lemma fderiv_tensorPullback [CompleteSpace F] {f : E → F} {T : F → Bilinear F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x)) (a v w : E) :
    (fderiv ℝ (tensorPullback f T) x a) v w =
      T (f x) (fderiv ℝ (fderiv ℝ f) x a v) (fderiv ℝ f x w) +
      T (f x) (fderiv ℝ f x v) (fderiv ℝ (fderiv ℝ f) x a w) +
      (fderiv ℝ T (f x) (fderiv ℝ f x a)) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hTf : DifferentiableAt ℝ (fun y => T (f y)) x := hT.comp (G := Bilinear F) x hfd
  rw [← fderiv_bilinear_const (differentiableAt_tensorPullback hf hT) v w a]
  change fderiv ℝ (fun y => T (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) x a = _
  rw [fderiv_bilinear_apply hTf (hA.clm_apply (differentiableAt_const v))
    (hA.clm_apply (differentiableAt_const w))]
  rw [fderiv_clm_apply hA (differentiableAt_const v),
    fderiv_clm_apply hA (differentiableAt_const w)]
  rw [show fderiv ℝ (fun y => T (f y)) x =
    (fderiv ℝ T (f x)).comp (fderiv ℝ f x) from fderiv_fun_comp (G := Bilinear F) x hT hfd]
  simp

theorem tensorLie_natural {f : E → F} {T : F → Bilinear F}
    {V : F → F} {W : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x))
    (hV : DifferentiableAt ℝ V (f x)) (hW : DifferentiableAt ℝ W x)
    (hrel : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (W y) = V (f y)) (v w : E) :
    tensorLie (tensorPullback f T) W x v w =
      tensorLie T V (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hD (u : E) : fderiv ℝ f x (fderiv ℝ W x u) +
      fderiv ℝ (fderiv ℝ f) x (W x) u =
        fderiv ℝ V (f x) (fderiv ℝ f x u) := by
    have h := congrArg (fun A : E →L[ℝ] F => A u) (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hrel)
    rw [fderiv_clm_apply hA hW] at h
    rw [show fderiv ℝ (fun y => V (f y)) x =
      (fderiv ℝ V (f x)).comp (fderiv ℝ f x) from fderiv_comp x hV hfd] at h
    simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      hsymm u (W x)] using h
  unfold tensorLie
  rw [fderiv_tensorPullback hf hT, hrel.self_of_nhds]
  simp only [tensorPullback, ContinuousLinearMap.bilinearComp_apply]
  rw [← hD v, ← hD w]
  simp only [map_add, add_apply]
  ring
end
end CKSTensorNaturality

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalAngularJet (γ : PhysicalPoint → Mat) (x : PhysicalPoint) : Jet :=
  (γ x, (fun i j k => D (CKSRealizedRound.basis i.succ) (fun y => γ y j k) x),
    fun a i j k => D (CKSRealizedRound.basis a.succ)
      (fun y => D (CKSRealizedRound.basis i.succ) (fun z => γ z j k) y) x)

def physicalAngularScalarJet (U : PhysicalPoint → ℝ) (x : PhysicalPoint) : ScalarJet :=
  (U x, (fun i => D (CKSRealizedRound.basis i.succ) U x),
    fun i j => D (CKSRealizedRound.basis i.succ)
      (D (CKSRealizedRound.basis j.succ) U) x)

lemma angular_frame_covector_contract {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (v α : Point) :
    (∑ b : Fin 2, (∑ k : Fin 2, v k * angularFrame U γ s b k) *
      (∑ j : Fin 2, α j * angularFrame U γ s b j)) =
      ∑ k : Fin 2, ∑ j : Fin 2, γ⁻¹ k j * v k * α j := by
  have hg (k j : Fin 2) :
      (∑ b : Fin 2, angularFrame U γ s b k * angularFrame U γ s b j) = γ⁻¹ k j := by
    exact congrFun (congrFun (angularFrame_gram hU hγ) k) j
  calc
    _ = ∑ k : Fin 2, ∑ j : Fin 2,
        (∑ b : Fin 2, angularFrame U γ s b k * angularFrame U γ s b j) * v k * α j := by
      simp only [Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma metric_inverse_covector_contract {γ : Mat} (hγ : γ.PosDef) (v α : Point) :
    (∑ k : Fin 2, ∑ j : Fin 2, γ⁻¹ k j * (∑ l : Fin 2, v l * γ l k) * α j) =
      ∑ j : Fin 2, v j * α j := by
  calc
    _ = ∑ j : Fin 2, (∑ l : Fin 2, v l * (γ * γ⁻¹) l j) * α j := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = _ := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')]
      simp

lemma physical_christoffel_lower (γ : PhysicalPoint → Mat) (x : PhysicalPoint)
    (j i k : Fin 2) :
    christoffel (physicalAngularJet γ x) j i k =
      ∑ l : Fin 2, (γ x)⁻¹ j l * angularLowerConnection γ x i k l := by
  simp only [christoffel, physicalAngularJet, inverse_eq, angularLowerConnection,
    Fin.sum_univ_two]
  ring

lemma inverse_symm_entry {γ : Mat} (hp : γ.PosDef) (i j : Fin 2) :
    γ⁻¹ i j = γ⁻¹ j i := by
  have hs := hp.inv.isHermitian
  have h := congrFun (congrFun hs.eq i) j
  simpa using h.symm

lemma induced_connection_covector {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint} (hU : U x ≠ 0)
    (hp : (γ x).PosDef) (a b : Fin 2) (α : Point) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
      (∑ j : Fin 2, α j * angularFrame (U x) (γ x) (s x) c j)) =
    (∑ j : Fin 2, D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => angularFrame (U y) (γ y) (s y) b j) x * α j) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b k *
      christoffel (physicalAngularJet γ x) j i k * α j := by
  simp only [inducedFrameCoefficient, add_mul, Finset.sum_add_distrib]
  rw [angular_frame_covector_contract hU hp, metric_inverse_covector_contract hp]
  congr 1
  rw [angular_frame_covector_contract hU hp]
  simp only [physical_christoffel_lower, Fin.sum_univ_two]
  rw [inverse_symm_entry hp 1 0]
  ring

lemma D_angular_sum (e : PhysicalPoint) {x : PhysicalPoint}
    (f : Fin 2 → PhysicalPoint → ℝ) (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
  simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

lemma D_angular_direction (U : ℝ) (γ : Mat) (s : Point)
    (a : Fin 2) (f : PhysicalPoint → ℝ) (x : PhysicalPoint) :
    D (adaptedFrame U γ s a.succ) f x =
      ∑ i : Fin 2, angularFrame U γ s a i * D (CKSRealizedRound.basis i.succ) f x := by
  rw [D_direction_expansion, Fin.sum_univ_succ, adaptedFrame_radial,
    zero_mul, zero_add]
  rfl

lemma extracted_leaf_connection (c : CKSFrame.ConnectionData) (a b d : Fin 2) :
    CKSFrame.leafConnection c a b d = CKSFrame.connection c a.succ b.succ d.succ := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> rfl

lemma physical_leaf_connection_extracted {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d : Fin 2) :
    CKSFrame.leafConnection (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b d =
      -inducedFrameCoefficient U γ s x a d b := by
  rw [extracted_leaf_connection, CKSFrame.connection_metric,
    frame_connection_actual (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds,
    physical_leaf_connection hp.self_of_nhds h0]

lemma angular_frame_tensor_contract {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) (T : Mat) :
    (∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
      angularFrame U γ s a i * angularFrame U γ s a j * T i j) =
      ∑ i : Fin 2, ∑ j : Fin 2, γ⁻¹ i j * T i j := by
  have hg (i j : Fin 2) :
      (∑ a : Fin 2, angularFrame U γ s a i * angularFrame U γ s a j) = γ⁻¹ i j := by
    exact congrFun (congrFun (angularFrame_gram hU hγ) i) j
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
      (∑ a : Fin 2, angularFrame U γ s a i * angularFrame U γ s a j) * T i j := by
      simp only [Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma physical_covector_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (α : Fin 2 → PhysicalPoint → ℝ) (hα : ∀ i, DifferentiableAt ℝ (α i) x) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    (∑ a : Fin 2, (D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x +
      ∑ b : Fin 2, CKSFrame.leafConnection c a b a *
        (∑ j : Fin 2, α j x * angularFrame (U x) (γ x) (s x) b j))) =
    ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
      (D (CKSRealizedRound.basis i.succ) (α j) x -
        ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * α k x) := by
  dsimp only
  have he (a j : Fin 2) : DifferentiableAt ℝ
      (fun y => angularFrame (U y) (γ y) (s y) a j) x :=
    differentiableAt_pi.mp ((adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds a.succ).differentiableAt (by simp)) j.succ
  have hsum (a : Fin 2) :
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x =
      ∑ j : Fin 2, (α j x * D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) a j) x +
        angularFrame (U x) (γ x) (s x) a j *
          D (adaptedFrame (U x) (γ x) (s x) a.succ) (α j) x) := by
    rw [D_angular_sum _ (fun j y => α j y * angularFrame (U y) (γ y) (s y) a j)
      (fun j => (hα j).mul (he a j))]
    apply Finset.sum_congr rfl
    intro j _
    exact D_mul _ (hα j) (he a j)
  calc
    _ = ∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j *
        (D (CKSRealizedRound.basis i.succ) (α j) x -
          ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * α k x) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [physical_leaf_connection_extracted hU hγ hs h0 hp,
        neg_mul, Finset.sum_neg_distrib]
      rw [induced_connection_covector h0 hp.self_of_nhds, hsum]
      simp only [D_angular_direction, Fin.sum_univ_two]
      ring
    _ = _ := angular_frame_tensor_contract h0 hp.self_of_nhds _

lemma physical_acceleration_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.accelDiv c dc =
      ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
        (D (CKSRealizedRound.basis i.succ)
          (fun y => D (CKSRealizedRound.basis j.succ) U y / U y) x -
          ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j *
            (D (CKSRealizedRound.basis k.succ) U x / U x)) := by
  dsimp only
  let α : Fin 2 → PhysicalPoint → ℝ := fun j y => D (CKSRealizedRound.basis j.succ) U y / U y
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, 0 < U y := hU.continuousAt.eventually (lt_mem_nhds h0)
  have hB (a : Fin 2) :
      (fun y => (frameConnectionField (fun z => foliationMetric (U z) (γ z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).B a) =ᶠ[𝓝 x]
      (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) := by
    filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
      hs1.eventually (by norm_num), hnear, hp.eventually_nhds] with y hyu hyg hys hyp hpg
    exact physical_acceleration_components (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp hpg a
  have hU2 : ContDiffAt ℝ 2 U x := hU.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hd (i : Fin 2) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i.succ) U) x :=
    (contDiffAt_D hU2 (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hα (i : Fin 2) : DifferentiableAt ℝ (α i) x :=
    diffAt_div (hd i) (hU.differentiableAt (by simp)) h0.ne'
  rw [CKSFrame.accelDiv]
  calc
    _ = ∑ a : Fin 2, (D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => ∑ j : Fin 2, α j y * angularFrame (U y) (γ y) (s y) a j) x +
      ∑ b : Fin 2, CKSFrame.leafConnection (frameConnectionField
        (fun y => foliationMetric (U y) (γ y) (s y))
        (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b a *
        (∑ j : Fin 2, α j x * angularFrame (U x) (γ x) (s x) b j)) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      · exact D_congr (hB a) _
      · apply Finset.sum_congr rfl
        intro b _
        congr 1
        exact (hB b).self_of_nhds
    _ = _ := physical_covector_divergence hU hγ hs h0.ne' hp α hα

theorem physical_acceleration_laplacian {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.accelDiv c dc - CKSFrame.accelNormSq c =
      -lapseLaplacian (physicalAngularJet γ x) (physicalAngularScalarJet U x) := by
  dsimp only
  rw [physical_acceleration_divergence hU hγ hs h0 hp,
    physical_acceleration_norm (hU.differentiableAt (by simp))
      (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  have hU2 : ContDiffAt ℝ 2 U x := hU.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hd (j : Fin 2) : DifferentiableAt ℝ (D (CKSRealizedRound.basis j.succ) U) x :=
    (contDiffAt_D hU2 (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [D_div _ (hd _) (hU.differentiableAt (by simp)) h0.ne',
    lapseLaplacian, physicalAngularScalarJet, physicalAngularJet, inverse_eq,
    Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def angularTensorFrame (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (T : PhysicalPoint → Mat)
    (x : PhysicalPoint) (a b : Fin 2) : ℝ :=
  ∑ i, ∑ j, T x i j * angularFrame (U x) (γ x) (s x) a i *
    angularFrame (U x) (γ x) (s x) b j

lemma angularFrame_component_diff {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef) (a i : Fin 2) :
    DifferentiableAt ℝ (fun y => angularFrame (U y) (γ y) (s y) a i) x :=
  differentiableAt_pi.mp ((adaptedFrame_contDiffAt hU hγ hs hp a.succ).differentiableAt
    (by simp)) i.succ

lemma D_angularTensorFrame {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef)
    (hT : DifferentiableAt ℝ T x) (v : PhysicalPoint) (a b : Fin 2) :
    D v (fun y => angularTensorFrame U γ s T y a b) x =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (D v (fun y => T y i j) x * angularFrame (U x) (γ x) (s x) a i *
          angularFrame (U x) (γ x) (s x) b j +
        T x i j * D v (fun y => angularFrame (U y) (γ y) (s y) a i) x *
          angularFrame (U x) (γ x) (s x) b j +
        T x i j * angularFrame (U x) (γ x) (s x) a i *
          D v (fun y => angularFrame (U y) (γ y) (s y) b j) x) := by
  have ht (i j : Fin 2) : DifferentiableAt ℝ (fun y => T y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hT i) j
  have he := angularFrame_component_diff hU hγ hs hp
  unfold angularTensorFrame
  rw [D_angular_sum _ _ (fun i => DifferentiableAt.fun_sum (fun j _ =>
    ((ht i j).fun_mul (he a i)).fun_mul (he b j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_angular_sum _ _ (fun j => ((ht i j).fun_mul (he a i)).fun_mul (he b j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [D_mul _ ((ht i j).fun_mul (he a i)) (he b j), D_mul _ (ht i j) (he a i)]
  ring

lemma induced_tensor_connection_left {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b d : Fin 2) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
      angularTensorFrame U γ s T x c d) =
    (∑ i : Fin 2, ∑ j : Fin 2, T x i j *
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) b i) x *
      angularFrame (U x) (γ x) (s x) d j) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b k *
      christoffel (physicalAngularJet γ x) l i k * T x l j *
      angularFrame (U x) (γ x) (s x) d j := by
  have h := induced_connection_covector (s := s) h0 hp a b
    (fun i => ∑ j : Fin 2, T x i j * angularFrame (U x) (γ x) (s x) d j)
  simp only [angularTensorFrame, Fin.sum_univ_two] at h ⊢
  linear_combination h

lemma induced_tensor_connection_right {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b d : Fin 2) :
    (∑ c : Fin 2, inducedFrameCoefficient U γ s x a d c *
      angularTensorFrame U γ s T x b c) =
    (∑ i : Fin 2, ∑ j : Fin 2, T x i j *
      angularFrame (U x) (γ x) (s x) b i *
      D (adaptedFrame (U x) (γ x) (s x) a.succ)
        (fun y => angularFrame (U y) (γ y) (s y) d j) x) +
    ∑ i : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2, ∑ j : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) d k *
      christoffel (physicalAngularJet γ x) l i k * T x j l *
      angularFrame (U x) (γ x) (s x) b j := by
  have h := induced_connection_covector (s := s) h0 hp a d
    (fun j => ∑ i : Fin 2, T x i j * angularFrame (U x) (γ x) (s x) b i)
  simp only [angularTensorFrame, Fin.sum_univ_two] at h ⊢
  linear_combination h

lemma physical_leaf_connection_direct {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d : Fin 2) :
    CKSFrame.leafConnection (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b d =
      inducedFrameCoefficient U γ s x a b d := by
  rw [extracted_leaf_connection,
    frame_connection_actual (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds,
    physical_leaf_connection hp.self_of_nhds h0]

lemma physical_leaf_tensor_covariant {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : DifferentiableAt ℝ T x) (a b d : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (D (E a.succ x) (fun y => angularTensorFrame U γ s T y b d) x -
      ∑ e : Fin 2, (CKSFrame.leafConnection c a b e * angularTensorFrame U γ s T x e d +
        CKSFrame.leafConnection c a d e * angularTensorFrame U γ s T x b e)) =
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
        angularFrame (U x) (γ x) (s x) d k *
          (D (CKSRealizedRound.basis i.succ) (fun y => T y j k) x -
            ∑ l : Fin 2, (christoffel (physicalAngularJet γ x) l i j * T x l k +
              christoffel (physicalAngularJet γ x) l i k * T x j l)) := by
  dsimp only
  simp only [physical_leaf_connection_direct hU hγ hs h0 hp, Finset.sum_add_distrib]
  rw [D_angularTensorFrame hU hγ hs hp.self_of_nhds hT,
    induced_tensor_connection_left h0 hp.self_of_nhds,
    induced_tensor_connection_right h0 hp.self_of_nhds]
  simp only [D_angular_direction, Fin.sum_univ_two]
  ring

theorem physical_leaf_tensor_divergence {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : DifferentiableAt ℝ T x) (a : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (∑ b : Fin 2, (D (E b.succ x) (fun y => angularTensorFrame U γ s T y b a) x -
      ∑ d : Fin 2, (CKSFrame.leafConnection c b b d * angularTensorFrame U γ s T x d a +
        CKSFrame.leafConnection c b a d * angularTensorFrame U γ s T x b d))) =
      ∑ k : Fin 2, tensorDiv (physicalAngularJet γ x)
        (fun i j => physicalAngularScalarJet (fun y => T y i j) x) k *
          angularFrame (U x) (γ x) (s x) a k := by
  dsimp only
  have hcov := physical_leaf_tensor_covariant hU hγ hs h0 hp hT
  dsimp only at hcov
  simp_rw [hcov]
  let e : Fin 2 → Point := fun a => angularFrame (U x) (γ x) (s x) a
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    D (CKSRealizedRound.basis i.succ) (fun y => T y j k) x -
      ∑ l : Fin 2, (christoffel (physicalAngularJet γ x) l i j * T x l k +
        christoffel (physicalAngularJet γ x) l i k * T x j l)
  calc
    (∑ b : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        e b i * e b j * e a k * A i j k) =
      ∑ k : Fin 2, (∑ b : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
        e b i * e b j * A i j k) * e a k := by
          simp only [Fin.sum_univ_two]
          ring
    _ = ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j * A i j k) * e a k := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun z => z * e a k)
        (angular_frame_tensor_contract (s := s x) h0 hp.self_of_nhds (fun i j => A i j k))
    _ = _ := by
      simp only [tensorDiv, physicalAngularScalarJet, inverse_eq, physicalAngularJet, A, e]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationNormal_succ (U : ℝ) (s : Point) (i : Fin 2) :
    foliationNormal U s i.succ = -U * s i := by
  fin_cases i <;> rfl

lemma tangential_frame_covector_expansion {U : ℝ} {γ : Mat} {s : Point}
    (h0 : U ≠ 0) (hp : γ.PosDef) (v : PhysicalPoint) (α : Point) :
    (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
      (∑ i : Fin 2, α i * angularFrame U γ s b i)) =
      ∑ i : Fin 2, α i * (v i.succ + s i * v 0) := by
  have he := orthonormal_frame_expansion (e := Matrix.of (fun a b => adaptedFrame U γ s a b))
    (adaptedFrame_orthonormal h0 hp s) v
  have hrad := he 0
  simp only [Matrix.of_apply, Fin.sum_univ_succ, adaptedFrame_radial, mul_zero,
    Finset.sum_const_zero, add_zero] at hrad
  change metricPair (foliationMetric U γ s) v (foliationNormal U s) * U = v 0 at hrad
  have ht (i : Fin 2) :
      (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
        angularFrame U γ s b i) = v i.succ + s i * v 0 := by
    have hh := he i.succ
    simp only [Matrix.of_apply, Fin.sum_univ_succ, adaptedFrame_first,
      foliationNormal_succ] at hh
    change metricPair (foliationMetric U γ s) v (foliationNormal U s) * (-U * s i) +
      (∑ b : Fin 2, metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) *
        angularFrame U γ s b i) = v i.succ at hh
    calc
      _ = v i.succ + s i * (metricPair (foliationMetric U γ s) v (foliationNormal U s) * U) := by
        linear_combination hh
      _ = _ := by rw [hrad]
  calc
    _ = ∑ i : Fin 2, α i * (∑ b : Fin 2,
        metricPair (foliationMetric U γ s) v (adaptedFrame U γ s b.succ) * angularFrame U γ s b i) := by
          simp only [Fin.sum_univ_two]
          ring
    _ = _ := by simp only [ht]

lemma adaptedFrame_normal_bracket {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hs : DifferentiableAt ℝ s x) (a i : Fin 2) :
    let E := fun b y => adaptedFrame (U y) (γ y) (s y) b
    actualFrameBracket E x 0 a.succ i.succ + s x i * actualFrameBracket E x 0 a.succ 0 =
      D (foliationNormal (U x) (s x))
        (fun y => angularFrame (U y) (γ y) (s y) a i) x +
        U x * D (E a.succ x) (fun y => s y i) x := by
  dsimp only
  have hdn := foliationNormal_derivative (adaptedFrame (U x) (γ x) (s x) a.succ) hU hs
  have hi := congrFun hdn i.succ
  have hzero := congrFun hdn 0
  have hni : foliationNormalDerivative (U x) (s x)
      (D (adaptedFrame (U x) (γ x) (s x) a.succ) U x)
      (fun j => D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => s y j) x) i.succ =
    -(D (adaptedFrame (U x) (γ x) (s x) a.succ) U x) * s x i -
      U x * D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => s y i) x := by
    fin_cases i <;> dsimp [foliationNormalDerivative]
  rw [hni] at hi
  change D (adaptedFrame (U x) (γ x) (s x) a.succ) U x = _ at hzero
  simp only [actualFrameBracket, adaptedFrame_radial, adaptedFrame_first, D_const]
  change D (foliationNormal (U x) (s x))
    (fun y => angularFrame (U y) (γ y) (s y) a i) x -
    D (adaptedFrame (U x) (γ x) (s x) a.succ) (fun y => foliationNormal (U y) (s y) i.succ) x +
    s x i * (0 - D (adaptedFrame (U x) (γ x) (s x) a.succ) U x) = _
  rw [hi]
  ring

lemma physical_normal_tangential_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a : Fin 2) (α : Point) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    (∑ b : Fin 2, (CKSFrame.connection c 0 a.succ b.succ - CKSFrame.chi c a b) *
      (∑ i : Fin 2, α i * angularFrame (U x) (γ x) (s x) b i)) =
      ∑ i : Fin 2, α i *
        (D (foliationNormal (U x) (s x))
          (fun y => angularFrame (U y) (γ y) (s y) a i) x +
          U x * D (E a.succ x) (fun y => s y i) x) := by
  dsimp only
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  have hmetric : ∀ᶠ y in 𝓝 x, (foliationMetric (U y) (γ y) (s y)).IsHermitian :=
    hp.mono fun y hy => metricBlock_hermitian _ _ hy.isHermitian
  simp only [← CKSFrame.connection_normal, frame_connection_actual ha,
    frameCoefficient_torsion hmetric]
  change (∑ b : Fin 2, metricPair (foliationMetric (U x) (γ x) (s x))
    (actualFrameBracket (fun i y => adaptedFrame (U y) (γ y) (s y) i) x 0 a.succ)
    (adaptedFrame (U x) (γ x) (s x) b.succ) *
      (∑ i : Fin 2, α i * angularFrame (U x) (γ x) (s x) b i)) = _
  rw [tangential_frame_covector_expansion (s := s x) h0 hp.self_of_nhds]
  apply Finset.sum_congr rfl
  intro i _
  rw [adaptedFrame_normal_bracket (hU.differentiableAt (by simp)) (hs.differentiableAt (by simp))]

theorem physical_normal_covector_lie {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {α : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hα : DifferentiableAt ℝ α x) (a : Fin 2) :
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    D (E 0 x) (fun y => ∑ i : Fin 2, α y i * angularFrame (U y) (γ y) (s y) a i) x -
      (∑ b : Fin 2, (CKSFrame.connection c 0 a.succ b.succ - CKSFrame.chi c a b) *
        (∑ i : Fin 2, α x i * angularFrame (U x) (γ x) (s x) b i)) =
    ∑ i : Fin 2, U x * (D (CKSRealizedRound.basis 0) (fun y => α y i) x -
      ∑ j : Fin 2, (s x j * D (CKSRealizedRound.basis j.succ) (fun y => α y i) x +
        α x j * D (CKSRealizedRound.basis i.succ) (fun y => s y j) x)) *
          angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  have he := angularFrame_component_diff hU hγ hs hp.self_of_nhds
  have hal (i : Fin 2) : DifferentiableAt ℝ (fun y => α y i) x := differentiableAt_pi.mp hα i
  have hd (i : Fin 2) :
      D (foliationNormal (U x) (s x)) (fun y => α y i) x =
        U x * D (CKSRealizedRound.basis 0) (fun y => α y i) x -
        U x * ∑ j : Fin 2, s x j * D (CKSRealizedRound.basis j.succ) (fun y => α y i) x := by
    rw [D_direction_expansion, Fin.sum_univ_succ]
    change U x * D (CKSRealizedRound.basis 0) (fun y => α y i) x +
      (∑ j : Fin 2, foliationNormal (U x) (s x) j.succ *
        D (CKSRealizedRound.basis j.succ) (fun y => α y i) x) = _
    simp only [foliationNormal_succ, Fin.sum_univ_two]
    ring
  rw [physical_normal_tangential_connection hU hγ hs h0 hp]
  rw [D_angular_sum _ _ (fun i => (hal i).fun_mul (he a i))]
  simp only [adaptedFrame_first]
  simp_rw [D_mul _ (hal _) (he a _), hd, D_angular_direction]
  simp only [Fin.sum_univ_two]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def leafTensorTrace (γ T : Mat) : ℝ := (γ⁻¹ * T).trace

def leafTensorTraceFree (γ T : Mat) : Mat := T - (leafTensorTrace γ T / 2) • γ

lemma foliationTensor_hermitian (U L : ℝ) (η : Point) {T : Mat}
    (hT : T.IsHermitian) (s : Point) : (foliationTensor U L η T s).IsHermitian :=
  metricBlock_hermitian _ _ hT

lemma metricPair_foliationTensor_normal {U L : ℝ} (h0 : U ≠ 0)
    (η : Point) {T : Mat} (hT : T.IsHermitian) (s : Point) :
    metricPair (foliationTensor U L η T s) (foliationNormal U s) (foliationNormal U s) = L := by
  have h := foliationTensor_normal (L := L) h0 η hT s
  simpa only [metricPair, dotProduct, mulVec, star_apply, star_trivial,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

lemma metricPair_foliationTensor_mixed {U L : ℝ} (h0 : U ≠ 0)
    (η : Point) {T : Mat} (hT : T.IsHermitian) (γ : Mat) (s : Point) (a : Fin 2) :
    metricPair (foliationTensor U L η T s) (foliationNormal U s) (adaptedFrame U γ s a.succ) =
      ∑ i : Fin 2, η i * angularFrame U γ s a i := by
  rw [metricPair_symm (foliationTensor_hermitian U L η hT s)]
  unfold metricPair
  rw [Fin.sum_univ_succ]
  simp only [adaptedFrame_radial, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (∑ j : Fin 3, foliationTensor U L η T s i.succ j * foliationNormal U s j) *
        angularFrame U γ s a i := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [angularFrame]
      ring
    _ = _ := by rw [foliationTensor_mixed h0]

lemma frameTensorData_eta (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (a : Fin 2) :
    (frameTensorData K E x).eta a = frameTensor K E x 0 a.succ := by
  fin_cases a <;> rfl

lemma frameTensorDerivative_eta (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) (a : Fin 2) :
    (frameTensorDerivativeData K E x j).eta a =
      D (E j x) (fun y => (frameTensorData K E y).eta a) x := by
  fin_cases a <;> rfl

lemma foliation_frame_tensor_eta {U L : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s η : PhysicalPoint → Point}
    {T : PhysicalPoint → Mat} {x : PhysicalPoint} (h0 : U x ≠ 0)
    (hT : (T x).IsHermitian) (a : Fin 2) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).eta a =
      ∑ i : Fin 2, η x i * angularFrame (U x) (γ x) (s x) a i := by
  rw [frameTensorData_eta]
  exact metricPair_foliationTensor_mixed h0 (η x) hT (γ x) (s x) a

lemma foliation_frame_tensor_tangential (U L : PhysicalPoint → ℝ)
    (γ : PhysicalPoint → Mat) (s η : PhysicalPoint → Point)
    (T : PhysicalPoint → Mat) (x : PhysicalPoint) (a b : Fin 2) :
    frameTensor (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ =
      angularTensorFrame U γ s T x a b := by
  unfold frameTensor
  rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ b)]
  rfl

lemma angularTensorFrame_trace {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (∑ a : Fin 2, angularTensorFrame U γ s T x a a) = leafTensorTrace (γ x) (T x) := by
  unfold angularTensorFrame leafTensorTrace
  rw [angular_trace_transform, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, angularFrame_gram h0 hp]

lemma angularTensorFrame_metric {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b : Fin 2) :
    angularTensorFrame U γ s γ x a b = if a = b then 1 else 0 := by
  have ho := adaptedFrame_orthonormal h0 hp (s x) a.succ b.succ
  rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ b)] at ho
  simpa only [angularTensorFrame, angularFrame, foliationMetric_angular, Fin.succ_inj] using ho

lemma angularTensorFrame_traceFree {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b : Fin 2) :
    angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (T y)) x a b =
      angularTensorFrame U γ s T x a b - leafTensorTrace (γ x) (T x) / 2 *
        (if a=b then 1 else 0) := by
  rw [← angularTensorFrame_metric h0 hp a b]
  simp only [angularTensorFrame, leafTensorTraceFree, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Fin.sum_univ_two]
  ring

lemma foliation_frame_tensor_trace {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).p = leafTensorTrace (γ x) (T x) := by
  change frameTensor _ _ x 1 1 + frameTensor _ _ x 2 2 = _
  have h := angularTensorFrame_trace (T := T) (s := s) h0 hp
  rw [Fin.sum_univ_two] at h
  rw [← foliation_frame_tensor_tangential U L γ s η T x 0 0,
    ← foliation_frame_tensor_tangential U L γ s η T x 1 1] at h
  exact h

lemma tensor_tau_entry (t : CKSFrame.TensorData) (a b : Fin 2) :
    CKSFrame.tau t a b = CKSFrame.tensor t a.succ b.succ - t.p / 2 *
      (if a=b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> simp [CKSFrame.tau, CKSFrame.tensor]

lemma foliation_frame_tensor_tau {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) (a b : Fin 2) :
    CKSFrame.tau (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b =
      angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (T y)) x a b := by
  rw [tensor_tau_entry, frameTensorData_exact _ (foliationTensor_hermitian _ _ _ hT _),
    foliation_frame_tensor_tangential, foliation_frame_tensor_trace h0 hp,
    angularTensorFrame_traceFree h0 hp]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma frameTensorDerivative_L (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) :
    (frameTensorDerivativeData K E x j).L =
      D (E j x) (fun y => (frameTensorData K E y).L) x := rfl

lemma frameTensorDerivative_p {K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hK : DifferentiableAt ℝ K x)
    (hE : ∀ i, DifferentiableAt ℝ (E i) x) (j : Fin 3) :
    (frameTensorDerivativeData K E x j).p =
      D (E j x) (fun y => (frameTensorData K E y).p) x := by
  exact (D_add _ (metricPair_differentiableAt hK (hE 1) (hE 1))
    (metricPair_differentiableAt hK (hE 2) (hE 2))).symm

lemma frameTensorDerivative_tau {K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hK : DifferentiableAt ℝ K x)
    (hE : ∀ i, DifferentiableAt ℝ (E i) x) (j : Fin 3) (a b : Fin 2) :
    CKSFrame.tau (frameTensorDerivativeData K E x j) a b =
      D (E j x) (fun y => CKSFrame.tau (frameTensorData K E y) a b) x := by
  have hf (i k : Fin 3) : DifferentiableAt ℝ (fun y => frameTensor K E y i k) x :=
    metricPair_differentiableAt hK (hE i) (hE k)
  have hd := D_div (E j x) ((hf 1 1).fun_sub (hf 2 2)) (differentiableAt_const (2 : ℝ)) (by norm_num)
  rw [D_sub _ (hf 1 1) (hf 2 2), D_const] at hd
  fin_cases a <;> fin_cases b
  · convert hd.symm using 1 <;>
      dsimp [CKSFrame.tau, frameTensorDerivativeData, frameTensorData, CKSFrame.extractTensor]
    ring
  · rfl
  · rfl
  · change -((D (E j x) (fun y => frameTensor K E y 1 1) x -
        D (E j x) (fun y => frameTensor K E y 2 2) x) / 2) =
      D (E j x) (fun y => -((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) x
    rw [show (fun y => -((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) =
      (fun y => (-1 : ℝ) * ((frameTensor K E y 1 1 - frameTensor K E y 2 2) / 2)) by funext y; ring,
      D_const_mul _ (-1) (diffAt_div ((hf 1 1).fun_sub (hf 2 2)) (differentiableAt_const 2) (by norm_num)), hd]
    ring

lemma foliationTensor_differentiableAt {U L : PhysicalPoint → ℝ}
    {T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hL : DifferentiableAt ℝ L x)
    (hT : DifferentiableAt ℝ T x) (hs : DifferentiableAt ℝ s x)
    (hη : DifferentiableAt ℝ η x) (h0 : U x ≠ 0) :
    DifferentiableAt ℝ (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)) x := by
  have hc (i j) : DifferentiableAt ℝ (fun y => T y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hT i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have hec (i) : DifferentiableAt ℝ (fun y => η y i) x := differentiableAt_pi.mp hη i
  have hu1 : DifferentiableAt ℝ (fun y => 2 / U y) x := diffAt_div (differentiableAt_const 2) hU h0
  have hu2 : DifferentiableAt ℝ (fun y => L y / U y ^ 2) x := diffAt_div hL (hU.pow 2) (pow_ne_zero 2 h0)
  have heu (i) : DifferentiableAt ℝ (fun y => η y i / U y) x := diffAt_div (hec i) hU h0
  have ha : DifferentiableAt ℝ (fun y => L y / U y ^ 2 + 2 / U y *
      (∑ a : Fin 2, η y a * s y a) + ∑ a : Fin 2, ∑ b : Fin 2, T y a b * s y a * s y b) x := by
    simp only [Fin.sum_univ_two]
    fun_prop
  have hb (a : Fin 2) : DifferentiableAt ℝ (fun y => η y a / U y + ∑ b : Fin 2, T y a b * s y b) x := by
    simp only [Fin.sum_univ_two]
    fun_prop
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    first | exact ha | exact hb 0 | exact hb 1 | exact hc 0 0 | exact hc 0 1 | exact hc 1 0 | exact hc 1 1

lemma leafTensorTrace_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTrace (γ y) (T y)) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have ht (i j) : ContDiffAt ℝ ∞ (fun y => T y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j
  have hd : ContDiffAt ℝ ∞ (fun y => determinant (γ y)) x := by
    change ContDiffAt ℝ ∞ (fun y => γ y 0 0 * γ y 1 1 - γ y 0 1 * γ y 1 0) x
    fun_prop
  have hd0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.det_pos.ne'
  have hi (i j) : ContDiffAt ℝ ∞ (fun y => inverse (γ y) i j) x := by
    fin_cases i <;> fin_cases j
    · exact (hc 1 1).div hd hd0
    · exact (hc 0 1).neg.div hd hd0
    · exact (hc 1 0).neg.div hd hd0
    · exact (hc 0 0).div hd hd0
  simp only [leafTensorTrace, ← inverse_eq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop

lemma leafTensorTraceFree_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTraceFree (γ y) (T y)) x := by
  have hp' := leafTensorTrace_contDiffAt hγ hT hp
  unfold leafTensorTraceFree
  exact hT.sub ((hp'.div_const 2).smul hγ)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafConnection_skew (c : CKSFrame.ConnectionData) (a b d : Fin 2) :
    CKSFrame.leafConnection c a b d = -CKSFrame.leafConnection c a d b := by
  fin_cases b <;> fin_cases d <;> simp [CKSFrame.leafConnection]

theorem physical_eta_divergence {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.etaDiv c (frameTensorData K E x) (frameTensorDerivativeData K E x) =
      covectorDiv (physicalAngularJet γ x) (fun i => physicalAngularScalarJet (fun y => η y i) x) := by
  dsimp only
  have he (a : Fin 2) :
      (fun y => (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).eta a) =ᶠ[𝓝 x]
      (fun y => ∑ i : Fin 2, η y i * angularFrame (U y) (γ y) (s y) a i) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hT] with y huy hty
    exact foliation_frame_tensor_eta huy hty a
  rw [CKSFrame.etaDiv]
  simp only [frameTensorDerivative_eta, D_congr (he _)]
  simp only [(he _).self_of_nhds]
  have hh := physical_covector_divergence hU hγ hs h0 hp (fun i y => η y i)
    (fun i => differentiableAt_pi.mp hη i)
  dsimp only at hh
  rw [show covectorDiv (physicalAngularJet γ x)
      (fun i => physicalAngularScalarJet (fun y => η y i) x) =
        ∑ i : Fin 2, ∑ j : Fin 2, (γ x)⁻¹ i j *
          (D (CKSRealizedRound.basis i.succ) (fun y => η y j) x -
            ∑ k : Fin 2, christoffel (physicalAngularJet γ x) k i j * η x k) by
    simp only [covectorDiv, physicalAngularScalarJet, physicalAngularJet, inverse_eq]]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro a _
  simp only [leafConnection_skew (a := a) (b := a), neg_mul,
    Finset.sum_neg_distrib, sub_neg_eq_add]

theorem physical_tau_divergence {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hη : DifferentiableAt ℝ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.tauDiv c (frameTensorData K E x) (frameTensorDerivativeData K E x) a =
      ∑ k : Fin 2, tensorDiv (physicalAngularJet γ x)
        (fun i j => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) i j) x) k *
          angularFrame (U x) (γ x) (s x) a k := by
  dsimp only
  have he (a b : Fin 2) :
      (fun y => CKSFrame.tau (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y) a b) =ᶠ[𝓝 x]
      (fun y => angularTensorFrame U γ s (fun z => leafTensorTraceFree (γ z) (T z)) y a b) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hp, hTs] with y huy hpy hty
    exact foliation_frame_tensor_tau huy hpy hty a b
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp)) hL
    (hT.differentiableAt (by simp)) (hs.differentiableAt (by simp)) hη h0
  have hE (i : Fin 3) := (adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i).differentiableAt (by simp)
  rw [CKSFrame.tauDiv]
  simp only [frameTensorDerivative_tau hk hE, D_congr (he _ _), (he _ _).self_of_nhds]
  exact physical_leaf_tensor_divergence hU hγ hs h0 hp
    ((leafTensorTraceFree_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)) a

theorem physical_eta_normal_lie {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y)) E x
    CKSFrame.normalLieEta c (frameTensorData K E x) (frameTensorDerivativeData K E x) a =
      ∑ i : Fin 2, U x * (D (CKSRealizedRound.basis 0) (fun y => η y i) x -
        covectorLie (fun j => physicalAngularScalarJet (fun y => s y j) x)
          (fun j => physicalAngularScalarJet (fun y => η y j) x) i) *
            angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  have he (a : Fin 2) :
      (fun y => (frameTensorData (fun z => foliationTensor (U z) (L z) (η z) (T z) (s z))
        (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).eta a) =ᶠ[𝓝 x]
      (fun y => ∑ i : Fin 2, η y i * angularFrame (U y) (γ y) (s y) a i) := by
    filter_upwards [hU.continuousAt.eventually_ne h0, hT] with y huy hty
    exact foliation_frame_tensor_eta huy hty a
  rw [CKSFrame.normalLieEta, frameTensorDerivative_eta, D_congr (he a)]
  simp only [(he _).self_of_nhds]
  exact physical_normal_covector_lie hU hγ hs h0 hp hη a

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma angularTensorFrame_pair {U : PhysicalPoint → ℝ}
    {γ X T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      angularTensorFrame U γ s X x a b * angularTensorFrame U γ s T x a b) =
      tensorPair (physicalAngularJet γ x) (X x) (T x) := by
  have hg (i j : Fin 2) :
      (∑ a : Fin 2, angularFrame (U x) (γ x) (s x) a i *
        angularFrame (U x) (γ x) (s x) a j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0 hp) i) j
  calc
    _ = ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
        (∑ a : Fin 2, angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j) *
        (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b k * angularFrame (U x) (γ x) (s x) b l) *
        X x i k * T x j l := by
      simp only [angularTensorFrame, Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg, tensorPair, physicalAngularJet, inverse_eq]

lemma angularTensorFrame_covector {U : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (B : Point) (a : Fin 2) :
    (∑ b : Fin 2, angularTensorFrame U γ s T x b a *
      (∑ k : Fin 2, B k * angularFrame (U x) (γ x) (s x) b k)) =
      ∑ j : Fin 2, (∑ i : Fin 2, ∑ k : Fin 2, T x i j * (γ x)⁻¹ i k * B k) *
        angularFrame (U x) (γ x) (s x) a j := by
  have hg (i j : Fin 2) :
      (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b i *
        angularFrame (U x) (γ x) (s x) b j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0 hp) i) j
  calc
    _ = ∑ j : Fin 2, (∑ i : Fin 2, ∑ k : Fin 2, T x i j *
        (∑ b : Fin 2, angularFrame (U x) (γ x) (s x) b i * angularFrame (U x) (γ x) (s x) b k) * B k) *
        angularFrame (U x) (γ x) (s x) a j := by
      simp only [angularTensorFrame, Fin.sum_univ_two]
      ring
    _ = _ := by simp only [hg]

lemma physical_shear_components {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0) =
      angularTensorFrame U γ s (fun y => leafTensorTraceFree (γ y) (sourceChi U γ s y)) x a b := by
  dsimp only
  rw [angularTensorFrame_traceFree h0.ne' hp.self_of_nhds,
    physical_chi_representation hU hγ hs h0 hp,
    physical_mean_curvature hU hγ hs h0 hp]
  rfl

lemma shearNormSq_sum (c : CKSFrame.ConnectionData) :
    CKSFrame.shearNormSq c = ∑ a : Fin 2, ∑ b : Fin 2,
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) *
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) := by
  simp [CKSFrame.shearNormSq, CKSFrame.chi, Fin.sum_univ_two]
  ring

lemma tauNormSq_sum (t : CKSFrame.TensorData) :
    CKSFrame.tauNormSq t = ∑ a : Fin 2, ∑ b : Fin 2, CKSFrame.tau t a b * CKSFrame.tau t a b := by
  simp [CKSFrame.tauNormSq, CKSFrame.tau, Fin.sum_univ_two]
  ring

lemma shearTau_sum (c : CKSFrame.ConnectionData) (t : CKSFrame.TensorData) :
    CKSFrame.shearTau c t = ∑ a : Fin 2, ∑ b : Fin 2,
      (CKSFrame.chi c a b - CKSFrame.mean c / 2 * (if a=b then 1 else 0)) * CKSFrame.tau t a b := by
  simp [CKSFrame.shearTau, CKSFrame.chi, CKSFrame.tau, Fin.sum_univ_two]
  ring

lemma physical_shear_norm {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    CKSFrame.shearNormSq c = tensorPair (physicalAngularJet γ x) X X := by
  dsimp only
  rw [shearNormSq_sum]
  simp only [physical_shear_components hU hγ hs h0 hp]
  exact angularTensorFrame_pair h0.ne' hp.self_of_nhds

lemma physical_tau_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) :
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let τ := leafTensorTraceFree (γ x) (T x)
    CKSFrame.tauNormSq t = tensorPair (physicalAngularJet γ x) τ τ := by
  dsimp only
  rw [tauNormSq_sum]
  simp only [foliation_frame_tensor_tau h0 hp hT]
  exact angularTensorFrame_pair h0 hp

lemma physical_shear_tau {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.shearTau c t = tensorPair (physicalAngularJet γ x)
      (leafTensorTraceFree (γ x) (sourceChi U γ s x)) (leafTensorTraceFree (γ x) (T x)) := by
  dsimp only
  rw [shearTau_sum]
  simp only [physical_shear_components hU hγ hs h0 hp, foliation_frame_tensor_tau h0.ne' hp.self_of_nhds hT]
  exact angularTensorFrame_pair h0.ne' hp.self_of_nhds

lemma physical_eta_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (hT : (T x).IsHermitian) :
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.etaNormSq t = covectorPair (physicalAngularJet γ x) (η x) (η x) := by
  dsimp only
  rw [CKSFrame.etaNormSq]
  simp only [foliation_frame_tensor_eta h0 hT]
  have h := angular_frame_covector_contract (s := s x) h0 hp (η x) (η x)
  simp only [Fin.sum_univ_two] at h
  simpa only [pow_two, covectorPair, physicalAngularJet, inverse_eq, Fin.sum_univ_two] using h

lemma physical_eta_acceleration {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    CKSFrame.etaAcceleration c t = covectorPair (physicalAngularJet γ x) (η x)
      (fun i => D (CKSRealizedRound.basis i.succ) U x / U x) := by
  dsimp only
  rw [CKSFrame.etaAcceleration]
  simp only [foliation_frame_tensor_eta h0.ne' hT, physical_acceleration_components
    (hU.differentiableAt (by simp)) (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  simpa only [covectorPair, physicalAngularJet, inverse_eq] using
    angular_frame_covector_contract (s := s x) h0.ne' hp.self_of_nhds (η x)
      (fun i => D (CKSRealizedRound.basis i.succ) U x / U x)

lemma accelTensor_traceFree (c : CKSFrame.ConnectionData) (t : CKSFrame.TensorData) (a : Fin 2) :
    CKSFrame.accelTensor c t a = (t.L-t.p/2)*c.B a - ∑ b, CKSFrame.tau t b a*c.B b := by
  fin_cases a <;> simp [CKSFrame.accelTensor, CKSFrame.tau, CKSFrame.tangential, Fin.sum_univ_two] <;> ring

lemma foliation_frame_tensor_L {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hT : (T x).IsHermitian) :
    (frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x).L = L x :=
  metricPair_foliationTensor_normal h0 (η x) hT (s x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physical_mean_curvature_C1 {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.mean (frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      leafTensorTrace (γ x) (sourceChi U γ s x) := by
  simp only [CKSFrame.mean, frameConnectionField, CKSFrame.extractConnection]
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    leaf_frame_chi hU hγ hs h0 hp, leaf_frame_chi hU hγ hs h0 hp]
  exact (Fin.sum_univ_two (fun a => angularTensorFrame U γ s (sourceChi U γ s) x a a)).symm.trans
    (angularTensorFrame_trace h0.ne' hp.self_of_nhds)

lemma physical_normal_mean {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E
    CKSFrame.normalMean (fun a => connectionFieldDerivative c (E a x) x) =
      D (E 0 x) (fun y => leafTensorTrace (γ y) (sourceChi U γ s y)) x := by
  dsimp only
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, 0 < U y := hU.continuousAt.eventually (lt_mem_nhds h0)
  have heq : (fun y => CKSFrame.mean (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y)) =ᶠ[𝓝 x]
      (fun y => leafTensorTrace (γ y) (sourceChi U γ s y)) := by
    filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
      hs1.eventually (by norm_num), hnear, hp.eventually_nhds] with y hyu hyg hys hyp hpg
    exact physical_mean_curvature_C1 (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp hpg
  have hG := foliationMetric_contDiffAt hU hγ hs h0.ne'
  have hdet := (foliationMetric_posDef h0.ne' hp.self_of_nhds (s x)).det_pos.ne'
  have hE (i : Fin 3) := adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i
  have hc (i j k : Fin 3) := (frameCoefficient_contDiffAt hG hdet hE i j k).differentiableAt (by simp)
  simp only [CKSFrame.normalMean, connectionFieldDerivative]
  have hd1 : DifferentiableAt ℝ (fun y => (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).chi11) x := hc 1 0 1
  have hd2 : DifferentiableAt ℝ (fun y => (frameConnectionField
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y).chi22) x := hc 2 0 2
  rw [← D_add _ hd1 hd2]
  exact D_congr heq _

lemma physical_tensor_derivative_L {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContinuousAt U x) (h0 : U x ≠ 0)
    (hT : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (j : Fin 3) :
    (frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x j).L =
      D (adaptedFrame (U x) (γ x) (s x) j) L x := by
  rw [frameTensorDerivative_L]
  apply D_congr
  filter_upwards [hU.eventually_ne h0, hT] with y hy hty
  exact foliation_frame_tensor_L hy hty

lemma physical_tensor_derivative_p {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hT : DifferentiableAt ℝ T x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (j : Fin 3) :
    (frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x j).p =
      D (adaptedFrame (U x) (γ x) (s x) j) (fun y => leafTensorTrace (γ y) (T y)) x := by
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp)) hL
    hT (hs.differentiableAt (by simp)) hη h0
  have hE (i : Fin 3) := (adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds i).differentiableAt (by simp)
  rw [frameTensorDerivative_p hk hE]
  apply D_congr
  filter_upwards [hU.continuousAt.eventually_ne h0, hp] with y hy hpy
  exact foliation_frame_tensor_trace hy hpy

lemma physical_tensor_tangential_trace_derivative {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : DifferentiableAt ℝ L x)
    (hT : ContDiffAt ℝ ∞ T x) (hη : DifferentiableAt ℝ η x)
    (h0 : U x ≠ 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (a : Fin 2) :
    let dt := frameTensorDerivativeData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    (dt a.succ).L + (dt a.succ).p / 2 =
      ∑ i : Fin 2, ((physicalAngularScalarJet L x).2.1 i +
        (physicalAngularScalarJet (fun y => leafTensorTrace (γ y) (T y) / 2) x).2.1 i) *
          angularFrame (U x) (γ x) (s x) a i := by
  dsimp only
  rw [physical_tensor_derivative_L hU.continuousAt h0 hTs,
    physical_tensor_derivative_p hU hγ hs hL (hT.differentiableAt (by simp)) hη h0 hp]
  have hd := (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hdiv (v : PhysicalPoint) :
      D v (fun y => leafTensorTrace (γ y) (T y) / 2) x =
        D v (fun y => leafTensorTrace (γ y) (T y)) x / 2 := by
    rw [D_div v hd (differentiableAt_const 2) (by norm_num), D_const]
    ring
  simp only [D_angular_direction, physicalAngularScalarJet, hdiv, Fin.sum_univ_two]
  ring

lemma physical_acceleration_tensor {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (hT : (T x).IsHermitian) (a : Fin 2) :
    let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let t := frameTensorData (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    CKSFrame.accelTensor c t a =
      ∑ j : Fin 2, ((L x - leafTensorTrace (γ x) (T x) / 2) * B j -
        ∑ i : Fin 2, ∑ k : Fin 2, leafTensorTraceFree (γ x) (T x) i j * (γ x)⁻¹ i k * B k) *
          angularFrame (U x) (γ x) (s x) a j := by
  dsimp only
  rw [accelTensor_traceFree, foliation_frame_tensor_L h0.ne' hT,
    foliation_frame_tensor_trace h0.ne' hp.self_of_nhds]
  simp only [foliation_frame_tensor_tau h0.ne' hp.self_of_nhds hT,
    physical_acceleration_components (hU.differentiableAt (by simp))
      (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp]
  rw [angularTensorFrame_covector h0.ne' hp.self_of_nhds]
  simp only [Fin.sum_univ_two]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 2
abbrev P := PhysicalPoint
abbrev Vect := CKSAngularGeometry.Point
abbrev Symbols := A → A → A → ℝ

def lift (v : Vect) : P := Fin.cases 0 v

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D (lift v) f x

lemma delta_expansion (v : Vect) (f : P → ℝ) (x : P) :
    delta v f x = ∑ i : A, v i * D (CKSRealizedRound.basis i.succ) f x := by
  rw [delta, D_direction_expansion, Fin.sum_univ_succ]
  simp only [lift, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]

lemma delta_mul (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y * g y) x = f x * delta v g x + g x * delta v f x :=
  D_mul _ hf hg

lemma delta_add (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y + g y) x = delta v f x + delta v g x :=
  D_add _ hf hg

lemma delta_sum (v : Vect) {x : P} (f : A → P → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    delta v (fun y => ∑ i, f i y) x = ∑ i, delta v (f i) x :=
  D_angular_sum _ f hf

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

lemma delta_moving (v : Vect) {W : P → Vect} {f : P → ℝ} {x : P}
    (hW : DifferentiableAt ℝ W x) (hf : ContDiffAt ℝ 2 f x) :
    delta v (fun y => delta (W y) f y) x =
      ∑ i : A, (W x i * delta v (D (CKSRealizedRound.basis i.succ) f) x +
        D (CKSRealizedRound.basis i.succ) f x * delta v (fun y => W y i) x) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hfi (i : A) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i.succ) f) x :=
    (contDiffAt_D hf (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [delta_expansion (W _)]
  rw [delta_sum _ (fun i y => W y i * D (CKSRealizedRound.basis i.succ) f y)
    (fun i => (hWi i).mul (hfi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact delta_mul _ (hWi i) (hfi i)

lemma delta_commutator {V W : P → Vect} {f : P → ℝ} {x : P}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hf : ContDiffAt ℝ 2 f x) :
    delta (V x) (fun y => delta (W y) f y) x -
      delta (W x) (fun y => delta (V y) f y) x = delta (bracket V W x) f x := by
  rw [delta_moving _ hW hf, delta_moving _ hV hf]
  simp only [delta_expansion, bracket, Fin.sum_univ_two]
  rw [D_comm hf (CKSRealizedRound.basis (0 : A).succ)
    (CKSRealizedRound.basis (1 : A).succ)]
  ring

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i.succ) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j.succ) (fun y => Γ y k i l) x +
    ∑ m : A, (Γ x m j l * Γ x k i m - Γ x m i l * Γ x k j m)

lemma delta_nabla (v : Vect) {Γ : P → Symbols} {W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hW : DifferentiableAt ℝ W x)
    (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    delta v (fun y => nabla Γ (W y) Z y k) x =
      delta v (fun y => delta (W y) (fun z => Z z k) y) x +
      ∑ i : A, ∑ j : A,
        (W x i * Z x j * delta v (fun y => Γ y k i j) x +
          Γ x k i j * (W x i * delta v (fun y => Z y j) x +
            Z x j * delta v (fun y => W y i) x)) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hZi (i : A) := contDiffAt_pi.mp hZ i
  have hdZi (i j : A) : DifferentiableAt ℝ
      (D (CKSRealizedRound.basis i.succ) (fun y => Z y j)) x :=
    (contDiffAt_D (hZi j) (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hΓi (a i j : A) : DifferentiableAt ℝ (fun y => Γ y a i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hΓ a) i) j
  have hvZ : DifferentiableAt ℝ (fun y => delta (W y) (fun z => Z z k) y) x := by
    simp only [delta_expansion]
    exact DifferentiableAt.fun_sum fun i _ => (hWi i).mul (hdZi i k)
  have ht (i j : A) : DifferentiableAt ℝ
      (fun y => W y i * Z y j * Γ y k i j) x :=
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))).mul (hΓi k i j)
  have hs (i : A) : DifferentiableAt ℝ (fun y => ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun j _ => ht i j
  have hss : DifferentiableAt ℝ (fun y => ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun i _ => hs i
  change delta v (fun y => delta (W y) (fun z => Z z k) y +
    ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x = _
  rw [delta_add _ hvZ hss, delta_sum _ _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [delta_sum _ _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [delta_mul v (f := fun y => W y i * Z y j) (g := fun y => Γ y k i j)
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))) (hΓi k i j),
    delta_mul v (f := fun y => W y i) (g := fun y => Z y j)
      (hWi i) ((hZi j).differentiableAt (by norm_num))]

theorem curvature_coordinate {Γ : P → Symbols} {V W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    curvature Γ V W Z x k = ∑ i : A, ∑ j : A, ∑ l : A,
      V x i * W x j * Z x l * coordCurvature Γ x k l i j := by
  change (delta (V x) (fun y => nabla Γ (W y) Z y k) x +
      ∑ i : A, ∑ j : A, V x i * nabla Γ (W x) Z x j * Γ x k i j) -
    (delta (W x) (fun y => nabla Γ (V y) Z y k) x +
      ∑ i : A, ∑ j : A, W x i * nabla Γ (V x) Z x j * Γ x k i j) -
    (delta (bracket V W x) (fun y => Z y k) x +
      ∑ i : A, ∑ j : A, bracket V W x i * Z x j * Γ x k i j) = _
  rw [delta_nabla _ hΓ hW hZ, delta_nabla _ hΓ hV hZ]
  have hc := delta_commutator hV hW (contDiffAt_pi.mp hZ k)
  rw [sub_eq_iff_eq_add.mp hc]
  simp only [nabla, coordCurvature, bracket, delta_expansion, Fin.sum_univ_two]
  ring

lemma nabla_congr {Γ : P → Symbols} {v : Vect} {W Z : P → Vect} {x : P}
    (h : W =ᶠ[𝓝 x] Z) : nabla Γ v W x = nabla Γ v Z x := by
  ext k
  simp only [nabla, h.self_of_nhds]
  congr 1
  apply D_congr
  filter_upwards [h] with y hy
  rw [hy]

lemma nabla_expansion {Γ : P → Symbols} (v : Vect) {x : P}
    {F : A → P → ℝ} {E : A → P → Vect}
    (hF : ∀ a, DifferentiableAt ℝ (F a) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x) (k : A) :
    nabla Γ v (fun y k => ∑ m : A, F m y * E m y k) x k =
      ∑ m : A, (delta v (F m) x * E m x k + F m x * nabla Γ v (E m) x k) := by
  change delta v (fun y => ∑ m : A, F m y * E m y k) x + _ = _
  rw [delta_sum v _ (fun m => (hF m).fun_mul (differentiableAt_pi.mp (hE m) k))]
  simp_rw [delta_mul v (hF _) (differentiableAt_pi.mp (hE _) k)]
  simp only [nabla, Fin.sum_univ_two]
  ring

lemma nabla_direction_expansion (Γ : P → Symbols) (f : A → ℝ) (E : A → Vect)
    (Z : P → Vect) (x : P) (k : A) :
    nabla Γ (fun i => ∑ a : A, f a * E a i) Z x k =
      ∑ a : A, f a * nabla Γ (E a) Z x k := by
  simp only [nabla, delta_expansion, Fin.sum_univ_two]
  ring

lemma nabla_torsion {Γ : P → Symbols} {V W : P → Vect} {x : P}
    (hs : ∀ k i j, Γ x k i j = Γ x k j i) :
    nabla Γ (V x) W x - nabla Γ (W x) V x = bracket V W x := by
  ext k
  simp only [nabla, bracket, Pi.sub_apply, Fin.sum_univ_two]
  rw [hs k 1 0]
  ring

def frameCurvature (F : P → Symbols) (E : A → P → Vect) (x : P)
    (a b d c : A) : ℝ :=
  delta (E a x) (fun y => F y b d c) x - delta (E b x) (fun y => F y a d c) x +
    ∑ m : A, (F x b d m * F x a m c - F x a d m * F x b m c -
      (F x a b m - F x b a m) * F x m d c)

lemma nabla_second_frame {Γ F : P → Symbols} {E : A → P → Vect} {x : P}
    (hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x)
    (hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (E a y) (E b) y k = ∑ c : A, F y a b c * E c y k)
    (a b d k : A) :
    nabla Γ (E a x) (fun y => nabla Γ (E b y) (E d) y) x k =
      ∑ m : A, (delta (E a x) (fun y => F y b d m) x * E m x k +
        F x b d m * ∑ c : A, F x a m c * E c x k) := by
  have h : (fun y => nabla Γ (E b y) (E d) y) =ᶠ[𝓝 x]
      (fun y k => ∑ c : A, F y b d c * E c y k) := by
    filter_upwards [hc] with y hy
    exact funext (hy b d)
  rw [nabla_congr h, nabla_expansion _ (hF b d) hE]
  simp only [hc.self_of_nhds]

theorem curvature_frame {Γ F : P → Symbols} {E : A → P → Vect} {x : P}
    (hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x)
    (hE : ∀ a, DifferentiableAt ℝ (E a) x)
    (hs : ∀ k i j, Γ x k i j = Γ x k j i)
    (hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (E a y) (E b) y k = ∑ c : A, F y a b c * E c y k)
    (a b d k : A) :
    curvature Γ (E a) (E b) (E d) x k =
      ∑ c : A, frameCurvature F E x a b d c * E c x k := by
  have hb : bracket (E a) (E b) x =
      fun i => ∑ m : A, (F x a b m - F x b a m) * E m x i := by
    rw [← nabla_torsion hs]
    ext i
    simp only [Pi.sub_apply, hc.self_of_nhds, Fin.sum_univ_two]
    ring
  change nabla Γ (E a x) (fun y => nabla Γ (E b y) (E d) y) x k -
    nabla Γ (E b x) (fun y => nabla Γ (E a y) (E d) y) x k -
    nabla Γ (bracket (E a) (E b) x) (E d) x k = _
  rw [nabla_second_frame hF hE hc, nabla_second_frame hF hE hc, hb,
    nabla_direction_expansion]
  simp only [hc.self_of_nhds, frameCurvature, Fin.sum_univ_two]
  ring

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped BigOperators Topology ContDiff NNReal Matrix.Norms.Elementwise
lemma physical_component_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => q y i k) x := by
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma physical_inverse_component_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : I) :
    DifferentiableAt ℝ (fun y => inverse (q y) i k) x := by
  unfold inverse
  apply CKSCalculus.diffAt_div
  · fin_cases i <;> fin_cases k <;> dsimp <;>
      first | exact (physical_component_diff hq _ _).differentiableAt (by norm_num)
            | exact ((physical_component_diff hq _ _).differentiableAt (by norm_num)).neg
  · exact ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  · exact h0

lemma physical_D_determinant {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (e : PhysicalPoint) :
    D e (fun y => determinant (q y)) x =
      q x 0 0 * D e (fun y => q y 1 1) x + q x 1 1 * D e (fun y => q y 0 0) x -
      (q x 0 1 * D e (fun y => q y 1 0) x + q x 1 0 * D e (fun y => q y 0 1) x) := by
  have hd i k := (physical_component_diff hq i k).differentiableAt (by norm_num)
  unfold determinant
  rw [D_sub e ((hd 0 0).fun_mul (hd 1 1)) ((hd 0 1).fun_mul (hd 1 0)),
    D_mul e (hd 0 0) (hd 1 1), D_mul e (hd 0 1) (hd 1 0)]

theorem physical_derivative_inverse {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a b : I) :
    D (CKSRealizedRound.basis s.succ) (fun y => inverse (q y) a b) x =
      inverseDerivative (physicalAngularJet q x) s a b := by
  have hd i k := (physical_component_diff hq i k).differentiableAt (by norm_num)
  have hdet : DifferentiableAt ℝ (fun y => determinant (q y)) x :=
    ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  have hdneg i k : D (CKSRealizedRound.basis s.succ) (fun y => -(q y i k)) x =
      - D (CKSRealizedRound.basis s.succ) (fun y => q y i k) x := by
    unfold D
    rw [fderiv_fun_neg]
    rfl
  unfold inverseDerivative
  simp only [physicalAngularJet, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> dsimp [inverse] <;>
    rw [D_div _ (by first | exact hd _ _ | exact (hd _ _).neg) hdet h0, physical_D_determinant hq] <;>
    (try rw [hdneg]) <;> dsimp [inverse,determinant] <;> field_simp <;> ring

lemma physical_D_sum {α : Type*} (u : Finset α) (f : α → PhysicalPoint → ℝ) (e x : PhysicalPoint)
    (hf : ∀ i ∈ u, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i ∈ u, f i y) x = ∑ i ∈ u, D e (f i) x := by
  simp only [D, fderiv_fun_sum hf, sum_apply]

lemma physical_D_div_const (e : PhysicalPoint) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    D e (fun y => f y/c) x = D e f x/c := by
  simp only [div_eq_mul_inv]
  rw [D_mul e hf (differentiableAt_const _),D_const]
  ring

lemma physical_first_diff {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x) (a i k : I) :
    DifferentiableAt ℝ (D (CKSRealizedRound.basis a.succ) (fun y => q y i k)) x :=
  (contDiffAt_D (physical_component_diff hq i k) (m := 1) (by norm_num) (CKSRealizedRound.basis a.succ)).differentiableAt (by norm_num)

theorem physical_derivative_connection {q : PhysicalPoint → Mat} {x : PhysicalPoint} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a i k : I) :
    D (CKSRealizedRound.basis s.succ) (fun y => christoffel (physicalAngularJet q y) a i k) x = christoffelDerivative (physicalAngularJet q x) s a i k := by
  let b (l : I) (y : PhysicalPoint) :=
    D (CKSRealizedRound.basis i.succ) (fun z => q z k l) y + D (CKSRealizedRound.basis k.succ) (fun z => q z i l) y - D (CKSRealizedRound.basis l.succ) (fun z => q z i k) y
  have hb l : DifferentiableAt ℝ (b l) x :=
    ((physical_first_diff hq i k l).fun_add (physical_first_diff hq k i l)).fun_sub (physical_first_diff hq l i k)
  have hterm l : DifferentiableAt ℝ (fun y => inverse (q y) a l * b l y) x :=
    (physical_inverse_component_diff hq h0 a l).fun_mul (hb l)
  have hsum : DifferentiableAt ℝ (fun y => ∑ l : I, inverse (q y) a l*b l y) x :=
    DifferentiableAt.fun_sum fun l hl => hterm l
  change D (CKSRealizedRound.basis s.succ) (fun y => (∑ l : I, inverse (q y) a l*b l y)/2) x = _
  rw [physical_D_div_const _ hsum]
  have hdsum := physical_D_sum Finset.univ (fun l y => inverse (q y) a l*b l y) (CKSRealizedRound.basis s.succ) x (fun l hl => hterm l)
  rw [hdsum]
  unfold christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [D_mul _ (physical_inverse_component_diff hq h0 a l) (hb l), physical_derivative_inverse hq h0]
  have hdb : D (CKSRealizedRound.basis s.succ) (b l) x =
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis i.succ) (fun y => q y k l)) x +
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis k.succ) (fun y => q y i l)) x -
      D (CKSRealizedRound.basis s.succ) (D (CKSRealizedRound.basis l.succ) (fun y => q y i k)) x := by
    dsimp [b]
    rw [D_sub _ ((physical_first_diff hq i k l).fun_add (physical_first_diff hq k i l)) (physical_first_diff hq l i k),
      D_add _ (physical_first_diff hq i k l) (physical_first_diff hq k i l)]
  rw [hdb]
  dsimp [physicalAngularJet,b]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLeafCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : Mat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

lemma pair_frame_sum (γ : Mat) (E : A → Vect)
    (ho : ∀ a b, pair γ (E a) (E b) = if a = b then 1 else 0)
    (f : A → ℝ) (a : A) :
    pair γ (fun k => ∑ c : A, f c * E c k) (E a) = f a := by
  calc
    _ = ∑ c : A, f c * pair γ (E c) (E a) := by
      simp only [pair, Fin.sum_univ_two]
      ring
    _ = _ := by simp [ho]

lemma inverse_metric_trace {γ : Mat} (hp : γ.PosDef) (k i : A) :
    (∑ m : A, γ k m * γ⁻¹ i m) = if k = i then 1 else 0 := by
  have h : (γ * γ⁻¹) k i = (1 : Mat) k i :=
    congrFun (congrFun (Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) k) i
  simpa only [Matrix.mul_apply, inverse_symm_entry hp, Matrix.one_apply] using h

theorem scalar_frame_contraction {γ : Mat} (hp : γ.PosDef) (E : A → Vect)
    (hg : ∀ i j, (∑ a : A, E a i * E a j) = γ⁻¹ i j)
    (R : A → A → A → A → ℝ) :
    (∑ a : A, ∑ b : A, pair γ
      (fun k => ∑ i : A, ∑ j : A, ∑ l : A, E a i * E b j * E b l * R k l i j)
      (E a)) = ∑ j : A, ∑ l : A, γ⁻¹ j l * ∑ k : A, R k l k j := by
  calc
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (∑ m : A, γ k m * (∑ a : A, E a i * E a m)) *
          (∑ b : A, E b j * E b l) * R k l i j := by
      simp only [pair, Fin.sum_univ_two]
      ring
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (if k = i then 1 else 0) * γ⁻¹ j l * R k l i j := by
      simp only [hg, inverse_metric_trace hp]
    _ = _ := by
      simp only [Fin.sum_univ_two]
      simp
      ring

end
end CKSLeafCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSLeafCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lift_angularFrame (U : ℝ) (γ : Mat) (s : Point) (a : Fin 2) :
    lift (angularFrame U γ s a) = adaptedFrame U γ s a.succ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (adaptedFrame_radial U γ s a).symm
  · rfl

lemma leafConnection_derivative (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) (a b d : Fin 2) :
    CKSFrame.leafConnection (connectionFieldDerivative c e x) a b d =
      D e (fun y => CKSFrame.leafConnection (c y) a b d) x := by
  fin_cases b <;> fin_cases d <;>
    simp [CKSFrame.leafConnection, connectionFieldDerivative, D, fderiv_fun_neg]

lemma physical_christoffel_differentiable {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ 2 γ x) (hp : (γ x).PosDef) :
    DifferentiableAt ℝ (fun y => christoffel (physicalAngularJet γ y)) x := by
  have h0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.det_pos.ne'
  refine differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun i =>
    differentiableAt_pi.mpr fun k => ?_
  change DifferentiableAt ℝ (fun y => (∑ l : Fin 2, inverse (γ y) a l *
    (D (CKSRealizedRound.basis i.succ) (fun z => γ z k l) y +
      D (CKSRealizedRound.basis k.succ) (fun z => γ z i l) y -
      D (CKSRealizedRound.basis l.succ) (fun z => γ z i k) y)) / 2) x
  apply diffAt_div _ (differentiableAt_const (2 : ℝ)) (by norm_num)
  exact DifferentiableAt.fun_sum fun l _ =>
    (physical_inverse_component_diff hγ h0 a l).fun_mul
      (((physical_first_diff hγ i k l).fun_add (physical_first_diff hγ k i l)).fun_sub
        (physical_first_diff hγ l i k))

lemma physical_christoffel_symmetric {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a i j : Fin 2) :
    christoffel (physicalAngularJet γ x) a i j =
      christoffel (physicalAngularJet γ x) a j i := by
  have hd (l : Fin 2) : D (CKSRealizedRound.basis l.succ) (fun y => γ y i j) x =
      D (CKSRealizedRound.basis l.succ) (fun y => γ y j i) x := by
    apply D_congr
    filter_upwards [hp] with y hy
    exact (hermitian_real_symmetry hy.isHermitian i j).symm
  simp only [christoffel, physicalAngularJet, hd]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma physical_nabla_angularFrame {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (h0 : U x ≠ 0) (hp : (γ x).PosDef) (a b k : Fin 2) :
    nabla (fun y => christoffel (physicalAngularJet γ y))
      (angularFrame (U x) (γ x) (s x) a)
      (fun y => angularFrame (U y) (γ y) (s y) b) x k =
      ∑ c : Fin 2, inducedFrameCoefficient U γ s x a b c *
        angularFrame (U x) (γ x) (s x) c k := by
  have h := induced_connection_covector (s := s) h0 hp a b (Pi.single k 1)
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [nabla, delta, lift_angularFrame]
  exact h.symm

theorem physical_leaf_curvature_coordinates {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b d k : Fin 2) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun i => connectionFieldDerivative (frameConnectionField G E) (E i x) x
    (∑ z : Fin 2, CKSFrame.leafCurvature c dc a b d z *
      angularFrame (U x) (γ x) (s x) z k) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
          angularFrame (U x) (γ x) (s x) d l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j := by
  let G := fun y => foliationMetric (U y) (γ y) (s y)
  let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
  let e := fun a y => angularFrame (U y) (γ y) (s y) a
  let F := fun y => CKSFrame.leafConnection (frameConnectionField G E y)
  let Γ := fun y => christoffel (physicalAngularJet γ y)
  have hactual := foliation_actualAdaptedAt hU hγ hs h0 hp
  have hE : ∀ i, ContDiffAt ℝ ∞ (E i) x :=
    adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds
  have he : ∀ i, ContDiffAt ℝ ∞ (e i) x := by
    intro i
    exact contDiffAt_pi.mpr fun j => contDiffAt_pi.mp (hE i.succ) j.succ
  have hFnear : ∀ᶠ y in 𝓝 x, ∀ a b c,
      F y a b c = frameCoefficient G E y a.succ b.succ c.succ := by
    filter_upwards [hactual] with y hy
    intro a b c
    rw [show F y a b c = CKSFrame.connection (frameConnectionField G E y)
      a.succ b.succ c.succ from extracted_leaf_connection _ a b c,
      frame_connection_actual hy]
  have hF : ∀ a b c, DifferentiableAt ℝ (fun y => F y a b c) x := by
    intro a b c
    apply ((frameCoefficient_contDiffAt (foliationMetric_contDiffAt hU hγ hs h0)
      (foliationMetric_posDef h0 hp.self_of_nhds (s x)).det_pos.ne' hE
      a.succ b.succ c.succ).differentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [hFnear] with y hy
    exact hy a b c
  have hc : ∀ᶠ y in 𝓝 x, ∀ a b k,
      nabla Γ (e a y) (e b) y k = ∑ c : Fin 2, F y a b c * e c y k := by
    filter_upwards [hFnear, hp, hU.continuousAt.eventually_ne h0] with y hy hyp hy0
    intro a b k
    have hind (c : Fin 2) : F y a b c = inducedFrameCoefficient U γ s y a b c :=
      (hy a b c).trans (physical_leaf_connection hyp hy0 a b c)
    simp only [hind]
    exact physical_nabla_angularFrame (s := s) hy0 hyp a b k
  have hγ2 : ContDiffAt ℝ 2 γ x :=
    hγ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hframe := curvature_frame hF (fun i => (he i).differentiableAt (by simp))
    (physical_christoffel_symmetric hp) hc a b d k
  have hcoord := curvature_coordinate (physical_christoffel_differentiable hγ2 hp.self_of_nhds)
    ((he a).differentiableAt (by simp)) ((he b).differentiableAt (by simp))
    ((he d).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) k
  have hcurv (z : Fin 2) : frameCurvature F e x a b d z =
      CKSFrame.leafCurvature (frameConnectionField G E x)
        (fun i => connectionFieldDerivative (frameConnectionField G E) (E i x) x) a b d z := by
    simp only [frameCurvature, CKSFrame.leafCurvature, leafConnection_derivative,
      F, e, E, delta, lift_angularFrame]
  exact (by simpa only [hcurv] using hframe.symm.trans hcoord)

lemma physical_coordinate_scalar {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ 2 γ x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    (∑ j : Fin 2, ∑ l : Fin 2, (γ x)⁻¹ j l *
      ∑ k : Fin 2, coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j) =
      scalarCurvature (physicalAngularJet γ x) := by
  have h0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.self_of_nhds.det_pos.ne'
  have hd (a k i j : Fin 2) :
      christoffelDerivative (physicalAngularJet γ x) a k i j =
        christoffelDerivative (physicalAngularJet γ x) a k j i := by
    rw [← physical_derivative_connection hγ h0, ← physical_derivative_connection hγ h0]
    apply D_congr
    filter_upwards [hp.eventually_nhds] with y hy
    exact physical_christoffel_symmetric hy k i j
  have hr (l j : Fin 2) :
      (∑ k : Fin 2, coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j) =
        ricci (physicalAngularJet γ x) l j := by
    have ht (k : Fin 2) :
        coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l k j =
        (christoffelDerivative (physicalAngularJet γ x) k k l j -
          christoffelDerivative (physicalAngularJet γ x) j k l k) +
        ∑ m : Fin 2, (christoffel (physicalAngularJet γ x) k k m *
          christoffel (physicalAngularJet γ x) m l j -
          christoffel (physicalAngularJet γ x) k j m *
          christoffel (physicalAngularJet γ x) m l k) := by
      rw [coordCurvature, physical_derivative_connection hγ h0,
        physical_derivative_connection hγ h0, hd k k j l, hd j k k l]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [physical_christoffel_symmetric hp m j l, physical_christoffel_symmetric hp m k l]
      ring
    simp only [ht, Finset.sum_add_distrib, ricci]
  calc
    _ = ∑ j : Fin 2, ∑ l : Fin 2, (γ x)⁻¹ j l * ricci (physicalAngularJet γ x) l j := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      congr 1
      exact hr l j
    _ = _ := by
      change _ = ∑ j : Fin 2, ∑ l : Fin 2, inverse (γ x) j l * ricci (physicalAngularJet γ x) j l
      simp only [inverse_eq, Fin.sum_univ_two]
      rw [inverse_symm_entry hp.self_of_nhds 1 0]
      ring

lemma angularFrame_orthonormal_pair {U : ℝ} {γ : Mat} (hU : U ≠ 0)
    (hp : γ.PosDef) (s : Point) (a b : Fin 2) :
    pair γ (angularFrame U γ s a) (angularFrame U γ s b) = if a = b then 1 else 0 := by
  have h := adaptedFrame_orthonormal hU hp s a.succ b.succ
  rw [metricPair_tangent_expanded U γ s _ _ (adaptedFrame_radial U γ s a)
    (adaptedFrame_radial U γ s b)] at h
  simpa only [pair, angularFrame, Fin.sum_univ_two, Fin.succ_inj,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using h

theorem physical_leaf_scalar {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    CKSFrame.leafScalar c dc = scalarCurvature (physicalAngularJet γ x) := by
  dsimp only
  let G := fun y => foliationMetric (U y) (γ y) (s y)
  let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
  let c := frameConnectionField G E x
  let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
  let e : Fin 2 → Point := fun a => angularFrame (U x) (γ x) (s x) a
  have ho := angularFrame_orthonormal_pair h0.ne' hp.self_of_nhds (s x)
  have hg (i j : Fin 2) : (∑ a : Fin 2, e a i * e a j) = (γ x)⁻¹ i j :=
    congrFun (congrFun (angularFrame_gram h0.ne' hp.self_of_nhds) i) j
  have hc (a b : Fin 2) :
      (fun k => ∑ z : Fin 2, CKSFrame.leafCurvature c dc a b b z * e z k) =
        (fun k => ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
          e a i * e b j * e b l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j) := by
    exact funext fun k => physical_leaf_curvature_coordinates hU hγ hs h0.ne' hp a b b k
  calc
    _ = ∑ a : Fin 2, ∑ b : Fin 2, pair (γ x)
        (fun k => ∑ z : Fin 2, CKSFrame.leafCurvature c dc a b b z * e z k) (e a) := by
      change (∑ a : Fin 2, ∑ b : Fin 2, CKSFrame.leafCurvature c dc a b b a) = _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact (pair_frame_sum (γ x) e ho (fun z => CKSFrame.leafCurvature c dc a b b z) a).symm
    _ = ∑ a : Fin 2, ∑ b : Fin 2, pair (γ x)
        (fun k => ∑ i : Fin 2, ∑ j : Fin 2, ∑ l : Fin 2,
          e a i * e b j * e b l *
            coordCurvature (fun y => christoffel (physicalAngularJet γ y)) x k l i j) (e a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hc a b]
    _ = _ := by
      rw [scalar_frame_contraction hp.self_of_nhds e hg]
      exact physical_coordinate_scalar
        (hγ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_source_constraints {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let H := fun y => leafTensorTrace (γ y) (sourceChi U γ s y)
    let p := fun y => leafTensorTrace (γ y) (T y)
    let X := fun y => leafTensorTraceFree (γ y) (sourceChi U γ s y)
    let τ := fun y => leafTensorTraceFree (γ y) (T y)
    let q := physicalAngularJet γ x
    let ηj := fun i => physicalAngularScalarJet (fun y => η y i) x
    let τj := fun i j => physicalAngularScalarJet (fun y => τ y i j) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    (actualFrameScalar G E x + ((G x)⁻¹ * K x).trace ^ 2 -
        ((G x)⁻¹ * K x * (G x)⁻¹ * K x).trace) / 2 =
      scalarCurvature q / 2 - D (E 0 x) H x -
        lapseLaplacian q (physicalAngularScalarJet U x) - 3/4 * (H x)^2 -
        tensorPair q (X x) (X x) / 2 + L x * p x + (p x)^2 / 4 -
        tensorPair q (τ x) (τ x) / 2 - covectorPair q (η x) (η x) ∧
    coordinateMomentum G K x (E 0 x) =
      normalMomentum q (H x) (L x) (p x / 2) (D (E 0 x) p x)
        (X x) (τ x) ηj B ∧
    ∀ a, coordinateMomentum G K x (E a.succ x) =
      ∑ i : Fin 2, angularMomentum q (H x) (U x)
        (physicalAngularScalarJet L x) (physicalAngularScalarJet (fun y => p y / 2) x)
        (fun j => physicalAngularScalarJet (fun y => s y j) x) ηj τj
        (fun j => D (CKSRealizedRound.basis 0) (fun y => η y j) x) B i *
          angularFrame (U x) (γ x) (s x) a i
 := by
  dsimp only
  have hUd := hU.differentiableAt (by simp)
  have hγd := hγ.differentiableAt (by simp)
  have hsd := hs.differentiableAt (by simp)
  have hLd := hL.differentiableAt (by simp)
  have hηd := hη.differentiableAt (by simp)
  have hTd := hT.differentiableAt (by simp)
  have hK := foliationTensor_differentiableAt hUd hLd hTd hsd hηd h0.ne'
  have hKs : ∀ᶠ y in 𝓝 x, (foliationTensor (U y) (L y) (η y) (T y) (s y)).IsHermitian := by
    filter_upwards [hTs] with y hy
    exact foliationTensor_hermitian _ _ _ hy _
  obtain ⟨hC, hQ, hZ⟩ := physical_foliation_constraints hU hγ hs h0 hp hK hKs
  dsimp only at hC hQ hZ
  constructor
  · rw [hC, physical_leaf_scalar hU hγ hs h0 hp,
      physical_normal_mean hU hγ hs h0 hp,
      physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      physical_shear_norm hU hγ hs h0 hp,
      foliation_frame_tensor_L h0.ne' hTs.self_of_nhds,
      foliation_frame_tensor_trace h0.ne' hp.self_of_nhds,
      physical_tau_norm h0.ne' hp.self_of_nhds hTs.self_of_nhds,
      physical_eta_norm h0.ne' hp.self_of_nhds hTs.self_of_nhds]
    have hA := physical_acceleration_laplacian hU hγ hs h0 hp
    dsimp only at hA
    linear_combination hA
  constructor
  · rw [hQ, physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      foliation_frame_tensor_L h0.ne' hTs.self_of_nhds,
      foliation_frame_tensor_trace h0.ne' hp.self_of_nhds,
      physical_shear_tau hU hγ hs h0 hp hTs.self_of_nhds,
      physical_tensor_derivative_p hU hγ hs hLd hTd hηd h0.ne' hp,
      physical_eta_divergence hU hγ hs hηd h0.ne' hp hTs,
      physical_eta_acceleration hU hγ hs h0 hp hTs.self_of_nhds]
    rfl
  · intro a
    rw [hZ a, physical_eta_normal_lie hU hγ hs hηd h0.ne' hp hTs,
      physical_mean_curvature_C1 hUd hγd hsd h0 hp,
      foliation_frame_tensor_eta h0.ne' hTs.self_of_nhds,
      physical_tau_divergence hU hγ hs hLd hηd hT h0.ne' hp hTs,
      physical_tensor_tangential_trace_derivative hU hγ hs hLd hT hηd h0.ne' hp hTs,
      physical_acceleration_tensor hU hγ hs h0 hp hTs.self_of_nhds]
    simp only [angularMomentum, physicalAngularScalarJet, physicalAngularJet, inverse_eq, Fin.sum_univ_two]
    ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceChi_contDiffAt {U : PhysicalPoint → ℝ} {γ : PhysicalPoint → Mat}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) : ContDiffAt ℝ ∞ (sourceChi U γ s) x := by
  have hg (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hgd (e) (i j) : ContDiffAt ℝ ∞ (D e (fun y => γ y i j)) x :=
    contDiffAt_D (hg i j) (by simp) e
  have hsd (e) (i) : ContDiffAt ℝ ∞ (D e (fun y => s y i)) x :=
    contDiffAt_D (hsc i) (by simp) e
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [sourceChi, Fin.sum_univ_two]
  fun_prop

theorem physical_source_mass_identity {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * leafTensorTrace (γ x) (sourceChi U γ s x) / 2) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let H := fun y => leafTensorTrace (γ y) (sourceChi U γ s y)
    let p := fun y => leafTensorTrace (γ y) (T y)
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    let τ := leafTensorTraceFree (γ x) (T x)
    let q := physicalAngularJet γ x
    let ηj := fun i => physicalAngularScalarJet (fun y => η y i) x
    let B := fun i => D (CKSRealizedRound.basis i.succ) U x / U x
    let F := CKSFrame.massField H p
    let u := x 0 * H x / 2
    let v := x 0 * p x / 2
    (actualFrameScalar G E x + ((G x)⁻¹ * K x).trace ^ 2 -
        ((G x)⁻¹ * K x * (G x)⁻¹ * K x).trace) / 2 -
      v/u * coordinateMomentum G K x (E 0 x) =
      2 * D (E 0 x) F x / (u*(x 0)^2) +
      (scalarCurvature q / 2 - 1/(x 0)^2) +
      (U x/u - 1) * (2 - 6*F x/(x 0))/(x 0)^2 -
      lapseLaplacian q (physicalAngularScalarJet U x) -
      (tensorPair q X X + tensorPair q τ τ) / 2 +
      v/u * tensorPair q X τ - covectorPair q (η x) (η x) -
      v/u * (covectorDiv q ηj - 2*covectorPair q (η x) B)
 := by
  dsimp only
  have hh := (leafTensorTrace_contDiffAt hγ (sourceChi_contDiffAt hU hγ hs)
    hp.self_of_nhds).differentiableAt (by simp)
  have ht := (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hd := CKSFrame.normal_mass_derivative hh ht (U x) (s x)
  change D (adaptedFrame (U x) (γ x) (s x) 0) _ x = _ at hd
  obtain ⟨hC, hQ, _⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hC hQ
  rw [hC, hQ, hd]
  have hnvec : CKSFrame.normalVector (U x) (s x) = adaptedFrame (U x) (γ x) (s x) 0 := rfl
  rw [hnvec]
  have hn : leafTensorTrace (γ x) (sourceChi U γ s x) ≠ 0 := by
    intro h; simp [h] at hu
  simp only [normalMomentum, CKSFrame.massField, physicalAngularScalarJet]
  simp only [covectorPair, div_eq_mul_inv]
  field_simp [hr.ne', hn]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x + ((G x)⁻¹*K x).trace^2 -
    ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2

def physicalDEC (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop :=
  Real.sqrt (metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x)) ≤
    physicalEnergy G K E x

def sourceH (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) : ℝ :=
  leafTensorTrace (γ x) (sourceChi U γ s x)
def sourceP (γ T : PhysicalPoint → Mat) (x : PhysicalPoint) : ℝ :=
  leafTensorTrace (γ x) (T x)
def sourceB (U : PhysicalPoint → ℝ) (x : PhysicalPoint) : Point :=
  fun i => D (CKSRealizedRound.basis i.succ) U x / U x

def sourceQ (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) : ℝ :=
  normalMomentum (physicalAngularJet γ x) (sourceH U γ s x) (L x)
    (sourceP γ T x / 2) (D (adaptedFrame (U x) (γ x) (s x) 0) (sourceP γ T) x)
    (leafTensorTraceFree (γ x) (sourceChi U γ s x)) (leafTensorTraceFree (γ x) (T x))
    (fun i => physicalAngularScalarJet (fun y => η y i) x) (sourceB U x)

def sourceZ (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) : Point :=
  angularMomentum (physicalAngularJet γ x) (sourceH U γ s x) (U x)
    (physicalAngularScalarJet L x) (physicalAngularScalarJet (fun y => sourceP γ T y / 2) x)
    (fun i => physicalAngularScalarJet (fun y => s y i) x)
    (fun i => physicalAngularScalarJet (fun y => η y i) x)
    (fun i j => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) i j) x)
    (fun i => D (CKSRealizedRound.basis 0) (fun y => η y i) x) (sourceB U x)

theorem physical_source_momentum_norm {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) =
      (sourceQ U L γ T s η x)^2 +
      covectorPair (physicalAngularJet γ x) (sourceZ U L γ T s η x) (sourceZ U L γ T s η x) := by
  dsimp only
  have hk := foliationTensor_differentiableAt (hU.differentiableAt (by simp))
    (hL.differentiableAt (by simp)) (hT.differentiableAt (by simp))
    (hs.differentiableAt (by simp)) (hη.differentiableAt (by simp)) h0.ne'
  have he := (foliation_actualAdaptedAt hU hγ hs h0.ne' hp).self_of_nhds
  rw [← physical_momentum_frame_norm he hk]
  simp_rw [actualFrameMomentum_coordinate he hk]
  rw [Fin.sum_univ_succ]
  obtain ⟨_, hQ, hZ⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hQ hZ
  rw [hQ]
  change (sourceQ U L γ T s η x)^2 + _ = _
  congr 1
  simp_rw [hZ]
  change (∑ a, (∑ i, sourceZ U L γ T s η x i * angularFrame (U x) (γ x) (s x) a i)^2) = _
  simp only [covectorPair, physicalAngularJet, inverse_eq]
  exact angular_covector_frame_square (s := s x) (sourceZ U L γ T s η x) h0.ne' hp.self_of_nhds

theorem physical_source_DEC_iff {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    physicalDEC G K E x ↔
      Real.sqrt ((sourceQ U L γ T s η x)^2 +
        covectorPair (physicalAngularJet γ x) (sourceZ U L γ T s η x) (sourceZ U L γ T s η x)) ≤
      physicalEnergy G K E x := by
  dsimp only [physicalDEC]
  rw [physical_source_momentum_norm hU hγ hs hL hη hT h0 hp hTs]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def sourceD (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (y : PhysicalPoint) : ℝ :=
  y 0 * sourceH U γ s y / (2*U y)

def sourceMass (U : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) : PhysicalPoint → ℝ :=
  CKSFrame.massField (sourceH U γ s) (sourceP γ T)

def physicalBaseLapse (r : ℝ) : ℝ := r*Real.sqrt (1+(1/r)^2)

def physicalMomentumInput (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ) : MomentumInput :=
  let r := x 0
  let t := fun y => sourceP γ T y/2
  (1/r,w,rescale (1/r^2) (physicalAngularJet γ x),
    ![r^3 • ((1/physicalBaseLapse r) • physicalAngularScalarJet U x-constantJet 1),
      r^3 • (physicalAngularScalarJet t x-constantJet 1),
      r^3 • (physicalAngularScalarJet L x-constantJet (1+w/r^2)),
      r^4 • physicalAngularScalarJet (D (CKSRealizedRound.basis 0) t) x,
      r^3 • (physicalAngularScalarJet (sourceD U γ s) x-constantJet 1)],
    r^5 • (fun a => physicalAngularScalarJet (fun y => s y a) x),
    r^2 • (fun a => physicalAngularScalarJet (fun y => η y a) x),
    r • (fun a b => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) a b) x),
    r • leafTensorTraceFree (γ x) (sourceChi U γ s x),
    r^3 • (fun a => D (CKSRealizedRound.basis 0) (fun y => η y a) x))

def physicalNullInput (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ) : NullInput :=
  (physicalMomentumInput U L γ T s η x w,physicalAngularScalarJet (sourceMass U γ T s) x,
    (x 0)^2*(D (CKSRealizedRound.basis 0) (sourceMass U γ T s) x-w/(x 0*Real.sqrt (x 0))))

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma inverse_radius_smul_cancel {r : ℝ} (hr : r ≠ 0) (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (1/r)^n • (r^n • v) = v := by
  rw [smul_smul, ← mul_pow, one_div_mul_cancel hr, one_pow, one_smul]

lemma physicalBaseLapse_ne {r : ℝ} (hr : r ≠ 0) : physicalBaseLapse r ≠ 0 :=
  mul_ne_zero hr (Real.sqrt_ne_zero'.mpr (by positivity))

lemma physicalBaseLapse_eq {r : ℝ} (hr : 0 < r) :
    physicalBaseLapse r = Real.sqrt (1+r^2) := by
  calc
    physicalBaseLapse r = Real.sqrt (r^2)*Real.sqrt (1+(1/r)^2) := by
      rw [Real.sqrt_sq hr.le]; rfl
    _ = Real.sqrt (r^2*(1+(1/r)^2)) := (Real.sqrt_mul (sq_nonneg r) _).symm
    _ = Real.sqrt (1+r^2) := by congr 1; field_simp; ring

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_L (hr : x 0 ≠ 0) :
    physicalLJet (physicalMomentumInput U L γ T s η x w) = physicalAngularScalarJet L x := by
  change constantJet (1+w*(1/x 0)^2)+
    (1/x 0)^3 • ((x 0)^3 • (physicalAngularScalarJet L x-constantJet (1+w/(x 0)^2))) = _
  rw [inverse_radius_smul_cancel hr]
  have he : 1+w*(1/x 0)^2 = 1+w/(x 0)^2 := by ring
  rw [he]
  abel

lemma physical_input_t (hr : x 0 ≠ 0) :
    physicalTJet (physicalMomentumInput U L γ T s η x w) =
      physicalAngularScalarJet (fun y => sourceP γ T y/2) x := by
  change constantJet 1+(1/x 0)^3 • ((x 0)^3 •
    (physicalAngularScalarJet (fun y => sourceP γ T y/2) x-constantJet 1)) = _
  rw [inverse_radius_smul_cancel hr]
  abel

lemma physical_input_lapseJet (hr : x 0 ≠ 0) :
    constantJet 1+mz (physicalMomentumInput U L γ T s η x w)^3 •
      mc (physicalMomentumInput U L γ T s η x w) 0 =
    (1/physicalBaseLapse (x 0)) • physicalAngularScalarJet U x := by
  change constantJet 1+(1/x 0)^3 • ((x 0)^3 •
    ((1/physicalBaseLapse (x 0)) • physicalAngularScalarJet U x-constantJet 1)) = _
  rw [inverse_radius_smul_cancel hr]
  abel

lemma physical_input_speed (hr : x 0 ≠ 0) :
    normalizedSpeed (physicalMomentumInput U L γ T s η x w) = U x/x 0 := by
  have he := congrArg Prod.fst (physical_input_lapseJet U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 0).1 = (1/physicalBaseLapse (x 0))*U x at he
  rw [normalizedSpeed, he]
  change Real.sqrt (1+(1/x 0)^2) * ((1/physicalBaseLapse (x 0))*U x) = _
  unfold physicalBaseLapse
  field_simp [hr, Real.sqrt_ne_zero'.mpr (by positivity : 0 < 1+(1/x 0)^2)]

lemma physical_input_d (hr : x 0 ≠ 0) :
    nullD (physicalMomentumInput U L γ T s η x w) = sourceD U γ s x := by
  change 1+(1/x 0)^3*((x 0)^3*(sourceD U γ s x-1)) = _
  field_simp
  ring

lemma physical_input_mean (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    normalizedMean (physicalMomentumInput U L γ T s η x w) = sourceH U γ s x := by
  change 2*normalizedSpeed (physicalMomentumInput U L γ T s η x w)*
    nullD (physicalMomentumInput U L γ T s η x w) = _
  rw [physical_input_speed U L γ T s η x w hr, physical_input_d U L γ T s η x w hr]
  unfold sourceD
  field_simp

lemma physical_input_ratio (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    nullRatio (physicalMomentumInput U L γ T s η x w) = sourceP γ T x/sourceH U γ s x := by
  have he := congrArg Prod.fst (physical_input_t U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 1).1 = sourceP γ T x/2 at he
  rw [nullRatio, he,physical_input_speed U L γ T s η x w hr,
    physical_input_d U L γ T s η x w hr]
  have hd : U x/x 0*sourceD U γ s x = sourceH U γ s x/2 := by
    unfold sourceD; field_simp
  rw [hd]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]
  ring

lemma physical_input_acceleration (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^3 •
      accelerationCoefficient (physicalMomentumInput U L γ T s η x w) = sourceB U x := by
  have he := congrArg Prod.fst (physical_input_lapseJet U L γ T s η x w hr)
  change 1+mz (physicalMomentumInput U L γ T s η x w)^3 *
    (mc (physicalMomentumInput U L γ T s η x w) 0).1 = (1/physicalBaseLapse (x 0))*U x at he
  funext a
  simp only [Pi.smul_apply,smul_eq_mul,accelerationCoefficient,he]
  change (1/x 0)^3*((x 0)^3*((1/physicalBaseLapse (x 0))*
    D (CKSRealizedRound.basis a.succ) U x-0)/((1/physicalBaseLapse (x 0))*U x)) = _
  unfold sourceB
  field_simp [hr,hU,physicalBaseLapse_ne hr]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma rescale_composition (a b : ℝ) (q : Jet) :
    rescale a (rescale b q) = rescale (a*b) q := by
  apply Prod.ext
  · funext i j; simp only [rescale]; ring
  · apply Prod.ext
    · funext d i j; simp only [rescale]; ring
    · funext c d i j; simp only [rescale]; ring

lemma rescale_one (q : Jet) : rescale 1 q = q := by
  rcases q with ⟨q,d,dd⟩
  simp only [rescale,one_mul]

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_q (hr : x 0 ≠ 0) :
    rescale (1/mz (physicalMomentumInput U L γ T s η x w)^2)
      (mq (physicalMomentumInput U L γ T s η x w)) = physicalAngularJet γ x := by
  change rescale (1/(1/x 0)^2) (rescale (1/(x 0)^2) (physicalAngularJet γ x)) = _
  rw [rescale_composition]
  have he : 1/(1/x 0)^2*(1/(x 0)^2) = 1 := by field_simp
  rw [he,rescale_one]

lemma physical_input_s (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^5 • mS (physicalMomentumInput U L γ T s η x w) =
      (fun a => physicalAngularScalarJet (fun y => s y a) x) :=
  inverse_radius_smul_cancel hr 5 _

lemma physical_input_eta (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^2 • mE (physicalMomentumInput U L γ T s η x w) =
      (fun a => physicalAngularScalarJet (fun y => η y a) x) :=
  inverse_radius_smul_cancel hr 2 _

lemma physical_input_tau (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) • mT (physicalMomentumInput U L γ T s η x w) =
      (fun a b => physicalAngularScalarJet (fun y => leafTensorTraceFree (γ y) (T y) a b) x) := by
  change (1/x 0) • ((x 0) • _) = _
  rw [smul_smul,one_div_mul_cancel hr,one_smul]

lemma physical_input_X (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) • mX (physicalMomentumInput U L γ T s η x w) =
      leafTensorTraceFree (γ x) (sourceChi U γ s x) := by
  change (1/x 0) • ((x 0) • _) = _
  rw [smul_smul,one_div_mul_cancel hr,one_smul]

lemma physical_input_Er (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^3 • mEr (physicalMomentumInput U L γ T s η x w) =
      (fun a => D (CKSRealizedRound.basis 0) (fun y => η y a) x) :=
  inverse_radius_smul_cancel hr 3 _

lemma physical_input_tau_value (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w) •
      ((fun a b => (mT (physicalMomentumInput U L γ T s η x w) a b).1) : Mat) =
      leafTensorTraceFree (γ x) (T x) := by
  have he := physical_input_tau U L γ T s η x w hr
  exact congrArg (fun t : CovariantTensorJet => fun a b => (t a b).1) he

lemma physical_input_eta_value (hr : x 0 ≠ 0) :
    mz (physicalMomentumInput U L γ T s η x w)^2 •
      (fun a => (mE (physicalMomentumInput U L γ T s η x w) a).1) = η x := by
  have he := physical_input_eta U L γ T s η x w hr
  exact congrArg (fun t : CovectorJet => fun a => (t a).1) he

lemma physical_normal_derivative (f : PhysicalPoint → ℝ) :
    D (adaptedFrame (U x) (γ x) (s x) 0) f x =
      U x*(D (CKSRealizedRound.basis 0) f x-
        ∑ a : Fin 2, s x a*D (CKSRealizedRound.basis a.succ) f x) := by
  rw [D_direction_expansion,Fin.sum_univ_succ]
  change U x*D (CKSRealizedRound.basis 0) f x+
    (∑ a : Fin 2, foliationNormal (U x) (s x) a.succ*D (CKSRealizedRound.basis a.succ) f x) = _
  simp only [foliationNormal_succ,Fin.sum_univ_two]
  ring

lemma physical_input_Np (hr : x 0 ≠ 0)
    (hp : DifferentiableAt ℝ (sourceP γ T) x) :
    let p := physicalMomentumInput U L γ T s η x w
    2*normalizedSpeed p*mz p^3*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a) =
      D (adaptedFrame (U x) (γ x) (s x) 0) (sourceP γ T) x := by
  dsimp only
  rw [physical_input_speed U L γ T s η x w hr,physical_normal_derivative]
  change 2*(U x/x 0)*(1/x 0)^3*((x 0)^4*D (CKSRealizedRound.basis 0)
    (fun y => sourceP γ T y/2) x-(1/x 0)^4*∑ a : Fin 2,
      ((x 0)^5*s x a)*((x 0)^3*(D (CKSRealizedRound.basis a.succ) (fun y => sourceP γ T y/2) x-0))) = _
  simp_rw [physical_D_div_const _ hp]
  simp only [Fin.sum_univ_two]
  field_simp
  ring

lemma physical_input_Q (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hp : DifferentiableAt ℝ (sourceP γ T) x) :
    coordinateQ (physicalMomentumInput U L γ T s η x w) = sourceQ U L γ T s η x := by
  unfold coordinateQ
  rw [physical_input_q U L γ T s η x w hr,physical_input_mean U L γ T s η x w hr hU,
    physical_input_L U L γ T s η x w hr,physical_input_t U L γ T s η x w hr,
    physical_input_Np U L γ T s η x w hr hp,physical_input_X U L γ T s η x w hr,
    physical_input_tau_value U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_acceleration U L γ T s η x w hr hU]
  rfl

lemma physical_input_Z (hr : x 0 ≠ 0) (hU : U x ≠ 0) :
    coordinateZ (physicalMomentumInput U L γ T s η x w) = sourceZ U L γ T s η x := by
  funext a
  unfold coordinateZ
  rw [physical_input_q U L γ T s η x w hr,physical_input_mean U L γ T s η x w hr hU,
    physical_input_L U L γ T s η x w hr,physical_input_t U L γ T s η x w hr,
    physical_input_speed U L γ T s η x w hr,physical_input_s U L γ T s η x w hr,
    physical_input_tau U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_Er U L γ T s η x w hr,physical_input_acceleration U L γ T s η x w hr hU]
  have he : U x/x 0 / (1/x 0) = U x := by field_simp
  change angularMomentum _ _ (U x/x 0/(1/x 0)) _ _ _ _ _ _ _ _ = _
  rw [he]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lapseLaplacian_lapse_smul (q : Jet) (z : ScalarJet) {c : ℝ}
    (hc : c ≠ 0) (hz : z.1 ≠ 0) : lapseLaplacian q (c • z) = lapseLaplacian q z := by
  unfold lapseLaplacian
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_two]
  field_simp

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

lemma physical_input_massrow (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hH : sourceH U γ s x ≠ 0) :
    let p := physicalNullInput U L γ T s η x w
    2*(mw (nP p)/(x 0*Real.sqrt (x 0))+mz (nP p)^2*nFr p-
      mz (nP p)^5*∑ a, (mS (nP p) a).1*(nF p).2.1 a)/nullD (nP p)*mz (nP p)^2 =
    2*D (adaptedFrame (U x) (γ x) (s x) 0) (sourceMass U γ T s) x/
      ((x 0*sourceH U γ s x/2)*(x 0)^2) := by
  dsimp only [physicalNullInput,nP,nFr,nF]
  rw [physical_input_d U L γ T s η x w hr,physical_normal_derivative]
  change 2*(w/(x 0*Real.sqrt (x 0))+(1/x 0)^2*((x 0)^2*
    (D (CKSRealizedRound.basis 0) (sourceMass U γ T s) x-w/(x 0*Real.sqrt (x 0))))-
    (1/x 0)^5*∑ a : Fin 2, ((x 0)^5*s x a)*D (CKSRealizedRound.basis a.succ) (sourceMass U γ T s) x)/
    sourceD U γ s x*(1/x 0)^2 = _
  simp only [Fin.sum_univ_two,sourceD]
  field_simp
  ring

lemma physical_input_smallNull_formula (hr : x 0 ≠ 0) (hU : U x ≠ 0)
    (hH : sourceH U γ s x ≠ 0) :
    let q := physicalAngularJet γ x
    let X := leafTensorTraceFree (γ x) (sourceChi U γ s x)
    let τ := leafTensorTraceFree (γ x) (T x)
    let F := sourceMass U γ T s
    let u := x 0*sourceH U γ s x/2
    let a := sourceP γ T x/sourceH U γ s x
    coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0) =
      2*D (adaptedFrame (U x) (γ x) (s x) 0) F x/(u*(x 0)^2)+
      (scalarCurvature q/2-1/(x 0)^2)+
      (U x/u-1)*(2-6*F x/(x 0))/(x 0)^2-
      lapseLaplacian q (physicalAngularScalarJet U x)-
      (tensorPair q X X+tensorPair q τ τ)/2+a*tensorPair q X τ-
      covectorPair q (η x) (η x)-
      a*(covectorDiv q (fun i => physicalAngularScalarJet (fun y => η y i) x)-
        2*covectorPair q (η x) (sourceB U x)) := by
  dsimp only
  unfold coordinateSmallNull
  rw [physical_input_massrow U L γ T s η x w hr hU hH]
  dsimp only [physicalNullInput,nP,nF]
  unfold physicalNullQuadratic physicalNullEta
  rw [physical_input_q U L γ T s η x w hr,physical_input_d U L γ T s η x w hr,
    physical_input_lapseJet U L γ T s η x w hr,physical_input_ratio U L γ T s η x w hr hU,
    physical_input_X U L γ T s η x w hr,physical_input_tau_value U L γ T s η x w hr,
    physical_input_eta_value U L γ T s η x w hr,physical_input_eta U L γ T s η x w hr,
    physical_input_acceleration U L γ T s η x w hr hU]
  rw [lapseLaplacian_lapse_smul _ _ (one_div_ne_zero (physicalBaseLapse_ne hr)) hU]
  have hc : (1/sourceD U γ s x-1)*(2-6*(1/x 0)*sourceMass U γ T s x)*(1/x 0)^2 =
      (U x/(x 0*sourceH U γ s x/2)-1)*(2-6*sourceMass U γ T s x/(x 0))/(x 0)^2 := by
    unfold sourceD
    field_simp
  change _+(_/2-(1/x 0)^2)+
    (1/sourceD U γ s x-1)*(2-6*(1/x 0)*sourceMass U γ T s x)*(1/x 0)^2-_
      +_ -_ = _
  rw [hc]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physical_input_smallNull {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0) =
      physicalEnergy G K E x-sourceP γ T x/sourceH U γ s x*sourceQ U L γ T s η x := by
  dsimp only
  have hH : sourceH U γ s x ≠ 0 := by intro h; simp [h] at hu
  have hm := physical_source_mass_identity hU hγ hs hL hη hT h0 hp hTs hr hu
  obtain ⟨_,hq,_⟩ := physical_source_constraints hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hm hq
  rw [hq] at hm
  have ha : (x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2) =
      sourceP γ T x/sourceH U γ s x := by field_simp
  change physicalEnergy (fun y => foliationMetric (U y) (γ y) (s y))
    (fun y => foliationTensor (U y) (L y) (η y) (T y) (s y))
    (fun i y => adaptedFrame (U y) (γ y) (s y) i) x-
      (x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2)*sourceQ U L γ T s η x = _ at hm
  change _ = 2*D (adaptedFrame (U x) (γ x) (s x) 0) (sourceMass U γ T s) x/
    ((x 0*sourceH U γ s x/2)*(x 0)^2)+
    (scalarCurvature (physicalAngularJet γ x)/2-1/(x 0)^2)+
    (U x/(x 0*sourceH U γ s x/2)-1)*(2-6*sourceMass U γ T s x/(x 0))/(x 0)^2-
    lapseLaplacian (physicalAngularJet γ x) (physicalAngularScalarJet U x)-
    (tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (sourceChi U γ s x))
      (leafTensorTraceFree (γ x) (sourceChi U γ s x))+
      tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (T x))
        (leafTensorTraceFree (γ x) (T x)))/2+
    ((x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2))*
      tensorPair (physicalAngularJet γ x) (leafTensorTraceFree (γ x) (sourceChi U γ s x))
        (leafTensorTraceFree (γ x) (T x))-
    covectorPair (physicalAngularJet γ x) (η x) (η x)-
    ((x 0*sourceP γ T x/2)/(x 0*sourceH U γ s x/2))*
      (covectorDiv (physicalAngularJet γ x) (fun i => physicalAngularScalarJet (fun y => η y i) x)-
        2*covectorPair (physicalAngularJet γ x) (η x) (sourceB U x)) at hm
  rw [ha] at hm
  exact (physical_input_smallNull_formula U L γ T s η x w hr.ne' h0.ne' hH).trans hm.symm

lemma physical_input_energy {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    coordinateEnergy (physicalNullInput U L γ T s η x w) (x 0) = physicalEnergy G K E x := by
  dsimp only
  have ht : DifferentiableAt ℝ (sourceP γ T) x :=
    (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  change coordinateSmallNull (physicalNullInput U L γ T s η x w) (x 0)+
    nullRatio (physicalMomentumInput U L γ T s η x w)*
      coordinateQ (physicalMomentumInput U L γ T s η x w) = _
  rw [physical_input_smallNull hU hγ hs hL hη hT h0 hp hTs hr hu w,
    physical_input_ratio U L γ T s η x w hr.ne' h0.ne',
    physical_input_Q U L γ T s η x w hr.ne' h0.ne' ht]
  ring

theorem physical_normalized_DEC_iff {U L : PhysicalPoint → ℝ}
    {γ T : PhysicalPoint → Mat} {s η : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hT : ContDiffAt ℝ ∞ T x)
    (h0 : 0 < U x) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hTs : ∀ᶠ y in 𝓝 x, (T y).IsHermitian) (hr : 0 < x 0)
    (hu : 0 < x 0 * sourceH U γ s x / 2) (w : ℝ) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let K := fun y => foliationTensor (U y) (L y) (η y) (T y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    physicalDEC G K E x ↔ coordinateDEC (physicalNullInput U L γ T s η x w) (x 0)
 := by
  dsimp only
  have ht : DifferentiableAt ℝ (sourceP γ T) x :=
    (leafTensorTrace_contDiffAt hγ hT hp.self_of_nhds).differentiableAt (by simp)
  have hd := physical_source_DEC_iff hU hγ hs hL hη hT h0 hp hTs
  dsimp only at hd
  rw [hd]
  unfold coordinateDEC
  change _ ↔ Real.sqrt ((coordinateQ (physicalMomentumInput U L γ T s η x w))^2+
    covectorPair (rescale (1/mz (physicalMomentumInput U L γ T s η x w)^2)
      (mq (physicalMomentumInput U L γ T s η x w)))
      (coordinateZ (physicalMomentumInput U L γ T s η x w))
      (coordinateZ (physicalMomentumInput U L γ T s η x w))) ≤
    coordinateEnergy (physicalNullInput U L γ T s η x w) (x 0)
  rw [physical_input_Q U L γ T s η x w hr.ne' h0.ne' ht,
    physical_input_Z U L γ T s η x w hr.ne' h0.ne',
    physical_input_q U L γ T s η x w hr.ne',
    physical_input_energy hU hγ hs hL hη hT h0 hp hTs hr hu w]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def leafRadialRate (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (x : PhysicalPoint) : Mat := fun a b =>
  D (CKSRealizedRound.basis 0) (fun y => γ y a b) x-
    ∑ c, (s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x+
      γ x c b*D (CKSRealizedRound.basis a.succ) (fun y => s y c) x+
      γ x a c*D (CKSRealizedRound.basis b.succ) (fun y => s y c) x)

def radialExpansion (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (x : PhysicalPoint) : ℝ := x 0/4*leafTensorTrace (γ x) (leafRadialRate γ s x)

def radialMassRadical (t F : PhysicalPoint → ℝ) (x : PhysicalPoint) : ℝ :=
  1+(x 0*t x)^2-2*F x/x 0

def radialMassLapse (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) (x : PhysicalPoint) : ℝ :=
  Real.sqrt (radialMassRadical t F x)/radialExpansion γ s x

def radialTangential (γ : PhysicalPoint → Mat) (t : PhysicalPoint → ℝ)
    (τ : PhysicalPoint → Mat) (x : PhysicalPoint) : Mat :=
  t x • γ x+leafTensorTraceFree (γ x) (τ x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

def leafBilinear (γ : Mat) : Bilinear PhysicalPoint :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    γ a b • (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj b.succ : PhysicalPoint →L[ℝ] ℝ)

def radialFlow (s : PhysicalPoint → Point) (x : PhysicalPoint) : PhysicalPoint :=
  CKSRealizedRound.basis 0-∑ a : Fin 2, s x a • CKSRealizedRound.basis a.succ
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise
lemma leafBilinear_apply (γ : Mat) (v w : PhysicalPoint) :
    leafBilinear γ v w = ∑ a : Fin 2, ∑ b : Fin 2, γ a b*v a.succ*w b.succ := by
  simp [leafBilinear,ContinuousLinearMap.smulRight_apply,mul_assoc]
lemma leafBilinear_apply_basis (γ : Mat) (v : PhysicalPoint) (b : Fin 2) :
    leafBilinear γ v (CKSRealizedRound.basis b.succ) = ∑ a : Fin 2, γ a b*v a.succ := by
  rw [leafBilinear_apply]
  apply Finset.sum_congr rfl
  intro a _
  fin_cases b <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_basis_apply (γ : Mat) (w : PhysicalPoint) (a : Fin 2) :
    leafBilinear γ (CKSRealizedRound.basis a.succ) w = ∑ b : Fin 2, γ a b*w b.succ := by
  rw [leafBilinear_apply]
  fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_basis (γ : Mat) (a b : Fin 2) :
    leafBilinear γ (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ)=γ a b := by
  rw [leafBilinear_apply_basis]
  fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_differentiableAt {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : DifferentiableAt ℝ γ x) : DifferentiableAt ℝ (fun y => leafBilinear (γ y)) x := by
  let : IsBoundedSMul ℝ (Bilinear PhysicalPoint) := @NormedSpace.toIsBoundedSMul ℝ (Bilinear PhysicalPoint) _ _ _
  unfold leafBilinear
  let T := fun (a b : Fin 2) =>
    (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj b.succ : PhysicalPoint →L[ℝ] ℝ)
  exact DifferentiableAt.fun_sum (u := Finset.univ)
    (A := fun a y => ∑ b : Fin 2, γ y a b • T a b) fun a _ =>
      DifferentiableAt.fun_sum (u := Finset.univ)
        (A := fun b y => γ y a b • T a b) fun b _ =>
          (differentiableAt_pi.mp (differentiableAt_pi.mp hγ a) b).smul_const (T a b)
lemma radialFlow_succ (s : PhysicalPoint → Point) (x : PhysicalPoint) (a : Fin 2) :
    radialFlow s x a.succ = -s x a := by
  fin_cases a <;> simp [radialFlow,Fin.sum_univ_two,CKSRealizedRound.basis]
lemma radialFlow_differentiableAt {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hs : DifferentiableAt ℝ s x) : DifferentiableAt ℝ (radialFlow s) x := by
  apply DifferentiableAt.sub (differentiableAt_const _)
  exact DifferentiableAt.fun_sum fun a _ => (differentiableAt_pi.mp hs a).smul_const _
lemma fderiv_radialFlow_succ {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hs : DifferentiableAt ℝ s x) (v : PhysicalPoint) (a : Fin 2) :
    (fderiv ℝ (radialFlow s) x v) a.succ = -fderiv ℝ (fun y => s y a) x v := by
  have h := fderiv_fun_comp x
    (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).differentiableAt
    (radialFlow_differentiableAt hs)
  have he : (fun y => (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ) (radialFlow s y)) =
      (fun y => -s y a) := funext (fun y => radialFlow_succ s y a)
  rw [he,fderiv_fun_neg] at h
  simpa only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,neg_apply] using
    (congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v) h).symm
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

theorem leafRadialRate_eq_tensorLie {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : DifferentiableAt ℝ γ x) (hs : DifferentiableAt ℝ s x)
    (a b : Fin 2) :
    leafRadialRate γ s x a b = tensorLie (fun y => leafBilinear (γ y)) (radialFlow s) x
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) := by
  have hd : (fderiv ℝ (fun y => leafBilinear (γ y)) x (radialFlow s x))
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) =
      D (CKSRealizedRound.basis 0) (fun y => γ y a b) x-
        ∑ c : Fin 2, s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x := by
    rw [← fderiv_bilinear_const (leafBilinear_differentiableAt hγ)]
    simp only [leafBilinear_basis,radialFlow,D,map_sub,map_sum,map_smul,smul_eq_mul]
  unfold tensorLie
  rw [hd,leafBilinear_apply_basis,leafBilinear_basis_apply]
  simp only [fderiv_radialFlow_succ hs]
  simp only [leafRadialRate,D,Finset.sum_add_distrib,mul_neg,Finset.sum_neg_distrib]
  ring
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

def angularBlock (A : Mat) : AmbientMat :=
  !![1,0,0;0,A 0 0,A 0 1;0,A 1 0,A 1 1]

def angularCongruence (A γ : Mat) : Mat := A.transpose * γ * A

def angularCovector (A : Mat) (η : Point) : Point := A.transpose *ᵥ η
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix
lemma foliationMetric_covariant (A : Mat) (U : ℝ) {γ : Mat}
    (hγ : γ.IsHermitian) (s : Point) :
    foliationMetric U (angularCongruence A γ) s =
      (angularBlock A).transpose * foliationMetric U γ (A *ᵥ s) * angularBlock A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foliationMetric, angularCongruence, angularBlock, metricBlock, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, transpose_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
      hermitian_real_symmetry hγ 0 1] <;> ring
lemma foliationTensor_covariant (A : Mat) (U L : ℝ) (η : Point) {T : Mat}
    (hT : T.IsHermitian) (s : Point) :
    foliationTensor U L (angularCovector A η) (angularCongruence A T) s =
      (angularBlock A).transpose * foliationTensor U L η T (A *ᵥ s) * angularBlock A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foliationTensor, angularCovector, angularCongruence, angularBlock, metricBlock,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const, zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
      hermitian_real_symmetry hT 0 1] <;> ring
theorem foliation_reconstruction_covariant (A : Mat) (U L : ℝ)
    {γ T : Mat} (hγ : γ.IsHermitian) (hT : T.IsHermitian) (η s : Point) :
    foliationMetric U (angularCongruence A γ) s =
      (angularBlock A).transpose * foliationMetric U γ (A *ᵥ s) * angularBlock A ∧
    foliationTensor U L (angularCovector A η) (angularCongruence A T) s =
      (angularBlock A).transpose * foliationTensor U L η T (A *ᵥ s) * angularBlock A :=
  ⟨foliationMetric_covariant A U hγ s, foliationTensor_covariant A U L η hT s⟩
lemma angularCongruence_inverse (A γ : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    (angularCongruence A γ)⁻¹ = A⁻¹ * γ⁻¹ * A.transpose⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have hAt : IsUnit A.transpose.det := by simpa using hA
  simp only [angularCongruence, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hAt]
  rw [← Matrix.mul_assoc γ⁻¹, Matrix.nonsing_inv_mul _ hγ, Matrix.one_mul]
  exact Matrix.nonsing_inv_mul _ hA
lemma leafTensorTrace_covariant (A γ T : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    leafTensorTrace (angularCongruence A γ) (angularCongruence A T) = leafTensorTrace γ T := by
  rw [leafTensorTrace, angularCongruence_inverse A γ hA hγ]
  have hAt : IsUnit A.transpose.det := by simpa using hA
  change (A⁻¹ * γ⁻¹ * A.transpose⁻¹ * (A.transpose * T * A)).trace = _
  have he : A⁻¹ * γ⁻¹ * A.transpose⁻¹ * (A.transpose * T * A) = A⁻¹ * (γ⁻¹*T) * A := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hAt]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
  rfl
theorem leaf_trace_covariant (A γ T : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    leafTensorTrace (angularCongruence A γ) (angularCongruence A T) = leafTensorTrace γ T ∧
    leafTensorTraceFree (angularCongruence A γ) (angularCongruence A T) =
      angularCongruence A (leafTensorTraceFree γ T) := by
  refine ⟨leafTensorTrace_covariant A γ T hA hγ, ?_⟩
  unfold leafTensorTraceFree
  rw [leafTensorTrace_covariant A γ T hA hγ]
  simp only [angularCongruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSAngularSlice CKSMixedGeometry

def angularChange (φ : Point → Point) (x : PhysicalPoint) : PhysicalPoint :=
  slice (x 0) (φ (angularProjection x))

def angularJacobian (φ : Point → Point) (x : PhysicalPoint) : Mat :=
  fun a b => fderiv ℝ φ (angularProjection x) (CKSAngularGeometry.basis b) a

def angularMetricPullback (φ : Point → Point) (γ : PhysicalPoint → Mat)
    (x : PhysicalPoint) : Mat := angularCongruence (angularJacobian φ x) (γ (angularChange φ x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
@[simp] lemma angularChange_zero (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ x 0 = x 0 := by simp [angularChange]
@[simp] lemma angularChange_succ (φ : Point → Point) (x : PhysicalPoint) (a : Fin 2) :
    angularChange φ x a.succ = φ (angularProjection x) a := by simp [angularChange]
lemma angularChange_contDiffAt {φ : Point → Point} {x : PhysicalPoint} {n : WithTop ℕ∞}
    (hφ : ContDiffAt ℝ n φ (angularProjection x)) : ContDiffAt ℝ n (angularChange φ) x := by
  have hr : ContDiffAt ℝ n (fun y : PhysicalPoint => (Pi.single 0 (y 0) : PhysicalPoint)) x := by
    apply contDiffAt_pi.2
    intro i
    by_cases hi : i=0
    · subst i
      change ContDiffAt ℝ n (fun y : PhysicalPoint => y 0) x
      fun_prop
    · simp only [Pi.single_apply, hi, ite_false]
      exact contDiffAt_const
  exact hr.add (injection.contDiff.contDiffAt.comp x (hφ.comp x angularProjection.contDiff.contDiffAt))
lemma angularChange_differentiableAt {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) : DifferentiableAt ℝ (angularChange φ) x := by
  have hr : DifferentiableAt ℝ (fun y : PhysicalPoint => (Pi.single 0 (y 0) : PhysicalPoint)) x := by
    apply differentiableAt_pi.2
    intro i
    by_cases hi : i=0
    · subst i
      change DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) x
      fun_prop
    · simp only [Pi.single_apply, hi, ite_false]
      exact differentiableAt_const _
  exact hr.add (injection.differentiableAt.comp x (hφ.comp x angularProjection.differentiableAt))
lemma fderiv_angularChange_zero {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (v : PhysicalPoint) :
    fderiv ℝ (angularChange φ) x v 0 = v 0 := by
  have h := congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v)
    (fderiv_fun_comp x (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).differentiableAt
      (angularChange_differentiableAt hφ))
  have hp : fderiv ℝ (fun y : PhysicalPoint => y 0) x = ContinuousLinearMap.proj 0 :=
    (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).fderiv
  simpa only [ContinuousLinearMap.proj_apply, angularChange_zero, hp, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply] using h.symm
lemma fderiv_angularChange_succ {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (v : PhysicalPoint) (a : Fin 2) :
    fderiv ℝ (angularChange φ) x v a.succ = fderiv ℝ φ (angularProjection x) (angularProjection v) a := by
  have h := congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v)
    (fderiv_fun_comp x (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).differentiableAt
      (angularChange_differentiableAt hφ))
  simp only [ContinuousLinearMap.proj_apply, angularChange_succ,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply] at h
  have hd := fderiv_fun_comp x (differentiableAt_pi.mp hφ a) angularProjection.differentiableAt
  rw [hd, ContinuousLinearMap.fderiv] at h
  simpa only [ContinuousLinearMap.comp_apply,fderiv_apply hφ,
    ContinuousLinearMap.proj_apply] using h.symm
lemma angularJacobian_mulVec (φ : Point → Point) (x : PhysicalPoint) (v : Point) :
    angularJacobian φ x *ᵥ v = fderiv ℝ φ (angularProjection x) v := by
  have hv : v = ∑ b : Fin 2, v b • CKSAngularGeometry.basis b := by
    ext a
    fin_cases a <;> simp [CKSAngularGeometry.basis,Pi.single_apply]
  conv_rhs => rw [hv]
  ext a
  simp only [map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, angularJacobian]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma fderiv_angularChange_basis {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (b : Fin 2) :
    fderiv ℝ (angularChange φ) x (CKSRealizedRound.basis b.succ) =
      ∑ a : Fin 2, angularJacobian φ x a b • CKSRealizedRound.basis a.succ := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [fderiv_angularChange_zero hφ,CKSRealizedRound.basis]
  · rw [fderiv_angularChange_succ hφ]
    have hb : angularProjection (CKSRealizedRound.basis b.succ)=CKSAngularGeometry.basis b := by
      ext c
      simp [angularProjection,CKSRealizedRound.basis,CKSAngularGeometry.basis,Pi.single_apply]
    rw [hb]
    fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply,angularJacobian]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
lemma leafBilinear_congruence (A γ : Mat) (v w : PhysicalPoint) :
    leafBilinear (angularCongruence A γ) v w =
      ∑ a : Fin 2, ∑ b : Fin 2, γ a b * (A *ᵥ angularProjection v) a * (A *ᵥ angularProjection w) b := by
  simp only [leafBilinear_apply, angularCongruence, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_two, angularProjection, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]
  ring
lemma leafBilinear_angularPullback {φ : Point → Point} (γ : PhysicalPoint → Mat)
    {x : PhysicalPoint} (hφ : DifferentiableAt ℝ φ (angularProjection x)) :
    leafBilinear (angularMetricPullback φ γ x) =
      tensorPullback (angularChange φ) (fun y => leafBilinear (γ y)) x := by
  ext v w
  change leafBilinear (angularCongruence (angularJacobian φ x) (γ (angularChange φ x))) v w =
    leafBilinear (γ (angularChange φ x)) (fderiv ℝ (angularChange φ) x v)
      (fderiv ℝ (angularChange φ) x w)
  rw [leafBilinear_congruence,leafBilinear_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [fderiv_angularChange_succ hφ, fderiv_angularChange_succ hφ,
    angularJacobian_mulVec,angularJacobian_mulVec]
@[simp] lemma radialFlow_zero (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    radialFlow s x 0 = 1 := by simp [radialFlow,CKSRealizedRound.basis]
lemma angularProjection_radialFlow (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    angularProjection (radialFlow s x) = -s x := by
  ext a
  exact radialFlow_succ s x a
lemma radialFlow_angular_related {φ : Point → Point} {s s' : PhysicalPoint → Point}
    {x : PhysicalPoint} (hφ : DifferentiableAt ℝ φ (angularProjection x))
    (hrel : angularJacobian φ x *ᵥ s' x = s (angularChange φ x)) :
    fderiv ℝ (angularChange φ) x (radialFlow s' x) = radialFlow s (angularChange φ x) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · rw [fderiv_angularChange_zero hφ,radialFlow_zero,radialFlow_zero]
  · rw [fderiv_angularChange_succ hφ,angularProjection_radialFlow,map_neg,
      ← angularJacobian_mulVec,hrel,radialFlow_succ]
    rfl
lemma tensorLie_angular_expansion (T : PhysicalPoint → Bilinear PhysicalPoint)
    (V : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (A : Mat) (a b : Fin 2) :
    tensorLie T V x (∑ c : Fin 2, A c a • CKSRealizedRound.basis c.succ)
        (∑ d : Fin 2, A d b • CKSRealizedRound.basis d.succ) =
      ∑ c : Fin 2, ∑ d : Fin 2, A c a * tensorLie T V x
        (CKSRealizedRound.basis c.succ) (CKSRealizedRound.basis d.succ) * A d b := by
  simp only [Fin.sum_univ_two,tensorLie,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
lemma leafRadialRate_angular_natural {φ : Point → Point} {γ γ' : PhysicalPoint → Mat}
    {s s' : PhysicalPoint → Point} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hγ : DifferentiableAt ℝ γ (angularChange φ x))
    (hγ' : DifferentiableAt ℝ γ' x)
    (hs : DifferentiableAt ℝ s (angularChange φ x))
    (hs' : DifferentiableAt ℝ s' x)
    (hrelγ : γ' =ᶠ[𝓝 x] angularMetricPullback φ γ)
    (hrels : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ s' y = s (angularChange φ y)) :
    leafRadialRate γ' s' x = angularCongruence (angularJacobian φ x)
      (leafRadialRate γ s (angularChange φ x)) := by
  have hφd := hφ.differentiableAt (by norm_num)
  have hφev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ (angularProjection y) :=
    angularProjection.continuous.continuousAt.tendsto.eventually
      ((hφ.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num))
  have hT : (fun y => leafBilinear (γ' y)) =ᶠ[𝓝 x]
      tensorPullback (angularChange φ) (fun y => leafBilinear (γ y)) := by
    filter_upwards [hrelγ,hφev] with y hy hdy
    rw [hy,leafBilinear_angularPullback γ hdy]
  have hV : ∀ᶠ y in 𝓝 x, fderiv ℝ (angularChange φ) y (radialFlow s' y) =
      radialFlow s (angularChange φ y) := by
    filter_upwards [hrels,hφev] with y hy hdy
    exact radialFlow_angular_related hdy hy
  ext a b
  rw [leafRadialRate_eq_tensorLie hγ' hs']
  have hLie : tensorLie (fun y => leafBilinear (γ' y)) (radialFlow s') x
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) =
      tensorLie (tensorPullback (angularChange φ) (fun y => leafBilinear (γ y))) (radialFlow s') x
        (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) := by
    unfold tensorLie
    rw [hT.fderiv_eq (𝕜 := ℝ),hT.self_of_nhds]
  rw [hLie,tensorLie_natural (angularChange_contDiffAt hφ) (leafBilinear_differentiableAt hγ)
    (radialFlow_differentiableAt hs) (radialFlow_differentiableAt hs') hV,
    fderiv_angularChange_basis hφd,fderiv_angularChange_basis hφd,tensorLie_angular_expansion]
  simp only [← leafRadialRate_eq_tensorLie hγ hs,angularCongruence,Matrix.mul_apply,
    Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem radial_lapse_angular_natural {φ : Point → Point} {γ γ' : PhysicalPoint → Mat}
    {s s' : PhysicalPoint → Point} {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hγ : DifferentiableAt ℝ γ (angularChange φ x))
    (hγ' : DifferentiableAt ℝ γ' x)
    (hs : DifferentiableAt ℝ s (angularChange φ x))
    (hs' : DifferentiableAt ℝ s' x)
    (hrelγ : γ' =ᶠ[𝓝 x] angularMetricPullback φ γ)
    (hrels : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ s' y = s (angularChange φ y))
    (hA : IsUnit (angularJacobian φ x).det) (hdet : IsUnit (γ (angularChange φ x)).det) :
    radialExpansion γ' s' x = radialExpansion γ s (angularChange φ x) ∧
    radialMassLapse γ' s' (t ∘ angularChange φ) (F ∘ angularChange φ) x =
      radialMassLapse γ s t F (angularChange φ x) := by
  have hD : radialExpansion γ' s' x = radialExpansion γ s (angularChange φ x) := by
    unfold radialExpansion
    rw [hrelγ.self_of_nhds,leafRadialRate_angular_natural hφ hγ hγ' hs hs' hrelγ hrels]
    change x 0/4*leafTensorTrace (angularCongruence (angularJacobian φ x) (γ (angularChange φ x)))
      (angularCongruence (angularJacobian φ x) (leafRadialRate γ s (angularChange φ x))) = _
    rw [leafTensorTrace_covariant _ _ _ hA hdet,angularChange_zero]
  refine ⟨hD,?_⟩
  simp only [radialMassLapse,radialMassRadical,Function.comp_apply,angularChange_zero,hD]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_add (γ A B : Mat) :
    leafTensorTrace γ (A+B) = leafTensorTrace γ A+leafTensorTrace γ B := by
  simp [leafTensorTrace, Matrix.mul_add]

lemma leafTensorTrace_sub (γ A B : Mat) :
    leafTensorTrace γ (A-B) = leafTensorTrace γ A-leafTensorTrace γ B := by
  simp [leafTensorTrace, Matrix.mul_sub]

lemma leafTensorTrace_smul (γ A : Mat) (c : ℝ) :
    leafTensorTrace γ (c • A) = c*leafTensorTrace γ A := by
  simp [leafTensorTrace]

lemma leafTensorTrace_self {γ : Mat} (hp : γ.PosDef) : leafTensorTrace γ γ = 2 := by
  rw [leafTensorTrace, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  norm_num

lemma leafTensorTrace_traceFree {γ : Mat} (hp : γ.PosDef) (A : Mat) :
    leafTensorTrace γ (leafTensorTraceFree γ A) = 0 := by
  rw [leafTensorTraceFree, leafTensorTrace_sub, leafTensorTrace_smul,
    leafTensorTrace_self hp]
  ring

lemma sourceChi_radialRate (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    sourceChi U γ s x = (U x/2) • leafRadialRate γ s x := rfl

lemma sourceH_radialExpansion (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    sourceH U γ s x = 2*U x*radialExpansion γ s x/x 0 := by
  rw [sourceH, sourceChi_radialRate, leafTensorTrace_smul]
  unfold radialExpansion
  field_simp
  ring

lemma sourceP_radialTangential {γ : PhysicalPoint → Mat} {x : PhysicalPoint} (hp : (γ x).PosDef)
    (t : PhysicalPoint → ℝ) (τ : PhysicalPoint → Mat) :
    sourceP γ (radialTangential γ t τ) x = 2*t x := by
  rw [sourceP, radialTangential, leafTensorTrace_add, leafTensorTrace_smul,
    leafTensorTrace_self hp, leafTensorTrace_traceFree hp]
  ring

lemma radialMassLapse_pos {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hd : 0 < radialExpansion γ s x) (hf : 0 < radialMassRadical t F x) :
    0 < radialMassLapse γ s t F x :=
  div_pos (Real.sqrt_pos.mpr hf) hd

lemma sourceH_radialMassLapse (γ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) {x : PhysicalPoint} (hr : x 0 ≠ 0)
    (hd : radialExpansion γ s x ≠ 0) :
    sourceH (radialMassLapse γ s t F) γ s x =
      2*Real.sqrt (radialMassRadical t F x)/x 0 := by
  rw [sourceH_radialExpansion _ _ _ hr, radialMassLapse]
  field_simp

theorem physical_radial_reconstruction
    (γ τ : PhysicalPoint → Mat) (s : PhysicalPoint → Point)
    (t F : PhysicalPoint → ℝ) (x : PhysicalPoint)
    (hr : 0 < x 0) (hp : (γ x).PosDef)
    (hd : 0 < radialExpansion γ s x) (hf : 0 < radialMassRadical t F x) :
    let U := radialMassLapse γ s t F
    let T := radialTangential γ t τ
    0 < U x ∧ sourceD U γ s x = radialExpansion γ s x ∧
      sourceH U γ s x = 2*Real.sqrt (radialMassRadical t F x)/x 0 ∧
      sourceP γ T x = 2*t x ∧ sourceMass U γ T s x = F x
    := by
  dsimp only
  have hU := radialMassLapse_pos hd hf
  have hH := sourceH_radialMassLapse γ s t F hr.ne' hd.ne'
  have hpT := sourceP_radialTangential hp t τ
  refine ⟨hU, ?_, hH, hpT, ?_⟩
  · rw [sourceD, hH]
    unfold radialMassLapse
    have hu := (Real.sqrt_pos.mpr hf).ne'
    field_simp
  · rw [sourceMass, CKSFrame.massField, hH, hpT]
    field_simp
    rw [Real.sq_sqrt hf.le]
    unfold radialMassRadical
    field_simp
    ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def radiusLogPoint (x : PhysicalPoint) : PhysicalPoint :=
  fun i => if i=0 then Real.log (x 0) else x i

def logPointDerivative (x : PhysicalPoint) : PhysicalPoint →L[ℝ] PhysicalPoint :=
  ContinuousLinearMap.pi (fun i => if i=0 then (x 0)⁻¹ • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma radiusLogPoint_smoothAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ radiusLogPoint x := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simp only [radiusLogPoint, ite_true]
    have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
    exact hrad.log hr
  · simp only [radiusLogPoint, hi, ite_false]
    fun_prop

lemma radiusLogPoint_hasFDerivAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    HasFDerivAt radiusLogPoint (logPointDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simpa [radiusLogPoint, logPointDerivative, Function.comp_def] using
      (Real.hasDerivAt_log hr).comp_hasFDerivAt x
        (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt
  · simp only [radiusLogPoint, hi, ite_false]
    exact (ContinuousLinearMap.proj i : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt

lemma logPointDerivative_basis (i : Fin 3) (x : PhysicalPoint) :
    logPointDerivative x (CKSRealizedRound.basis i) =
      (if i=0 then (x 0)⁻¹ else 1) • CKSRealizedRound.basis i := by
  ext j
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j; simp [logPointDerivative, CKSRealizedRound.basis]
  · subst i; simp [logPointDerivative, CKSRealizedRound.basis, hj]
  · subst j; simp [logPointDerivative, CKSRealizedRound.basis, hi, Ne.symm hi]
  · simp [logPointDerivative, CKSRealizedRound.basis, hi, hj]

lemma D_radiusLogPoint (i : Fin 3) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : DifferentiableAt ℝ f (radiusLogPoint x)) :
    D (CKSRealizedRound.basis i) (fun y => f (radiusLogPoint y)) x =
      (if i=0 then (x 0)⁻¹ else 1)*D (CKSRealizedRound.basis i) f (radiusLogPoint x) := by
  unfold D
  change (fderiv ℝ (f ∘ radiusLogPoint) x) _ = _
  rw [fderiv_comp x hf (radiusLogPoint_hasFDerivAt hr).differentiableAt,
    (radiusLogPoint_hasFDerivAt hr).fderiv]
  simp only [ContinuousLinearMap.comp_apply, logPointDerivative_basis,
    map_smul, smul_eq_mul]

@[simp] lemma radiusLogPoint_slice (r : ℝ) (a : Point) :
    radiusLogPoint (slice r a) = slice (Real.log r) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radiusLogPoint]
  · simp [radiusLogPoint]

@[simp] lemma radiusLogPoint_logRadiusChart (x : PhysicalPoint) :
    radiusLogPoint (CKSMixedGeometry.logRadiusChart x) = x := by
  ext i
  by_cases hi : i=0
  · subst i; simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart]
  · simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, hi]

@[simp] lemma logRadiusChart_radiusLogPoint {x : PhysicalPoint} (hr : 0 < x 0) :
    CKSMixedGeometry.logRadiusChart (radiusLogPoint x) = x := by
  ext i
  by_cases hi : i=0
  · subst i; simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, Real.exp_log hr]
  · simp [radiusLogPoint, CKSMixedGeometry.logRadiusChart, hi]

lemma physicalAngularScalarJet_slice {f : PhysicalPoint → ℝ} {r : ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f (slice r x)) :
    physicalAngularScalarJet f (slice r x) = actualScalarJet (fun y => f (slice r y)) x :=
  (actualScalarJet_slice r hf).symm

lemma physicalAngularJet_slice {γ : PhysicalPoint → Mat} {r : ℝ} {x : Point}
    (hγ : ContDiffAt ℝ 2 γ (slice r x)) :
    physicalAngularJet γ (slice r x) = actualJet (fun y => γ (slice r y)) x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a i j
    exact (D_slice a r ((contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j).differentiableAt (by norm_num))).symm
  · funext a b i j
    exact (congrFun (congrFun (congrArg (fun p : ScalarJet => p.2.2)
      (physicalAngularScalarJet_slice (contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j))) a) b)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

structure LogCollarData.SmoothAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ ∞ f.sigma x
  metricError : ContDiffAt ℝ ∞ f.metricError x
  shift : ContDiffAt ℝ ∞ f.shift x
  tError : ContDiffAt ℝ ∞ f.tError x
  LError : ContDiffAt ℝ ∞ f.LError x
  massError : ContDiffAt ℝ ∞ f.massError x
  fstar : ContDiffAt ℝ ∞ f.fstar x
  etaDivR : ContDiffAt ℝ ∞ f.etaDivR x
  tauDivR2 : ContDiffAt ℝ ∞ f.tauDivR2 x

lemma LogCollarData.SmoothAt.regularAt {f : LogCollarData} {x : MP}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.metricError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.shift.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.LError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.massError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.fstar.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.etaDivR.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.tauDivR2.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalCollarGamma (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Mat :=
  (x 0)^2 • collarQ R f (radiusLogPoint x)
def physicalCollarShift (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Point :=
  collarShift R f (radiusLogPoint x)
def physicalCollarT (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarT R f (radiusLogPoint x)
def physicalCollarF (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarF R f (radiusLogPoint x)
def physicalCollarL (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : ℝ :=
  collarL R f (radiusLogPoint x)
def physicalCollarEta (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Point :=
  x 0 • collarEtaDivR R f (radiusLogPoint x)

def physicalCollarRawTau (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : Mat :=
  ((x 0)^2*(1-roundingWeight R (x 0))) • f.tauDivR2 (radiusLogPoint x)
def physicalCollarU (R : ℝ) (f : LogCollarData) : PhysicalPoint → ℝ :=
  radialMassLapse (physicalCollarGamma R f) (physicalCollarShift R f)
    (physicalCollarT R f) (physicalCollarF R f)
def physicalCollarTangential (R : ℝ) (f : LogCollarData) : PhysicalPoint → Mat :=
  radialTangential (physicalCollarGamma R f) (physicalCollarT R f) (physicalCollarRawTau R f)
def physicalCollarMetric (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : AmbientMat :=
  foliationMetric (physicalCollarU R f x) (physicalCollarGamma R f x) (physicalCollarShift R f x)
def physicalCollarTensor (R : ℝ) (f : LogCollarData) (x : PhysicalPoint) : AmbientMat :=
  foliationTensor (physicalCollarU R f x) (physicalCollarL R f x)
    (physicalCollarEta R f x) (physicalCollarTangential R f x) (physicalCollarShift R f x)
def physicalCollarFrame (R : ℝ) (f : LogCollarData) : LocalFrame :=
  fun i x => adaptedFrame (physicalCollarU R f x) (physicalCollarGamma R f x)
    (physicalCollarShift R f x) i

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma radialLift_smoothAt {h : ℝ → ℝ} {y : MP}
    (hh : ContDiffAt ℝ ∞ h (Real.exp (y 0))) : ContDiffAt ℝ ∞ (radialLift h) y :=
  hh.comp y (by fun_prop)

lemma collarWeight_smoothAt (R : ℝ) (y : MP) :
    ContDiffAt ℝ ∞ (radialLift (roundingWeight R)) y :=
  radialLift_smoothAt (roundingWeight_smooth R).contDiffAt

lemma collarQ_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.metricError)

lemma collarShift_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarShift R f) y :=
  (contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.shift

lemma collarT_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarT R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.tError)

lemma collarLb_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarLb R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.LError)

lemma collarL_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarL R f) y := by
  apply (collarLb_smoothAt R hf).add
  apply ((paddingWeight_smooth R).contDiffAt.comp y (show ContDiffAt ℝ ∞ (fun y : MP => Real.exp (y 0)) y by fun_prop)).div
  · fun_prop
  · positivity

lemma collarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarF R f) y :=
  (hf.fstar.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.massError)).add
    (radialLift_smoothAt ((paddingMass_smooth hR).contDiffAt
      (isOpen_Ioi.mem_nhds (Real.exp_pos (y 0)))))

lemma collarEta_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarEtaDivR R f) y :=
  (contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.etaDivR

lemma collarQ_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.metricError)

lemma collarShift_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarShift R f) y :=
  (contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.shift

lemma LogCollarData.SmoothAt.eventually_regularAt {f : LogCollarData} {x : MP}
    (hf : f.SmoothAt x) : ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  have hr := hf.regularAt
  filter_upwards [hr.sigma.eventually (by norm_num), hr.metricError.eventually (by norm_num),
    hr.shift.eventually (by norm_num),hr.tError.eventually (by norm_num),
    hr.LError.eventually (by norm_num),hr.massError.eventually (by norm_num),
    hr.fstar.eventually (by norm_num),hr.etaDivR.eventually (by norm_num),
    hr.tauDivR2.eventually (by norm_num)] with y h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarShift_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarShift R f) x :=
  (collarShift_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarT_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarT R f) x :=
  (collarT_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarF R f) x :=
  (collarF_smoothAt hR hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarL_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarL R f) x :=
  (collarL_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarEta_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarEta R f) x :=
  (show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x by fun_prop).smul
    ((collarEta_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarRawTau_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarRawTau R f) x := by
  have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
  exact ((hrad.pow 2).mul (contDiffAt_const.sub ((roundingWeight_smooth R).contDiffAt.comp x hrad))).smul
    (hf.tauDivR2.comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarGamma_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ 3 (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))

lemma physicalCollarShift_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarShift R f) x :=
  (collarShift_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open Matrix CKSAngularGeometry

structure LogCollarData.AngularRelatedAt (φ : AP → AP) (f f' : LogCollarData) (y : MP) : Prop where
  sigma : f'.sigma y = angularCongruence (angularJacobian φ y) (f.sigma (angularChange φ y))
  metricError : f'.metricError y = angularCongruence (angularJacobian φ y) (f.metricError (angularChange φ y))
  shift : angularJacobian φ y *ᵥ f'.shift y = f.shift (angularChange φ y)
  tError : f'.tError y = f.tError (angularChange φ y)
  LError : f'.LError y = f.LError (angularChange φ y)
  massError : f'.massError y = f.massError (angularChange φ y)
  fstar : f'.fstar y = f.fstar (angularChange φ y)
  etaDivR : f'.etaDivR y = angularCovector (angularJacobian φ y) (f.etaDivR (angularChange φ y))
  tauDivR2 : f'.tauDivR2 y = angularCongruence (angularJacobian φ y) (f.tauDivR2 (angularChange φ y))
end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff
@[simp] lemma angularProjection_radiusLogPoint (x : PhysicalPoint) :
    angularProjection (radiusLogPoint x) = angularProjection x := by
  ext a
  simp [angularProjection,radiusLogPoint]
@[simp] lemma angularJacobian_radiusLogPoint (φ : Point → Point) (x : PhysicalPoint) :
    angularJacobian φ (radiusLogPoint x) = angularJacobian φ x := by
  unfold angularJacobian
  rw [angularProjection_radiusLogPoint]
@[simp] lemma angularChange_radiusLogPoint (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ (radiusLogPoint x) = radiusLogPoint (angularChange φ x) := by
  simp [angularChange,radiusLogPoint_slice,radiusLogPoint]
lemma angularCongruence_add (A B C : Mat) :
    angularCongruence A (B+C) = angularCongruence A B+angularCongruence A C := by
  simp [angularCongruence,Matrix.mul_add,Matrix.add_mul]
lemma angularCongruence_smul (A B : Mat) (c : ℝ) :
    angularCongruence A (c • B) = c • angularCongruence A B := by
  simp [angularCongruence]
lemma angularCovector_smul (A : Mat) (v : Point) (c : ℝ) :
    angularCovector A (c • v) = c • angularCovector A v := by
  simp only [angularCovector,Matrix.mulVec_smul]
lemma physicalCollarGamma_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarGamma R f' x = angularMetricPullback φ (physicalCollarGamma R f) x := by
  unfold physicalCollarGamma angularMetricPullback collarQ
  rw [h.sigma,h.metricError]
  simp [radialLift,radiusLogPoint,angularCongruence_add,angularCongruence_smul]
lemma physicalCollarShift_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    angularJacobian φ x *ᵥ physicalCollarShift R f' x =
      physicalCollarShift R f (angularChange φ x) := by
  simp only [physicalCollarShift,collarShift,Matrix.mulVec_smul]
  have hs := h.shift
  simp only [angularJacobian_radiusLogPoint,angularChange_radiusLogPoint] at hs
  rw [hs]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarT_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarT R f' x = physicalCollarT R f (angularChange φ x) := by
  unfold physicalCollarT collarT
  rw [h.tError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarF_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarF R f' x = physicalCollarF R f (angularChange φ x) := by
  unfold physicalCollarF collarF
  rw [h.fstar,h.massError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarL_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarL R f' x = physicalCollarL R f (angularChange φ x) := by
  unfold physicalCollarL collarL collarLb
  rw [h.LError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarEta_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarEta R f' x = angularCovector (angularJacobian φ x)
      (physicalCollarEta R f (angularChange φ x)) := by
  unfold physicalCollarEta collarEtaDivR
  rw [h.etaDivR]
  simp [radialLift,radiusLogPoint,angularCovector_smul]
lemma physicalCollarRawTau_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarRawTau R f' x = angularCongruence (angularJacobian φ x)
      (physicalCollarRawTau R f (angularChange φ x)) := by
  unfold physicalCollarRawTau
  rw [h.tauDivR2]
  simp [angularCongruence_smul]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma physicalCollarU_angular_covariant {R : ℝ} {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.SmoothAt (radiusLogPoint (angularChange φ x)))
    (hf' : f'.SmoothAt (radiusLogPoint x))
    (hrel : ∀ᶠ y in 𝓝 (radiusLogPoint x), f.AngularRelatedAt φ f' y)
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef) :
    physicalCollarU R f' x = physicalCollarU R f (angularChange φ x) := by
  have hr' : angularChange φ x 0 ≠ 0 := by simpa using hr.ne'
  have he : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' (radiusLogPoint y) :=
    (radiusLogPoint_smoothAt hr.ne').continuousAt.tendsto.eventually hrel
  have hgm : physicalCollarGamma R f' =ᶠ[𝓝 x] angularMetricPullback φ (physicalCollarGamma R f) :=
    he.mono fun y hy => physicalCollarGamma_angular_covariant R hy
  have hsm : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ physicalCollarShift R f' y =
      physicalCollarShift R f (angularChange φ y) := he.mono fun y hy => physicalCollarShift_angular_covariant R hy
  have hd := (radial_lapse_angular_natural (t := physicalCollarT R f) (F := physicalCollarF R f) hφ
    ((physicalCollarGamma_smoothAt R hr' hf).differentiableAt (by simp))
    ((physicalCollarGamma_smoothAt R hr.ne' hf').differentiableAt (by simp))
    ((physicalCollarShift_smoothAt R hr' hf).differentiableAt (by simp))
    ((physicalCollarShift_smoothAt R hr.ne' hf').differentiableAt (by simp))
    hgm hsm hA (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')).1
  unfold physicalCollarU radialMassLapse radialMassRadical
  rw [hd,physicalCollarT_angular_covariant R he.self_of_nhds,physicalCollarF_angular_covariant R he.self_of_nhds,
    angularChange_zero]
lemma physicalCollarTangential_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x))
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef) :
    physicalCollarTangential R f' x = angularCongruence (angularJacobian φ x)
      (physicalCollarTangential R f (angularChange φ x)) := by
  unfold physicalCollarTangential radialTangential
  rw [physicalCollarT_angular_covariant R h,physicalCollarGamma_angular_covariant R h,
    physicalCollarRawTau_angular_covariant R h]
  dsimp only [angularMetricPullback]
  rw [(leaf_trace_covariant _ _ _ hA (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')).2]
  simp [angularCongruence_add,angularCongruence_smul]
theorem physicalCollar_angular_covariant {R : ℝ} (_hR : 0 < R)
    {φ : Point → Point} {f f' : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.SmoothAt (radiusLogPoint (angularChange φ x)))
    (hf' : f'.SmoothAt (radiusLogPoint x))
    (hrel : ∀ᶠ y in 𝓝 (radiusLogPoint x), f.AngularRelatedAt φ f' y)
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef)
    (hτ : (physicalCollarRawTau R f (angularChange φ x)).IsHermitian) :
    physicalCollarMetric R f' x = (angularBlock (angularJacobian φ x)).transpose *
      physicalCollarMetric R f (angularChange φ x) * angularBlock (angularJacobian φ x) ∧
    physicalCollarTensor R f' x = (angularBlock (angularJacobian φ x)).transpose *
      physicalCollarTensor R f (angularChange φ x) * angularBlock (angularJacobian φ x) := by
  have h := hrel.self_of_nhds
  have hT : (physicalCollarTangential R f (angularChange φ x)).IsHermitian := by
    unfold physicalCollarTangential radialTangential leafTensorTraceFree
    exact (hγ.isHermitian.smul (by rfl)).add (hτ.sub (hγ.isHermitian.smul (by rfl)))
  constructor
  · unfold physicalCollarMetric
    rw [physicalCollarU_angular_covariant hr hφ hf hf' hrel hA hγ,physicalCollarGamma_angular_covariant R h]
    dsimp only [angularMetricPullback]
    rw [foliationMetric_covariant _ _ hγ.isHermitian,physicalCollarShift_angular_covariant R h]
  · unfold physicalCollarTensor
    rw [physicalCollarU_angular_covariant hr hφ hf hf' hrel hA hγ,physicalCollarL_angular_covariant R h,
      physicalCollarEta_angular_covariant R h,physicalCollarTangential_angular_covariant R h hA hγ,
      foliationTensor_covariant _ _ _ _ hT,physicalCollarShift_angular_covariant R h]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarGamma R f (slice (Real.exp ρ) a) =
      Real.exp ρ^2 • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarGamma, slice_zero, radiusLogPoint_slice, Real.log_exp,
    collarQ_slice]

lemma physicalCollarShift_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarShift R f (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5) • fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarShift, radiusLogPoint_slice, Real.log_exp]
  rw [← collarShift_slice, smul_smul]
  simp

lemma physicalCollarT_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarT R f (slice (Real.exp ρ) a) =
      1+(1/Real.exp ρ)^3*fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarT, radiusLogPoint_slice, Real.log_exp]
  rw [← collarT_slice]
  field_simp
  ring

lemma physicalCollarF_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarF R f (slice (Real.exp ρ) a) =
      fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarF, radiusLogPoint_slice, Real.log_exp]
  exact collarF_slice R ρ f a

lemma physicalCollarL_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarL R f (slice (Real.exp ρ) a) =
      1+paddingWeight R (Real.exp ρ)/Real.exp ρ^2+
        (1/Real.exp ρ)^3*fieldL (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarL, radiusLogPoint_slice, Real.log_exp, collarL, slice_zero]
  rw [← collarLb_slice]
  field_simp
  ring

lemma physicalCollarEta_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarEta R f (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^2) • fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarEta, slice_zero, radiusLogPoint_slice, Real.log_exp]
  rw [← collarEta_slice, smul_smul]
  congr 1
  field_simp

lemma physicalCollarRawTau_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarRawTau R f (slice (Real.exp ρ) a) =
      ((1-roundingWeight R (Real.exp ρ))/Real.exp ρ) • (f.angular ρ).tau a := by
  simp [physicalCollarRawTau,LogCollarData.angular,smul_smul]
  congr 1
  field_simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (i j : Fin 2) :
    D (CKSRealizedRound.basis 0) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      2*Real.exp ρ*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a i j+
        (1/Real.exp ρ^2)*fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) a i j := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hq : ContDiffAt ℝ 3 (fun y => collarQ R f y i j) (slice ρ a) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j
  have hq' : DifferentiableAt ℝ (fun y => collarQ R f y i j)
      (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using hq.differentiableAt (by norm_num)
  have hrad : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) (slice (Real.exp ρ) a) := by fun_prop
  change D _ (fun y => (y 0)^2*collarQ R f (radiusLogPoint y) i j) _ = _
  erw [D_mul _ (hrad.pow 2) (hq'.comp _ (radiusLogPoint_hasFDerivAt hr).differentiableAt),
    D_pow _ 2 hrad, D_radiusLogPoint 0 hr hq']
  have hder : D (CKSRealizedRound.basis 0) (fun y : PhysicalPoint => y 0)
      (slice (Real.exp ρ) a) = 1 := by
    exact CKSRealizedRound.D_coord 0 0 _
  simp only [ite_true, Pi.pow_apply, Function.comp_apply,
    radiusLogPoint_slice, Real.log_exp, slice_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, hder, mul_one, collarQ_slice]
  rw [← collarQ_radial R ρ hf hσ i j]
  simp only [CKSRealizedRound.basis, CKSMixedGeometry.basis]
  field_simp
  ring

lemma physicalCollarGamma_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i j : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      Real.exp ρ^2*D (basis b)
        (fun y => fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hg := physicalCollarGamma_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarGamma R f (slice (Real.exp ρ) y) i j) =
      fun y => Real.exp ρ^2*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j := by
    funext y
    rw [physicalCollarGamma_slice]
    rfl
  rw [he]
  have hqa : ContDiffAt ℝ 3 (fun y => fieldQ (collarParams R (Real.exp ρ))
      (f.angular ρ) y i j) a := by
    have hh := (contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
    simpa only [Function.comp_def,collarQ_slice] using hh
  exact D_const_mul _ _ (hqa.differentiableAt (by norm_num))

lemma physicalCollarShift_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarShift R f y i)
      (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5)*D (basis b)
        (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := physicalCollarShift_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp hs i).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarShift R f (slice (Real.exp ρ) y) i) =
      fun y => (1/Real.exp ρ^5)*fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i := by
    funext y
    rw [physicalCollarShift_slice]
    rfl
  rw [he]
  have hsa : ContDiffAt ℝ 3 (fun y => fieldS (collarParams R (Real.exp ρ))
      (f.angular ρ) y i) a := by
    have hh := ((contDiffAt_pi.mp (collarShift_regularAt R hf) i).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).const_smul
        (Real.exp ρ^5)
    have heS : (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) =
        fun y => Real.exp ρ^5*collarShift R f (slice ρ y) i := by
      funext y
      rw [← collarShift_slice]
      rfl
    rw [heS]
    exact hh
  exact D_const_mul _ _ (hsa.differentiableAt (by norm_num))

lemma physicalCollarRadialRate (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0) :
    leafRadialRate (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      (2*Real.exp ρ) • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a+
        (1/Real.exp ρ^2) • fieldC (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  ext i j
  simp only [leafRadialRate, physicalCollarGamma_radial R ρ hf hσ,
    physicalCollarGamma_angular R ρ hf, physicalCollarShift_angular R ρ hf,
    physicalCollarGamma_slice,physicalCollarShift_slice,
    Matrix.add_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  simp only [fieldC,normalizedLie,collarParams,Matrix.cons_val_zero,
    Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_eq (γ T : Mat) :
    leafTensorTrace γ T = ∑ i, ∑ j, inverse γ i j*T j i := by
  simp only [leafTensorTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, inverse_eq]

lemma leafTensorTrace_metric_smul (γ T : Mat) {c : ℝ} (hc : c ≠ 0) :
    leafTensorTrace (c • γ) T = leafTensorTrace γ T/c := by
  simp only [leafTensorTrace_eq, inverse_smul c γ hc]
  simp only [Fin.sum_univ_two]
  ring

lemma leafTensorTraceFree_add (γ A B : Mat) :
    leafTensorTraceFree γ (A+B) = leafTensorTraceFree γ A+leafTensorTraceFree γ B := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_add]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma leafTensorTraceFree_smul (γ A : Mat) (c : ℝ) :
    leafTensorTraceFree γ (c • A) = c • leafTensorTraceFree γ A := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_smul]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma leafTensorTraceFree_self {γ : Mat} (hp : γ.PosDef) :
    leafTensorTraceFree γ γ = 0 := by
  rw [leafTensorTraceFree,leafTensorTrace_self hp]
  norm_num

lemma leafTensorTraceFree_metric_smul (γ T : Mat) {c : ℝ} (hc : c ≠ 0) :
    leafTensorTraceFree (c • γ) T = leafTensorTraceFree γ T := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_metric_smul γ T hc]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp

lemma traceFreeField_eq (q t : Point → Mat) (y : Point) :
    traceFreeField q t y = leafTensorTraceFree (q y) (t y) := by
  ext i j
  simp only [traceFreeField,leafTensorTraceFree,leafTensorTrace_eq,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma physicalCollarGamma_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef ↔
      (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).PosDef := by
  rw [physicalCollarGamma_slice]
  constructor
  · intro hp
    have h := hp.smul (show 0 < 1/Real.exp ρ^2 by positivity)
    simpa only [smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] using h
  · intro hp
    exact hp.smul (by positivity)

lemma physicalCollarExpansion_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp
  rw [radialExpansion, physicalCollarRadialRate R ρ hf hσ, physicalCollarGamma_slice,
    leafTensorTrace_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTrace_add,leafTensorTrace_smul,leafTensorTrace_smul,leafTensorTrace_self hq]
  simp only [slice_zero,lapseDField,fieldD,leafTensorTrace_eq]
  field_simp
  ring

lemma physicalCollarShear_unscaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (sourceChi (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f)
        (slice (Real.exp ρ) a)) =
      (physicalCollarU R f (slice (Real.exp ρ) a)/(2*Real.exp ρ^2)) •
        leafTensorTraceFree (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a)
          (fieldC (collarParams R (Real.exp ρ)) (f.angular ρ) a) := by
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp
  rw [sourceChi_radialRate,physicalCollarRadialRate R ρ hf hσ,physicalCollarGamma_slice,
    leafTensorTraceFree_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTraceFree_smul,leafTensorTraceFree_add,leafTensorTraceFree_smul,
    leafTensorTraceFree_smul,leafTensorTraceFree_self hq,smul_zero,zero_add,smul_smul]
  congr 1
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafRadialRate_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x) :
    ContDiffAt ℝ ∞ (leafRadialRate γ s) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hd (k : Fin 3) (i j) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => γ y i j)) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hsd (k : Fin 3) (i) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => s y i)) x :=
    contDiffAt_D (hsc i) (by simp) _
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [leafRadialRate,Fin.sum_univ_two]
  fun_prop

lemma radialExpansion_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (hp : (γ x).PosDef) : ContDiffAt ℝ ∞ (radialExpansion γ s) x := by
  unfold radialExpansion
  exact ((show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x by fun_prop).div_const 4).mul
    (leafTensorTrace_contDiffAt hγ (leafRadialRate_smoothAt hγ hs) hp)

lemma radialMassRadical_smoothAt {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassRadical t F) x := by
  have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
  exact (contDiffAt_const.add ((hrad.mul ht).pow 2)).sub
    ((contDiffAt_const.mul hF).div hrad hr)

lemma radialMassLapse_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : x 0 ≠ 0) (hp : (γ x).PosDef)
    (hd : radialExpansion γ s x ≠ 0) (hu : radialMassRadical t F x ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassLapse γ s t F) x :=
  ((radialMassRadical_smoothAt ht hF hr).sqrt hu).div
    (radialExpansion_smoothAt hγ hs hp) hd

lemma radialTangential_smoothAt {γ τ : PhysicalPoint → Mat} {t : PhysicalPoint → ℝ}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hτ : ContDiffAt ℝ ∞ τ x)
    (ht : ContDiffAt ℝ ∞ t x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (radialTangential γ t τ) x :=
  (ht.smul hγ).add (leafTensorTraceFree_contDiffAt hγ hτ hp)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lapseNormalizedField_rad (z : ℝ) (T F d : Point → ℝ) (a : Point) :
    lapseNormalizedField z T F d a =
      Real.sqrt (lapseRadField z T F a)/lapseDField z d a := by
  unfold lapseNormalizedField lapseRadField lapseVField lapseDField
  congr 2
  have h : 1+z^2 ≠ 0 := by positivity
  field_simp
  ring

lemma physicalCollarRadical_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) =
      (1+Real.exp ρ^2)*lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [radialMassRadical,physicalCollarT_slice,physicalCollarF_slice,slice_zero,
    lapse_radical_reconstruction (Real.exp_pos ρ)]
  unfold lapseRadField lapseVField
  congr 2
  ring

lemma physicalCollarRadical_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) ↔
      0 < lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [physicalCollarRadical_slice,mul_pos_iff_of_pos_left (by positivity : 0 < 1+Real.exp ρ^2)]

lemma physicalCollarU_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    physicalCollarU R f (slice (Real.exp ρ) a) = physicalBaseLapse (Real.exp ρ)*
      fieldNormalizedLapse (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarU,radialMassLapse,physicalCollarRadical_slice,
    physicalCollarExpansion_slice R ρ hf hσ hp,
    Real.sqrt_mul (by positivity : 0 ≤ 1+Real.exp ρ^2),
    physicalBaseLapse_eq (Real.exp_pos ρ)]
  unfold fieldNormalizedLapse
  rw [lapseNormalizedField_rad]
  simp only [collarParams,Matrix.cons_val_zero]
  ring

lemma physicalCollarU_coefficient (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f)
      (slice (Real.exp ρ) a)) :
    physicalCollarU R f (slice (Real.exp ρ) a) = physicalBaseLapse (Real.exp ρ)*
      (1+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) a) := by
  rw [physicalCollarU_slice R ρ hf hσ hp]
  apply congrArg (physicalBaseLapse (Real.exp ρ) * ·)
  apply lapseAField_identity
  · exact (physicalCollarRadical_pos_iff R ρ f a).mp hu
  · change lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a ≠ 0
    rw [← physicalCollarExpansion_slice R ρ hf hσ hp]
    exact hd.ne'

lemma physicalCollarTangential_trace (R : ℝ) (f : LogCollarData) {x : PhysicalPoint}
    (hp : (physicalCollarGamma R f x).PosDef) :
    sourceP (physicalCollarGamma R f) (physicalCollarTangential R f) x/2 = physicalCollarT R f x := by
  rw [physicalCollarTangential,sourceP_radialTangential hp]
  ring

lemma radialTangential_traceFree {γ : Mat} (hp : γ.PosDef) (τ : Mat) (t : ℝ) :
    leafTensorTraceFree γ (t • γ+leafTensorTraceFree γ τ) = leafTensorTraceFree γ τ := by
  unfold leafTensorTraceFree
  rw [leafTensorTrace_add,leafTensorTrace_smul,leafTensorTrace_self hp,
    ← leafTensorTraceFree,leafTensorTrace_traceFree hp]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma physicalCollarTau_slice (R ρ : ℝ) (f : LogCollarData) {a : Point}
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (physicalCollarTangential R f (slice (Real.exp ρ) a)) =
      (1/Real.exp ρ) • fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarTangential,radialTangential,radialTangential_traceFree hp,
    physicalCollarGamma_slice,physicalCollarRawTau_slice,
    leafTensorTraceFree_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTraceFree_smul]
  rw [fieldTau,traceFreeField_eq,smul_smul]
  congr 1
  change (1-roundingWeight R (Real.exp ρ))/Real.exp ρ = 1/Real.exp ρ*(1-roundingWeight R (Real.exp ρ))
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma collarT_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarT R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).mul hf.tError)

lemma collarF_regularAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarF R f) y :=
  (hf.fstar.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).mul hf.massError)).add
    ((radialLift_smoothAt ((paddingMass_smooth hR).contDiffAt
      (isOpen_Ioi.mem_nhds (Real.exp_pos (y 0))))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

lemma collarEta_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (collarEtaDivR R f) y :=
  (contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).smul hf.etaDivR

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarT_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) :
    D (CKSRealizedRound.basis 0) (physicalCollarT R f) (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^4)*fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have ht : DifferentiableAt ℝ (collarT R f) (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (collarT_regularAt R hf).differentiableAt (by norm_num)
  unfold physicalCollarT
  rw [D_radiusLogPoint 0 hr ht]
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp]
  rw [← collarT_radial R ρ hf]
  simp only [CKSRealizedRound.basis,CKSMixedGeometry.basis]
  field_simp

lemma physicalCollarEta_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (i : Fin 2) :
    D (CKSRealizedRound.basis 0) (fun y => physicalCollarEta R f y i) (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^3)*fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) a i := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have he : DifferentiableAt ℝ (fun y => collarEtaDivR R f y i)
      (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (contDiffAt_pi.mp (collarEta_regularAt R hf) i).differentiableAt (by norm_num)
  have hrad : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) (slice (Real.exp ρ) a) := by fun_prop
  change D _ (fun y => y 0*collarEtaDivR R f (radiusLogPoint y) i) _ = _
  erw [D_mul _ hrad (he.comp _ (radiusLogPoint_hasFDerivAt hr).differentiableAt),
    D_radiusLogPoint 0 hr he]
  have hder : D (CKSRealizedRound.basis 0) (fun y : PhysicalPoint => y 0)
      (slice (Real.exp ρ) a) = 1 := CKSRealizedRound.D_coord 0 0 _
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp,Function.comp_apply,hder,mul_one]
  rw [← collarEta_radial R ρ hf i]
  simp only [CKSRealizedRound.basis,CKSMixedGeometry.basis]
  field_simp
  ring

lemma physicalCollarF_radial {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0) :
    D (CKSRealizedRound.basis 0) (physicalCollarF R f) (slice (Real.exp ρ) a) =
      paddingWeight R (Real.exp ρ)/(Real.exp ρ*Real.sqrt (Real.exp ρ))+
      (1/Real.exp ρ^2)*((1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial a-
        (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap a) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have ht : DifferentiableAt ℝ (collarF R f) (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using (collarF_regularAt hR hf).differentiableAt (by norm_num)
  unfold physicalCollarF
  rw [D_radiusLogPoint 0 hr ht]
  simp only [ite_true,slice_zero,radiusLogPoint_slice,Real.log_exp]
  change (Real.exp ρ)⁻¹*D (CKSMixedGeometry.basis 0) (collarF R f) (slice ρ a) = _
  rw [collarF_radial hR ρ hf hstar]
  rw [← paddingDensity_rpow (Real.exp_pos ρ)]
  unfold paddingDensity
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalAngularScalarJet_congr {f g : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (h : f =ᶠ[𝓝 x] g) : physicalAngularScalarJet f x = physicalAngularScalarJet g x := by
  apply Prod.ext
  · exact h.self_of_nhds
  apply Prod.ext
  · ext a
    exact D_congr h (CKSRealizedRound.basis a.succ)
  · ext a b
    have hd : D (CKSRealizedRound.basis b.succ) f =ᶠ[𝓝 x] D (CKSRealizedRound.basis b.succ) g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : PhysicalPoint →L[ℝ] ℝ => L (CKSRealizedRound.basis b.succ)) hy
    exact D_congr hd (CKSRealizedRound.basis a.succ)

lemma D_eventually_congr {f g : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (h : f =ᶠ[𝓝 x] g) (v : PhysicalPoint) : D v f =ᶠ[𝓝 x] D v g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : PhysicalPoint →L[ℝ] ℝ => L v) hy

lemma radial_positive_eventually {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : 0 < x 0) (hp : (γ x).PosDef)
    (hd : 0 < radialExpansion γ s x) (hu : 0 < radialMassRadical t F x) :
    (∀ᶠ y in 𝓝 x, 0 < radialExpansion γ s y) ∧
      (∀ᶠ y in 𝓝 x, 0 < radialMassRadical t F y) := by
  exact ⟨(radialExpansion_smoothAt hγ hs hp).continuousAt.eventually (eventually_gt_nhds hd),
    (radialMassRadical_smoothAt ht hF hr.ne').continuousAt.eventually (eventually_gt_nhds hu)⟩

lemma radial_reconstruction_eventually {γ τ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : 0 < x 0) (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hd : 0 < radialExpansion γ s x) (hu : 0 < radialMassRadical t F x) :
    (sourceMass (radialMassLapse γ s t F) γ (radialTangential γ t τ) s =ᶠ[𝓝 x] F) ∧
    (sourceD (radialMassLapse γ s t F) γ s =ᶠ[𝓝 x] radialExpansion γ s) ∧
    ((fun y => sourceP γ (radialTangential γ t τ) y/2) =ᶠ[𝓝 x] t) := by
  obtain ⟨hd',hu'⟩ := radial_positive_eventually hγ hs ht hF hr hp.self_of_nhds hd hu
  have hr' : ∀ᶠ y in 𝓝 x, 0 < y 0 :=
    (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).continuous.continuousAt.eventually (eventually_gt_nhds hr)
  have he : ∀ᶠ y in 𝓝 x,
      sourceMass (radialMassLapse γ s t F) γ (radialTangential γ t τ) s y = F y ∧
      sourceD (radialMassLapse γ s t F) γ s y = radialExpansion γ s y ∧
      sourceP γ (radialTangential γ t τ) y/2 = t y := by
    filter_upwards [hp,hd',hu',hr'] with y hyp hyd hyu hyr
    have h := physical_radial_reconstruction γ τ s t F y hyr hyp hyd hyu
    exact ⟨h.2.2.2.2,h.2.1,by rw [h.2.2.2.1]; ring⟩
  exact ⟨he.mono (fun _ h => h.1),he.mono (fun _ h => h.2.1),he.mono (fun _ h => h.2.2)⟩

lemma physicalCollar_positive_eventually {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) y) ∧
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) y) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  exact radial_positive_eventually (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') (physicalCollarT_smoothAt R hr hf')
    (physicalCollarF_smoothAt hR hr hf') (by simpa using Real.exp_pos ρ) hp hd hu

lemma physicalCollar_reconstruction_eventually {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    (sourceMass (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarTangential R f)
      (physicalCollarShift R f) =ᶠ[𝓝 (slice (Real.exp ρ) a)] physicalCollarF R f) ∧
    (sourceD (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f) =ᶠ[𝓝 (slice (Real.exp ρ) a)]
      radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)) ∧
    ((fun y => sourceP (physicalCollarGamma R f) (physicalCollarTangential R f) y/2) =ᶠ[𝓝 (slice (Real.exp ρ) a)] physicalCollarT R f) := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  exact radial_reconstruction_eventually (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') (physicalCollarT_smoothAt R hr hf')
    (physicalCollarF_smoothAt hR hr hf') (by simpa using Real.exp_pos ρ) hp hd hu

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma rescale_eq_smul (c : ℝ) (q : Jet) : rescale c q = c • q := rfl

lemma radius_inverse_smul_cancel {r : ℝ} (hr : r ≠ 0) (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    r^n • ((1/r)^n • v) = v := by
  rw [smul_smul,← mul_pow,mul_one_div_cancel hr,one_pow,one_smul]

lemma actualScalarJet_affine {g : Point → ℝ} {a : Point} (hg : ContDiffAt ℝ 2 g a) (c d : ℝ) :
    actualScalarJet (fun y => c+d*g y) a = constantJet c+d • actualScalarJet g a := by
  erw [actualScalarJet_add contDiffAt_const (hg.const_smul d),actualScalarJet_const,
    actualScalarJet_smul d hg]

lemma physicalAngularScalarJet_affine {f : PhysicalPoint → ℝ} {g : Point → ℝ} {r : ℝ} {a : Point}
    (hf : ContDiffAt ℝ 2 f (slice r a)) (hg : ContDiffAt ℝ 2 g a) (c d : ℝ)
    (he : (fun y => f (slice r y)) =ᶠ[𝓝 a] (fun y => c+d*g y)) :
    physicalAngularScalarJet f (slice r a) = constantJet c+d • actualScalarJet g a := by
  rw [physicalAngularScalarJet_slice hf,actualScalarJet_congr he,actualScalarJet_affine hg]

lemma physicalCollarGamma_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    rescale (1/Real.exp ρ^2) (physicalAngularJet (physicalCollarGamma R f) (slice (Real.exp ρ) a)) =
      actualJet (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hg := (physicalCollarGamma_smoothAt R hr hf').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [physicalAngularJet_slice hg]
  have he : (fun y => physicalCollarGamma R f (slice (Real.exp ρ) y)) =
      fun y => Real.exp ρ^2 • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    funext y
    exact physicalCollarGamma_slice R ρ f y
  have hqa := (fieldQ_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  rw [he,actualJet_smul _ hqa,rescale_eq_smul,smul_smul]
  simp

lemma physicalCollarT_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^3 • (physicalAngularScalarJet (physicalCollarT R f) (slice (Real.exp ρ) a)-constantJet 1) =
      actualScalarJet (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht := (physicalCollarT_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hta := fieldT_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))
  rw [physicalAngularScalarJet_affine ht hta 1 ((1/Real.exp ρ)^3)
    (Filter.Eventually.of_forall (physicalCollarT_slice R ρ f))]
  rw [add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

lemma physicalCollarL_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^3 • (physicalAngularScalarJet (physicalCollarL R f) (slice (Real.exp ρ) a)-
      constantJet (1+paddingWeight R (Real.exp ρ)/Real.exp ρ^2)) =
      actualScalarJet (fieldL (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hl := (physicalCollarL_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hla := fieldL_diff (collarParams R (Real.exp ρ))
    (angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))
  rw [physicalAngularScalarJet_affine hl hla _ ((1/Real.exp ρ)^3)
    (Filter.Eventually.of_forall (physicalCollarL_slice R ρ f))]
  rw [add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSAngularGeometry
open scoped Topology ContDiff
lemma LogCollarData.SmoothAt.angular_regular {f : LogCollarData} {ρ : ℝ} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) : (f.angular ρ).RegularAt a :=
  CKSAngularSlice.angular_regular hf.regularAt (hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalAngularScalarJet_scaled {f : PhysicalPoint → ℝ} {g : Point → ℝ} {r : ℝ} {a : Point}
    (hf : ContDiffAt ℝ 2 f (slice r a)) (hg : ContDiffAt ℝ 2 g a) (c : ℝ)
    (he : (fun y => f (slice r y)) =ᶠ[𝓝 a] (fun y => c*g y)) :
    physicalAngularScalarJet f (slice r a) = c • actualScalarJet g a := by
  rw [physicalAngularScalarJet_slice hf,actualScalarJet_congr he]
  exact actualScalarJet_smul c hg

lemma physicalCollarShift_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^5 • (fun i => physicalAngularScalarJet (fun y => physicalCollarShift R f y i)
      (slice (Real.exp ρ) a)) =
        fun i => actualScalarJet (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := (physicalCollarShift_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsa := (fieldS_diff (collarParams R (Real.exp ρ)) hf.angular_regular).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  funext i
  change Real.exp ρ^5 • physicalAngularScalarJet _ _ = _
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp hs i) (contDiffAt_pi.mp hsa i)
    (1/Real.exp ρ^5) (Filter.Eventually.of_forall (fun y => congrFun (physicalCollarShift_slice R ρ f y) i)),smul_smul]
  simp

lemma physicalCollarEta_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^2 • (fun i => physicalAngularScalarJet (fun y => physicalCollarEta R f y i)
      (slice (Real.exp ρ) a)) =
        fun i => actualScalarJet (fun y => fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := (physicalCollarEta_smoothAt R hr hf').of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsa : ContDiffAt ℝ 2 (fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    hf.angular_regular.2.2.2.1.const_smul _
  funext i
  change Real.exp ρ^2 • physicalAngularScalarJet _ _ = _
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp hs i) (contDiffAt_pi.mp hsa i)
    (1/Real.exp ρ^2) (Filter.Eventually.of_forall (fun y => congrFun (physicalCollarEta_slice R ρ f y) i)),smul_smul]
  simp

lemma physicalCollarEta_radial_scaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) :
    Real.exp ρ^3 • (fun i => D (CKSRealizedRound.basis 0) (fun y => physicalCollarEta R f y i)
      (slice (Real.exp ρ) a)) = fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  funext i
  change Real.exp ρ^3 * D _ _ _ = _
  rw [physicalCollarEta_radial R ρ hf i]
  field_simp

lemma physicalCollarF_jet {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    physicalAngularScalarJet (physicalCollarF R f) (slice (Real.exp ρ) a) =
      actualScalarJet (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  rw [physicalAngularScalarJet_slice ((physicalCollarF_smoothAt hR hr hf').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  congr 1
  funext y
  exact physicalCollarF_slice R ρ f y

lemma physicalCollarTr_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a)) :
    Real.exp ρ^4 • physicalAngularScalarJet
      (D (CKSRealizedRound.basis 0) (physicalCollarT R f)) (slice (Real.exp ρ) a) =
      actualScalarJet (fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht : ContDiffAt ℝ 2 (D (CKSRealizedRound.basis 0) (physicalCollarT R f)) (slice (Real.exp ρ) a) :=
    (contDiffAt_D (physicalCollarT_smoothAt R hr hf') (by simp) _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he : (fun y => D (CKSRealizedRound.basis 0) (physicalCollarT R f) (slice (Real.exp ρ) y))
      =ᶠ[𝓝 a] fun y => (1/Real.exp ρ^4)*fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt] with y hy
    exact physicalCollarT_radial R ρ hy
  rw [physicalAngularScalarJet_scaled ht (fieldTr_diff _ hf.angular_regular) _ he,smul_smul]
  simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarU_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hp : (physicalCollarGamma R f x).PosDef)
    (hd : radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x ≠ 0)
    (hu : radialMassRadical (physicalCollarT R f) (physicalCollarF R f) x ≠ 0) :
    ContDiffAt ℝ ∞ (physicalCollarU R f) x :=
  radialMassLapse_smoothAt (physicalCollarGamma_smoothAt R hr hf)
    (physicalCollarShift_smoothAt R hr hf) (physicalCollarT_smoothAt R hr hf)
    (physicalCollarF_smoothAt hR hr hf) hr hp hd hu

lemma physicalCollarTangential_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hp : (physicalCollarGamma R f x).PosDef) :
    ContDiffAt ℝ ∞ (physicalCollarTangential R f) x :=
  radialTangential_smoothAt (physicalCollarGamma_smoothAt R hr hf)
    (physicalCollarRawTau_smoothAt R hr hf) (physicalCollarT_smoothAt R hr hf) hp

lemma physicalCollarU_jet {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    Real.exp ρ^3 • ((1/physicalBaseLapse (Real.exp ρ)) •
      physicalAngularScalarJet (physicalCollarU R f) (slice (Real.exp ρ) a)-constantJet 1) =
      actualScalarJet (fieldA (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hU := (physicalCollarU_smoothAt hR hr hf' hp.self_of_nhds hd.ne' hu.ne').of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hrad := (physicalCollarRadical_pos_iff R ρ f a).mp hu
  have hdf : lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a ≠ 0 := by
    rw [← physicalCollarExpansion_slice R ρ hf.regularAt hσ.self_of_nhds hp.self_of_nhds]
    exact hd.ne'
  have hA : ContDiffAt ℝ 2 (fieldA (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    lapseAField_diff _ (fieldT_diff _ hf.angular_regular) (fieldF_diff _ hf.angular_regular)
      (fieldD_diff _ hf.angular_regular hq0) hrad hdf
  obtain ⟨hde,hue⟩ := physicalCollar_positive_eventually hR hf hp.self_of_nhds hd hu
  have he : (fun y => physicalCollarU R f (slice (Real.exp ρ) y)) =ᶠ[𝓝 a]
      fun y => physicalBaseLapse (Real.exp ρ)*(1+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) y) := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt,
      (slice_smooth ρ).continuous.continuousAt.tendsto.eventually hσ,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hde,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hue] with y hy hyσ hyp hyd hyu
    exact physicalCollarU_coefficient R ρ hy hyσ hyp hyd hyu
  rw [physicalAngularScalarJet_slice hU,actualScalarJet_congr he]
  have haf : ContDiffAt ℝ 2 (fun y => (1:ℝ)+(1/Real.exp ρ)^3*fieldA (collarParams R (Real.exp ρ)) (f.angular ρ) y) a :=
    contDiffAt_const.add (contDiffAt_const.mul hA)
  rw [actualScalarJet_smul (physicalBaseLapse (Real.exp ρ)) haf,
    actualScalarJet_affine hA 1 ((1/Real.exp ρ)^3),smul_smul]
  have hb : physicalBaseLapse (Real.exp ρ) ≠ 0 := by unfold physicalBaseLapse; positivity
  rw [one_div_mul_cancel hb,one_smul,add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

lemma physicalCollarExpansion_jet (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) :
    Real.exp ρ^3 • (physicalAngularScalarJet
      (radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f))
      (slice (Real.exp ρ) a)-constantJet 1) =
        actualScalarJet (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hD := (radialExpansion_smoothAt (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarShift_smoothAt R hr hf') hp.self_of_nhds).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have he : (fun y => radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) y)) =ᶠ[𝓝 a]
      fun y => 1+(1/Real.exp ρ)^3*fieldD (collarParams R (Real.exp ρ)) (f.angular ρ) y := by
    filter_upwards [(slice_smooth ρ).continuous.continuousAt.tendsto.eventually hf.eventually_regularAt,
      (slice_smooth ρ).continuous.continuousAt.tendsto.eventually hσ,
      (slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp] with y hy hyσ hyp
    exact physicalCollarExpansion_slice R ρ hy hyσ hyp
  rw [physicalAngularScalarJet_affine hD (fieldD_diff _ hf.angular_regular hq0) 1 _ he,
    add_sub_cancel_left,radius_inverse_smul_cancel (Real.exp_ne_zero ρ)]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarTau_jets (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) :
    Real.exp ρ • (fun i j => physicalAngularScalarJet (fun y =>
      leafTensorTraceFree (physicalCollarGamma R f y) (physicalCollarTangential R f y) i j)
        (slice (Real.exp ρ) a)) =
      matrixScalarJets (fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have ht := (leafTensorTraceFree_contDiffAt (physicalCollarGamma_smoothAt R hr hf')
    (physicalCollarTangential_smoothAt R hr hf' hp.self_of_nhds) hp.self_of_nhds).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp.self_of_nhds
  have hq0 : determinant (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hta : ContDiffAt ℝ 2 (fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ)) a :=
    (traceFreeField_diff ((fieldQ_diff _ hf.angular_regular).of_le (by norm_num))
      hf.angular_regular.2.2.2.2 hq0).const_smul _
  funext i j
  change Real.exp ρ • physicalAngularScalarJet _ _ = actualScalarJet _ a
  have he : (fun y => leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) y))
      (physicalCollarTangential R f (slice (Real.exp ρ) y)) i j) =ᶠ[𝓝 a]
      fun y => (1/Real.exp ρ)*fieldTau (collarParams R (Real.exp ρ)) (f.angular ρ) y i j := by
    filter_upwards [(slice_smooth (Real.exp ρ)).continuous.continuousAt.tendsto.eventually hp] with y hy
    exact congrFun (congrFun (physicalCollarTau_slice R ρ f hy) i) j
  rw [physicalAngularScalarJet_scaled (contDiffAt_pi.mp (contDiffAt_pi.mp ht i) j) (component_diff hta i j) _ he,smul_smul]
  simp

lemma physicalCollarShear_scaled (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    Real.exp ρ • leafTensorTraceFree (physicalCollarGamma R f (slice (Real.exp ρ) a))
      (sourceChi (physicalCollarU R f) (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a)) = fieldX (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarShear_unscaled R ρ hf hσ hp,physicalCollarU_slice R ρ hf hσ hp,
    smul_smul,fieldX,traceFreeField_eq]
  congr 1
  simp only [physicalBaseLapse,collarParams,Matrix.cons_val_zero]
  field_simp

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_collar_null_realization {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j,
      D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f)
      (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f)
      (slice (Real.exp ρ) a)) :
    physicalNullInput (physicalCollarU R f) (physicalCollarL R f)
      (physicalCollarGamma R f) (physicalCollarTangential R f)
      (physicalCollarShift R f) (physicalCollarEta R f)
      (slice (Real.exp ρ) a) (paddingWeight R (Real.exp ρ)) =
    fieldNullInput (collarParams R (Real.exp ρ)) (f.angular ρ) a
 := by
  have hrec := physicalCollar_reconstruction_eventually hR hf hp hd hu
  have hmass := (physicalAngularScalarJet_congr hrec.1).trans (physicalCollarF_jet hR ρ hf)
  have ht := physicalAngularScalarJet_congr hrec.2.2
  have htr := physicalAngularScalarJet_congr (D_eventually_congr hrec.2.2 (CKSRealizedRound.basis 0))
  have hde := physicalAngularScalarJet_congr hrec.2.1
  have hder := D_congr hrec.1 (CKSRealizedRound.basis 0)
  have hF : (Real.exp ρ)^2*(D (CKSRealizedRound.basis 0)
      (sourceMass (physicalCollarU R f) (physicalCollarGamma R f)
       (physicalCollarTangential R f) (physicalCollarShift R f))
      (slice (Real.exp ρ) a)-paddingWeight R (Real.exp ρ)/(Real.exp ρ*Real.sqrt (Real.exp ρ))) =
      (1-(collarParams R (Real.exp ρ)) 1)*(f.angular ρ).massRadial a-
        (collarParams R (Real.exp ρ)) 2*(f.angular ρ).massGap a := by
    rw [hder,physicalCollarF_radial hR ρ hf.regularAt hstar]
    change (Real.exp ρ)^2*(_+1/Real.exp ρ^2*_-_) =
      (1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial a-
      (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap a
    field_simp
    ring
  unfold physicalNullInput
  simp only [slice_zero]
  rw [hmass,hF]
  apply Prod.ext
  · unfold physicalMomentumInput
    simp only [slice_zero]
    rw [ht,htr,hde,physicalCollarGamma_jet R ρ hf,physicalCollarU_jet hR ρ hf hσ hp hd hu,
      physicalCollarT_jet R ρ hf,physicalCollarL_jet R ρ hf,physicalCollarTr_jet R ρ hf,
      physicalCollarExpansion_jet R ρ hf hσ hp,physicalCollarShift_jets R ρ hf,
      physicalCollarEta_jets R ρ hf,physicalCollarTau_jets R ρ hf hp,
      physicalCollarShear_scaled R ρ hf.regularAt hσ.self_of_nhds hp.self_of_nhds,
      physicalCollarEta_radial_scaled R ρ hf.regularAt]
    rfl
  · rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTraceFree_isHermitian {γ τ : Mat} (hγ : γ.IsHermitian) (hτ : τ.IsHermitian) :
    (leafTensorTraceFree γ τ).IsHermitian := hτ.sub (hγ.smul (by rfl))

lemma physicalCollarTangential_isHermitian (R : ℝ) (f : LogCollarData) (x : PhysicalPoint)
    (hγ : (physicalCollarGamma R f x).IsHermitian)
    (hτ : (f.tauDivR2 (radiusLogPoint x)).IsHermitian) :
    (physicalCollarTangential R f x).IsHermitian :=
  (hγ.smul (by rfl)).add (leafTensorTraceFree_isHermitian hγ (hτ.smul (by rfl)))

theorem physical_collar_DEC_iff {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hR : 0 < R) (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), ∀ i j,
      D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) y=0)
    (hstar : D (CKSRealizedRound.basis 0) f.fstar (slice ρ a)=0)
    (hτ : ∀ᶠ y in 𝓝 (slice ρ a), (f.tauDivR2 y).IsHermitian)
    (hp : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a))
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a)) :
    physicalDEC (physicalCollarMetric R f) (physicalCollarTensor R f)
      (physicalCollarFrame R f) (slice (Real.exp ρ) a) ↔
      coordinateDEC (fieldNullInput (collarParams R (Real.exp ρ)) (f.angular ρ) a) (Real.exp ρ)
 := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hrp : 0 < (slice (Real.exp ρ) a) 0 := by simpa using Real.exp_pos ρ
  have hf' : f.SmoothAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hτ' : ∀ᶠ y in 𝓝 (radiusLogPoint (slice (Real.exp ρ) a)), (f.tauDivR2 y).IsHermitian := by simpa using hτ
  have hTs : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarTangential R f y).IsHermitian := by
    filter_upwards [hp,(radiusLogPoint_smoothAt hr).continuousAt.tendsto.eventually hτ'] with y hyp hyτ
    exact physicalCollarTangential_isHermitian R f y hyp.isHermitian hyτ
  have hU0 : 0 < physicalCollarU R f (slice (Real.exp ρ) a) := radialMassLapse_pos hd hu
  have hH : 0 < sourceH (physicalCollarU R f) (physicalCollarGamma R f)
      (physicalCollarShift R f) (slice (Real.exp ρ) a) := by
    rw [physicalCollarU,sourceH_radialMassLapse _ _ _ _ hr hd.ne']
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hu)) hrp
  have hhat : 0 < (slice (Real.exp ρ) a) 0 * sourceH (physicalCollarU R f) (physicalCollarGamma R f)
      (physicalCollarShift R f) (slice (Real.exp ρ) a)/2 := div_pos (mul_pos hrp hH) (by norm_num)
  have h := physical_normalized_DEC_iff
    (physicalCollarU_smoothAt hR hr hf' hp.self_of_nhds hd.ne' hu.ne')
    (physicalCollarGamma_smoothAt R hr hf') (physicalCollarShift_smoothAt R hr hf')
    (physicalCollarL_smoothAt R hr hf') (physicalCollarEta_smoothAt R hr hf')
    (physicalCollarTangential_smoothAt R hr hf' hp.self_of_nhds)
    hU0 hp hTs hrp hhat (paddingWeight R (Real.exp ρ))
  dsimp only at h
  rw [physical_collar_null_realization hR hf hσ hstar hp hd hu] at h
  unfold physicalCollarMetric physicalCollarTensor physicalCollarFrame
  simpa only [slice_zero] using h

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma positiveAngular_posDef {q : Mat} (hs : q.IsHermitian) (hp : positiveAngular q) : q.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro v hv
  have he : star v ⬝ᵥ (q *ᵥ v) = determinant q/q 1 1*(v 0)^2+
      q 1 1*(v 1+q 0 1/q 1 1*v 0)^2 := by
    simp only [dotProduct,mulVec,Fin.sum_univ_two,star_trivial]
    rw [hermitian_real_symmetry hs 1 0]
    unfold determinant
    rw [hermitian_real_symmetry hs 1 0]
    field_simp [hp.1.ne']
    ring
  rw [he]
  by_cases h0 : v 0=0
  · have h1 : v 1 ≠ 0 := by
      intro hh
      apply hv
      funext i
      fin_cases i <;> simp [h0,hh]
    simp only [h0,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add]
    exact mul_pos hp.1 (sq_pos_of_ne_zero h1)
  · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hp.2 hp.1) (sq_pos_of_ne_zero h0))
      (mul_nonneg hp.1.le (sq_nonneg _))

lemma positiveAngular_continuousAt {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hp : positiveAngular (q x)) :
    ∀ᶠ y in 𝓝 x, positiveAngular (q y) := by
  have h1 := ((continuous_apply 1).continuousAt.comp
    ((continuous_apply 1).continuousAt.comp hq)).eventually (Ioi_mem_nhds hp.1)
  have hd := (determinant_smooth.continuous.continuousAt.comp hq).eventually (Ioi_mem_nhds hp.2)
  filter_upwards [h1,hd] with y hy1 hyd
  exact ⟨hy1,hyd⟩

lemma posDef_eventually_of_symmetric {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hs : ∀ᶠ y in 𝓝 x, (q y).IsHermitian) (hp : (q x).PosDef) :
    ∀ᶠ y in 𝓝 x, (q y).PosDef := by
  have ha : positiveAngular (q x) := ⟨hp.diag_pos,(determinant_eq _).symm ▸ hp.det_pos⟩
  filter_upwards [hs,positiveAngular_continuousAt hq ha] with y hys hyp
  exact positiveAngular_posDef hys hyp

lemma physicalCollarGamma_isHermitian (R : ℝ) (f : LogCollarData) (x : PhysicalPoint)
    (hσ : (f.sigma (radiusLogPoint x)).IsHermitian)
    (he : (f.metricError (radiusLogPoint x)).IsHermitian) :
    (physicalCollarGamma R f x).IsHermitian :=
  (hσ.add (he.smul (by rfl))).smul (by rfl)

lemma physicalCollarGamma_eventually_posDef {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hσ : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.sigma z).IsHermitian)
    (he : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.metricError z).IsHermitian)
    (hp : (physicalCollarGamma R f x).PosDef) :
    ∀ᶠ y in 𝓝 x, (physicalCollarGamma R f y).PosDef := by
  apply posDef_eventually_of_symmetric (physicalCollarGamma_smoothAt R hr hf).continuousAt _ hp
  filter_upwards [(radiusLogPoint_smoothAt hr).continuousAt.tendsto.eventually (hσ.and he)] with y hy
  exact physicalCollarGamma_isHermitian R f y hy.1 hy.2

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def sourceFrame (f : SourceMassFields) : LocalFrame :=
  fun i x => adaptedFrame (sourceLapse f x) (sourceGamma f x) (sourceShift f x) i

lemma sourceLapse_pos {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    0 < sourceLapse f x := one_div_pos.mpr (Real.sqrt_pos.mpr (metricBlock_schur_positive hp))

lemma source_metric_foliation {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    foliationMetric (sourceLapse f x) (sourceGamma f x) (sourceShift f x)=sourceMetric f x := by
  have hq : determinant (sourceGamma f x) ≠ 0 := by
    rw [determinant_eq]
    exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f x := metricBlock_schur_positive hp
  have hr : 1/(sourceLapse f x)^2=sourceSchur f x := by
    rw [sourceLapse,div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold foliationMetric sourceMetric
  rw [hr]
  have hv : (fun a => ∑ b, sourceGamma f x a b*sourceShift f x b)=f.b x := by
    funext a
    exact inverse_mul_vector (sourceGamma f x) hq (f.b x) a
  rw [hv]
  congr 1
  unfold sourceSchur sourceShift
  rw [inverse_quadratic _ hq]
  ring

lemma source_tensor_foliation {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base x).PosDef) (hk : (sourceTangentialK f.base x).IsHermitian) :
    foliationTensor (sourceLapse f.base x) (sourceOriginalL f x) (sourceOriginalEta f x)
      (sourceTangentialK f.base x) (sourceShift f.base x)=sourceTensor f x := by
  have hU := (sourceLapse_pos hp).ne'
  have heta : ∀ a, sourceOriginalEta f x a/sourceLapse f.base x =
      f.kb x a-∑ b, sourceTangentialK f.base x a b*sourceShift f.base x b := by
    intro a
    change sourceLapse f.base x * _ / sourceLapse f.base x = _
    rw [mul_div_cancel_left₀ _ hU]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [hermitian_real_symmetry hk a b]
    ring
  have hL : sourceOriginalL f x/(sourceLapse f.base x)^2 =
      sourceRadialK f x-2*∑ a, sourceShift f.base x a*f.kb x a+
        ∑ a, ∑ b, sourceTangentialK f.base x a b*(sourceShift f.base x a*sourceShift f.base x b) := by
    unfold sourceOriginalL sourceLapse
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hU)
  have heta' (a) := (div_eq_iff hU).mp (heta a)
  unfold foliationTensor sourceTensor
  have hcross : (fun a => sourceOriginalEta f x a/sourceLapse f.base x+
      ∑ b, sourceTangentialK f.base x a b*sourceShift f.base x b)=f.kb x := by
    funext a
    rw [heta a]
    ring
  rw [hcross,hL]
  congr 1
  simp_rw [heta']
  simp only [Fin.sum_univ_two]
  field_simp
  ring

lemma source_radialExpansion_eq (f : SourceMassFields) (x : Point) :
    radialExpansion (sourceGamma f) (sourceShift f) x=sourceExpansion f x := by
  unfold radialExpansion sourceExpansion
  rw [leafTensorTrace_eq]
  rfl

lemma source_radialMassRadical_eq {f : SourceMassFields} {x : Point} (hr : x 0 ≠ 0) :
    radialMassRadical (sourceT f) (sourcePhysicalMass f) x=
      (sourceLapse f x*sourceExpansion f x)^2 := by
  unfold radialMassRadical sourcePhysicalMass sourceT sourceLapse
  field_simp
  ring

lemma source_radialMassLapse_eq {f : SourceMassFields} {x : Point}
    (hr : x 0 ≠ 0) (hp : (sourceMetric f x).PosDef) (hd : 0 < sourceExpansion f x) :
    radialMassLapse (sourceGamma f) (sourceShift f) (sourceT f) (sourcePhysicalMass f) x=
      sourceLapse f x := by
  rw [radialMassLapse,source_radialExpansion_eq,source_radialMassRadical_eq hr,
    Real.sqrt_sq (mul_nonneg (sourceLapse_pos hp).le hd.le)]
  exact mul_div_cancel_right₀ _ hd.ne'

lemma source_radialTangential_eq {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base x).PosDef) :
    radialTangential (sourceGamma f.base) (sourceT f.base) (sourceOriginalTau f) x=
      sourceTangentialK f.base x := by
  have hγ := metricBlock_leaf_posDef hp
  have ht : sourceOriginalTau f x=leafTensorTraceFree (sourceGamma f.base x)
      (sourceTangentialK f.base x) := by
    rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]
    rfl
  have hpull : leafTensorTraceFree (sourceGamma f.base x) (sourceOriginalTau f x)=sourceOriginalTau f x := by
    unfold leafTensorTraceFree
    rw [ht,leafTensorTrace_traceFree hγ]
    simp
  rw [radialTangential,hpull,sourceOriginalTau]
  have he : sourceT f.base x=traceProduct (inverse (sourceGamma f.base x)) (sourceTangentialK f.base x)/2 := by
    unfold sourceT
    ring
  rw [he]
  abel

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSBending
noncomputable section
open CKSCalculus Filter CKSAngularGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma collarParams_initial {R r S : ℝ} (hR : 0 < R) (hr : r ≤ R) :
    collarParams R r = oldParams (collarParams S r) := by
  have hr2 : r ≤ 2*R := hr.trans (by linarith)
  ext i
  fin_cases i <;> simp [collarParams,oldParams,roundingWeight_zero hR hr2,
    roundingWeight_deriv_initial hR hr2,paddingMass_initial hR hr,paddingWeight_zero hR hr]

end
end CKSBending

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma radiusLogPoint_exp {x : PhysicalPoint} (hr : 0 < x 0) :
    Real.exp (radiusLogPoint x 0)=x 0 := by simp [radiusLogPoint,Real.exp_log hr]

lemma inner_collar_fields {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hR : 0 < R) (hr : 0 < x 0) (hi : x 0 ≤ R) :
    physicalCollarGamma R f x = (x 0)^2 • (f.sigma (radiusLogPoint x)+f.metricError (radiusLogPoint x)) ∧
    physicalCollarShift R f x = f.shift (radiusLogPoint x) ∧
    physicalCollarT R f x = 1+f.tError (radiusLogPoint x) ∧
    physicalCollarF R f x = f.fstar (radiusLogPoint x)+f.massError (radiusLogPoint x) ∧
    physicalCollarL R f x = 1+f.LError (radiusLogPoint x) ∧
    physicalCollarEta R f x = x 0 • f.etaDivR (radiusLogPoint x) ∧
    physicalCollarRawTau R f x = (x 0)^2 • f.tauDivR2 (radiusLogPoint x) := by
  have hi2 : x 0 ≤ 2*R := hi.trans (by linarith)
  simp only [physicalCollarGamma,physicalCollarShift,physicalCollarT,physicalCollarF,
    physicalCollarL,physicalCollarEta,physicalCollarRawTau,collarQ,collarShift,collarT,
    collarF,collarL,collarLb,collarEtaDivR,radialLift,radiusLogPoint_exp hr,
    roundingWeight_zero hR hi2,paddingWeight_zero hR hi,paddingMass_initial hR hi,
    sub_zero,one_smul,one_mul,zero_div,add_zero,mul_one,true_and]

lemma radialExpansion_congr {γ δ : PhysicalPoint → Mat} {s t : PhysicalPoint → Point}
    {x : PhysicalPoint} (hq : γ =ᶠ[𝓝 x] δ) (hs : s =ᶠ[𝓝 x] t) :
    radialExpansion γ s x=radialExpansion δ t x := by
  have hqD (i a b) := D_congr (hq.mono (fun y hy => congrArg (fun q : Mat => q a b) hy))
    (CKSRealizedRound.basis i)
  have hsD (i a) := D_congr (hs.mono (fun y hy => congrFun hy a)) (CKSRealizedRound.basis i)
  have hd : leafRadialRate γ s x=leafRadialRate δ t x := by
    funext a b
    simp only [leafRadialRate,hq.self_of_nhds,hs.self_of_nhds,hqD,hsD]
  unfold radialExpansion
  rw [hq.self_of_nhds,hd]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_inner_collar_fields {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hR : 0 < R) (hr : 0 < x 0) (hi : x 0 ≤ R)
    (hf : f.base.RegularAt x) (hp : (sourceMetric f.base x).PosDef) :
    physicalCollarGamma R (sourceCollarData f.logFields) x = sourceGamma f.base x ∧
    physicalCollarShift R (sourceCollarData f.logFields) x = sourceShift f.base x ∧
    physicalCollarT R (sourceCollarData f.logFields) x = sourceT f.base x ∧
    physicalCollarF R (sourceCollarData f.logFields) x = sourcePhysicalMass f.base x ∧
    physicalCollarL R (sourceCollarData f.logFields) x = sourceOriginalL f x ∧
    physicalCollarEta R (sourceCollarData f.logFields) x = sourceOriginalEta f x ∧
    physicalCollarRawTau R (sourceCollarData f.logFields) x = sourceOriginalTau f x := by
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := inner_collar_fields (f:=sourceCollarData f.logFields) hR hr hi
  have hc := logRadiusChart_radiusLogPoint hr
  have he := radiusLogPoint_exp hr
  have hg := congrFun (sourceGamma_pullback f.base) (radiusLogPoint x)
  have hshift := congrFun (sourceShift_pullback f.base) (radiusLogPoint x)
  have htan := congrFun (sourceT_pullback f.base) (radiusLogPoint x)
  have hl := congrFun (sourceOriginalL_pullback f) (radiusLogPoint x)
  have heta := congrFun (sourceOriginalEta_pullback f) (radiusLogPoint x)
  have htau := congrFun (sourceOriginalTau_pullback f) (radiusLogPoint x)
  rw [hc] at hg hshift htan hl heta htau
  have hfp : f.base.RegularAt (logRadiusChart (radiusLogPoint x)) := hc.symm ▸ hf
  have hpp : (sourceMetric f.base (logRadiusChart (radiusLogPoint x))).PosDef := hc.symm ▸ hp
  have hmass := sourcePhysicalMass_pullback hfp hpp
  rw [hc] at hmass
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hγ]
    change (x 0)^2 • (f.logFields.base.sigma (radiusLogPoint x)+logQError f.logFields.base (radiusLogPoint x)) = _
    rw [logQError_scaled,he]
    have hh : f.logFields.base.sigma (radiusLogPoint x)+
        ((1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x)-f.logFields.base.sigma (radiusLogPoint x)) =
        (1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x) := by abel
    rw [hh,smul_smul, mul_one_div_cancel (pow_ne_zero _ hr.ne'),one_smul]
    exact hg.symm
  · rw [hs]
    exact hshift.symm
  · rw [ht]
    change 1+(logT f.base.logFields (radiusLogPoint x)-1)=sourceT f.base x
    rw [← htan]
    ring
  · rw [hF]
    change cksLeadingField f.base.logFields (radiusLogPoint x)+
      (logPhysicalMass f.base.logFields (radiusLogPoint x)-cksLeadingField f.base.logFields (radiusLogPoint x))=_
    rw [← hmass]
    ring
  · rw [hL]
    change 1+(logOriginalL f.logFields (radiusLogPoint x)-1)=_
    rw [← hl]
    ring
  · rw [hη]
    funext a
    change x 0*(logOriginalEta f.logFields (radiusLogPoint x) a/Real.exp (radiusLogPoint x 0))=_
    rw [he,← heta]
    field_simp
  · rw [hτ]
    funext a b
    change (x 0)^2*(logOriginalTau f.logFields (radiusLogPoint x) a b/Real.exp (radiusLogPoint x 0)^2)=_
    rw [he,← htau]
    field_simp

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma actualMetricFirstJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : actualMetricFirstJet G x = actualMetricFirstJet H x := by
  funext i j k
  exact D_congr (h.mono (fun y hy => congrArg (fun q : AmbientMat => q j k) hy)) _

lemma coordinateChristoffel_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : coordinateChristoffel G x = coordinateChristoffel H x := by
  unfold coordinateChristoffel
  rw [h.self_of_nhds,actualMetricFirstJet_congr h]

lemma covariantVector_congr {G H : PhysicalPoint → AmbientMat}
    {W V : PhysicalPoint → PhysicalPoint} {x e : PhysicalPoint}
    (hG : G =ᶠ[𝓝 x] H) (hW : W =ᶠ[𝓝 x] V) :
    covariantVector G e W x = covariantVector H e V x := by
  funext k
  have hd := D_congr (hW.mono (fun y hy => congrFun hy k)) e
  simp only [covariantVector,hW.self_of_nhds,coordinateChristoffel_congr hG,hd]

lemma frameCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameCoefficient G E x = frameCoefficient H F x := by
  funext i j k
  unfold frameCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds i,hE.self_of_nhds k,
    covariantVector_congr hG (hE.mono (fun y hy => hy j))]

lemma actualFrameBracket_congr {E F : LocalFrame} {x : PhysicalPoint}
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameBracket E x = actualFrameBracket F x := by
  funext i j k
  unfold actualFrameBracket
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hE.mono (fun y hy => congrFun (hy j) k)),
    D_congr (hE.mono (fun y hy => congrFun (hy i) k))]

lemma frameBracketCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameBracketCoefficient G E x = frameBracketCoefficient H F x := by
  funext i j k
  unfold frameBracketCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds k,actualFrameBracket_congr hE]

lemma actualFrameCurvature_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameCurvature G E x = actualFrameCurvature H F x := by
  have hc : ∀ᶠ y in 𝓝 x, frameCoefficient G E y=frameCoefficient H F y := by
    filter_upwards [hG.eventually_nhds,hE.eventually_nhds] with y hyG hyE
    exact frameCoefficient_congr hyG hyE
  funext i j k l
  unfold actualFrameCurvature
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hc.mono (fun y hy => congrArg (fun q => q j k l) hy)),
    D_congr (hc.mono (fun y hy => congrArg (fun q => q i k l) hy)),
    hc.self_of_nhds,frameBracketCoefficient_congr hG hE]

lemma actualFrameScalar_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameScalar G E x = actualFrameScalar H F x := by
  unfold actualFrameScalar
  rw [actualFrameCurvature_congr hG hE]

lemma coordinateConnectionVector_congr {G H : PhysicalPoint → AmbientMat}
    {x e v : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) :
    coordinateConnectionVector G e v x = coordinateConnectionVector H e v x := by
  unfold coordinateConnectionVector
  rw [coordinateChristoffel_congr hG]

lemma coordinateTensorCovariant_congr {G H K L : PhysicalPoint → AmbientMat}
    {x e v w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateTensorCovariant G K e v w x = coordinateTensorCovariant H L e v w x := by
  unfold coordinateTensorCovariant
  have hd (i j) := D_congr (hK.mono (fun y hy => congrArg (fun k : AmbientMat => k i j) hy)) e
  simp only [hK.self_of_nhds,coordinateConnectionVector_congr hG,hd]

lemma coordinateMomentum_congr {G H K L : PhysicalPoint → AmbientMat}
    {x w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateMomentum G K x w = coordinateMomentum H L x w := by
  have hc : ∀ i j, coordinateTensorCovariant G K (CKSRealizedRound.basis i)
      (CKSRealizedRound.basis j) w x = coordinateTensorCovariant H L
      (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
    fun _ _ => coordinateTensorCovariant_congr hG hK
  have ht : (fun y => ((G y)⁻¹*K y).trace) =ᶠ[𝓝 x] (fun y => ((H y)⁻¹*L y).trace) := by
    filter_upwards [hG,hK] with y hyG hyK
    rw [hyG,hyK]
  simp only [coordinateMomentum,hG.self_of_nhds,hc,D_congr ht]

lemma momentumCovector_congr {G H K L : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    momentumCovector G K x = momentumCovector H L x := by
  funext i
  exact coordinateMomentum_congr hG hK

theorem physicalDEC_congr {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    physicalDEC G K E x ↔ physicalDEC H L F x := by
  unfold physicalDEC physicalEnergy
  rw [momentumCovector_congr hG hK,actualFrameScalar_congr hG hE,
    hG.self_of_nhds,hK.self_of_nhds]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_inner_collar_fields_eventually {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef) :
    ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R (sourceCollarData f.logFields) y = sourceGamma f.base y ∧
      physicalCollarShift R (sourceCollarData f.logFields) y = sourceShift f.base y ∧
      physicalCollarT R (sourceCollarData f.logFields) y = sourceT f.base y ∧
      physicalCollarF R (sourceCollarData f.logFields) y = sourcePhysicalMass f.base y ∧
      physicalCollarL R (sourceCollarData f.logFields) y = sourceOriginalL f y ∧
      physicalCollarEta R (sourceCollarData f.logFields) y = sourceOriginalEta f y ∧
      physicalCollarRawTau R (sourceCollarData f.logFields) y = sourceOriginalTau f y := by
  have hr' := ((continuous_apply 0).continuousAt (x := x)).eventually (Ioi_mem_nhds hr)
  have hi' := ((continuous_apply 0).continuousAt (x := x)).eventually (Iio_mem_nhds hi)
  filter_upwards [hr',hi',hf.eventually,hp] with y hyr hyi hyf hyp
  exact source_inner_collar_fields (hr.trans hi) hyr hyi.le hyf hyp

lemma source_inner_collar_lapse {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x) :
    physicalCollarU R (sourceCollarData f.logFields) x=sourceLapse f.base x := by
  have h := source_inner_collar_fields_eventually hr hi hf hp
  have he := radialExpansion_congr (h.mono (fun _ hy => hy.1))
    (h.mono (fun _ hy => hy.2.1))
  have ht := h.self_of_nhds.2.2.1
  have hF := h.self_of_nhds.2.2.2.1
  unfold physicalCollarU radialMassLapse
  rw [he]
  unfold radialMassRadical
  rw [ht,hF]
  exact source_radialMassLapse_eq hr.ne' hp.self_of_nhds hd

lemma source_inner_collar_recovery {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x)
    (hk : (sourceTangentialK f.base x).IsHermitian) :
    physicalCollarMetric R (sourceCollarData f.logFields) x=sourceMetric f.base x ∧
    physicalCollarTensor R (sourceCollarData f.logFields) x=sourceTensor f x ∧
    ∀ i, physicalCollarFrame R (sourceCollarData f.logFields) i x=sourceFrame f.base i x := by
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := source_inner_collar_fields (hr.trans hi) hr hi.le hf hp.self_of_nhds
  have hU := source_inner_collar_lapse hr hi hf hp hd
  have hT : physicalCollarTangential R (sourceCollarData f.logFields) x=sourceTangentialK f.base x := by
    unfold physicalCollarTangential radialTangential
    rw [hγ,ht,hτ]
    exact source_radialTangential_eq hp.self_of_nhds
  refine ⟨?_,?_,?_⟩
  · unfold physicalCollarMetric
    rw [hU,hγ,hs]
    exact source_metric_foliation hp.self_of_nhds
  · unfold physicalCollarTensor
    rw [hU,hL,hη,hT,hs]
    exact source_tensor_foliation hp.self_of_nhds hk
  · intro i
    unfold physicalCollarFrame sourceFrame
    rw [hU,hγ,hs]

theorem physical_source_inner_collar_DEC_iff {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : ∀ᶠ y in 𝓝 x, 0 < sourceExpansion f.base y)
    (hk : ∀ᶠ y in 𝓝 x, (sourceTangentialK f.base y).IsHermitian) :
    physicalDEC (physicalCollarMetric R (sourceCollarData f.logFields))
      (physicalCollarTensor R (sourceCollarData f.logFields))
      (physicalCollarFrame R (sourceCollarData f.logFields)) x ↔
      physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base) x := by
  have hr' := ((continuous_apply 0).continuousAt (x := x)).eventually (Ioi_mem_nhds hr)
  have hi' := ((continuous_apply 0).continuousAt (x := x)).eventually (Iio_mem_nhds hi)
  have hrec : ∀ᶠ y in 𝓝 x,
      physicalCollarMetric R (sourceCollarData f.logFields) y=sourceMetric f.base y ∧
      physicalCollarTensor R (sourceCollarData f.logFields) y=sourceTensor f y ∧
      ∀ i, physicalCollarFrame R (sourceCollarData f.logFields) i y=sourceFrame f.base i y := by
    filter_upwards [hr',hi',hf.eventually,hp.eventually_nhds,hd,hk] with y hyr hyi hyf hyp hyd hyk
    exact source_inner_collar_recovery hyr hyi hyf hyp hyd hyk
  exact physicalDEC_congr (hrec.mono (fun _ h => h.1)) (hrec.mono (fun _ h => h.2.1))
    (hrec.mono (fun _ h => h.2.2))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

structure SourceTensorFields.AngularRelatedAt (φ : Angle → Angle)
    (f f' : SourceTensorFields) (x : Point) : Prop where
  sigma : f'.base.sigma (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.sigma (φ (angularProjection x)))
  mg : f'.base.mg (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.mg (φ (angularProjection x)))
  mK : f'.base.mK (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.mK (φ (angularProjection x)))
  mr : f'.base.mr (angularProjection x) = f.base.mr (φ (angularProjection x))
  eg : f'.base.eg x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.eg (angularChange φ x))
  ek : f'.base.ek x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.ek (angularChange φ x))
  b : f'.base.b x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
    (f.base.b (angularChange φ x))
  err : f'.base.err x = f.base.err (angularChange φ x)
  kr : f'.kr x = f.kr (angularChange φ x)
  kb : f'.kb x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
    (f.kb (angularChange φ x))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix
lemma angular_inverse_mulVec (A γ : Mat) (b : Point) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    A *ᵥ ((angularCongruence A γ)⁻¹ *ᵥ angularCovector A b) = γ⁻¹ *ᵥ b := by
  rw [angularCongruence_inverse A γ hA hγ]
  simp only [angularCovector,Matrix.mulVec_mulVec]
  have hAt : IsUnit A.transpose.det := by simpa using hA
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hAt,Matrix.mul_one,← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hA,Matrix.one_mul]
lemma angular_dual_contraction (A : Mat) (b v : Point) :
    angularCovector A b ⬝ᵥ v = b ⬝ᵥ (A *ᵥ v) := by
  unfold angularCovector
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
lemma angular_bilinear_contraction (A T : Mat) (v w : Point) :
    v ⬝ᵥ (angularCongruence A T *ᵥ w) = (A *ᵥ v) ⬝ᵥ (T *ᵥ (A *ᵥ w)) := by
  unfold angularCongruence
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  rw [dotProduct_comm,← angularCovector,angular_dual_contraction,dotProduct_comm]
lemma angular_covector_tensor (A T : Mat) (v : Point) :
    (angularCongruence A T).transpose *ᵥ v =
      angularCovector A (T.transpose *ᵥ (A *ᵥ v)) := by
  simp only [angularCongruence,Matrix.transpose_mul,Matrix.transpose_transpose,angularCovector,
    Matrix.mulVec_mulVec,Matrix.mul_assoc]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
@[simp] lemma angularProjection_angularChange (φ : Angle → Angle) (x : Point) :
    angularProjection (angularChange φ x) = φ (angularProjection x) := by
  ext a; simp [angularProjection,angularChange]
lemma sourceGamma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceGamma f'.base x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceGamma f.base (angularChange φ x)) := by
  unfold sourceGamma
  rw [h.sigma,h.mg,h.eg]
  simp [angularCongruence_add,angularCongruence_smul]
lemma sourceTangentialK_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceTangentialK f'.base x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceTangentialK f.base (angularChange φ x)) := by
  unfold sourceTangentialK
  rw [h.sigma,h.mK,h.ek]
  simp [angularCongruence_add,angularCongruence_smul]
lemma sourceRadialMetric_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceRadialMetric f'.base x = sourceRadialMetric f.base (angularChange φ x) := by
  simp only [sourceRadialMetric,h.mr,h.err,angularProjection_angularChange,angularChange_zero]
lemma sourceRadialK_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceRadialK f' x = sourceRadialK f (angularChange φ x) := by
  simp only [sourceRadialK,h.kr,angularChange_zero]
lemma sourceShift_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    CKSAngularGeometry.angularJacobian φ x *ᵥ sourceShift f'.base x =
      sourceShift f.base (angularChange φ x) := by
  have hs (k : SourceMassFields) (y : Point) : sourceShift k y = (sourceGamma k y)⁻¹ *ᵥ k.b y := by
    ext a
    change (∑ b, inverse (sourceGamma k y) a b*k.b y b) =
      ∑ b, (sourceGamma k y)⁻¹ a b*k.b y b
    rw [inverse_eq]
  rw [hs,hs,sourceGamma_angular h,h.b]
  exact angular_inverse_mulVec _ _ _ hA hγ
lemma sourceSchur_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceSchur f'.base x = sourceSchur f.base (angularChange φ x) := by
  have he (k : SourceMassFields) (y : Point) : sourceSchur k y =
      sourceRadialMetric k y-k.b y ⬝ᵥ sourceShift k y := by
    simp only [sourceSchur,sourceShift,dotProduct,Fin.sum_univ_two]
    ring
  rw [he,he,sourceRadialMetric_angular h,h.b,angular_dual_contraction,sourceShift_angular h hA hγ]
lemma sourceLapse_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceLapse f'.base x = sourceLapse f.base (angularChange φ x) := by
  simp only [sourceLapse,sourceSchur_angular h hA hγ]
lemma sourceT_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceT f'.base x = sourceT f.base (angularChange φ x) := by
  have he (g T : Mat) : traceProduct (inverse g) T = leafTensorTrace g T := by
    rw [leafTensorTrace_eq]; rfl
  simp only [sourceT,he,sourceGamma_angular h,sourceTangentialK_angular h,
    leafTensorTrace_covariant _ _ _ hA hγ]
lemma sourceOriginalL_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalL f' x = sourceOriginalL f (angularChange φ x) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalL k y = (sourceLapse k.base y)^2 *
      (sourceRadialK k y-2*(k.kb y ⬝ᵥ sourceShift k.base y)+
        sourceShift k.base y ⬝ᵥ (sourceTangentialK k.base y *ᵥ sourceShift k.base y)) := by
    simp only [sourceOriginalL,sourceLapse,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [he,he,sourceLapse_angular h hA hγ,sourceRadialK_angular h,h.kb,
    angular_dual_contraction,sourceTangentialK_angular h,angular_bilinear_contraction,
    sourceShift_angular h hA hγ]
lemma sourceOriginalEta_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalEta f' x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
      (sourceOriginalEta f (angularChange φ x)) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalEta k y = sourceLapse k.base y •
      (k.kb y-(sourceTangentialK k.base y).transpose *ᵥ sourceShift k.base y) := by
    ext a
    simp only [sourceOriginalEta,sourceLapse,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Fin.sum_univ_two]
    ring
  rw [he,he,sourceLapse_angular h hA hγ,h.kb,sourceTangentialK_angular h,
    angular_covector_tensor,sourceShift_angular h hA hγ]
  unfold angularCovector
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub]
lemma sourceOriginalTau_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalTau f' x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceOriginalTau f (angularChange φ x)) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalTau k y =
      leafTensorTraceFree (sourceGamma k.base y) (sourceTangentialK k.base y) := by
    rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]
    rfl
  rw [he,he,sourceGamma_angular h,sourceTangentialK_angular h]
  exact (leaf_trace_covariant _ _ _ hA hγ).2
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma angularJacobian_contDiffAt {φ : Point → Point} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x)) :
    ContDiffAt ℝ 1 (angularJacobian φ) x := by
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  have hF := (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply
    (show ContDiffAt ℝ 1 (fun _ : Point => CKSAngularGeometry.basis b) (angularProjection x) from contDiffAt_const)
  exact (contDiffAt_pi.mp hF a).comp x angularProjection.contDiff.contDiffAt
lemma matrix_det_isUnit_eventually {E : Type*} [TopologicalSpace E] {f : E → Mat} {x : E}
    (hc : ContinuousAt f x) (h : IsUnit (f x).det) : ∀ᶠ y in 𝓝 x, IsUnit (f y).det := by
  exact (((continuous_id.matrix_det : Continuous (Matrix.det : Mat → ℝ)).continuousAt.comp hc).eventually_ne
    (isUnit_iff_ne_zero.mp h)).mono fun _ hy => isUnit_iff_ne_zero.mpr hy
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma sourceExpansion_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (hr : x 0 ≠ 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.RegularAt (angularChange φ x)) (hf' : f'.RegularAt x)
    (hrel : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' y)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hp : (sourceMetric f.base (angularChange φ x)).PosDef)
    (hp' : (sourceMetric f'.base x).PosDef) :
    sourceExpansion f'.base x = sourceExpansion f.base (angularChange φ x) := by
  have hr' : angularChange φ x 0 ≠ 0 := by simpa using hr
  have hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  have hγ' : IsUnit (sourceGamma f'.base x).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp').det_pos.ne'
  have hγε : ∀ᶠ y in 𝓝 x, IsUnit (sourceGamma f.base (angularChange φ y)).det :=
    matrix_det_isUnit_eventually ((sourceGamma_regular hf.base hr').continuousAt.comp
      ((angularChange_contDiffAt hφ).continuousAt)) hγ
  have hAε := matrix_det_isUnit_eventually (angularJacobian_contDiffAt hφ).continuousAt hA
  have hrels : ∀ᶠ y in 𝓝 x, CKSAngularGeometry.angularJacobian φ y *ᵥ sourceShift f'.base y =
      sourceShift f.base (angularChange φ y) := by
    filter_upwards [hrel,hγε,hAε] with y hy hgy hay
    exact sourceShift_angular hy hay hgy
  have hgdet : determinant (sourceGamma f.base (angularChange φ x)) ≠ 0 := by
    rw [determinant_eq]; exact isUnit_iff_ne_zero.mp hγ
  have hgdet' : determinant (sourceGamma f'.base x) ≠ 0 := by
    rw [determinant_eq]; exact isUnit_iff_ne_zero.mp hγ'
  have hd := (radial_lapse_angular_natural (t := sourceT f.base) (F := sourcePhysicalMass f.base) hφ
    ((sourceGamma_regular hf.base hr').differentiableAt (by norm_num))
    ((sourceGamma_regular hf'.base hr).differentiableAt (by norm_num))
    ((sourceShift_regular hf.base hr' hgdet).differentiableAt (by norm_num))
    ((sourceShift_regular hf'.base hr hgdet').differentiableAt (by norm_num))
    (hrel.mono fun y hy => sourceGamma_angular hy) hrels hA hγ).1
  simpa only [source_radialExpansion_eq] using hd
lemma sourcePhysicalMass_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (hr : x 0 ≠ 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.RegularAt (angularChange φ x)) (hf' : f'.RegularAt x)
    (hrel : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' y)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hp : (sourceMetric f.base (angularChange φ x)).PosDef)
    (hp' : (sourceMetric f'.base x).PosDef) :
    sourcePhysicalMass f'.base x = sourcePhysicalMass f.base (angularChange φ x) := by
  have he (k : SourceMassFields) (y : Point) : sourcePhysicalMass k y = y 0/2*
      (1+(y 0*sourceT k y)^2-(sourceLapse k y*sourceExpansion k y)^2) := by
    simp only [sourcePhysicalMass,sourceT,sourceLapse]
    ring
  have hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  rw [he,he,sourceT_angular hrel.self_of_nhds hA hγ,sourceLapse_angular hrel.self_of_nhds hA hγ,
    sourceExpansion_angular hr hφ hf hf' hrel hA hp hp',angularChange_zero]
lemma sourceAspect_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection x))).det) :
    sourceAspect f'.base (angularProjection x) = sourceAspect f.base (φ (angularProjection x)) := by
  have he (g T : Mat) : traceProduct (inverse g) T = leafTensorTrace g T := by
    rw [leafTensorTrace_eq]; rfl
  unfold sourceAspect
  rw [he,he,h.sigma,h.mg,h.mK,h.mr,
    ← angularCongruence_smul,← angularCongruence_add,leafTensorTrace_covariant _ _ _ hA hσ]
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def angleTransition (P Q : SmoothAngularPatch) (θ : Angle) : Angle := Q.extension (P.param θ)
def angularOverlap (P Q : SmoothAngularPatch) : Set Angle :=
  P.chart.target ∩ P.chart.symm ⁻¹' Q.chart.source
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped Topology
lemma sourceRemainder_leading_limit {j q : ℕ} {R : ℝ} {W : Set Angle}
    {f : Point → ℝ} {M : Angle → ℝ}
    (h : SourceRemainderOn j (q+1) (angularRadialTail R W)
      (fun y => f y-ordinaryLeadingComponent q M y)) {θ : Angle} (hθ : θ ∈ W) :
    Tendsto (fun r : ℝ => r^q * f (slice r θ)) atTop (𝓝 (M θ)) := by
  obtain ⟨B,hB,hb⟩ := h.bound
  have he : ∀ᶠ r : ℝ in atTop, ‖r^q * f (slice r θ) - M θ‖ ≤ B/r := by
    filter_upwards [eventually_gt_atTop (max R 0)] with r hr
    have hr0 : 0<r := lt_of_le_of_lt (le_max_right _ _) hr
    have hrR : R<r := lt_of_le_of_lt (le_max_left _ _) hr
    have hbr := hb (slice r θ) (by exact ⟨by simpa using hrR,by simpa only [angularProjection_slice] using hθ⟩) [] (by simp)
    simp only [scaledIter,slice_zero] at hbr
    have hid : r^q * f (slice r θ)-M θ = r^q*(f (slice r θ)-ordinaryLeadingComponent q M (slice r θ)) := by
      simp only [ordinaryLeadingComponent,slice_zero,angularProjection_slice]
      field_simp
    rw [Real.norm_eq_abs,hid,abs_mul,abs_of_pos (pow_pos hr0 q)]
    calc
      r^q * |f (slice r θ)-ordinaryLeadingComponent q M (slice r θ)| ≤ r^q * (B/r^(q+1)) :=
        mul_le_mul_of_nonneg_left hbr (pow_nonneg hr0.le _)
      _ = B/r := by rw [pow_succ]; field_simp
  have ht : Tendsto (fun r : ℝ => r^q * f (slice r θ)-M θ) atTop (𝓝 0) :=
    squeeze_zero_norm' he (tendsto_const_nhds.div_atTop tendsto_id)
  simpa only [sub_add_cancel,zero_add] using ht.add_const (M θ)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma angularOverlap_open (P Q : SmoothAngularPatch) : IsOpen (angularOverlap P Q) :=
  P.chart.symm.isOpen_inter_preimage Q.chart.open_source
lemma angleTransition_eq_chart {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : angleTransition P Q θ = Q.chart (P.chart.symm θ) :=
  Q.extension_eq _ hθ.2
lemma angleTransition_target {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : angleTransition P Q θ ∈ Q.chart.target := by
  rw [angleTransition_eq_chart hθ]
  exact Q.chart.map_source hθ.2
lemma param_angleTransition {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : Q.param (angleTransition P Q θ) = P.param θ := by
  rw [angleTransition_eq_chart hθ]
  exact Q.param_chart hθ.2
lemma angleTransition_smoothAt {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : ContDiffAt ℝ ∞ (angleTransition P Q) θ := by
  exact (Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds (Q.source_domain _ hθ.2))).comp θ
    (P.param_contDiffAt hθ.1)
lemma polar_angularTransition_eq {P Q : SmoothAngularPatch} {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ angularOverlap P Q) :
    polarParam Q (angularChange (angleTransition P Q) y) = polarParam P y := by
  simp only [polarParam,angularChange,angularProjection_slice,slice_zero]
  rw [param_angleTransition hy]
lemma polar_angularTransition_eventuallyEq {P Q : SmoothAngularPatch} {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ angularOverlap P Q) :
    (polarParam Q ∘ angularChange (angleTransition P Q)) =ᶠ[𝓝 y] polarParam P := by
  filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)] with z hz
  exact polar_angularTransition_eq hz
lemma polarTensor_angularTransition (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) (a b : CKSMixedGeometry.I) :
    coordinateTensorPullback (angularChange (angleTransition P Q)) (polarTensorComponents Q A) a b y =
      polarTensorComponents P A a b y := by
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  have h := polarTensor_covariance P Q A (angularChange_differentiableAt ht)
    ((polarParam_contDiffAt P hy.1).differentiableAt (by simp))
    ((polarParam_contDiffAt Q (by simpa only [angularChange,angularProjection_slice] using angleTransition_target hy)).differentiableAt (by simp))
    (differentiableAt_id (𝕜 := ℝ)) (polar_angularTransition_eventuallyEq hy) a b
  have hid : spatialTensorPullback (id : E → E) A = A := by
    funext z; ext v w
    simp [spatialTensorPullback,ContinuousLinearMap.bilinearComp]
  rw [hid] at h
  exact h
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice
lemma angularCongruence_entries (J A : Mat) (a b : Fin 2) : angularCongruence J A a b =
    ∑ i : Fin 2, ∑ j : Fin 2, J i a * A i j * J j b := by
  simp [angularCongruence,Matrix.mul_apply,Fin.sum_univ_two]
  ring
lemma fderiv_angularChange_radial {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) :
    fderiv ℝ (angularChange φ) x (CKSRealizedRound.basis 0) = CKSRealizedRound.basis 0 := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact fderiv_angularChange_zero hφ _
  · rw [fderiv_angularChange_succ hφ]
    have hz : angularProjection (CKSRealizedRound.basis 0) = 0 := by
      ext a; simp [CKSRealizedRound.basis,angularProjection]
    rw [hz,map_zero]
    simp [CKSRealizedRound.basis]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensor_angular_radial (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    polarTensorComponents P A 0 0 y =
      polarTensorComponents Q A 0 0 (angularChange (angleTransition P Q) y) := by
  have h := (polarTensor_angularTransition P Q A hy 0 0).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A 0 0] at h
  change polarTensorComponents P A 0 0 y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0))) at h
  rw [fderiv_angularChange_radial ht] at h
  exact h
lemma polarTensor_angular_tangential (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    (fun a b : Fin 2 => polarTensorComponents P A a.succ b.succ y) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (fun a b : Fin 2 => polarTensorComponents Q A a.succ b.succ (angularChange (angleTransition P Q) y)) := by
  ext a b
  have h := (polarTensor_angularTransition P Q A hy a.succ b.succ).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A a.succ b.succ] at h
  change polarTensorComponents P A a.succ b.succ y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis a.succ)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis b.succ))) at h
  rw [fderiv_angularChange_basis ht a,fderiv_angularChange_basis ht b] at h
  rw [h]
  refine Eq.trans ?_ (angularCongruence_entries
    (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
    (fun a b => polarTensorComponents Q A a.succ b.succ (angularChange (angleTransition P Q) y)) a b).symm
  simp only [Fin.sum_univ_two,map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,polarTensorComponents,CKSMixedGeometry.basis,CKSRealizedRound.basis]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise Matrix
lemma CKS_tangential_leading_overlap (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ} {j j' q q' : ℕ}
    (hA : SourceCKSComponents j q (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents j' q' (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    {θ : Angle} (hθ : θ ∈ angularOverlap P Q) (hW : angleTransition P Q θ ∈ W) (hW' : θ ∈ W') :
    (fun a b : Fin 2 => mg' a.succ b.succ θ) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ))
        (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ)) := by
  let J := CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ)
  have hl : Tendsto (fun r : ℝ => (fun a b : Fin 2 => r * polarTensorComponents Q A a.succ b.succ
      (slice r (angleTransition P Q θ)))) atTop
      (𝓝 (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ))) := by
    apply tendsto_pi_nhds.2
    intro a
    apply tendsto_pi_nhds.2
    intro b
    simpa only [pow_one] using sourceRemainder_leading_limit
      (hA.angular a.succ b.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _)) hW
  have hl' : Tendsto (fun r : ℝ => (fun a b : Fin 2 => r * polarTensorComponents P A a.succ b.succ
      (slice r θ))) atTop (𝓝 (fun a b : Fin 2 => mg' a.succ b.succ θ)) := by
    apply tendsto_pi_nhds.2
    intro a
    apply tendsto_pi_nhds.2
    intro b
    simpa only [pow_one] using sourceRemainder_leading_limit
      (hA'.angular a.succ b.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _)) hW'
  have hc : Continuous (angularCongruence J) := by
    unfold angularCongruence
    fun_prop
  have he (r : ℝ) :
      angularCongruence J (fun a b : Fin 2 => r * polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ))) =
      (fun a b : Fin 2 => r * polarTensorComponents P A a.succ b.succ (slice r θ)) := by
    change angularCongruence J (r • (fun a b : Fin 2 => polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ)))) =
      r • (fun a b : Fin 2 => polarTensorComponents P A a.succ b.succ (slice r θ))
    refine (angularCongruence_smul J
      (fun a b => polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ))) r).trans ?_
    congr 1
    have h := polarTensor_angular_tangential P Q A (y := slice r θ)
      (by simpa only [angularProjection_slice] using hθ)
    have hJ : CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice r θ) = J := by
      unfold J
      unfold CKSAngularGeometry.angularJacobian
      rw [angularProjection_slice,angularProjection_slice]
    have hch : angularChange (angleTransition P Q) (slice r θ) = slice r (angleTransition P Q θ) := by
      simp only [angularChange,slice_zero,angularProjection_slice]
    rw [hJ,hch] at h
    exact h.symm
  exact tendsto_nhds_unique hl' ((hc.tendsto _).comp hl |>.congr' (Filter.Eventually.of_forall he))

theorem CKS_angular_leading_overlap (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ} {mg mg' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    {j j' : ℕ}
    (hA : SourceCKSComponents j 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents j' 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    {θ : Angle} (hθ : θ ∈ angularOverlap P Q) (hW : angleTransition P Q θ ∈ W) (hW' : θ ∈ W') :
    mr' θ = mr (angleTransition P Q θ) ∧
    (fun a b : Fin 2 => mg' a.succ b.succ θ) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ))
        (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ)) := by
  refine ⟨?_, CKS_tangential_leading_overlap P Q A hA hA' hθ hW hW'⟩
  have hl := sourceRemainder_leading_limit hA.radial hW
  have hl' := sourceRemainder_leading_limit hA'.radial hW'
  apply tendsto_nhds_unique hl'
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro r
  have h := polarTensor_angular_radial P Q A (y := slice r θ)
    (by simpa only [angularProjection_slice] using hθ)
  simpa only [angularChange,slice_zero,angularProjection_slice] using congrArg (fun z : ℝ => r^5*z) h.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensor_angular_mixed (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    (fun a : Fin 2 => polarTensorComponents P A 0 a.succ y) =
      angularCovector (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (fun a : Fin 2 => polarTensorComponents Q A 0 a.succ (angularChange (angleTransition P Q) y)) := by
  ext a
  have h := (polarTensor_angularTransition P Q A hy 0 a.succ).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A 0 a.succ] at h
  change polarTensorComponents P A 0 a.succ y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis a.succ))) at h
  rw [fderiv_angularChange_radial ht,fderiv_angularChange_basis ht a] at h
  rw [h]
  simp only [Fin.sum_univ_two,map_add,map_smul,
    smul_eq_mul,polarTensorComponents,CKSMixedGeometry.basis,CKSRealizedRound.basis,
    angularCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_two]
lemma angularRoundMetric_overlap (P Q : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    angularRoundMetric P.param (angularProjection y) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (angularRoundMetric Q.param (angleTransition P Q (angularProjection y))) := by
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  have hq := (Q.param_contDiffAt (angleTransition_target hy)).differentiableAt (by simp)
  have he : (Q.param ∘ angleTransition P Q) =ᶠ[𝓝 (angularProjection y)] P.param := by
    filter_upwards [(angularOverlap_open P Q).mem_nhds hy] with θ hθ
    exact param_angleTransition hθ
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp _ hq ht] at hd
  have hvec (a : Fin 2) :
      fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) =
      ∑ i : Fin 2, CKSAngularGeometry.angularJacobian (angleTransition P Q) y i a •
        fderiv ℝ Q.param (angleTransition P Q (angularProjection y)) (CKSAngularGeometry.basis i) := by
    rw [← hd,ContinuousLinearMap.comp_apply]
    conv_lhs => arg 2; rw [← angular_vector_expansion (fderiv ℝ (angleTransition P Q) (angularProjection y) (CKSAngularGeometry.basis a))]
    simp only [map_sum,map_smul]
    rfl
  ext a b
  dsimp only [angularRoundMetric]
  rw [hvec,hvec,angularCongruence_entries]
  simp only [Fin.sum_univ_two,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,angularRoundMetric]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

theorem actual_CKS_fields_angular_related (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W') :
    (cksSourceFields (angularRoundMetric Q.param) (polarTensorComponents Q A) (polarTensorComponents Q B) mr mg mK).AngularRelatedAt
      (angleTransition P Q)
      (cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A) (polarTensorComponents P B) mr' mg' mK') y := by
  obtain ⟨hmr,hmg⟩ := CKS_angular_leading_overlap P Q A hA hA' hy hW hW'
  have hmK := CKS_tangential_leading_overlap P Q B hB hB' hy hW hW'
  have hJ : CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 (angularProjection y)) =
      CKSAngularGeometry.angularJacobian (angleTransition P Q) y := by
    unfold CKSAngularGeometry.angularJacobian
    rw [angularProjection_slice]
  rw [hJ] at hmg hmK
  have hsub (J X Y : CKSAngularGeometry.Mat) :
      angularCongruence J (X-Y) = angularCongruence J X-angularCongruence J Y := by
    simp only [angularCongruence,Matrix.mul_sub,Matrix.sub_mul]
  have hrem (C : SpatialTensor)
      (m m' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ)
      (hm : (fun a b : Fin 2 => m' a.succ b.succ (angularProjection y)) =
        angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
          (fun a b : Fin 2 => m a.succ b.succ (angleTransition P Q (angularProjection y)))) :
      (fun a b : Fin 2 => polarTensorComponents P C a.succ b.succ y - ordinaryLeadingComponent 1 (m' a.succ b.succ) y) =
        angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
          (fun a b : Fin 2 => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y) -
            ordinaryLeadingComponent 1 (m a.succ b.succ) (angularChange (angleTransition P Q) y)) := by
    simp only [ordinaryLeadingComponent,pow_one,angularChange_zero,angularProjection_angularChange]
    change (fun a b : Fin 2 => polarTensorComponents P C a.succ b.succ y) -
        (1/y 0) • (fun a b : Fin 2 => m' a.succ b.succ (angularProjection y)) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        ((fun a b : Fin 2 => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y)) -
          (1/y 0) • (fun a b : Fin 2 => m a.succ b.succ (angleTransition P Q (angularProjection y))))
    rw [polarTensor_angular_tangential P Q C hy,hm]
    let J := CKSAngularGeometry.angularJacobian (angleTransition P Q) y
    let X : CKSAngularGeometry.Mat :=
      fun a b => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y)
    let Y : CKSAngularGeometry.Mat := fun a b => m a.succ b.succ (angleTransition P Q (angularProjection y))
    exact ((hsub J X ((1 / y 0) • Y)).trans
      (congrArg (fun Z : CKSAngularGeometry.Mat => angularCongruence J X - Z)
        (angularCongruence_smul J Y (1 / y 0)))).symm
  refine ⟨?_,hmg,hmK,hmr,hrem A mg mg' hmg,hrem B mK mK' hmK,?_,?_,?_,?_⟩
  · exact angularRoundMetric_overlap P Q hy
  · exact polarTensor_angular_mixed P Q A hy
  · change polarTensorComponents P A 0 0 y - ordinaryLeadingComponent 5 mr' y =
      polarTensorComponents Q A 0 0 (angularChange (angleTransition P Q) y) -
        ordinaryLeadingComponent 5 mr (angularChange (angleTransition P Q) y)
    rw [polarTensor_angular_radial P Q A hy]
    simp only [ordinaryLeadingComponent,angularChange_zero,angularProjection_angularChange,hmr]
  · exact polarTensor_angular_radial P Q B hy
  · exact polarTensor_angular_mixed P Q B hy
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma actual_angleTransition_isUnit (P Q : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    IsUnit (CKSAngularGeometry.angularJacobian (angleTransition P Q) y).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hp := (P.roundMetric_posDef hy.1).det_pos
  have ht := congrArg Matrix.det (angularRoundMetric_overlap P Q hy)
  simp only [angularCongruence,Matrix.det_mul,Matrix.det_transpose,hz,mul_zero,zero_mul] at ht
  rw [ht] at hp
  exact lt_irrefl _ hp
lemma actual_CKS_fields_angular_related_eventually (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} (hWo : IsOpen W) (hW'o : IsOpen W') {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W') :
    ∀ᶠ z in 𝓝 y,
      (cksSourceFields (angularRoundMetric Q.param) (polarTensorComponents Q A) (polarTensorComponents Q B) mr mg mK).AngularRelatedAt
        (angleTransition P Q)
        (cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A) (polarTensorComponents P B) mr' mg' mK') z := by
  have ho := angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)
  have hw := ((angleTransition_smoothAt hy).continuousAt.comp angularProjection.continuous.continuousAt).preimage_mem_nhds (hWo.mem_nhds hW)
  have hw' := angularProjection.continuous.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW')
  filter_upwards [ho,hw,hw'] with z hz hzW hzW'
  exact actual_CKS_fields_angular_related P Q A B hA hA' hB hB' hz hzW hzW'
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice
@[simp] lemma angularJacobian_logRadiusChart (φ : Point → Point) (x : PhysicalPoint) :
    angularJacobian φ (logRadiusChart x) = angularJacobian φ x := by
  unfold angularJacobian
  rw [angularProjection_logRadiusChart]
@[simp] lemma angularChange_logRadiusChart (φ : Point → Point) (x : PhysicalPoint) :
    angularChange φ (logRadiusChart x) = logRadiusChart (angularChange φ x) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,angularChange]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma source_log_leading_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y))
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ y).det)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection y))).det) :
    cksLeadingField f'.base.logFields y = cksLeadingField f.base.logFields (angularChange φ y) := by
  rw [source_leading_mass,source_leading_mass]
  dsimp only
  rw [angularProjection_angularChange]
  have hJA : IsUnit (CKSAngularGeometry.angularJacobian φ (logRadiusChart y)).det := by simpa using hA
  have hs : IsUnit (f.base.sigma (φ (angularProjection (logRadiusChart y)))).det := by simpa only [angularProjection_logRadiusChart] using hσ
  simpa only [angularProjection_logRadiusChart] using congrArg (fun z : ℝ => z/4) (sourceAspect_angular h hJA hs)
lemma source_logGamma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    logGamma f'.base.logFields y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (logGamma f.base.logFields (angularChange φ y)) := by
  have hg := sourceGamma_angular h
  rw [angularJacobian_logRadiusChart,angularChange_logRadiusChart,
    congrFun (sourceGamma_pullback f'.base) y,
    congrFun (sourceGamma_pullback f.base) (angularChange φ y)] at hg
  exact hg
lemma source_logSigma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    f'.base.logFields.sigma y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (f.base.logFields.sigma (angularChange φ y)) := by
  simpa only [SourceMassFields.logFields,angularLift,angularProjection_angularChange,
    angularJacobian_logRadiusChart,angularProjection_logRadiusChart] using h.sigma
lemma source_logQError_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    logQError f'.base.logFields y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (logQError f.base.logFields (angularChange φ y)) := by
  rw [logQError_scaled,logQError_scaled,source_logGamma_angular h,source_logSigma_angular h]
  simp only [angularChange_zero,angularCongruence,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul]
theorem sourceCollarData_angular_related {φ : Angle → Angle} {f f' : SourceTensorFields}
    {y : Point} (hφ : ContDiffAt ℝ 2 φ (angularProjection y))
    (hf : f.RegularAt (angularChange φ (logRadiusChart y)))
    (hf' : f'.RegularAt (logRadiusChart y))
    (hrel : ∀ᶠ x in 𝓝 (logRadiusChart y), f.AngularRelatedAt φ f' x)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ y).det)
    (hp : (sourceMetric f.base (angularChange φ (logRadiusChart y))).PosDef)
    (hp' : (sourceMetric f'.base (logRadiusChart y)).PosDef)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection y))).det) :
    (sourceCollarData f.logFields).AngularRelatedAt φ (sourceCollarData f'.logFields) y := by
  have h := hrel.self_of_nhds
  have hJA : IsUnit (CKSAngularGeometry.angularJacobian φ (logRadiusChart y)).det := by simpa using hA
  have hγ : IsUnit (sourceGamma f.base (angularChange φ (logRadiusChart y))).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  have hlead := source_log_leading_angular h hA hσ
  have hs := sourceShift_angular h hJA hγ
  have ht := sourceT_angular h hJA hγ
  have hL := sourceOriginalL_angular h hJA hγ
  have hη := sourceOriginalEta_angular h hJA hγ
  have hτ := sourceOriginalTau_angular h hJA hγ
  have hφx : ContDiffAt ℝ 2 φ (angularProjection (logRadiusChart y)) := by simpa only [angularProjection_logRadiusChart] using hφ
  have hr : logRadiusChart y 0 ≠ 0 := by simp [logRadiusChart]
  have hmass := sourcePhysicalMass_angular hr hφx hf hf' hrel hJA hp hp'
  rw [angularChange_logRadiusChart] at hmass hf hp
  rw [sourcePhysicalMass_pullback hf'.base hp',sourcePhysicalMass_pullback hf.base hp] at hmass
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceShift_pullback f'.base) y,congrFun (sourceShift_pullback f.base) (angularChange φ y)] at hs
  rw [angularChange_logRadiusChart,congrFun (sourceT_pullback f'.base) y,
    congrFun (sourceT_pullback f.base) (angularChange φ y)] at ht
  rw [angularChange_logRadiusChart,congrFun (sourceOriginalL_pullback f') y,
    congrFun (sourceOriginalL_pullback f) (angularChange φ y)] at hL
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceOriginalEta_pullback f') y,congrFun (sourceOriginalEta_pullback f) (angularChange φ y)] at hη
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceOriginalTau_pullback f') y,congrFun (sourceOriginalTau_pullback f) (angularChange φ y)] at hτ
  refine ⟨source_logSigma_angular h,source_logQError_angular h,hs,?_,?_,?_,hlead,?_,?_⟩
  · change logT f'.base.logFields y-1=logT f.base.logFields (angularChange φ y)-1
    rw [ht]
  · change logOriginalL _ y-1=logOriginalL _ (angularChange φ y)-1
    rw [hL]
  · change logPhysicalMass f'.base.logFields y-cksLeadingField f'.base.logFields y=
      logPhysicalMass f.base.logFields (angularChange φ y)-cksLeadingField f.base.logFields (angularChange φ y)
    rw [hmass,hlead]
  · change (fun a => logOriginalEta f'.logFields y a/Real.exp (y 0)) =
      angularCovector (CKSAngularGeometry.angularJacobian φ y)
        (fun a => logOriginalEta f.logFields (angularChange φ y) a/Real.exp (angularChange φ y 0))
    have hscale (z : Angle) (r : ℝ) : (fun a => z a/r) = (1/r) • z := by ext a; simp [div_eq_mul_inv,mul_comm]
    rw [hscale,hscale,hη,angularCovector_smul,angularChange_zero]
  · change (fun a b => logOriginalTau f'.logFields y a b/Real.exp (y 0)^2) =
      angularCongruence (CKSAngularGeometry.angularJacobian φ y)
        (fun a b => logOriginalTau f.logFields (angularChange φ y) a b/Real.exp (angularChange φ y 0)^2)
    have hscale (z : Mat) (r : ℝ) : (fun a b => z a b/r) = (1/r) • z := by ext a b; simp [div_eq_mul_inv,mul_comm]
    rw [hscale,hscale,hτ,angularCongruence_smul,angularChange_zero]
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SourceMassFields.SmoothAt (f : SourceMassFields) (y : Point) : Prop where
  sigma : ContDiffAt ℝ ∞ f.sigma (angularProjection y)
  mg : ContDiffAt ℝ ∞ f.mg (angularProjection y)
  mK : ContDiffAt ℝ ∞ f.mK (angularProjection y)
  mr : ContDiffAt ℝ ∞ f.mr (angularProjection y)
  eg : ContDiffAt ℝ ∞ f.eg y
  ek : ContDiffAt ℝ ∞ f.ek y
  b : ContDiffAt ℝ ∞ f.b y
  err : ContDiffAt ℝ ∞ f.err y

structure SourceTensorFields.SmoothAt (f : SourceTensorFields) (y : Point) : Prop where
  base : f.base.SmoothAt y
  kr : ContDiffAt ℝ ∞ f.kr y
  kb : ContDiffAt ℝ ∞ f.kb y

lemma SourceMassFields.SmoothAt.regularAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x := by
  exact ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.mr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.eg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.b.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.err.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma SourceTensorFields.SmoothAt.regularAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.base.regularAt,hf.kr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.kb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma inverse_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact determinant_smooth.contDiffAt.comp x hq
  · exact h0

lemma traceProduct_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (hp : ContDiffAt ℝ ∞ p x) :
    ContDiffAt ℝ ∞ (fun y => traceProduct (q y) (p y)) x :=
  ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hp k) i)

lemma sourceGamma_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceGamma f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

lemma sourceTangentialK_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceTangentialK f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mK))).add hf.ek

lemma sourceRadialMetric_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceRadialMetric f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact ((contDiffAt_const.div (contDiffAt_const.add (hr.pow 2)) (by positivity)).add
    ((angularLift_diff hf.mr).div (hr.pow 5) (pow_ne_zero _ hy))).add hf.err

lemma sourceShift_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceShift f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact contDiffAt_pi.mpr fun a => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceSchur_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceSchur f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact (sourceRadialMetric_smoothAt hf hy).sub (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul ((contDiffAt_pi.mp hf.b a).mul (contDiffAt_pi.mp hf.b b)))

lemma sourceLapse_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceLapse f) y := by
  have hs : 0 < sourceSchur f y := metricBlock_schur_positive hp
  exact contDiffAt_const.div ((sourceSchur_smoothAt hf hy hp).sqrt hs.ne') (Real.sqrt_ne_zero'.mpr hs)

lemma sourceExpansion_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceExpansion f) y := by
  have he : sourceExpansion f=radialExpansion (sourceGamma f) (sourceShift f) :=
    funext fun x => (source_radialExpansion_eq f x).symm
  rw [he]
  exact radialExpansion_smoothAt (sourceGamma_smoothAt hf hy) (sourceShift_smoothAt hf hy hp)
    (metricBlock_leaf_posDef hp)

lemma sourceT_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceT f) y := by
  have he : sourceT f=fun x => leafTensorTrace (sourceGamma f x) (sourceTangentialK f x)/2 := by
    funext x; rw [leafTensorTrace_eq,sourceT]; unfold traceProduct; ring
  rw [he]
  exact (leafTensorTrace_contDiffAt (sourceGamma_smoothAt hf hy) (sourceTangentialK_smoothAt hf hy)
    (metricBlock_leaf_posDef hp)).div_const 2

lemma sourcePhysicalMass_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourcePhysicalMass f) y := by
  have he : sourcePhysicalMass f=fun x => x 0/2*(1+(x 0*sourceT f x)^2-
      (sourceLapse f x*sourceExpansion f x)^2) := by
    funext x; unfold sourcePhysicalMass sourceT sourceLapse; ring
  rw [he]
  have hT := sourceT_smoothAt hf hy hp
  have hU := sourceLapse_smoothAt hf hy hp
  have hd := sourceExpansion_smoothAt hf hy hp
  fun_prop

lemma sourceRadialK_smoothAt {f : SourceTensorFields} {y : Point} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ ∞ (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.div hh (by positivity)).add hf.kr

lemma sourceOriginalL_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalL f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  exact (hU.pow 2).mul (((sourceRadialK_smoothAt hf).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hf.kb a)))).add
      (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).mul
        ((contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hshift b))))

lemma sourceOriginalEta_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalEta f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  apply contDiffAt_pi.mpr
  intro a
  exact hU.mul ((contDiffAt_pi.mp hf.kb a).sub (ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp hshift b).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hk b) a)))

lemma sourceOriginalTau_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalTau f) y := by
  have he : sourceOriginalTau f=fun x => leafTensorTraceFree (sourceGamma f.base x) (sourceTangentialK f.base x) := by
    funext x; rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]; rfl
  rw [he]
  exact leafTensorTraceFree_contDiffAt (sourceGamma_smoothAt hf.base hy) (sourceTangentialK_smoothAt hf.base hy)
    (metricBlock_leaf_posDef hp)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry

abbrev spatialSourceFields (P : SmoothAngularPatch) (A B : SpatialTensor)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) : SourceTensorFields :=
  cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A)
    (polarTensorComponents P B) mr mg mK
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Filter
open scoped Topology
lemma SourceTensorFields.RegularAt.eventually {f : SourceTensorFields} {y : Point}
    (hf : f.RegularAt y) : ∀ᶠ z in 𝓝 y, f.RegularAt z := by
  filter_upwards [hf.base.eventually,hf.kr.eventually (by norm_num),hf.kb.eventually (by norm_num)] with z hb hr hk
  exact ⟨hb,hr,hk⟩
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

theorem actual_log_collar_angular_related (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} (hWo : IsOpen W) (hW'o : IsOpen W') {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W')
    (hf : (spatialSourceFields Q A B mr mg mK).RegularAt
      (angularChange (angleTransition P Q) (logRadiusChart y)))
    (hf' : (spatialSourceFields P A B mr' mg' mK').RegularAt (logRadiusChart y))
    (hp : ∀ᶠ z in 𝓝 (angularChange (angleTransition P Q) (logRadiusChart y)),
      (sourceMetric (spatialSourceFields Q A B mr mg mK).base z).PosDef)
    (hp' : ∀ᶠ z in 𝓝 (logRadiusChart y),
      (sourceMetric (spatialSourceFields P A B mr' mg' mK').base z).PosDef) :
    ∀ᶠ z in 𝓝 y,
      (sourceCollarData (spatialSourceFields Q A B mr mg mK).logFields).AngularRelatedAt
        (angleTransition P Q) (sourceCollarData (spatialSourceFields P A B mr' mg' mK').logFields) z := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x := y)
  have hφ : ContDiffAt ℝ ∞ (angleTransition P Q) (angularProjection (logRadiusChart y)) := by
    simpa only [angularProjection_logRadiusChart] using angleTransition_smoothAt hy
  have ht := (angularChange_contDiffAt hφ).continuousAt.comp hc
  have hov := angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)
  have hw := ((angleTransition_smoothAt hy).continuousAt.comp angularProjection.continuous.continuousAt).preimage_mem_nhds (hWo.mem_nhds hW)
  have hw' := angularProjection.continuous.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW')
  filter_upwards [ht.tendsto.eventually hf.eventually,hc.tendsto.eventually hf'.eventually,
    ht.tendsto.eventually hp,hc.tendsto.eventually hp',hov,hw,hw'] with z hfr hfr' hpr hpr' hz hzW hzW'
  apply sourceCollarData_angular_related
    ((angleTransition_smoothAt hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hfr hfr' ?_ (actual_angleTransition_isUnit P Q hz) hpr hpr' ?_
  · apply actual_CKS_fields_angular_related_eventually P Q A B hWo hW'o hA hA' hB hB'
    · rwa [angularProjection_logRadiusChart]
    · rwa [angularProjection_logRadiusChart]
    · rwa [angularProjection_logRadiusChart]
  · exact isUnit_iff_ne_zero.mpr (Q.roundMetric_posDef (angleTransition_target hz)).det_pos.ne'
end
end CKSLorentz

end

end OAI
