import Mathlib
import OAI.Geometry.BallPacking.Compactness.MarkedCurves

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance grcInst1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance grcInst2 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance

def geometricHolder {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (geometricResidual u)) : HMap ℂ (Phase n) :=
  jetValueCLM _ (ofBoundedCThree (boundedCThree_of_compactSupport (geometricResidual_smooth hu) hc))

@[simp] lemma geometricHolder_value {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (geometricResidual u)) (z : ℂ) :
    valueCLM _ (geometricHolder hu hc) z=geometricResidual u z := rfl

lemma affineSource_distance (c x y : ℂ) {r : ℝ} (hr : 0<r) :
    dist (r⁻¹ • (x-c)) (r⁻¹ • (y-c))=r⁻¹*dist x y := by
  rw [dist_eq_norm,←smul_sub]
  have he : (x-c)-(y-c)=x-y := by abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),dist_eq_norm]

lemma residual_difference_pullback {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    (c : ℂ) {r : ℝ} (hr : 0<r) (i j : ℕ) {x : ℂ} (hx : dist x c<r/4) :
    valueCLM _ (g i-g j) x=r⁻¹ •
      valueCLM _ (localResidual (hu i) c r-localResidual (hu j) c r) (r⁻¹ • (x-c)) := by
  change valueCLM _ (g i) x-valueCLM _ (g j) x=_
  rw [hg,hg,localResidual_at_original (hu i) c hr hx,localResidual_at_original (hu j) c hr hx,←smul_sub]
  rfl

lemma local_residual_small_differences {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    (c : ℂ) {r : ℝ} (hr : 0<r)
    (hlocal : CauchySeq (fun i => localResidual (hu i) c r)) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,
      (∀ x,dist x c<r/4 →‖valueCLM _ (g i-g j) x‖≤ε) ∧
      (∀ x y,dist x c<r/4 →dist y c<r/4 →
        ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤ε*dist x y^((1:ℝ)/3)) := by
  intro ε hε
  let a := r⁻¹
  have ha : 0<a := inv_pos.mpr hr
  have haα : 0<a^((1:ℝ)/3) := Real.rpow_pos_of_pos ha _
  let C := a+a*a^((1:ℝ)/3)+1
  have hC : 0<C := by dsimp [C]; positivity
  have hCa : a≤C := by dsimp [C]; nlinarith [mul_nonneg ha.le haα.le]
  have hCap : a*a^((1:ℝ)/3)≤C := by dsimp [C]; linarith
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hlocal (ε/C) (div_pos hε hC)
  refine ⟨N,fun i hi j hj => ?_⟩
  let v := localResidual (hu i) c r-localResidual (hu j) c r
  have hv : ‖v‖≤ε/C := by simpa only [dist_eq_norm] using (hN i hi j hj).le
  have haV : a*‖v‖≤ε := by
    calc
      a*‖v‖≤C*‖v‖ := mul_le_mul_of_nonneg_right hCa (norm_nonneg v)
      _≤C*(ε/C) := mul_le_mul_of_nonneg_left hv hC.le
      _=ε := mul_div_cancel₀ ε hC.ne'
  have hapV : (a*a^((1:ℝ)/3))*‖v‖≤ε := by
    calc
      (a*a^((1:ℝ)/3))*‖v‖≤C*‖v‖ := mul_le_mul_of_nonneg_right hCap (norm_nonneg v)
      _≤C*(ε/C) := mul_le_mul_of_nonneg_left hv hC.le
      _=ε := mul_div_cancel₀ ε hC.ne'
  refine ⟨?_,?_⟩
  · intro x hx
    rw [residual_difference_pullback hu hg c hr i j hx,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left (norm_value_le v _) ha.le).trans haV
  · intro x y hx hy
    rw [residual_difference_pullback hu hg c hr i j hx,
      residual_difference_pullback hu hg c hr i j hy,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    have hh := norm_sub_value_le v (r⁻¹ • (x-c)) (r⁻¹ • (y-c))
    rw [affineSource_distance c x y hr,Real.mul_rpow ha.le dist_nonneg] at hh
    have hd : 0≤dist x y^((1:ℝ)/3) := Real.rpow_nonneg dist_nonneg _
    exact (mul_le_mul_of_nonneg_left hh ha.le).trans ((by
      nlinarith [mul_le_mul_of_nonneg_right hapV hd] :
        a*(‖v‖*(a^((1:ℝ)/3)*dist x y^((1:ℝ)/3)))≤ε*dist x y^((1:ℝ)/3)))

lemma geometric_residual_cauchy {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    {g : ℕ → HMap ℂ (Phase n)} (hg : ∀ i z,valueCLM _ (g i) z=geometricResidual (u i) z)
    {K : Set ℂ} (hK : IsCompact K) (hsupp : ∀ i z,z∉K  → geometricResidual (u i) z=0)
    {r : ℝ} (hr : 0<r)
    (hlocal : ∀ c,CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i) c r))) :
    CauchySeq g := by
  apply compact_local_holder_cauchy hK (div_pos hr (by norm_num : (0:ℝ)<4))
  · intro i z hz
    rw [hg,hsupp i z hz]
  · intro c
    exact local_residual_small_differences hu hg c hr (localResidual_cauchy hu c r (hlocal c))


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance clcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance clcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance clcInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance clcInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

lemma compact_structure_norm_standard {J : Phase n → End n}
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ B : ℝ,∀ x,B<‖x‖ →J x=standardJ n := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (f := fun x : Phase n => x) continuous_id.continuousOn
  refine ⟨B,fun x hx => ?_⟩
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) (fun hh => (not_le_of_gt hx) (hB x hh)))

lemma marked_value_continuous (p q : Phase n) (z : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => markedCurve p q w z) :=
  (continuous_const.add ((markedSlope_continuous p q).const_smul z)).add (jetEval z).continuous

lemma cDeriv_eval_continuous (z h : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => cDeriv w z h) := by
  have hc : Continuous (fun w : COne ℂ (Phase n) => cDeriv w z) :=
    ((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp
      ((valueCLM ((1:ℝ)/3)).continuous.comp (jetDerivCLM ((1:ℝ)/3)).continuous))
  exact hc.clm_apply continuous_const

lemma marked_derivative_eval_continuous (p q : Phase n) (z h : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => fderiv ℝ (markedCurve p q w) z h) := by
  simp only [markedCurve_fderiv,add_apply,complexSlope_apply]
  exact ((markedSlope_continuous p q).const_smul h).add (cDeriv_eval_continuous z h)

lemma represented_line_slope_nonzero {J : Phase n → End n} {p q : Phase n}
    (w : COne ℂ (Phase n)) (hu : AffineLineCurve J p q (markedCurve p q w)) :
    markedSlope p q w≠0 := by
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have he := tendsto_nhds_unique (markedCurve_asymptote p q w) hlim
  exact fun hz => ha (he ▸ hz)

lemma completed_line_cr_closed {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} {s : ℝ} (hsI : s∈Icc (0:ℝ) 1) (hs : Tendsto t atTop (𝓝 s))
    {p q : Phase n} {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)}
    (hw : Tendsto w atTop (𝓝 v))
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    ∀ z,fderiv ℝ (markedCurve p q v) z Complex.I=
      lineHomotopy J s (markedCurve p q v z) (fderiv ℝ (markedCurve p q v) z 1) := by
  intro z
  have hz := ((marked_value_continuous p q z).tendsto v).comp hw
  have hd1 := ((marked_derivative_eval_continuous p q z 1).tendsto v).comp hw
  have hdI := ((marked_derivative_eval_continuous p q z Complex.I).tendsto v).comp hw
  have hA := (lineHomotopy_joint_contDiffAt hJs hJ (v := (s,markedCurve p q v z)) hsI).continuousAt.tendsto.comp
    (hs.prodMk_nhds hz)
  have hAp : Continuous (fun v : End n × Phase n => v.1 v.2) := continuous_fst.clm_apply continuous_snd
  have hR := ((hAp.tendsto _).comp (hA.prodMk_nhds hd1))
  have he (i : ℕ) := (hu i).2.1 z
  apply tendsto_nhds_unique hdI
  convert hR using 1
  funext i
  simpa only [mul_one,Function.comp_def] using (he i).2 1

lemma completed_line_slope_limit_nonzero {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    markedSlope p q v≠0 := by
  obtain ⟨d,hd,hlo⟩ := exact_line_slope_lower_bound hJs hJ hJc hST hT hout hpq
  have hsl := ((markedSlope_continuous p q).tendsto v).comp hw
  have hdotc : Continuous (fun a : Phase n => stdDot n a a) := (stdDot n).continuous.clm_apply continuous_id
  have hdot := (hdotc.tendsto _).comp hsl
  have hle : d ≤ stdDot n (markedSlope p q v) (markedSlope p q v) := by
    apply ge_of_tendsto hdot
    exact Eventually.of_forall fun i => hlo (t i) (ht i) _ (hu i) _
      (represented_line_slope_nonzero (w i) (hu i)) (markedCurve_asymptote p q (w i))
  intro hz
  simp only [hz,map_zero] at hle
  exact (not_le_of_gt hd) hle

lemma completed_line_closed {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
    (hw0 : ∀ i,cValue (w i) 0=0)
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    AffineLineCurve (lineHomotopy J s) p q (markedCurve p q v) := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  have hv0 : cValue v 0=0 := tendsto_nhds_unique (((jetEval 0).continuous.tendsto v).comp hw)
    (by simpa only [Function.comp_def,jetEval_apply,hw0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Phase n)) atTop (𝓝 0)))
  have ha := completed_line_slope_limit_nonzero hJs hJ hJc hST hT hout hpq ht hw hu
  have hcr := completed_line_cr_closed hJs hJ hsI hs hw hu
  obtain ⟨B,hB⟩ := compact_structure_norm_standard (lineHomotopy_compact hJc hsI)
  have hcomp := lineHomotopy_compatible hJ hsI
  refine ⟨completed_markedCurve_contDiff (lineHomotopy_slice_contDiff hJs hJ hsI) hcomp hB p q v ha hcr,
    ?_,markedCurve_zero p q hv0,markedCurve_one p q v,markedSlope p q v,ha,markedCurve_asymptote p q v⟩
  intro z
  exact ⟨(markedCurve_hasFDerivAt p q v z).differentiableAt,
    realCR_axis_implies_all _ (hcomp _).1 _ (hcr z)⟩


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance eccInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eccInst2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance eccInst3 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance eccInst4 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance eccInst5 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance eccInst6 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance

lemma represented_line_by_inverse {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) {K : Set ℂ} (hK : IsCompact K)
    (g : supportedHolder (E := Phase n) K) (hg : ∀ z,valueCLM _ g.val z=geometricResidual u z) :
    markedCurve p q (standardHolderInverse hK g)=u := by
  obtain ⟨a,_,ha⟩ := hu.2.2.2.2
  exact (marked_reconstruction_from_correction (standardHolderInverse hK g)
    (inverse_correction_holomorphic hu.1 hK g hg) ha hu.2.2.1 hu.2.2.2.1
      (standardHolderInverse_zero hK g)).1

lemma subtype_cauchySeq_of_val {X : Type*} [PseudoMetricSpace X] {A : Set X} {g : ℕ → A}
    (hg : CauchySeq (fun i => (g i).val)) : CauchySeq g := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  exact hg

theorem exact_marked_completed_convergence {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
    {v : ℂ → Phase n} (hv : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
    ∃ (w : ℕ → COne ℂ (Phase n)) (a : COne ℂ (Phase n)),
      (∀ i,markedCurve p q (w i)=u i ∧ cValue (w i) 0=0) ∧
      Tendsto w atTop (𝓝 a) ∧ markedCurve p q a=v ∧
      AffineLineCurve (lineHomotopy J s) p q v := by
  obtain ⟨R,hR,hsupp⟩ := exact_marked_line_uniform_defect_support hJs hJ hJc hST hT hout p q hpq
  let K := Metric.closedBall (0:ℂ) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hc (i : ℕ) : HasCompactSupport (geometricResidual (u i)) :=
    geometricResidual_compact (hu i) (lineHomotopy_compact hJc (ht i))
  let G : ℕ → HMap ℂ (Phase n) := fun i => geometricHolder (hu i).1 (hc i)
  have hG (i : ℕ) (z : ℂ) : valueCLM _ (G i) z=geometricResidual (u i) z := rfl
  have hsupp' (i : ℕ) (z : ℂ) (hz : z∉K) : geometricResidual (u i) z=0 := by
    have hz' : R<‖z‖ := by simpa only [K,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (hsupp (t i) (ht i) (u i) (hu i) z hz').2
  have hGK (i : ℕ) : G i∈supportedHolder K := by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    rw [hG,hsupp' i z hz]
  let g : ℕ → supportedHolder (E := Phase n) K := fun i => ⟨G i,hGK i⟩
  obtain ⟨r,hr,_,hlocal⟩ := exact_marked_local_jet_cauchy hJs hJ hJc hST hT hout ht hs hu hv
  have hGC : CauchySeq G := geometric_residual_cauchy (fun i => (hu i).1) hG hK hsupp' hr hlocal
  have hgC : CauchySeq g := subtype_cauchySeq_of_val hGC
  obtain ⟨g₀,hg₀⟩ := cauchySeq_tendsto_of_complete hgC
  let w := fun i => standardHolderInverse hK (g i)
  let a := standardHolderInverse hK g₀
  have hw : Tendsto w atTop (𝓝 a) := ((standardHolderInverse hK).continuous.tendsto g₀).comp hg₀
  have hrec (i : ℕ) : markedCurve p q (w i)=u i := represented_line_by_inverse (hu i) hK (g i) (hG i)
  have hw0 (i : ℕ) : cValue (w i) 0=0 := standardHolderInverse_zero hK (g i)
  have hline (i : ℕ) : AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i)) := by
    rw [hrec i]
    exact hu i
  have haline := completed_line_closed hJs hJ hJc hST hT hout hpq ht hs hw hw0 hline
  have hav : markedCurve p q a=v := by
    funext z
    have hpoint := ((marked_value_continuous p q z).tendsto a).comp hw
    have huv := (hv {z} isCompact_singleton).tendsto_at (mem_singleton z)
    apply tendsto_nhds_unique hpoint
    simpa only [Function.comp_def,hrec] using huv
  exact ⟨w,a,fun i => ⟨hrec i,hw0 i⟩,hw,hav,hav ▸ haline⟩

theorem exact_marked_completed_compactness {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i)) :
    ∃ (φ : ℕ → ℕ),StrictMono φ ∧ ∃ (w : ℕ → COne ℂ (Phase n)) (a : COne ℂ (Phase n)),
      (∀ i,markedCurve p q (w i)=u (φ i) ∧ cValue (w i) 0=0) ∧
      Tendsto w atTop (𝓝 a) ∧ AffineLineCurve (lineHomotopy J s) p q (markedCurve p q a) := by
  obtain ⟨v,_,_,φ,hφ,hsub⟩ := exact_marked_line_czero_compactness hJs hJ hJc hST hT hout ht hu
  obtain ⟨w,a,hrec,hw,hav,haline⟩ := exact_marked_completed_convergence hJs hJ hJc hST hT hout hpq
    (fun i => ht (φ i)) (hs.comp hφ.tendsto_atTop) (fun i => hu (φ i)) hsub
  exact ⟨φ,hφ,w,a,hrec,hw,hav.symm ▸ haline⟩


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
variable {n : ℕ}
local instance empInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance empInst2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

lemma markedCurve_injective (p q : Phase n) : Function.Injective (markedCurve p q) := by
  intro v w hvw
  have hs : markedSlope p q v=markedSlope p q w := by
    apply tendsto_nhds_unique (markedCurve_asymptote p q v)
    rw [hvw]
    exact markedCurve_asymptote p q w
  apply cValue_ext
  intro z
  have hz := congrFun hvw z
  change p+z • markedSlope p q v+cValue v z=p+z • markedSlope p q w+cValue w z at hz
  rw [hs] at hz
  exact add_left_cancel hz

def exactMarkedZeroSet (J : Phase n → End n) (p q : Phase n) : Set (ℝ × COne ℂ (Phase n)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ cValue v.2 0=0 ∧
    AffineLineCurve (lineHomotopy J v.1) p q (markedCurve p q v.2)}

lemma correction_limit_zero {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)}
    (hw : Tendsto w atTop (𝓝 v)) (hw0 : ∀ i,cValue (w i) 0=0) : cValue v 0=0 := by
  have hh := ((jetEval (E := Phase n) 0).continuous.tendsto v).comp hw
  apply tendsto_nhds_unique hh
  simpa only [Function.comp_def,jetEval_apply,hw0] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Phase n)) atTop (𝓝 0))

theorem exact_marked_zeroSet_compact {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) : IsCompact (exactMarkedZeroSet J p q) := by
  apply IsSeqCompact.isCompact
  intro x hx
  obtain ⟨s,hsI,ψ,hψ,hs⟩ := isCompact_Icc.isSeqCompact (fun i => (hx i).1)
  have htime : Tendsto (fun i => (x (ψ i)).1) atTop (𝓝 s) := hs
  obtain ⟨φ,hφ,w,a,hrec,hwa,haline⟩ := exact_marked_completed_compactness hJs hJ hJc hST hT hout hpq
    (fun i => (hx (ψ i)).1) htime (fun i => (hx (ψ i)).2.2)
  have he (i : ℕ) : w i=(x (ψ (φ i))).2 := markedCurve_injective p q (hrec i).1
  have ha0 : cValue a 0=0 := correction_limit_zero hwa (fun i => (hrec i).2)
  refine ⟨(s,a),⟨hsI,ha0,haline⟩,ψ ∘ φ,hψ.comp hφ,?_⟩
  have htend := htime.comp hφ.tendsto_atTop
  have hw' : Tendsto (fun i => (x (ψ (φ i))).2) atTop (𝓝 a) := by
    have hew : w=(fun i => (x (ψ (φ i))).2) := funext he
    rw [hew] at hwa
    exact hwa
  exact htend.prodMk_nhds hw'

theorem exact_marked_existence_parameters_closed {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) : IsClosed (Prod.fst '' exactMarkedZeroSet J p q) :=
  ((exact_marked_zeroSet_compact hJs hJ hJc hST hT hout hpq).image continuous_fst).isClosed



end HigherDimensionalBallPacking.Rigidity
end

end OAI
