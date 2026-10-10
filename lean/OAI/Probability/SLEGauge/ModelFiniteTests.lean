import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TailBatches

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator LoewnerRestart CompactSequence

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

lemma subdisk_measurable (l : ℕ) : Measurable (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l) := by
  let (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (M.mass v b) := M.canonical.finite_compact v b
  exact subdiskMass_measurable a ha M.mass M.mass_measurable _ l

lemma subdisk_raw_measurable (θ : Angle) (l : ℕ) :
    Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>subdiskMass a M.mass (subdiskRadius M.radiusIndex) l (θ,b)) := by
  let (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (M.mass v b) := M.canonical.finite_compact v b
  exact subdiskMass_raw_measurable _ a ha M.mass θ l
    (M.canonical.optional_measurable _ (centeredTime_stopping a ha θ l))

lemma subdisk_ge_law (l : ℕ) (H : ℝ≥0∞) :
    (finiteAngleLaw W a l) {p | H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p}=
      M.law {x | H ≤ x l} := by
  have he := lintegral_coordinate M.law (finiteAngleLaw W a l)
    (subdiskMass a M.mass (subdiskRadius M.radiusIndex)) M.subdisk_measurable l (M.finite_laws l)
    ((Ici H).indicator (fun _=>(1:ℝ≥0∞))) (measurable_const.indicator measurableSet_Ici)
  have he₁ : (fun x : ℕ→ℝ≥0∞=>(Ici H).indicator (fun _=>(1:ℝ≥0∞)) (x l))=
      {x : ℕ→ℝ≥0∞ | H ≤ x l}.indicator (fun _=>(1:ℝ≥0∞)) := by ext x; rfl
  have he₂ : (fun p=>(Ici H).indicator (fun _=>(1:ℝ≥0∞))
      (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p))=
      {p | H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p}.indicator (fun _=>(1:ℝ≥0∞)) := by ext x; rfl
  rw [he₁,he₂,lintegral_indicator (measurableSet_le measurable_const (measurable_pi_apply l)),
    lintegral_indicator (measurableSet_le measurable_const (M.subdisk_measurable l)),lintegral_one,lintegral_one,Measure.restrict_apply_univ,Measure.restrict_apply_univ] at he
  exact he.symm

lemma subdisk_tail_le (l : ℕ) (H : ℝ) (_hH : 0 ≤ H) :
    (finiteAngleLaw W a l) {p | ENNReal.ofReal H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p} ≤ 
      M.law {x | H ≤ sequenceMassReal x} := by
  rw [M.subdisk_ge_law]
  apply measure_mono_ae
  filter_upwards [M.increasing_finite] with x hx
  intro hh
  exact (ENNReal.ofReal_le_iff_le_toReal hx.2.ne).mp (hh.trans (le_iSup x l))

 

lemma normalized_tail_le [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0<z.im) (σ : ℝ) (hσ : 0<σ) (hσz : σ ≤ z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : σ=z.im*Real.exp (-2*a*s))
    (l : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (radialLaw W a z (σ*Real.exp (-2*a*l)))
      {b | ENNReal.ofReal H ≤ LoewnerRestart.normalizedTest a z σ
        (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l) b} ≤ 
      2*M.law {x | H ≤ sequenceMassReal x} := by
  let E : Set (Angle×GDriver) := {p | ENNReal.ofReal H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p}
  have hE : MeasurableSet E := measurableSet_le measurable_const (M.subdisk_measurable l)
  have hm := normalizedTest_measurable a ha z hz σ hσ hσz _ (M.subdisk_measurable l)
  have hF : MeasurableSet {b | ENNReal.ofReal H ≤ LoewnerRestart.normalizedTest a z σ
      (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l) b} :=
    measurableSet_le measurable_const hm
  have hh := (normalizedTest_conditional_bounds W hW a ha z hz z.im σ hσ hσz le_rfl
    s hs hgap l univ MeasurableSet.univ (E.indicator (fun _=>(1:ℝ≥0∞)))
      (measurable_const.indicator hE)).2
  have he : LoewnerRestart.normalizedTest a z σ (E.indicator (fun _=>(1:ℝ≥0∞)))=
      {b | ENNReal.ofReal H ≤ LoewnerRestart.normalizedTest a z σ
        (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l) b}.indicator (fun _=>(1:ℝ≥0∞)) := by
    funext b
    rfl
  have := radialLaw_probability W hW a ha z hz (σ*Real.exp (-2*a*l))
    (mul_pos hσ (Real.exp_pos _)) ((mul_le_of_le_one_right hσ.le
      (Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α:=ℝ) l; nlinarith))).trans hσz)
  rw [he,setLIntegral_univ,lintegral_indicator hF,lintegral_indicator hE,lintegral_one,lintegral_one,
    Measure.restrict_apply_univ,Measure.restrict_apply_univ,measure_univ,mul_one] at hh
  exact hh.trans (by gcongr; exact M.subdisk_tail_le l H hH)

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain

lemma hasDerivWithinAt_primitive_Icc {f : ℝ→ℂ} {T u : ℝ} (hT : 0≤T)
    (hf : ContinuousOn f (Icc 0 T)) (hu : u∈Icc 0 T) :
    HasDerivWithinAt (fun v=>∫s in (0:ℝ)..v,f s) (f u) (Icc 0 T) u := by
  let F : ℝ→ℂ := fun s=>f (projIcc 0 T hT s)
  have hF : Continuous F := hf.domRestrict.comp continuous_projIcc
  have he (s : ℝ) (hs : s∈Icc 0 T) : F s=f s := by
    dsimp [F]; rw [projIcc_of_mem _ hs]
  have hi (v : ℝ) (hv : v∈Icc 0 T) : (∫s in (0:ℝ)..v,F s)=∫s in (0:ℝ)..v,f s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hv.1] at hs
    exact he s ⟨hs.1,hs.2.trans hv.2⟩
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hF.intervalIntegrable 0 u) hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  rw [he u hu] at hd
  exact hd.hasDerivWithinAt.congr_of_mem (fun v hv=>(hi v hv).symm) hu

 
def logVariation (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ∫s in (0:ℝ)..u,-(a:ℂ)/(loewnerMap a b s.toNNReal z-(b s.toNNReal:ℂ))^2

def firstVariation (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (logVariation a b z u)

lemma firstVariation_eq_deriv {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {u : ℝ≥0} (hu : alive a b u z) :
    firstVariation a b z u=deriv (loewnerMap a b u) z :=
  (hasDerivAt_loewnerMap hb hu).deriv.symm

lemma logVariation_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (logVariation a b z)
      (-(a:ℂ)/(loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))^2) (Icc 0 (T:ℝ)) u := by
  obtain ⟨f,hf⟩ := hT
  apply hasDerivWithinAt_primitive_Icc T.coe_nonneg _ hu
  have hc : ContinuousOn (fun s:ℝ=>-(a:ℂ)/(f s-(b s.toNNReal:ℂ))^2) (Icc 0 (T:ℝ)) :=
    continuousOn_const.div ((odeUntil_center_continuousOn hb hf).pow 2)
      (fun s hs=>pow_ne_zero _ (odeUntil_center_ne_zero hf hs))
  exact hc.congr (fun s hs=>by rw [loewnerMap_eq_solution_time hf hs])

lemma firstVariation_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (firstVariation a b z)
      (-(a:ℂ)/(loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))^2 * firstVariation a b z u)
      (Icc 0 (T:ℝ)) u := by
  convert! (logVariation_hasDerivWithinAt hb hT hu).cexp using 1; first | rfl | (dsimp only [firstVariation]; ring)

lemma firstVariation_continuousOn {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) :
    ContinuousOn (firstVariation a b z) (Icc 0 (T:ℝ)) :=
  fun _ hu=>(firstVariation_hasDerivWithinAt hb hT hu).continuousWithinAt

 
def secondVariationIntegral (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ∫u in (0:ℝ)..t,2*(a:ℂ)*firstVariation a b z u /
    (loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))^3

lemma secondVariationIntegral_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (secondVariationIntegral a b z)
      (2*(a:ℂ)*firstVariation a b z u /
        (loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))^3) (Icc 0 (T:ℝ)) u := by
  have hc := firstVariation_continuousOn hb hT
  obtain ⟨f,hf⟩ := hT
  apply hasDerivWithinAt_primitive_Icc T.coe_nonneg _ hu
  have hd : ContinuousOn (fun s=>2*(a:ℂ)*firstVariation a b z s/(f s-(b s.toNNReal:ℂ))^3)
      (Icc 0 (T:ℝ)) := (continuousOn_const.mul hc).div ((odeUntil_center_continuousOn hb hf).pow 3)
    (fun s hs=>pow_ne_zero _ (odeUntil_center_ne_zero hf hs))
  exact hd.congr (fun s hs=>by rw [loewnerMap_eq_solution_time hf hs])

lemma secondVariationIntegral_continuousOn {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) :
    ContinuousOn (secondVariationIntegral a b z) (Icc 0 (T:ℝ)) :=
  fun _ hu=>(secondVariationIntegral_hasDerivWithinAt hb hT hu).continuousWithinAt

 

theorem hasDerivAt_deriv_loewnerMap {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) :
    HasDerivAt (deriv (loewnerMap a b T))
      (firstVariation a b z T * secondVariationIntegral a b z T) z := by
  obtain ⟨ε,δ,F,hε,hδ,hFc,hFe,hode,hmap,hIm⟩ := loewner_local_cutoff hb hT
  let Z : ℂ→ℝ→ℂ := fun w u=>heightClamp ε (F u.toNNReal w-(b u.toNNReal:ℂ))
  let K : ℂ→ℝ→ℂ := fun w u=>-(a:ℂ)/(Z w u)^2
  let D : ℂ→ℝ→ℂ := fun w u=>Complex.exp (∫v in (0:ℝ)..u,K w v)
  let P : ℂ→ℝ→ℂ := fun w u=>2*(a:ℂ)*D w u/(Z w u)^3
  have hZ (w : ℂ) : Continuous (Z w) := (heightClamp_lipschitz ε).continuous.comp
    (((hFc w).comp continuous_real_toNNReal).sub
      (Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)))
  have hZn (w : ℂ) (u : ℝ) : Z w u≠0 := heightClamp_ne_zero hε _
  have hK (w : ℂ) : Continuous (K w) := continuous_const.div ((hZ w).pow 2)
    (fun u=>pow_ne_zero _ (hZn w u))
  have hD (w : ℂ) : Continuous (D w) := by
    apply Complex.continuous_exp.comp
    exact intervalIntegral.continuous_primitive (hK w).intervalIntegrable 0
  have hP (w : ℂ) : Continuous (P w) := (continuous_const.mul (hD w)).div ((hZ w).pow 3)
    (fun u=>pow_ne_zero _ (hZn w u))
  have htime {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) : u.toNNReal≤T := by
    simpa using Real.toNNReal_le_toNNReal hu.2
  have hZe (w : ℂ) (hw : w∈ball z δ) (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) :
      Z w u=loewnerMap a b u.toNNReal w-(b u.toNNReal:ℂ) := by
    rw [hmap w hw _ (htime hu)]
    exact heightClamp_eq (by simpa using (hIm w hw _ (htime hu)).le)
  have hDe (w : ℂ) (hw : w∈ball z δ) (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) :
      D w u=firstVariation a b w u := by
    dsimp only [D,firstVariation,logVariation]
    apply congrArg Complex.exp
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hu.1] at hv
    change -(a:ℂ)/(Z w v)^2= _
    rw [hZe w hw v ⟨hv.1,hv.2.trans hu.2⟩]
  have hDd (w : ℂ) (hw : w∈ball z δ) (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) :
      D w u=deriv (loewnerMap a b u.toNNReal) w := by
    rw [hDe w hw u hu]
    convert! firstVariation_eq_deriv hb ⟨_,odeUntil_mono (hode w hw) (htime hu)⟩ using 1
    rw [Real.coe_toNNReal _ hu.1]
  have hd (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) (w : ℂ) (hw : w∈ball z δ) :
      HasDerivAt (fun w=>K w u) (P w u) w := by
    have h := ((hasDerivAt_loewnerMap hb
      (show alive a b u.toNNReal w from ⟨_,odeUntil_mono (hode w hw) (htime hu)⟩)).sub_const
        (b u.toNNReal:ℂ)).pow 2
    rw [←(hasDerivAt_loewnerMap hb
      (show alive a b u.toNNReal w from ⟨_,odeUntil_mono (hode w hw) (htime hu)⟩)).deriv,
      ←hDd w hw u hu] at h
    change HasDerivAt (fun x=>(loewnerMap a b u.toNNReal x-(b u.toNNReal:ℂ))^2)
      ((2:ℂ)*(loewnerMap a b u.toNNReal w-(b u.toNNReal:ℂ))^(2-1)*D w u) w at h
    have hq := (hasDerivAt_const w (-(a:ℂ))).div h
      (by rw [←hZe w hw u hu]; exact pow_ne_zero _ (hZn w u))
    have he : (fun x=>K x u)=ᶠ[𝓝 w]
        (fun x=>-(a:ℂ)/(loewnerMap a b u.toNNReal x-(b u.toNNReal:ℂ))^2) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      dsimp only [K]; rw [hZe x hx u hu]
    convert! hq.congr_of_eventuallyEq he using 1
    dsimp only [P]
    rw [hZe w hw u hu]
    simp only [Nat.reduceSub,pow_one]
    field_simp
    ring
  let L : ℝ := Real.exp ((2*|a|/ε^2)*(T:ℝ))
  have hL : 0<L := Real.exp_pos _
  have hDb (w : ℂ) (hw : w∈ball z δ) (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) : ‖D w u‖≤L := by
    rw [hDd w hw u hu]
    have hLip : LipschitzOnWith ⟨L,hL.le⟩ (loewnerMap a b u.toNNReal) (ball z δ) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      change dist (loewnerMap a b u.toNNReal x) (loewnerMap a b u.toNNReal y)≤L*dist x y
      rw [hmap x hx _ (htime hu),hmap y hy _ (htime hu)]
      apply (cutoff_loewner_dist hε hb hFc hFe x y u.toNNReal).trans
      rw [Real.coe_toNNReal _ hu.1]
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hu.2 (by positivity))) dist_nonneg).trans_eq (mul_comm _ _)
    exact norm_deriv_le_of_lipschitzOn (isOpen_ball.mem_nhds hw) hLip
  have hPb (u : ℝ) (hu : u∈Icc 0 (T:ℝ)) (w : ℂ) (hw : w∈ball z δ) :
      ‖P w u‖≤2 * |a| * L/ε^3 := by
    have hn : ε≤‖Z w u‖ := heightClamp_norm_lower ε _
    have hn0 : 0<‖Z w u‖ := hε.trans_le hn
    dsimp only [P]
    rw [norm_div,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat]
    exact div_le_div₀ (by positivity) (by gcongr; exact hDb w hw u hu)
      (by positivity) (by gcongr)
  have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := K) (F' := P) (bound := fun _=>2 * |a| * L/ε^3) (a := 0) (b := (T:ℝ))
    (ball_mem_nhds z hδ)
    (Eventually.of_forall (fun w=>(hK w).aestronglyMeasurable.restrict))
    ((hK z).intervalIntegrable 0 T) (hP z).aestronglyMeasurable.restrict
    (ae_of_all volume (fun u hu=>hPb u (by rw [uIoc_of_le T.coe_nonneg] at hu; exact Ioc_subset_Icc_self hu)))
    intervalIntegrable_const
    (ae_of_all volume (fun u hu=>hd u (by rw [uIoc_of_le T.coe_nonneg] at hu; exact Ioc_subset_Icc_self hu)))
  have he : (fun w=>D w T)=ᶠ[𝓝 z] (deriv (loewnerMap a b T)) := by
    filter_upwards [ball_mem_nhds z hδ] with w hw
    simpa only [Real.toNNReal_coe] using hDd w hw T ⟨T.coe_nonneg,le_rfl⟩
  have hfinal := hdiff.2.cexp.congr_of_eventuallyEq he.symm
  have hpi : (∫u in (0:ℝ)..(T:ℝ),P z u)=secondVariationIntegral a b z T := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le T.coe_nonneg] at hu
    dsimp only [P,secondVariationIntegral]
    rw [hDe z (mem_ball_self hδ) u hu,hZe z (mem_ball_self hδ) u hu]
  rw [hpi] at hfinal
  convert! hfinal using 1
  change firstVariation a b z T * secondVariationIntegral a b z T =
    D z T * secondVariationIntegral a b z T
  rw [hDe z (mem_ball_self hδ) T ⟨T.coe_nonneg,le_rfl⟩]

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace
namespace SLEExactGauge.LoewnerGeometry

lemma real_inner_mul_self (v c : ℂ) : ⟪v,c*v⟫_ℝ=c.re*‖v‖^2 := by
  rw [real_inner_eq_re_inner ℂ]
  change (inner ℂ v (c • v)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change (c*(‖v‖:ℂ)^2).re = _
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma norm_le_of_affine_dissipative {B c f : ℝ→ℂ} {T R : ℝ}
    (hT : 0≤T) (hR : 0≤R)
    (hd : ∀ u∈Icc 0 T, HasDerivWithinAt B (c u*B u+f u) (Icc 0 T) u)
    (h0 : ‖B 0‖≤R)
    (hc : ∀ u∈Icc 0 T,(c u).re<0)
    (hf : ∀ u∈Icc 0 T,‖f u‖≤-R*(c u).re) : ‖B T‖≤R := by
  have cont : ContinuousOn (fun u=>‖B u‖^2) (Icc 0 T) :=
    fun u hu=>(hd u hu).norm_sq.continuousWithinAt
  have deriv (u : ℝ) (hu : u∈Ico 0 T) :
      HasDerivWithinAt (fun u=>‖B u‖^2)
        (2*⟪B u,c u*B u+f u⟫_ℝ) (Ici u) u := by
    apply (hd u ⟨hu.1,hu.2.le⟩).norm_sq.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ v:ℝ in 𝓝[Ici u] u,v<T from nhdsWithin_le_nhds (Iio_mem_nhds hu.2))]
      with v hv hvT
    exact ⟨hu.1.trans hv,hvT.le⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : 0<R+ε := by linarith
  have barrier := image_le_of_deriv_right_lt_deriv_boundary cont deriv
    (B := fun _=> (R+ε)^2) (B' := fun _=>0)
    (by nlinarith [norm_nonneg (B 0)])
    (fun _=>hasDerivAt_const _ _)
    (by
      intro u hu he
      have hh : ‖B u‖=R+ε := (sq_eq_sq₀ (norm_nonneg _) hpos.le).mp he
      have hcf := hc u ⟨hu.1,hu.2.le⟩
      have hb := (real_inner_le_norm (B u) (f u)).trans
        (mul_le_mul_of_nonneg_left (hf u ⟨hu.1,hu.2.le⟩) (norm_nonneg _))
      rw [inner_add_right,real_inner_mul_self]
      rw [hh] at hb ⊢
      have hn : (c u).re*(R+ε)*ε<0 := mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hcf hpos) hε
      nlinarith)
  have ht := barrier (right_mem_Icc.mpr hT)
  nlinarith [norm_nonneg (B T)]

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain LoewnerRestart

lemma loewner_time_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ}
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (fun t=>loewnerMap a b t.toNNReal z)
      ((a:ℂ)/(loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) u := by
  obtain ⟨f,hf⟩ := hT
  rw [loewnerMap_eq_solution_time hf hu]
  exact (hf.2 u hu).2.congr_of_mem (fun v hv=>loewnerMap_eq_solution_time hf hv) hu

lemma loewner_height_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ}
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (fun t=>(loewnerMap a b t.toNNReal z).im)
      (-a*(loewnerMap a b u.toNNReal z).im /
        Complex.normSq (loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) u := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u
    (loewner_time_hasDerivWithinAt hT hu)
  convert! hd using 1
  simp only [Complex.imCLM_apply,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.sub_im,sub_zero,zero_mul,zero_div,zero_sub]
  ring

def coefficientDrift (a : ℝ) (Z : ℂ) : ℂ :=
  -(a:ℂ)/(Complex.normSq Z:ℂ)+(a:ℂ)/Z^2

def coefficientForcing (a : ℝ) (Z : ℂ) : ℂ :=
  -coefficientDrift a Z-Complex.I*(2*(a:ℂ)*(Z.im:ℂ)/Z^3)

lemma coefficientDrift_re (a : ℝ) {Z : ℂ} (hZ : Z≠0) :
    (coefficientDrift a Z).re= -(2*a*Z.im^2/(Complex.normSq Z)^2) := by
  have hn : Complex.normSq Z≠0 := mt Complex.normSq_eq_zero.mp hZ
  dsimp only [coefficientDrift]
  simp only [Complex.add_re,Complex.neg_re,Complex.div_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.normSq_ofReal,
    pow_two,Complex.mul_re,Complex.mul_im]
  field_simp
  simp only [Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im]
  ring

lemma coefficientForcing_eq (a : ℝ) {Z : ℂ} (hZ : Z≠0) :
    coefficientForcing a Z =
      (-(4*a*Z.im^2/(Complex.normSq Z)^2):ℝ)*(star Z/Z) := by
  have hN : (Complex.normSq Z:ℂ)=Z*star Z := (Complex.mul_conj Z).symm
  have hY : (Z.im:ℂ)=(Z-star Z)/(2*Complex.I) := Complex.im_eq_sub_conj Z
  have hZn : star Z≠0 := star_ne_zero.mpr hZ
  simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  dsimp only [coefficientForcing,coefficientDrift]
  rw [hN,hY]
  field_simp
  simp only [Complex.I_sq]
  ring_nf

lemma coefficientForcing_norm {a : ℝ} (ha : 0<a) {Z : ℂ} (hZ : Z≠0) :
    ‖coefficientForcing a Z‖ = -2*(coefficientDrift a Z).re := by
  rw [coefficientForcing_eq a hZ,norm_mul,norm_div,norm_star,div_self (norm_ne_zero_iff.mpr hZ),
    mul_one,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity),
    coefficientDrift_re a hZ]
  ring

 

def secondCoefficient (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  1-Complex.I*((loewnerMap a b u.toNNReal z).im * secondVariationIntegral a b z u /
    firstVariation a b z u)

lemma secondCoefficient_hasDerivWithinAt {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) {u : ℝ} (hu : u∈Icc 0 (T:ℝ)) :
    HasDerivWithinAt (secondCoefficient a b z)
      (coefficientDrift a (loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))*secondCoefficient a b z u+
        coefficientForcing a (loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) u := by
  have htime : u.toNNReal≤T := by simpa using Real.toNNReal_le_toNNReal hu.2
  have hz : loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ)≠0 := by
    obtain ⟨f,hf⟩ := hT
    rw [loewnerMap_eq_solution_time hf hu]
    exact odeUntil_center_ne_zero hf hu
  have hD : firstVariation a b z u≠0 := Complex.exp_ne_zero _
  have hy := (loewner_height_hasDerivWithinAt hT hu).ofReal_comp
  have hp := secondVariationIntegral_hasDerivWithinAt hb hT hu
  have hd := firstVariation_hasDerivWithinAt hb hT hu
  have h := (((hy.mul hp).div hd hD).const_mul Complex.I).const_sub 1
  convert! h using 1
  dsimp only [secondCoefficient,coefficientDrift,coefficientForcing,Pi.mul_apply]
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.ofReal_neg,
    Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  ring

lemma secondCoefficient_zero (a : ℝ) (b : ℝ≥0→ℝ) (z : ℂ) :
    secondCoefficient a b z 0=1 := by
  simp [secondCoefficient,secondVariationIntegral]

 
theorem secondCoefficient_norm_le {a : ℝ} (ha : 0<a) {b : ℝ≥0→ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) : ‖secondCoefficient a b z T‖≤2 := by
  apply norm_le_of_affine_dissipative T.coe_nonneg (by norm_num)
    (fun u hu=>secondCoefficient_hasDerivWithinAt hb hT hu)
  · rw [secondCoefficient_zero]; norm_num
  · intro u hu
    obtain ⟨f,hf⟩ := hT
    have hy : 0<(loewnerMap a b u.toNNReal z-(b u.toNNReal:ℂ)).im := by
      rw [loewnerMap_eq_solution_time hf hu]
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (hf.2 u hu).1
    have hn := odeUntil_center_ne_zero hf hu
    rw [←loewnerMap_eq_solution_time hf hu] at hn
    rw [coefficientDrift_re a hn]
    exact neg_neg_of_pos (div_pos (by positivity) (sq_pos_of_ne_zero
      (mt Complex.normSq_eq_zero.mp hn)))
  · intro u hu
    obtain ⟨f,hf⟩ := hT
    have hn := odeUntil_center_ne_zero hf hu
    rw [←loewnerMap_eq_solution_time hf hu] at hn
    exact (coefficientForcing_norm ha hn).le

end SLEExactGauge.LoewnerGeometry
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerGeometry
open ExactSLEMain LoewnerRestart FlowIdentification

lemma hasDerivAt_deriv_inverseMap {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    HasDerivAt (deriv (inverseMap a b T))
      (-secondVariationIntegral a b.1 (inverseMap a b T w) T /
        (firstVariation a b.1 (inverseMap a b T w) T)^2) w := by
  have hz := inverseMap_alive ha b T hw
  have hg := hasDerivAt_deriv_loewnerMap b.1.continuous hz
  have hf := (inverseMap_hasStrictDerivAt ha b T hw).hasDerivAt
  rw [←firstVariation_eq_deriv b.1.continuous hz] at hf
  have hD : firstVariation a b.1 (inverseMap a b T w) T≠0 := Complex.exp_ne_zero _
  have hd := (hg.comp w hf).inv (by
    dsimp only [Function.comp_def]; rw [←firstVariation_eq_deriv b.1.continuous hz]; exact hD)
  have he : deriv (inverseMap a b T)=ᶠ[𝓝 w]
      (fun w=> (deriv (loewnerMap a b.1 T) (inverseMap a b T w))⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with v hv
    exact deriv_inverseMap ha b T hv
  convert! hd.congr_of_eventuallyEq he using 1
  dsimp only [Function.comp_def]
  rw [←firstVariation_eq_deriv b.1.continuous hz]
  field_simp

lemma inverseMap_second_coefficient {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    1+Complex.I*(w.im:ℂ)*(deriv (deriv (inverseMap a b T)) w/deriv (inverseMap a b T) w)=
      secondCoefficient a b.1 (inverseMap a b T w) T := by
  rw [(hasDerivAt_deriv_inverseMap ha b T hw).deriv,deriv_inverseMap ha b T hw,
    ←firstVariation_eq_deriv b.1.continuous (inverseMap_alive ha b T hw)]
  have hD : firstVariation a b.1 (inverseMap a b T w) T≠0 := Complex.exp_ne_zero _
  have hy := congrArg Complex.im (centered_inverseMap ha b T hw)
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hy
  dsimp only [secondCoefficient]
  rw [Real.toNNReal_coe,hy]
  field_simp
  ring

 

lemma inverseMap_second_coefficient_norm_le {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    ‖1+Complex.I*(w.im:ℂ)*(deriv (deriv (inverseMap a b T)) w/deriv (inverseMap a b T) w)‖≤2 := by
  rw [inverseMap_second_coefficient ha b T hw]
  exact secondCoefficient_norm_le ha b.1.continuous (inverseMap_alive ha b T hw)

 
theorem inverseMap_preSchwarzian_bound {a : ℝ} (ha : 0<a) (b : GDriver) (T : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    ‖deriv (deriv (inverseMap a b T)) w‖ ≤ (3/w.im)*‖deriv (inverseMap a b T) w‖ := by
  have hn := inverseMap_second_coefficient_norm_le ha b T hw
  have h := norm_sub_le (1+Complex.I*(w.im:ℂ)*
    (deriv (deriv (inverseMap a b T)) w/deriv (inverseMap a b T) w)) (1:ℂ)
  have htriangle : ‖Complex.I*(w.im:ℂ)*(deriv (deriv (inverseMap a b T)) w/
      deriv (inverseMap a b T) w)‖≤3 := by
    calc
      _ ≤ ‖1+Complex.I*(w.im:ℂ)*(deriv (deriv (inverseMap a b T)) w/
        deriv (inverseMap a b T) w)‖+‖(1:ℂ)‖ := by simpa only [add_sub_cancel_left] using h
      _ ≤ 3 := by rw [norm_one]; linarith
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hw,norm_div] at htriangle
  have hd : 0<‖deriv (inverseMap a b T) w‖ := norm_pos_iff.mpr (deriv_inverseMap_ne_zero ha b T hw)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hw).mpr
  rw [←mul_div_assoc] at htriangle
  have ha' := (div_le_iff₀ hd).mp htriangle
  nlinarith

end SLEExactGauge.LoewnerGeometry
end
end

end OAI
