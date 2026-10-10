import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.UpperTimeCut

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma integral_ball_polar_flip {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec→W} {R : ℝ} (hg : IntegrableOn g (ball (0:Vec) R)) :
    (∫z in ball (0:Vec) R,g z)=
      ∫n : Sphere,∫r in Ioo (0:ℝ) R,r^2 • g (-(r • n.1)) ∂volume ∂sphereMeasure := by
  classical
  let H := (ball (0:Vec) R).indicator g
  have hi : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr hg
  rw [←integral_indicator measurableSet_ball]
  change (∫z,H z)=_
  rw [←integral_neg_eq_self H volume,integral_polar hi.comp_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    have he : ∀r∈Ioi (0:ℝ),r^2 • H (-(r • n.1))=
        (Iio R).indicator (fun r=>r^2 • g (-(r • n.1))) r := by
      intro r hr
      have hnorm : ‖-(r • n.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
      by_cases h : r<R
      · rw [show H (-(r • n.1))=g (-(r • n.1)) from indicator_of_mem
          (show -(r • n.1)∈ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          indicator_of_mem (show r∈Iio R from h)]
      · rw [show H (-(r • n.1))=0 from indicator_of_notMem
          (show -(r • n.1)∉ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          smul_zero,indicator_of_notMem (show r∉Iio R from h)]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Iio]
    rfl)

lemma normalisedSignedForce_flux {r : ℝ} (n a v b : Vec)
    (hr : r≠0) (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    (1-dot n a) • normalisedSignedForce r a (velocity v) n b=
      r^2 • (forceTransportKernel r n a v+forceSourceKernel r n a v b) := by
  rw [normalisedSignedForce,smul_smul]
  have hc : (1-dot n a)*((1-dot n (velocity v))/(1-dot n a))=1-dot n (velocity v) := by
    field_simp
  rw [hc,normalisedElectricKernel_eq hr,receiverQ_smul,smul_comm,
    ←physical_force_kernel r n a v b hr hn]

lemma coneRadius_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0<r) :
    coneRadius x (x-r • n.1)=r := by
  simp only [coneRadius,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]

lemma coneDirection_sub_smul (x : Vec) (n : Sphere) {r : ℝ} (hr : 0<r) :
    coneDirection x (x-r • n.1)=n.1 := by
  rw [coneDirection,coneRadius_sub_smul x n hr,sub_sub_cancel,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

lemma retardedForceKernel_polar_normalised (s : Solution) (t : ℝ) (x a v : Vec)
    (n : Sphere) {r : ℝ} (hr : 0<r) (hD : 1-dot n.1 a≠0) :
    r^2 • retardedForceKernel s t x a (x-r • n.1) v=
      (1-dot n.1 a) • (s.f (t-r,(x-r • n.1,v)) •
        normalisedSignedForce r a (velocity v) n.1
          (sourceAcceleration s (t-r,(x-r • n.1,v)))) := by
  rw [smul_comm (1-dot n.1 a),normalisedSignedForce_flux n.1 a v _ hr.ne' (sphere_norm n) hD]
  rw [smul_comm]
  congr 1
  simp only [retardedForceKernel,coneRadius_sub_smul x n hr,coneDirection_sub_smul x n hr,
    sourceAcceleration]

lemma classical_retarded_force_polar_before {d : Datum} {s : Solution} {H t : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s)
    (ht : 0<t) (htH : t<H) (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫r in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (t-r,(x-r • n.1,v)) •
          normalisedSignedForce r a (velocity v) n.1
            (sourceAcceleration s (t-r,(x-r • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  rw [classical_retarded_force_representation_before hs hm ht htH x a]
  congr 2
  have hi := integrable_joint_retardedForceKernel hs.1 hs.2.1.continuousOn
    hs.2.2.1.continuousOn hs.2.2.2.2.2.2.1 ht.le le_rfl x a
  rw [integral_ball_polar_flip hi.integral_prod_left]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [←integral_smul,←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>by
      rw [←sub_eq_add_neg]
      exact retardedForceKernel_polar_normalised s t x a v n hr.1
        (by
          have hh := dot_le_norm n.1 a
          rw [sphere_norm,one_mul] at hh
          linarith)))

lemma sourceAcceleration_cutoff {s : Solution} {τ H σ : ℝ} (hτH : τ<H)
    (hσ : σ≤τ) (p : Phase) :
    sourceAcceleration (cutoffPrefix τ H s) (σ,p)=sourceAcceleration s (σ,p) := by
  simp only [sourceAcceleration,(cutoffPrefix_eq hτH hσ s).2.1 p.1,
    (cutoffPrefix_eq hτH hσ s).2.2 p.1]

lemma SmoothClassicalPrefix.retarded_force_polar {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
    (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫r in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (t-r,(x-r • n.1,v)) •
          normalisedSignedForce r a (velocity v) n.1
            (sourceAcceleration s (t-r,(x-r • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  let τ := (t+H)/2
  have htτ : t<τ := by dsimp [τ]; linarith
  have hτH : τ<H := by dsimp [τ]; linarith
  have he := classical_retarded_force_polar_before
    (hs.cutoff_classical_before (ht.le.trans htτ.le) hτH) (hs.cutoff_smooth hτH)
    ht htτ x a ha
  rw [(cutoffPrefix_eq hτH htτ.le s).2.1 x,(cutoffPrefix_eq hτH htτ.le s).2.2 x] at he
  refine he.trans ?_
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have hσ : t-r≤τ := by linarith [hr.1]
    dsimp only
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>by
      dsimp only
      rw [(cutoffPrefix_eq hτH hσ s).1,sourceAcceleration_cutoff hτH hσ]))

lemma integral_Ioo_reflect {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : ℝ→W) {t : ℝ} (ht : 0≤t) :
    (∫σ in Ioo (0:ℝ) t,g (t-σ))=∫r in Ioo (0:ℝ) t,g r := by
  have he := intervalIntegral.integral_comp_sub_left (a:=0) (b:=t) g t
  simpa only [sub_self,sub_zero,intervalIntegral.integral_of_le ht,
    integral_Ioc_eq_integral_Ioo] using he

lemma SmoothClassicalPrefix.retarded_force_source_polar {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0<t) (htH : t<H)
    (x a : Vec) (ha : ‖a‖<1) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫n : Sphere,∫σ in Ioo (0:ℝ) t,
        (1-dot n.1 a) • ∫v : Vec,s.f (σ,(x-(t-σ) • n.1,v)) •
          normalisedSignedForce (t-σ) a (velocity v) n.1
            (sourceAcceleration s (σ,(x-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  rw [hs.retarded_force_polar ht htH x a ha]
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    rw [←integral_Ioo_reflect (fun r=> (1-dot n.1 a) • ∫v : Vec,
      s.f (t-r,(x-r • n.1,v)) • normalisedSignedForce r a (velocity v) n.1
        (sourceAcceleration s (t-r,(x-r • n.1,v)))) ht.le]
    simp only [sub_sub_cancel])

end RVM

end

end OAI
