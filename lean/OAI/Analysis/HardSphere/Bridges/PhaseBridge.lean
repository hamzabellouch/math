import Mathlib
import OAI.Analysis.HardSphere.Geometry.CoordinateLine
import OAI.Analysis.HardSphere.Conditioning.PhaseMeasure

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def liftedBridgePath {N : ℕ} (t : ℝ) (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    C(Time,LiftedConfiguration N) :=
  ⟨fun s i j ↦ (1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s,by fun_prop⟩

def projectedBridgePath {N : ℕ} (L : Length) (t : ℝ) (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    ConfigurationPath N L :=
  ⟨fun s ↦ project N L (liftedBridgePath t X Y β s),(continuous_project N L).comp (liftedBridgePath t X Y β).continuous⟩

lemma reconstructed_bridge_eq {N : ℕ} (L : Length) {t : ℝ} (ht : 0<t)
    (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    freeTrajectory N L t
      (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β))
      (project N L X)=projectedBridgePath L t X Y β := by
  have ht' : Real.sqrt (2*t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  ext s i j
  change (X i j:AddCircle L.val)+
    (((Real.sqrt (2*t)*((Y i j-X i j)/Real.sqrt (2*t)*(s:ℝ)+β (i,j) s)):ℝ):AddCircle L.val)=
    (((1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s:ℝ):AddCircle L.val)
  rw [←AddCircle.coe_add]
  congr 1
  field_simp
  ring

lemma projectedBridgePath_endpoints {N : ℕ} (L : Length) (t : ℝ) (X Y : LiftedConfiguration N) :
    ∀ᵐ β ∂coordinateBridge N, projectedBridgePath L t X Y β 0=project N L X ∧
      projectedBridgePath L t X Y β 1=project N L Y := by
  filter_upwards [coordinateBridge_endpoints N] with β hβ
  constructor <;> ext i j
  · change (((1-(0:Time).val)*X i j+(0:Time).val*Y i j+Real.sqrt (2*t)*β (i,j) 0:ℝ):AddCircle L.val)=_
    simp [(hβ (i,j)).1]
    rfl
  · change (((1-(1:Time).val)*X i j+(1:Time).val*Y i j+Real.sqrt (2*t)*β (i,j) 1:ℝ):AddCircle L.val)=_
    simp [(hβ (i,j)).2]
    rfl

lemma killed_ae_lifted_bridges {N : ℕ} (L : Length) (a : ℝ) {t : ℝ} (ht : 0<t)
    (c : LiftedConfiguration N) {P : Configuration N L → Configuration N L → Prop}
    (hP : ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1)) :
    ∀ᵐ X ∂volume.restrict (localLiftBox L c), ∀ᵐ Y ∂(volume : Measure (LiftedConfiguration N)),
      ∀ᵐ β ∂coordinateBridge N, projectedBridgePath L t X Y β ∈ staysAllowed N L a →
        P (project N L X) (project N L Y) := by
  have hf : ∀ᵐ ω ∂freePathLaw N L t, ω∈staysAllowed N L a → P (ω 0) (ω 1) :=
    (ae_restrict_iff' (staysAllowed_open N L a).measurableSet).mp hP
  have hfree : MeasurePreserving (fun p : CoordinatePaths N × Configuration N L ↦
      freeTrajectory N L t p.1 p.2) ((coordinateWiener N).prod volume) (freePathLaw N L t) :=
    ⟨(freeTrajectory_continuous N L t).measurable,rfl⟩
  have hswap := (measurePreserving_swap (μ:= (volume : Measure (Configuration N L))) (ν:=coordinateWiener N))
  have hp := (localLiftBox_preserving L c).prod (reconstructCoordinates_preserving N)
  have hh := (hfree.comp (hswap.comp hp)).quasiMeasurePreserving.ae hf
  have hha := ae_ae_of_ae_prod hh
  filter_upwards [hha] with X hX
  have hxg := ae_ae_of_ae_prod hX
  have hxl := hxg.filter_mono (gaussianCoordinates_ac' N).ae_le
  have hxy := (endpointNoise_quasi ht X).ae hxl
  filter_upwards [hxy] with Y hY
  filter_upwards [hY,projectedBridgePath_endpoints L t X Y] with β hβ he
  change freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β))
    (project N L X)∈staysAllowed N L a → P
      (freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β)) (project N L X) 0)
      (freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β)) (project N L X) 1) at hβ
  rw [reconstructed_bridge_eq L ht X Y β] at hβ
  intro hs
  simpa only [he.1,he.2] using hβ hs

lemma exists_bridge_bounded_positive (N : ℕ) : ∃ B : ℝ, 0<B ∧
    coordinateBridge N {β | ‖β‖≤B} ≠ 0 := by
  by_contra! h
  have hz : coordinateBridge N (⋃ n : ℕ, {β | ‖β‖≤(n:ℝ)+1})=0 :=
    measure_iUnion_null (fun n ↦ h ((n:ℝ)+1) (by positivity))
  have he : (⋃ n : ℕ, {β : CoordinatePaths N | ‖β‖≤(n:ℝ)+1})=univ := by
    apply eq_univ_of_forall
    intro β
    obtain ⟨n,hn⟩ := exists_nat_gt ‖β‖
    exact mem_iUnion.mpr ⟨n,by simp only [mem_ofPred_eq]; linarith⟩
  rw [he,measure_univ] at hz
  exact one_ne_zero hz

lemma liftedBridge_distance {N : ℕ} {t : ℝ} (ht : 0≤t)
    (X Y : LiftedConfiguration N) (β : CoordinatePaths N) (s : Time) :
    dist (liftedBridgePath t X Y β s) ((1-(s:ℝ)) • X+(s:ℝ) • Y) ≤
      Real.sqrt (2*t)*‖β‖ := by
  have hscale : 0 ≤ Real.sqrt (2*t) := by
    simpa only [Real.sqrt_zero] using
      Real.sqrt_le_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht)
  apply (dist_pi_le_iff (mul_nonneg hscale (norm_nonneg β))).mpr
  intro i
  apply (dist_pi_le_iff (mul_nonneg hscale (norm_nonneg β))).mpr
  intro j
  change dist ((1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s)
    ((1-(s:ℝ))*X i j+(s:ℝ)*Y i j) ≤ _
  rw [Real.dist_eq,add_sub_cancel_left,abs_mul,abs_of_nonneg hscale]
  apply mul_le_mul_of_nonneg_left _ hscale
  exact (ContinuousMap.norm_coe_le_norm (β (i,j)) s).trans (norm_le_pi_norm β (i,j))

lemma projectedBridge_stays_of_bounded {N : ℕ} (L : Length) (a : ℝ)
    {c X Y : LiftedConfiguration N} {R t B : ℝ} (ht : 0≤t)
    (hball : Metric.ball c R ⊆ (project N L) ⁻¹' allowed N L a)
    (hX : X∈Metric.ball c (R/2)) (hY : Y∈Metric.ball c (R/2))
    (hsmall : Real.sqrt (2*t)*B<R/2) {β : CoordinatePaths N} (hβ : ‖β‖≤B) :
    projectedBridgePath L t X Y β ∈ staysAllowed N L a := by
  rintro _ ⟨s,rfl⟩
  apply hball
  have hz := (convex_ball c (R/2)) hX hY (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel 1 (s:ℝ))
  exact (dist_triangle _ ((1-(s:ℝ)) • X+(s:ℝ) • Y) c).trans_lt
    (lt_of_le_of_lt (add_le_add ((liftedBridge_distance ht X Y β s).trans
      (mul_le_mul_of_nonneg_left hβ (Real.sqrt_nonneg _))) (le_refl _)) (by
        change Real.sqrt (2*t)*B+dist ((1-(s:ℝ)) • X+(s:ℝ) • Y) c<R
        change dist ((1-(s:ℝ)) • X+(s:ℝ) • Y) c<R/2 at hz
        linarith))

lemma killed_ae_local_pairs {N : ℕ} (L : Length) (a : ℝ)
    {P : Configuration N L → Configuration N L → Prop}
    (hP : ∀t, 0<t → ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1))
    (c : LiftedConfiguration N) {R : ℝ} (hR : 0<R) (hL : R≤L.val)
    (hball : Metric.ball c R ⊆ (project N L) ⁻¹' allowed N L a) :
    ∀ᵐ X ∂volume.restrict (Metric.ball c (R/2)),
    ∀ᵐ Y ∂volume.restrict (Metric.ball c (R/2)), P (project N L X) (project N L Y) := by
  obtain ⟨B,hB,hpos⟩ := exists_bridge_bounded_positive N
  let t : ℝ := (R/(4*(B+1)))^2/2
  have ha : 0<R/(4*(B+1)) := div_pos hR (by positivity)
  have ht : 0<t := by dsimp [t]; positivity
  have hsqrt : Real.sqrt (2*t)=R/(4*(B+1)) := by
    rw [show 2*t=(R/(4*(B+1)))^2 by dsimp [t]; ring,Real.sqrt_sq ha.le]
  have hsmall : Real.sqrt (2*t)*B<R/2 := by
    rw [hsqrt]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0<4*(B+1))).mpr
    nlinarith
  have hh := killed_ae_lifted_bridges L a ht c (hP t ht)
  have hsub := ball_subset_localLiftBox L c (show R/2≤L.val/2 by linarith)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hh,ae_restrict_mem measurableSet_ball] with X hX hmemX
  filter_upwards [ae_restrict_of_ae hX,ae_restrict_mem measurableSet_ball] with Y hY hmemY
  obtain ⟨β,hβ,hpair⟩ := exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hY)
  exact hpair (projectedBridge_stays_of_bounded L a ht.le hball hmemX hmemY hsmall hβ)

end HardSphere

end

end OAI
