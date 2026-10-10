import OAI.MathematicalPhysics.Boltzmann.Branching.NormalOutgoingSymmetry
import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantParameterSupport
import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantPlaneIntegral
import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanNormalCoordinates
import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanOperator
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier

namespace OAI

section

/-! # The normal-and-plane Jacobian in physical velocity coordinates -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

def physicalFrame (n : Velocity) : V → Velocity :=
  (MeasurableEquiv.toLp 2 V) ∘ frame (WithLp.ofLp n) ‖transverse n‖

theorem physicalFrame_measurable (n : Velocity) : Measurable (physicalFrame n) :=
  (MeasurableEquiv.toLp 2 V).measurable.comp
    (frame (WithLp.ofLp n) ‖transverse n‖).continuous_of_finiteDimensional.measurable

theorem transverse_norm_sq (n : Velocity) :
    ‖transverse n‖^2 = n 0^2+n 1^2 := by
  simp [transverse,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]

theorem normal_normSq (n : Velocity) : RedundantPlane.normSq (WithLp.ofLp n) = ‖n‖^2 := by
  simp [RedundantPlane.normSq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]

theorem physicalFrame_map_volume {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) :
    Measure.map (physicalFrame n) (volume : Measure V) = ENNReal.ofReal ‖transverse n‖ • volume := by
  have hN : RedundantPlane.normSq (WithLp.ofLp n) = 1 := by rw [normal_normSq,hn,one_pow]
  have hF := unit_frame_map_volume (norm_pos_iff.mpr ht) (transverse_norm_sq n) hN
  have hm := (frame (WithLp.ofLp n) ‖transverse n‖).continuous_of_finiteDimensional.measurable
  rw [physicalFrame,← Measure.map_map (MeasurableEquiv.toLp 2 V).measurable hm,hF,
    Measure.map_smul]
  · congr 1
    exact (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  · exact (MeasurableEquiv.toLp 2 V).measurable.aemeasurable

theorem lintegral_physicalFrame {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Velocity, F w) = ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ q : V, F (physicalFrame n q) := by
  have h := lintegral_map (μ := (volume : Measure V)) hF (physicalFrame_measurable n)
  rw [physicalFrame_map_volume hn ht,lintegral_smul_measure,smul_eq_mul] at h
  have hr := norm_pos_iff.mpr ht
  rw [ENNReal.ofReal_inv_of_pos hr]
  rw [← h,← mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top,one_mul]

theorem normalComponent_physicalFrame {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) (v : Velocity) (q : V) :
    normalComponent v (v+physicalFrame n q) n = q 0 := by
  have h := frame_dot (norm_pos_iff.mpr ht) (transverse_norm_sq n) q
  rw [normal_normSq,hn,one_pow,mul_one] at h
  change inner ℝ (v-(v+physicalFrame n q)) n = q 0
  rw [show v-(v+physicalFrame n q) = -physicalFrame n q by abel,inner_neg_left,real_inner_comm]
  have he : inner ℝ n (physicalFrame n q) =
      WithLp.ofLp n ⬝ᵥ frame (WithLp.ofLp n) ‖transverse n‖ q := by
    simp [physicalFrame,PiLp.inner_apply,RCLike.inner_apply,dotProduct,mul_comm]
  rw [he,h,neg_neg]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Matching the tangent columns with the manuscript's collision-plane chart -/
noncomputable section
open MeasureTheory Matrix
open scoped Matrix RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine BoltzmannNonuniqueness.TransverseAverage
namespace BoltzmannNonuniqueness.CarlemanCoordinates

def planeFrame (n : Velocity) (z s : ℝ) : Velocity := physicalFrame n ![0,z,s]

theorem axial_planeFrame (n : Velocity) (z s : ℝ) : axial (planeFrame n z s) = z := by
  simp [planeFrame,physicalFrame,frame_apply,axial]

theorem transverse_planeFrame (n : Velocity) (z s : ℝ) :
    transverse (planeFrame n z s) =
      line (direction (transverse n)) (-n 2/‖transverse n‖*z) s := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  fin_cases i <;>
    simp [planeFrame,physicalFrame,frame_apply,transverse,line,quarterTurn,direction] <;> ring

theorem planeFrame_eq_origin_chart (n : Velocity) (z s : ℝ) :
    planeFrame n z s = chart 0 (-n) z s := by
  apply split.injective
  rw [split_apply,split_apply]
  apply Prod.ext
  · rw [axial_planeFrame,axial_chart]
    simp [axial]
  · rw [transverse_planeFrame,transverse_chart]
    have hn : normal 0 (-n) = transverse n := by
      simp [normal]
    rw [hn]
    simp [offset,PlaneChart.slope,normal,axial,show transverse (0 : Velocity) = 0 from rfl]
    congr 1
    ring

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The positive radial normal recovers the exact translated collision chart -/
noncomputable section
open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine BoltzmannNonuniqueness.TransverseAverage
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem planeFrame_orthogonal {n : Velocity} (ht : transverse n ≠ 0) (z s : ℝ) :
    inner ℝ n (planeFrame n z s) = 0 := by
  have hn : normal 0 (-n) ≠ 0 := by simpa [normal,transverse_sub] using ht
  have h := chart_on_plane 0 (-n) z s hn
  simpa only [zero_sub,neg_neg,sub_zero,← planeFrame_eq_origin_chart] using h

theorem normal_scaled (v n : Velocity) (a : ℝ) : normal v (v-a • n) = a • transverse n := by
  unfold normal
  rw [show v-(v-a • n) = a • n by module]
  rfl

theorem direction_pos_scaled {a : ℝ} (ha : 0 < a) (u : Transverse) :
    direction (a • u) = direction u := by
  simp [direction,norm_smul,Real.norm_eq_abs,abs_of_pos ha,smul_smul,ha.ne']

theorem positive_chart_frame (v : Velocity) {n : Velocity} (ht : transverse n ≠ 0)
    {a : ℝ} (ha : 0 < a) (z s : ℝ) :
    chart v (v-a • n) z (s+RedundantPlane.tangentOffset v (v-a • n)) =
      v+planeFrame n z s := by
  have hn : normal v (v-a • n) ≠ 0 := by
    rw [normal_scaled]
    exact smul_ne_zero ha.ne' ht
  have hd : direction (normal v (v-a • n)) = direction (transverse n) := by
    rw [normal_scaled,direction_pos_scaled ha]
  have hp : inner ℝ (v-(v-a • n)) (v+planeFrame n z s-v) = 0 := by
    rw [show v-(v-a • n) = a • n by module,add_sub_cancel_left,real_inner_smul_left,
      planeFrame_orthogonal ht,mul_zero]
  have hc := chart_recovers v (v-a • n) (v+planeFrame n z s) hn hp
  have hz : axial (v+planeFrame n z s)-axial v = z := by
    change axial v+axial (planeFrame n z s)-axial v = z
    rw [axial_planeFrame]
    ring
  have hs : inner ℝ (quarterTurn (direction (normal v (v-a • n))))
      (transverse (v+planeFrame n z s)) = s+RedundantPlane.tangentOffset v (v-a • n) := by
    change inner ℝ (quarterTurn (direction (normal v (v-a • n))))
      (transverse v+transverse (planeFrame n z s)) = _
    rw [inner_add_right,transverse_planeFrame,hd,
      inner_quarterTurn_line _ _ _ (norm_direction ht)]
    rw [RedundantPlane.tangentOffset,hd,add_comm]
  rwa [hz,hs] at hc

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Removing the symmetric average from the nonnegative gain -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness

def rawNonnegativeGain (f g : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  ∫⁻ w : Velocity, ∫⁻ n : Sphere,
    ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)*g (scatterRight v w n)
    ∂sphereArea

theorem scatter_complement_left (v w n : Velocity) :
    v+w-scatterLeft v w n = scatterRight v w n := by
  unfold scatterLeft scatterRight
  module

theorem scatter_complement_right (v w n : Velocity) :
    v+w-scatterRight v w n = scatterLeft v w n := by
  unfold scatterLeft scatterRight
  module

theorem normal_cross_integral_symm (v w : Velocity) {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n) ∂sphereArea) =
    ∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*
      g (scatterLeft v w n)*f (scatterRight v w n) ∂sphereArea := by
  let H : Velocity → ℝ≥0∞ := fun u => f u*g (v+w-u)
  have hH : Measurable H := hf.mul (hg.comp (by fun_prop))
  have h := (normal_left_integral_outgoing v w hH).trans
    (normal_right_integral_outgoing v w hH).symm
  simpa only [H,scatter_complement_left,scatter_complement_right,mul_assoc,
    mul_left_comm,mul_comm] using h

def rawGainIntegrand (f g : Velocity → ℝ≥0∞) (v : Velocity) (p : Velocity × Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel v p.1 p.2)*f (scatterLeft v p.1 p.2)*g (scatterRight v p.1 p.2)

theorem rawGainIntegrand_measurable {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    Measurable (rawGainIntegrand f g v) := by
  have hleft : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hright : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hker : Measurable (fun p : Velocity × Sphere => ENNReal.ofReal (collisionKernel v p.1 p.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hker.mul (hf.comp hleft)).mul (hg.comp hright)

theorem rawGain_eq_lintegral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v = ∫⁻ p, rawGainIntegrand f g v p ∂gainPairMeasure := by
  exact (lintegral_prod _ (rawGainIntegrand_measurable hf hg v).aemeasurable).symm

theorem rawNonnegativeGain_symm {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v = rawNonnegativeGain g f v := by
  apply lintegral_congr
  intro w
  exact normal_cross_integral_symm v w hf hg

theorem nonnegativeGain_eq_raw {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    nonnegativeGain f g v = rawNonnegativeGain f g v := by
  have hfg := rawGainIntegrand_measurable hf hg v
  have hgf := rawGainIntegrand_measurable hg hf v
  have he : nonnegativeGain f g v =
      ∫⁻ p, (2 : ℝ≥0∞)⁻¹*(rawGainIntegrand f g v p+rawGainIntegrand g f v p)
        ∂gainPairMeasure := by
    apply lintegral_congr
    intro p
    unfold rawGainIntegrand
    rw [div_eq_mul_inv,mul_add,mul_add]
    ac_rfl
  rw [he]
  change (∫⁻ p, (2 : ℝ≥0∞)⁻¹*((rawGainIntegrand f g v+rawGainIntegrand g f v) p)
    ∂gainPairMeasure) = _
  rw [lintegral_const_mul _ (hfg.add hgf)]
  change (2 : ℝ≥0∞)⁻¹ * (∫⁻ p, rawGainIntegrand f g v p+rawGainIntegrand g f v p
    ∂gainPairMeasure) = _
  rw [lintegral_add_left hfg,
    ← rawGain_eq_lintegral hf hg v,← rawGain_eq_lintegral hg hf v,
    ← rawNonnegativeGain_symm hf hg v,← two_mul,← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

end BoltzmannNonuniqueness

end

end

section

/-! # Measurable collision-plane averages and their orientation invariance -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem physicalFrame_joint_measurable :
    Measurable (fun x : Velocity × V => physicalFrame x.1 x.2) := by
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  simp_rw [frame_apply]
  apply Measurable.of_eval
  intro i
  fin_cases i <;> fun_prop

attribute [local irreducible] physicalFrame frame

def planeAverage (g : Velocity → ℝ≥0∞) (v n : Velocity) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (v+planeFrame n z s)

theorem planeFrame_joint_measurable :
    Measurable (fun x : Velocity × (ℝ × ℝ) => planeFrame x.1 x.2.1 x.2.2) := by
  unfold planeFrame
  have hm : Measurable (fun x : Velocity × (ℝ × ℝ) => (x.1, (![0,x.2.1,x.2.2] : V))) := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  exact physicalFrame_joint_measurable.comp hm

attribute [local irreducible] planeFrame

theorem planeAverage_measurable {g : Velocity → ℝ≥0∞} (hg : Measurable g)
    (v : Velocity) : Measurable (planeAverage g v) := by
  have hm : Measurable (fun x : (Velocity × ℝ) × ℝ =>
      g (v+planeFrame x.1.1 x.1.2 x.2)) := by
    apply hg.comp
    apply measurable_const.add
    exact planeFrame_joint_measurable.comp
      ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.lintegral_prod_right'.lintegral_prod_right'

theorem planeFrame_neg (n : Velocity) (z s : ℝ) :
    planeFrame (-n) z s = planeFrame n z (-s) := by
  have ht : transverse (-n) = -transverse n := rfl
  ext i
  fin_cases i <;> simp [planeFrame,physicalFrame,frame_apply,ht]

theorem planeAverage_neg {g : Velocity → ℝ≥0∞} (hg : Measurable g)
    (v n : Velocity) : planeAverage g v (-n) = planeAverage g v n := by
  apply lintegral_congr
  intro z
  simp_rw [planeFrame_neg]
  have hm : Measurable (fun s => g (v+planeFrame n z s)) := by
    apply hg.comp
    apply measurable_const.add
    exact planeFrame_joint_measurable.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h := lintegral_map (μ := (volume : Measure ℝ)) hm measurable_neg
  rw [Measure.map_neg_eq_self] at h
  exact h.symm

theorem planeAverage_eq_chart (g : Velocity → ℝ≥0∞) (v : Velocity)
    {n : Velocity} (ht : transverse n ≠ 0) {a : ℝ} (ha : 0 < a) :
    planeAverage g v n = ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (PlaneChart.chart v (v-a • n) z s) := by
  apply lintegral_congr
  intro z
  calc
    _ = ∫⁻ s : ℝ, g (PlaneChart.chart v (v-a • n) z
        (s+RedundantPlane.tangentOffset v (v-a • n))) := by
      apply lintegral_congr
      intro s
      rw [positive_chart_frame v ht ha]
    _ = _ := lintegral_add_right_eq_self
      (fun s : ℝ => g (PlaneChart.chart v (v-a • n) z s)) _

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Splitting normal displacement from the two collision-plane parameters -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem physicalFrame_decomposition (n : Velocity) (q : V) :
    physicalFrame n q = (-q 0) • n + physicalFrame n ![0,q 1,q 2] := by
  ext i
  fin_cases i <;> simp [physicalFrame,frame_apply] <;> ring

theorem scatterLeft_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) (q : V) :
    scatterLeft v (v+physicalFrame n q) n = v-q 0 • n := by
  unfold scatterLeft
  rw [normalComponent_physicalFrame hn ht]

theorem scatterRight_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) (q : V) :
    scatterRight v (v+physicalFrame n q) n = v+physicalFrame n ![0,q 1,q 2] := by
  unfold scatterRight
  rw [normalComponent_physicalFrame hn ht,physicalFrame_decomposition]
  module

theorem lintegral_shifted_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Velocity, F w) = ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ a : ℝ, ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (v+physicalFrame n ![a,z,s]) := by
  have hm : Measurable (fun w : Velocity => F (v+w)) := hF.comp (by fun_prop)
  have h := lintegral_physicalFrame hn ht hm
  rw [lintegral_add_left_eq_self] at h
  rw [h]
  congr 1
  let G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun x => F (v+physicalFrame n ![x.1,x.2.1,x.2.2])
  have hg : Measurable G := by
    apply hF.comp
    apply measurable_const.add
    apply (physicalFrame_measurable n).comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  have he : (fun q : V => F (v+physicalFrame n q)) = G ∘ RedundantPlane.splitThree := by
    funext q
    dsimp [G,RedundantPlane.splitThree_apply,Function.comp_def]
    congr 2
  rw [he]
  change (∫⁻ q : V, G (RedundantPlane.splitThree q)) = _
  rw [RedundantPlane.splitThree_measurePreserving.lintegral_comp hg]
  rw [MeasureTheory.Measure.volume_eq_prod,lintegral_prod _ hg.aemeasurable]
  apply lintegral_congr
  intro a
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact lintegral_prod _ ((hg.comp measurable_prodMk_left).aemeasurable)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The exceptional axial normal directions have zero sphere area -/
noncomputable section
open MeasureTheory Set
open scoped Pointwise ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem sphere_ae_transverse_ne_zero :
    ∀ᵐ n : Sphere ∂sphereArea, transverse n.1 ≠ 0 := by
  have hm : MeasurableSet {n : Sphere | transverse n.1 = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    unfold transverse
    fun_prop
  have hzero : (volume : Measure Velocity) {x | transverse x = 0} = 0 := by
    simpa only [not_not] using ae_iff.mp SheetApplication.ae_transverse_ne_zero
  have hcone : (volume : Measure Velocity)
      (Ioo (0 : ℝ) 1 • ((↑) '' {n : Sphere | transverse n.1 = 0})) = 0 := by
    apply measure_mono_null _ hzero
    rintro x ⟨r,-,y,⟨n,hn,rfl⟩,rfl⟩
    change transverse (r • n.1) = 0
    have he : transverse (r • n.1) = r • transverse n.1 := rfl
    rw [he,hn,smul_zero]
  rw [ae_iff]
  simp only [not_not]
  change (volume : Measure Velocity).toSphere {n : Sphere | transverse n.1 = 0} = 0
  rw [Measure.toSphere_apply' _ hm,hcone,mul_zero]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Splitting an even nonnegative integral at zero -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem lintegral_even_halfline {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (heven : ∀ a, F (-a) = F a) :
    (∫⁻ a : ℝ, F a) = 2 * ∫⁻ a in Ioi (0 : ℝ), F a := by
  have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
  have he : Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by ext a; simp
  rw [he] at hp
  have hi := hp.lintegral_comp hF
  simp only [heven] at hi
  have hu : Iio (0 : ℝ) ∪ Ioi 0 = ({0} : Set ℝ)ᶜ := by
    ext a
    simp only [mem_union,mem_Iio,mem_Ioi,mem_compl_iff,mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
    · exact lt_or_gt_of_ne
  have hd : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    apply disjoint_left.mpr
    intro a ha hb
    change a < 0 at ha
    change 0 < a at hb
    linarith
  have h := lintegral_union (μ := (volume : Measure ℝ)) (f := F) measurableSet_Ioi hd
  rw [hu,restrict_compl_singleton] at h
  rw [h,hi,two_mul]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The gain integral after splitting the incoming velocity along a fixed normal -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeFrame physicalFrame planeAverage

theorem planePoint_measurable (v n : Velocity) :
    Measurable (fun p : ℝ × ℝ => v+planeFrame n p.1 p.2) := by
  apply measurable_const.add
  exact planeFrame_joint_measurable.comp (measurable_const.prodMk measurable_id)

theorem lintegral_plane_const_mul (c : ℝ≥0∞) {g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v n : Velocity) :
    (∫⁻ z : ℝ, ∫⁻ s : ℝ, c*g (v+planeFrame n z s)) = c*planeAverage g v n := by
  unfold planeAverage
  have hm := hg.comp (planePoint_measurable v n)
  calc
    _ = ∫⁻ z : ℝ, c * ∫⁻ s : ℝ, g (v+planeFrame n z s) := by
      apply lintegral_congr
      intro z
      exact lintegral_const_mul c (hm.comp measurable_prodMk_left)
    _ = _ := lintegral_const_mul c hm.lintegral_prod_right'

theorem normal_gain_integral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity)
    {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0) :
    (∫⁻ w : Velocity, ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n)) =
    ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ a : ℝ, ENNReal.ofReal |a| * f (v-a • n)*planeAverage g v n := by
  have hm : Measurable (fun w : Velocity => ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n)) := by
    have hl : Measurable (fun w : Velocity => scatterLeft v w n) := by
      unfold scatterLeft normalComponent
      fun_prop
    have hr : Measurable (fun w : Velocity => scatterRight v w n) := by
      unfold scatterRight normalComponent
      fun_prop
    have hk : Measurable (fun w : Velocity => ENNReal.ofReal (collisionKernel v w n)) := by
      unfold collisionKernel normalComponent
      fun_prop
    exact (hk.mul (hf.comp hl)).mul (hg.comp hr)
  rw [lintegral_shifted_frame hn ht v hm]
  congr 1
  apply lintegral_congr
  intro a
  simp_rw [collisionKernel,normalComponent_physicalFrame hn ht,
    scatterLeft_frame hn ht,scatterRight_frame hn ht]
  change (∫⁻ z : ℝ, ∫⁻ s : ℝ, (ENNReal.ofReal |a| * f (v-a • n))*
    g (v+physicalFrame n ![0,z,s])) = _
  simpa only [planeFrame] using lintegral_plane_const_mul (ENNReal.ofReal |a| * f (v-a • n)) hg v n

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # A measurable radial integrand, even after integration over the sphere -/
noncomputable section
open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeAverage planeFrame physicalFrame

def radialIntegrand (f g : Velocity → ℝ≥0∞) (v : Velocity) (a : ℝ) (n : Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (‖transverse n.1‖⁻¹) *
    (ENNReal.ofReal |a| * f (v-a • n.1) * planeAverage g v n.1)

theorem radialIntegrand_measurable {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    Measurable (Function.uncurry (radialIntegrand f g v)) := by
  have hr : Measurable (fun x : ℝ × Sphere => ENNReal.ofReal (‖transverse x.2.1‖⁻¹)) := by
    unfold transverse
    fun_prop
  have ha : Measurable (fun x : ℝ × Sphere => ENNReal.ofReal |x.1|) := by fun_prop
  have hp : Measurable (fun x : ℝ × Sphere => f (v-x.1 • x.2.1)) := hf.comp (by fun_prop)
  have hq : Measurable (fun x : ℝ × Sphere => planeAverage g v x.2.1) :=
    (planeAverage_measurable hg v).comp (measurable_subtype_coe.comp measurable_snd)
  exact hr.mul ((ha.mul hp).mul hq)

theorem radialIntegrand_neg {f g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v : Velocity) (a : ℝ) (n : Sphere) :
    radialIntegrand f g v (-a) n = radialIntegrand f g v a (-n) := by
  have ht : transverse (-n.1) = -transverse n.1 := rfl
  simp [radialIntegrand,ht,planeAverage_neg hg,neg_smul,smul_neg]

attribute [local irreducible] radialIntegrand

theorem angularRadial_even {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) (a : ℝ) :
    (∫⁻ n : Sphere, radialIntegrand f g v (-a) n ∂sphereArea) =
      ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  simp_rw [radialIntegrand_neg hg]
  exact sphereArea_antipodal.lintegral_comp
    ((radialIntegrand_measurable hf hg v).comp measurable_prodMk_left)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The measurable Carleman profile and its radial weight -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] chart physicalFrame planeFrame

def chartProfile (g : Velocity → ℝ≥0∞) (v p : Velocity) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (chart v p z s)

theorem chartProfile_measurable {g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v : Velocity) : Measurable (chartProfile g v) := by
  have hm : Measurable (fun x : (Velocity × ℝ) × ℝ => g (chart v x.1.1 x.1.2 x.2)) :=
    hg.comp ((ChartKernel.measurable_point v).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hn : Measurable (fun p : Velocity => ENNReal.ofReal (‖normal v p‖⁻¹)) := by
    unfold normal
    exact ((ChartKernel.measurable_transverse.comp (measurable_const.sub measurable_id)).norm.inv).ennreal_ofReal
  exact hn.mul hm.lintegral_prod_right'.lintegral_prod_right'

theorem chartGain_eq_density_integral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    chartGain (volume.withDensity f) g v = 2 * ∫⁻ p : Velocity, f p*chartProfile g v p := by
  change 2 * (∫⁻ p : Velocity, chartProfile g v p ∂volume.withDensity f) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (chartProfile_measurable hg v)]
  rfl

theorem radial_chart_weight {v n : Velocity} (ht : transverse n ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (a^2) * ENNReal.ofReal (‖normal v (v-a • n)‖⁻¹) =
      ENNReal.ofReal (‖transverse n‖⁻¹) * ENNReal.ofReal a := by
  rw [normal_scaled,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  rw [← ENNReal.ofReal_mul (sq_nonneg a),← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
  congr 1
  field_simp [ha.ne', (norm_pos_iff.mpr ht).ne']

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Polar coordinates identify the chart profile with the positive normal integral -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] PlaneChart.chart physicalFrame planeFrame planeAverage

theorem lintegral_positive_radial_weight {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ a : Ioi (0 : ℝ), H a ∂Measure.volumeIoiPow 2) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a^2)*H a := by
  unfold Measure.volumeIoiPow
  calc
    _ = ∫⁻ a : Ioi (0 : ℝ), ENNReal.ofReal ((a : ℝ)^2)*H a
        ∂volume.comap Subtype.val := by
      simpa only [Pi.mul_apply,Function.comp_apply] using
        lintegral_withDensity_eq_lintegral_mul (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))
          (show Measurable (fun a : Ioi (0 : ℝ) => ENNReal.ofReal ((a : ℝ)^2)) by fun_prop)
          (hH.comp measurable_subtype_coe)
    _ = _ := lintegral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => ENNReal.ofReal (a^2)*H a)

theorem radial_chart_integrand {f g : Velocity → ℝ≥0∞} (v : Velocity)
    {n : Sphere} (ht : transverse n.1 ≠ 0) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (a^2)*(f (v-a • n.1)*chartProfile g v (v-a • n.1)) =
      radialIntegrand f g v a n := by
  rw [chartProfile,← planeAverage_eq_chart g v ht ha]
  calc
    _ = (ENNReal.ofReal (a^2)*ENNReal.ofReal (‖PlaneChart.normal v (v-a • n.1)‖⁻¹))*
        (f (v-a • n.1)*planeAverage g v n.1) := by ac_rfl
    _ = _ := by
      rw [radial_chart_weight ht ha]
      simp only [radialIntegrand,abs_of_pos ha]
      ac_rfl

theorem chart_integral_eq_positive_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    (∫⁻ p : Velocity, f p*chartProfile g v p) =
      ∫⁻ n : Sphere, ∫⁻ a in Ioi (0 : ℝ), radialIntegrand f g v a n ∂volume ∂sphereArea := by
  let H : Velocity → ℝ≥0∞ := fun p => f p*chartProfile g v p
  have hH : Measurable H := hf.mul (chartProfile_measurable hg v)
  have hT : Measurable (fun y : Velocity => H (v-y)) := hH.comp (by fun_prop)
  calc
    _ = ∫⁻ y : Velocity, H (v-y) := by
      calc
        _ = ∫⁻ y : Velocity, H (v+y) := (lintegral_add_left_eq_self H v).symm
        _ = _ := (lintegral_neg_eq_self (fun y : Velocity => H (v+y))).symm
    _ = ∫⁻ n : Sphere, ∫⁻ a : Ioi (0 : ℝ), H (v-(a:ℝ) • n.1)
        ∂Measure.volumeIoiPow 2 ∂sphereArea := lintegral_velocity_polar hT
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [sphere_ae_transverse_ne_zero] with n hn
      calc
        _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a^2)*H (v-a • n.1) :=
          lintegral_positive_radial_weight (H := fun a : ℝ => H (v-a • n.1))
            (hH.comp (by fun_prop))
        _ = _ := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro a ha
          exact radial_chart_integrand v hn ha

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The full gain as twice a positive radial integral -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeAverage planeFrame physicalFrame radialIntegrand

theorem rawGain_eq_signed_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v =
      ∫⁻ a : ℝ, ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  have hraw := rawGainIntegrand_measurable hf hg v
  have hrad := radialIntegrand_measurable hf hg v
  calc
    _ = ∫⁻ n : Sphere, ∫⁻ w : Velocity, ENNReal.ofReal (collisionKernel v w n)*
        f (scatterLeft v w n)*g (scatterRight v w n) ∂volume ∂sphereArea :=
      lintegral_lintegral_swap hraw.aemeasurable
    _ = ∫⁻ n : Sphere, ∫⁻ a : ℝ, radialIntegrand f g v a n ∂volume ∂sphereArea := by
      apply lintegral_congr_ae
      filter_upwards [sphere_ae_transverse_ne_zero] with n hn
      have hunit : ‖n.1‖ = 1 := mem_sphere_zero_iff_norm.mp n.property
      rw [normal_gain_integral hf hg v hunit hn]
      simpa only [radialIntegrand,Pi.mul_apply,Function.comp_apply] using (lintegral_const_mul _
        (((show Measurable (fun a : ℝ => ENNReal.ofReal |a|) by fun_prop).mul
          (hf.comp (by fun_prop))).mul_const _)).symm
    _ = _ := (lintegral_lintegral_swap hrad.aemeasurable).symm

theorem rawGain_eq_positive_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v =
      2 * ∫⁻ a in Ioi (0 : ℝ), ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  rw [rawGain_eq_signed_radial hf hg v]
  exact lintegral_even_halfline (radialIntegrand_measurable hf hg v).lintegral_prod_right'
    (angularRadial_even hf hg v)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The nonnegative hard-sphere Carleman identity

This proves the precise density identity used from Gamba--Panferov--Villani,
ARMA 194 (2009), Appendix C, Lemma 16 and its hard-sphere specialization.
Only nonnegative measurable densities are used; no identity for atomic
incoming measures is asserted.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness
open CarlemanCoordinates

theorem nonnegativeGain_eq_chartGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    nonnegativeGain f g v = chartGain (volume.withDensity f) g v := by
  rw [nonnegativeGain_eq_raw hf hg v,rawGain_eq_positive_radial hf hg v,
    chartGain_eq_density_integral hf hg v,chart_integral_eq_positive_radial hf hg v]
  congr 1
  exact lintegral_lintegral_swap (radialIntegrand_measurable hf hg v).aemeasurable

namespace Published

theorem gpv2009CarlemanInput : GPV2009CarlemanInput := by
  intro f g hf hg
  exact Filter.Eventually.of_forall (nonnegativeGain_eq_chartGain hf hg)

end Published
end BoltzmannNonuniqueness

end

end

end OAI
