import OAI.Probability.GaussianReplacement.Slab

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


section PosteriorWeight
variable {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S]

lemma posterior_weight_integral (P : Measure (O×S)) [IsFiniteMeasure P]
    (b : S→ℝ≥0∞) (hb : Measurable b) (f : O→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z.1*b z.2 ∂P) =
      ∫⁻ o, f o*(∫⁻ s, b s ∂P.condKernel o) ∂P.fst := by
  have hm : Measurable (fun z : O×S => f z.1*b z.2) :=
    (hf.comp measurable_fst).mul (hb.comp measurable_snd)
  rw [←Measure.lintegral_condKernel hm]
  congr 1
  funext o
  simpa only [Prod.fst,Prod.snd] using (lintegral_const_mul (μ:=P.condKernel o) (f o) hb)

lemma posterior_weighted_fst (P : Measure (O×S)) [IsFiniteMeasure P]
    (b : S→ℝ≥0∞) (hb : Measurable b) :
    (P.withDensity (fun z : O×S => b z.2)).fst =
      P.fst.withDensity (fun o => ∫⁻ s, b s ∂P.condKernel o) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.fst,lintegral_map hf measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : O×S => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : O×S => f z.1) from hf.comp measurable_fst),
    lintegral_withDensity_eq_lintegral_mul _ (hb.lintegral_kernel (κ:=P.condKernel)) hf]
  simp only [Pi.mul_apply]
  simp_rw [mul_comm (b _) (f _),mul_comm (∫⁻ s, b s ∂P.condKernel _) (f _)]
  exact posterior_weight_integral P b hb f hf
end PosteriorWeight

def sphericalPosteriorWeight (d k : ℕ) [Nonempty (Sphere d)] (b : Sphere d→ℝ≥0∞)
    (o : Rows k d×(Fin k→ℝ)) : ℝ≥0∞ := ∫⁻ s, b s ∂sphericalFiberKernel d k o

lemma measurable_sphericalPosteriorWeight {d k : ℕ} [Nonempty (Sphere d)]
    {b : Sphere d→ℝ≥0∞} (hb : Measurable b) : Measurable (sphericalPosteriorWeight d k b) :=
  hb.lintegral_kernel

lemma fiberObservationLaw_fst (d k : ℕ) :
    (fiberObservationLaw d k).fst = projectionJoint (uniformSphere d) (gaussianRows k d) := by
  rw [fiberObservationLaw,
    Measure.fst_map_prodMk (measurable_fst.prodMk measurable_own_label) measurable_snd]
  rfl

lemma fiberObservationLaw_weighted_fst {d k : ℕ} (b : Sphere d→ℝ≥0∞) (hb : Measurable b) :
    ((fiberObservationLaw d k).withDensity (fun z => b z.2)).fst =
      projectionJoint ((uniformSphere d).withDensity b) (gaussianRows k d) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.fst,lintegral_map hf measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => f z.1) from hf.comp measurable_fst)]
  simp only [Pi.mul_apply]
  rw [fiberObservationLaw,lintegral_map
    (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d => b z.2*f z.1) from
      (hb.comp measurable_snd).mul (hf.comp measurable_fst)) measurable_fiberObservationMap]
  rw [projectionJoint,lintegral_map hf (measurable_fst.prodMk measurable_own_label),
    prod_withDensity_right hb,lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Rows k d×Sphere d => b z.2) from hb.comp measurable_snd)
      (show Measurable (fun z : Rows k d×Sphere d => f (z.1,label z.1 (z.2:Vector d))) from
        hf.comp (measurable_fst.prodMk measurable_own_label))]
  rfl

lemma sphericalPosterior_density {d k : ℕ} [Nonempty (Sphere d)]
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b)
    [IsFiniteMeasure ((uniformSphere d).withDensity b)]
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume) :
    (fun o : Rows k d×(Fin k→ℝ) => exactDensity ((uniformSphere d).withDensity b) o.1 o.2) =ᵐ[
      (gaussianRows k d).prod (volume : Measure (Fin k→ℝ))]
      (fun o => exactDensity (uniformSphere d) o.1 o.2 * sphericalPosteriorWeight d k b o) := by
  have hρ : ∀ᵐ C ∂gaussianRows k d, labelLaw ((uniformSphere d).withDensity b) C ≪ volume := by
    filter_upwards [hAC] with C hC
    exact (Measure.AbsolutelyContinuous.map (withDensity_absolutelyContinuous _ b)
      (by unfold label; fun_prop)).trans hC
  apply (withDensity_eq_iff_of_sigmaFinite (measurable_exactDensity _).aemeasurable
    ((measurable_exactDensity _).mul (measurable_sphericalPosteriorWeight hb)).aemeasurable).mp
  rw [projectionJoint_withDensity _ _ hρ,
    withDensity_mul _ (measurable_exactDensity _) (measurable_sphericalPosteriorWeight hb),
    projectionJoint_withDensity _ _ hAC]
  rw [←fiberObservationLaw_fst]
  change _ = (fiberObservationLaw d k).fst.withDensity
    (fun o => ∫⁻ s, b s ∂(fiberObservationLaw d k).condKernel o)
  rw [←posterior_weighted_fst _ b hb,fiberObservationLaw_weighted_fst b hb]



def fiberBilinearTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (z : Rows k d×(Sphere d×Sphere d)) : ℝ≥0∞ :=
  (H z.1 : ℝ≥0∞)*b z.2.1*a z.2.2

lemma measurable_fiberBilinearTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {b a : Sphere d→ℝ≥0∞} (hb : Measurable b) (ha : Measurable a) :
    Measurable (fiberBilinearTest H b a) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  exact ((hH.comp measurable_fst).mul (hb.comp measurable_snd.fst)).mul (ha.comp measurable_snd.snd)

lemma fiberLeft_bilinear {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ o : Rows k d×(Fin k→ℝ), (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2 *
        sphericalPosteriorWeight d k b o * sphericalPosteriorWeight d k a o
        ∂projectionJoint (uniformSphere d) (gaussianRows k d) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hp := measurable_exactDensity (k:=k) (uniformSphere d)
  have hap := measurable_sphericalPosteriorWeight (d:=d) (k:=k) ha
  have hbp := measurable_sphericalPosteriorWeight (d:=d) (k:=k) hb
  have hf : Measurable (fun o : Rows k d×(Fin k→ℝ) =>
      (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2*sphericalPosteriorWeight d k a o) :=
    ((hH.comp measurable_fst).mul hp).mul hap
  have hObs : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hinner (z : Rows k d×Sphere d) :
      (∫⁻ t : Sphere d, (H z.1 : ℝ≥0∞)*b z.2*a t ∂sphericalFiberKernel d k (z.1,label z.1 (z.2:Vector d))) =
      (H z.1 : ℝ≥0∞)*b z.2*sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d)) :=
    lintegral_const_mul _ ha
  calc
    _ = ∫⁻ z : Rows k d×Sphere d,
        exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)) *
        ((H z.1 : ℝ≥0∞)*b z.2*sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d)))
        ∂(gaussianRows k d).prod (uniformSphere d) := by
      rw [fiberTwoPointLeft,lintegral_map (measurable_fiberBilinearTest H hb ha) (by fun_prop)]
      rw [Measure.lintegral_compProd (by
        change Measurable (fun z : (Rows k d×Sphere d)×Sphere d =>
          (H z.1.1 : ℝ≥0∞)*b z.1.2*a z.2)
        fun_prop)]
      simp only [fiberBilinearTest,Kernel.comap_apply]
      simp_rw [hinner]
      exact lintegral_withDensity_eq_lintegral_mul _ (measurable_own_exact (uniformSphere d))
        (show Measurable (fun z : Rows k d×Sphere d => (H z.1 : ℝ≥0∞)*b z.2 *
          sphericalPosteriorWeight d k a (z.1,label z.1 (z.2:Vector d))) from
          ((hH.comp measurable_fst).mul (hb.comp measurable_snd)).mul (hap.comp hObs))
    _ = ∫⁻ z, ((H z.1.1 : ℝ≥0∞)*exactDensity (uniformSphere d) z.1.1 z.1.2*
        sphericalPosteriorWeight d k a z.1)*b z.2 ∂fiberObservationLaw d k := by
      rw [fiberObservationLaw,lintegral_map
        (show Measurable (fun z : (Rows k d×(Fin k→ℝ))×Sphere d =>
          ((H z.1.1 : ℝ≥0∞)*exactDensity (uniformSphere d) z.1.1 z.1.2*
          sphericalPosteriorWeight d k a z.1)*b z.2) from
          (hf.comp measurable_fst).mul (hb.comp measurable_snd)) measurable_fiberObservationMap]
      apply lintegral_congr
      intro z
      dsimp only
      ac_rfl
    _ = _ := by
      rw [posterior_weight_integral _ b hb _ hf,fiberObservationLaw_fst]
      apply lintegral_congr
      intro o
      change (H o.1 : ℝ≥0∞)*exactDensity (uniformSphere d) o.1 o.2*
        sphericalPosteriorWeight d k a o*sphericalPosteriorWeight d k b o = _
      ac_rfl

lemma fiberLeft_bilinear_comm {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H a b z ∂fiberTwoPointLeft d k := by
  rw [fiberLeft_bilinear H b a hb ha,fiberLeft_bilinear H a b ha hb]
  apply lintegral_congr
  intro o
  ac_rfl

lemma fiberLeft_quadratic {d k : ℕ} [Nonempty (Sphere d)]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b)
    [IsFiniteMeasure ((uniformSphere d).withDensity b)]
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointLeft d k) =
      ∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b)
        z.1 (label z.1 (z.2:Vector d)) ∂(gaussianRows k d).prod ((uniformSphere d).withDensity b) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hp := measurable_exactDensity (k:=k) ((uniformSphere d).withDensity b)
  have hpb := measurable_sphericalPosteriorWeight (d:=d) (k:=k) hb
  have he := sphericalPosterior_density b hb hAC
  have hE : (fun o : Rows k d×(Fin k→ℝ) => exactDensity ((uniformSphere d).withDensity b) o.1 o.2) =ᵐ[
      projectionJoint (uniformSphere d) (gaussianRows k d)]
      (fun o => exactDensity (uniformSphere d) o.1 o.2*sphericalPosteriorWeight d k b o) := by
    rw [←projectionJoint_withDensity _ _ hAC]
    exact (withDensity_absolutelyContinuous _ _).ae_le he
  rw [fiberLeft_bilinear H b b hb hb]
  calc
    _ = ∫⁻ o : Rows k d×(Fin k→ℝ), sphericalPosteriorWeight d k b o *
        ((H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2)
        ∂projectionJoint (uniformSphere d) (gaussianRows k d) := by
      apply lintegral_congr_ae
      filter_upwards [hE] with o ho
      rw [ho]
      ac_rfl
    _ = ∫⁻ o : Rows k d×(Fin k→ℝ), (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2
        ∂projectionJoint ((uniformSphere d).withDensity b) (gaussianRows k d) := by
      rw [←fiberObservationLaw_weighted_fst b hb,posterior_weighted_fst _ b hb,
        fiberObservationLaw_fst]
      symm
      exact lintegral_withDensity_eq_lintegral_mul _ hpb
        (show Measurable (fun o : Rows k d×(Fin k→ℝ) =>
          (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2) from
          (hH.comp measurable_fst).mul hp)
    _ = _ := lintegral_map
      (show Measurable (fun o : Rows k d×(Fin k→ℝ) =>
        (H o.1 : ℝ≥0∞)*exactDensity ((uniformSphere d).withDensity b) o.1 o.2) from
        (hH.comp measurable_fst).mul hp) (measurable_fst.prodMk measurable_own_label)



lemma measurable_perpendicularRowsMap (d k : ℕ) :
    Measurable (fun z : (Sphere d×Sphere d)×Rows k d =>
      fun i => perpendicularRow ((z.1.1:Vector d)-(z.1.2:Vector d)) (z.2 i)) := by
  unfold perpendicularRow
  fun_prop

instance perpendicularRowsKernel_markov (d k : ℕ) : IsMarkovKernel (perpendicularRowsKernel d k) :=
  dependentMapKernel_markov _ _ (measurable_perpendicularRowsMap d k)

lemma perpendicularRow_neg {d : ℕ} (v g : Vector d) : perpendicularRow (-v) g = perpendicularRow v g := by
  simp [perpendicularRow,neg_div,neg_smul,sub_eq_add_neg]

lemma fiberPerpendicularTest_swap {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (z : Sphere d×Sphere d) : fiberPerpendicularTest H z.swap = fiberPerpendicularTest H z := by
  unfold fiberPerpendicularTest
  change (∫⁻ C, (H (fun i => perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) : ℝ≥0∞) ∂gaussianRows k d) = _
  rw [show (z.1:Vector d)-(z.2:Vector d) = -((z.2:Vector d)-(z.1:Vector d)) by abel]
  simp only [perpendicularRow_neg]

lemma fiberPairInverse_swap {d k : ℕ} (z : Sphere d×Sphere d) :
    fiberPairInverse k z.swap = fiberPairInverse k z := by
  simp only [fiberPairInverse,Prod.swap,norm_sub_rev]

lemma measurable_fiberDistanceWeight {d k : ℕ} : Measurable (fiberDistanceWeight (d:=d) k) := by
  unfold fiberDistanceWeight
  fun_prop

lemma fiberDistanceWeight_eq {d k : ℕ} {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    fiberDistanceWeight k z = fiberPairInverse k z := by
  have hv : 0 < ‖(z.2:Vector d)-(z.1:Vector d)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Subtype.coe_injective.ne hz.symm))
  rw [fiberDistanceWeight,fiberPairInverse,ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos hv,norm_sub_rev (z.1:Vector d) (z.2:Vector d)]

lemma fiberDistanceWeight_ae {d k : ℕ} (hd : 2≤d) :
    fiberDistanceWeight (d:=d) k =ᵐ[(uniformSphere d).prod (uniformSphere d)] fiberPairInverse k := by
  have hne := weightedSphere_pair_ne hd (fun _ => 1)
  have hne' : ∀ᵐ z ∂(uniformSphere d).prod (uniformSphere d), z.1 ≠ z.2 := by
    simpa only [withDensity_const,one_smul] using hne
  exact hne'.mono (fun z hz => fiberDistanceWeight_eq hz)

lemma perpendicularRowsKernel_lintegral {d k : ℕ}
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (z : Sphere d×Sphere d) :
    (∫⁻ C, (H C : ℝ≥0∞) ∂perpendicularRowsKernel d k z) = fiberPerpendicularTest H z := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  rw [perpendicularRowsKernel,dependentMapKernel_apply _ _ (measurable_perpendicularRowsMap d k),
    Kernel.const_apply]
  rw [lintegral_map hH (show Measurable (fun C : Rows k d => fun i =>
    perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) from
    (measurable_perpendicularRowsMap d k).comp (measurable_const.prodMk measurable_id))]
  change (∫⁻ C, (H (fun i => perpendicularRow ((z.1:Vector d)-(z.2:Vector d)) (C i)) : ℝ≥0∞)
    ∂gaussianRows k d) = _
  rw [show (z.1:Vector d)-(z.2:Vector d) = -((z.2:Vector d)-(z.1:Vector d)) by abel]
  simp only [perpendicularRow_neg,fiberPerpendicularTest]

lemma fiberRight_bilinear {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k) =
      ∫⁻ z : Sphere d×Sphere d, b z.1*a z.2 *
        (fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z))
        ∂(uniformSphere d).prod (uniformSphere d) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hF := measurable_fiberBilinearTest H hb ha
  have hinner (z : Sphere d×Sphere d) :
      (∫⁻ C, fiberBilinearTest H b a (C,z) ∂perpendicularRowsKernel d k z) =
      b z.1*a z.2*fiberPerpendicularTest H z := by
    simp only [fiberBilinearTest]
    rw [show (fun C : Rows k d => (H C : ℝ≥0∞)*b z.1*a z.2) =
        (fun C => (b z.1*a z.2)*(H C : ℝ≥0∞)) by funext C; ac_rfl,
      lintegral_const_mul _ hH,perpendicularRowsKernel_lintegral]
  rw [fiberTwoPointRight,lintegral_smul_measure,smul_eq_mul,
    lintegral_map hF measurable_swap]
  have hi := Measure.lintegral_compProd
    (μ:=((uniformSphere d).prod (uniformSphere d)).withDensity (fiberDistanceWeight k))
    (κ:=perpendicularRowsKernel d k)
    (f:=fun z : (Sphere d×Sphere d)×Rows k d => fiberBilinearTest H b a z.swap)
    (hF.comp measurable_swap)
  rw [hi]
  simp only [Prod.swap]
  simp_rw [hinner]
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_fiberDistanceWeight
    (show Measurable (fun z : Sphere d×Sphere d => b z.1*a z.2*fiberPerpendicularTest H z) from
      ((hb.comp measurable_fst).mul (ha.comp measurable_snd)).mul (measurable_fiberPerpendicularTest H)),
    ←lintegral_const_mul' _ _ (show fiberTwoPointConstant k ≠ ∞ from ENNReal.ofReal_ne_top)]
  apply lintegral_congr_ae
  filter_upwards [fiberDistanceWeight_ae (k:=k) hd] with z hz
  simp only [Pi.mul_apply]
  rw [hz]
  ac_rfl

lemma fiberRight_bilinear_comm {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k) =
      ∫⁻ z, fiberBilinearTest H a b z ∂fiberTwoPointRight d k := by
  rw [fiberRight_bilinear hd H b a hb ha,fiberRight_bilinear hd H a b ha hb]
  calc
    _ = ∫⁻ z : Sphere d×Sphere d, a z.swap.1*b z.swap.2*
        (fiberPairInverse k z.swap*(fiberTwoPointConstant k*fiberPerpendicularTest H z.swap))
        ∂(uniformSphere d).prod (uniformSphere d) := by
      apply lintegral_congr
      intro z
      rw [fiberPairInverse_swap, fiberPerpendicularTest_swap]
      dsimp only [Prod.swap]
      rw [mul_comm (b z.1) (a z.2)]
    _ = _ := lintegral_prod_swap (fun z : Sphere d×Sphere d => a z.1*b z.2*
      (fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)))

lemma fiberRight_quadratic {d k : ℕ} (hd : 2≤d)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointRight d k) =
      ∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)
        ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b) := by
  rw [fiberRight_bilinear hd H b b hb hb,prod_withDensity hb hb]
  symm
  exact lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (fun z : Sphere d×Sphere d => b z.1*b z.2) from
      (hb.comp measurable_fst).mul (hb.comp measurable_snd))
    (show Measurable (fun z : Sphere d×Sphere d =>
      fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z)) from
      measurable_fiberPairInverse.mul (measurable_const.mul (measurable_fiberPerpendicularTest H)))

lemma fiberRight_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1) :
    IsFiniteMeasure (fiberTwoPointRight d k) := by
  have : IsFiniteMeasure (((uniformSphere d).prod (uniformSphere d)).withDensity (fiberDistanceWeight k)) := by
    apply isFiniteMeasure_withDensity
    rw [lintegral_congr_ae (fiberDistanceWeight_ae (k:=k) (by omega))]
    exact spherical_pair_inverse_finite hk hkd
  unfold fiberTwoPointRight
  exact Measure.smul_finite _ (show fiberTwoPointConstant k ≠ ∞ from ENNReal.ofReal_ne_top)

lemma fiber_quadratic_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ s, b s≤M) :
    (∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H b b z ∂fiberTwoPointRight d k := by
  have := finite_bounded_withDensity (uniformSphere d) b M hM hbM
  rw [fiberLeft_quadratic H b hb (spherical_projection_ac hk hkd),fiberRight_quadratic (by omega) H b hb]
  exact spherical_energy_identity _ H (weightedSphere_projection_ac hk hkd b)
    (weightedSphere_pair_ne (by omega) b) (weightedSphere_pair_inverse_finite hk hkd b hb M hM hbM)



end CurrentProjection

end

end OAI
