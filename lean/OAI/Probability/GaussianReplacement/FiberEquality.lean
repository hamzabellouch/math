import OAI.Probability.GaussianReplacement.FiberConditional

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma fiberLeft_finite {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1) :
    IsFiniteMeasure (fiberTwoPointLeft d k) := by
  have := fiberRight_finite hk hkd
  have h := fiber_quadratic_eq hk hkd 1 (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => le_rfl)
  simp only [fiberBilinearTest,BoundedContinuousFunction.coe_one,Pi.one_apply,
    ENNReal.coe_one,mul_one,lintegral_one] at h
  constructor
  rw [h]
  exact measure_lt_top _ _

lemma fiberBilinear_integral_ne_top {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    [IsFiniteMeasure μ] (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) {M N : ℝ≥0∞} (hM : M≠∞) (hN : N≠∞)
    (hbM : ∀ s, b s≤M) (haN : ∀ s, a s≤N) :
    (∫⁻ z, fiberBilinearTest H b a z ∂μ) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hM) hN)
      (measure_ne_top μ Set.univ))
  calc
    _ ≤ ∫⁻ z, (nndist H 0 : ℝ≥0∞)*M*N ∂μ := by
      apply lintegral_mono
      intro z
      exact mul_le_mul (mul_le_mul (ENNReal.coe_le_coe.mpr (show H z.1≤nndist H 0 by
        simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) z.1)))
        (hbM z.2.1) bot_le bot_le) (haN z.2.2) bot_le bot_le
    _ = _ := lintegral_const _

lemma fiberBilinear_add_left {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (b a c : Sphere d→ℝ≥0∞)
    (hb : Measurable b) (hc : Measurable c) :
    (∫⁻ z, fiberBilinearTest H (b+a) c z ∂μ) =
      (∫⁻ z, fiberBilinearTest H b c z ∂μ)+(∫⁻ z, fiberBilinearTest H a c z ∂μ) := by
  rw [show fiberBilinearTest H (b+a) c = (fun z => fiberBilinearTest H b c z+fiberBilinearTest H a c z) by
    funext z; simp only [fiberBilinearTest,Pi.add_apply,mul_add,add_mul]]
  exact lintegral_add_left (measurable_fiberBilinearTest H hb hc) _

lemma fiberBilinear_add_right {d k : ℕ} (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (b a c : Sphere d→ℝ≥0∞)
    (hb : Measurable b) (ha : Measurable a) :
    (∫⁻ z, fiberBilinearTest H b (a+c) z ∂μ) =
      (∫⁻ z, fiberBilinearTest H b a z ∂μ)+(∫⁻ z, fiberBilinearTest H b c z ∂μ) := by
  rw [show fiberBilinearTest H b (a+c) = (fun z => fiberBilinearTest H b a z+fiberBilinearTest H b c z) by
    funext z; simp only [fiberBilinearTest,Pi.add_apply,mul_add]]
  exact lintegral_add_left (measurable_fiberBilinearTest H hb ha) _

lemma fiber_bilinear_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (b a : Sphere d→ℝ≥0∞) (hb : Measurable b) (ha : Measurable a)
    {M N : ℝ≥0∞} (hM : M≠∞) (hN : N≠∞) (hbM : ∀ s, b s≤M) (haN : ∀ s, a s≤N) :
    (∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointLeft d k) =
      ∫⁻ z, fiberBilinearTest H b a z ∂fiberTwoPointRight d k := by
  have := fiberRight_finite hk hkd
  have hbb := fiber_quadratic_eq hk hkd H b hb M hM hbM
  have haa := fiber_quadratic_eq hk hkd H a ha N hN haN
  have hsum := fiber_quadratic_eq hk hkd H (b+a) (hb.add ha) (M+N)
    (ENNReal.add_ne_top.mpr ⟨hM,hN⟩) (fun s => add_le_add (hbM s) (haN s))
  rw [fiberBilinear_add_left _ H b a (b+a) hb (hb.add ha),
    fiberBilinear_add_right _ H b b a hb hb,
    fiberBilinear_add_right _ H a b a ha hb,
    fiberBilinear_add_left _ H b a (b+a) hb (hb.add ha),
    fiberBilinear_add_right _ H b b a hb hb,
    fiberBilinear_add_right _ H a b a ha hb,
    fiberLeft_bilinear_comm H a b ha hb,fiberRight_bilinear_comm (by omega) H a b ha hb,
    hbb,haa] at hsum
  have hbbfin := fiberBilinear_integral_ne_top (fiberTwoPointRight d k) H b b hM hM hbM hbM
  have haafin := fiberBilinear_integral_ne_top (fiberTwoPointRight d k) H a a hN hN haN haN
  simp only [add_assoc] at hsum
  have h := (ENNReal.add_right_inj hbbfin).mp hsum
  rw [←add_assoc,←add_assoc] at h
  have h' := (ENNReal.add_left_inj haafin).mp h
  rw [←mul_two,←mul_two] at h'
  exact (ENNReal.mul_left_inj (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠∞)).mp h'




lemma fiber_indicator_lintegral {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {B D : Set (Sphere d)} (hB : MeasurableSet B) (hD : MeasurableSet D) :
    (∫⁻ C, (H C : ℝ≥0∞) ∂(μ.restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst) =
      ∫⁻ z, fiberBilinearTest H (B.indicator (fun _ => 1)) (D.indicator (fun _ => 1)) z ∂μ := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  rw [lintegral_map hH measurable_fst,←lintegral_indicator (MeasurableSet.univ.prod (hB.prod hD))]
  apply lintegral_congr
  intro z
  by_cases hb : z.2.1∈B <;> by_cases hd : z.2.2∈D <;>
    simp [fiberBilinearTest,Set.indicator,hb,hd]

lemma fst_restrict_sphere_rectangle {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    {A : Set (Rows k d)} {B D : Set (Sphere d)} (hA : MeasurableSet A) :
    ((μ.restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst) A = μ (A ×ˢ (B ×ˢ D)) := by
  rw [Measure.map_apply measurable_fst hA,Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext z
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]

lemma snd_restrict_sphere_rectangle {d k : ℕ}
    (μ : Measure (Rows k d×(Sphere d×Sphere d)))
    {A : Set (Rows k d)} {E : Set (Sphere d×Sphere d)} (hE : MeasurableSet E) :
    ((μ.restrict (A ×ˢ Set.univ)).map Prod.snd) E = μ (A ×ˢ E) := by
  rw [Measure.map_apply measurable_snd hE,Measure.restrict_apply (measurable_snd hE)]
  congr 1
  ext z
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  exact and_comm

lemma fiber_three_rectangle_eq {d k : ℕ} [Nonempty (Sphere d)] (hk : 1≤k) (hkd : k<d-1)
    {A : Set (Rows k d)} {B D : Set (Sphere d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hD : MeasurableSet D) :
    fiberTwoPointLeft d k (A ×ˢ (B ×ˢ D)) = fiberTwoPointRight d k (A ×ˢ (B ×ˢ D)) := by
  have := fiberLeft_finite hk hkd
  have heq : ((fiberTwoPointLeft d k).restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst =
      ((fiberTwoPointRight d k).restrict (Set.univ ×ˢ (B ×ˢ D))).map Prod.fst := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro H
    rw [fiber_indicator_lintegral _ H hB hD,fiber_indicator_lintegral _ H hB hD]
    apply fiber_bilinear_eq hk hkd H _ _ (measurable_const.indicator hB) (measurable_const.indicator hD)
      (M:=1) (N:=1) (by norm_num) (by norm_num)
    · intro s
      by_cases hs : s∈B <;> simp [hs]
    · intro s
      by_cases hs : s∈D <;> simp [hs]
  have h := congrArg (fun μ : Measure (Rows k d) => μ A) heq
  simpa only [fst_restrict_sphere_rectangle _ hA] using h


theorem fiberTwoPointMain : FiberTwoPointMain := by
  intro d k hk hkd
  let : IsProbabilityMeasure (uniformSphere d) :=
    uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  have := fiberLeft_finite hk hkd
  have := fiberRight_finite hk hkd
  refine ⟨inferInstance,inferInstance,?_⟩
  apply Measure.ext_prod
  intro A E hA hE
  have heq : ((fiberTwoPointLeft d k).restrict (A ×ˢ Set.univ)).map Prod.snd =
      ((fiberTwoPointRight d k).restrict (A ×ˢ Set.univ)).map Prod.snd := by
    apply Measure.ext_prod
    intro B D hB hD
    rw [snd_restrict_sphere_rectangle _ (hB.prod hD),snd_restrict_sphere_rectangle _ (hB.prod hD)]
    exact fiber_three_rectangle_eq hk hkd hA hB hD
  have h := congrArg (fun μ : Measure (Sphere d×Sphere d) => μ E) heq
  simpa only [snd_restrict_sphere_rectangle _ hE] using h





def fiberTwoPointFromVersions (d k : ℕ)
    (p : Rows k d×(Fin k→ℝ) → ℝ≥0∞)
    (κ : Kernel (Rows k d×(Fin k→ℝ)) (Sphere d)) :
    Measure (Rows k d×(Sphere d×Sphere d)) :=
  ((((gaussianRows k d).prod (uniformSphere d)).withDensity
    (fun z => p (z.1,label z.1 (z.2:Vector d)))) ⊗ₘ
    (κ.comap (fun z => (z.1,label z.1 (z.2:Vector d)))
      (measurable_fst.prodMk measurable_own_label))).map
    (fun z => (z.1.1,(z.1.2,z.2)))




lemma fiberTwoPoint_version_invariance {d k : ℕ} [Nonempty (Sphere d)]
    (hk : 1 ≤ k) (hkd : k < d-1)
    (p : Rows k d×(Fin k→ℝ) → ℝ≥0∞) (hpmeas : Measurable p)
    (hp : ((gaussianRows k d).prod (volume : Measure (Fin k→ℝ))).withDensity p =
      (fiberObservationLaw d k).fst)
    (κ : Kernel (Rows k d×(Fin k→ℝ)) (Sphere d)) [IsMarkovKernel κ]
    (hκ : (fiberObservationLaw d k).fst ⊗ₘ κ = fiberObservationLaw d k) :
    fiberTwoPointFromVersions d k p κ = fiberTwoPointLeft d k := by
  let μ := (gaussianRows k d).prod (uniformSphere d)
  let obs : Rows k d×Sphere d → Rows k d×(Fin k→ℝ) :=
    fun z => (z.1,label z.1 (z.2:Vector d))
  have hobs : Measurable obs := measurable_fst.prodMk measurable_own_label
  have hdens := projectionJoint_withDensity (uniformSphere d) (gaussianRows k d)
    (spherical_projection_ac hk hkd)
  have hp' : p =ᵐ[(gaussianRows k d).prod (volume : Measure (Fin k→ℝ))]
      (fun o => exactDensity (uniformSphere d) o.1 o.2) := by
    apply (withDensity_eq_iff_of_sigmaFinite hpmeas.aemeasurable
      (measurable_exactDensity (uniformSphere d)).aemeasurable).mp
    rw [hp,hdens,fiberObservationLaw_fst]
  have hpObs : p =ᵐ[projectionJoint (uniformSphere d) (gaussianRows k d)]
      (fun o => exactDensity (uniformSphere d) o.1 o.2) := by
    rw [←hdens]
    exact (withDensity_absolutelyContinuous _ _).ae_le hp'
  have hpo : (fun z => p (obs z)) =ᵐ[μ]
      (fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))) :=
    ae_of_ae_map hobs.aemeasurable hpObs
  have hκeq : κ =ᵐ[(fiberObservationLaw d k).fst] sphericalFiberKernel d k := by
    apply Kernel.ae_eq_of_compProd_eq
    rw [hκ]
    exact ((fiberObservationLaw d k).disintegrate (fiberObservationLaw d k).condKernel).symm
  rw [fiberObservationLaw_fst] at hκeq
  have hκobs : (fun z => κ (obs z)) =ᵐ[μ]
      (fun z => sphericalFiberKernel d k (obs z)) := ae_of_ae_map hobs.aemeasurable hκeq
  have hκweight : κ.comap obs hobs =ᵐ[μ.withDensity
      (fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)))]
      (sphericalFiberKernel d k).comap obs hobs :=
    (withDensity_absolutelyContinuous _ _).ae_le hκobs
  unfold fiberTwoPointFromVersions fiberTwoPointLeft
  rw [withDensity_congr_ae hpo]
  rw [Measure.compProd_congr hκweight]



lemma fiberTwoPoint_allVersions {d k : ℕ} [Nonempty (Sphere d)]
    (hk : 1 ≤ k) (hkd : k < d-1)
    (p : Rows k d×(Fin k→ℝ) → ℝ≥0∞) (hpmeas : Measurable p)
    (hp : ((gaussianRows k d).prod (volume : Measure (Fin k→ℝ))).withDensity p =
      (fiberObservationLaw d k).fst)
    (κ : Kernel (Rows k d×(Fin k→ℝ)) (Sphere d)) [IsMarkovKernel κ]
    (hκ : (fiberObservationLaw d k).fst ⊗ₘ κ = fiberObservationLaw d k) :
    IsFiniteMeasure (fiberTwoPointFromVersions d k p κ) ∧
      IsFiniteMeasure (fiberTwoPointRight d k) ∧
      fiberTwoPointFromVersions d k p κ = fiberTwoPointRight d k := by
  rw [fiberTwoPoint_version_invariance hk hkd p hpmeas hp κ hκ]
  exact fiberTwoPointMain d k hk hkd



end CurrentProjection

end

end OAI
