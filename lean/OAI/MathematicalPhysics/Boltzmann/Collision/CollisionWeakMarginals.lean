import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityPolynomialBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.SpatialCutoffIntegrability

namespace OAI

section

/-! # Integrable velocity majorants for hard-sphere pair densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

def pairKernel (q : ℝ) (p : Velocity × Velocity) : ℝ :=
  (1+‖p.1‖+‖p.2‖)*H q p.1*H q p.2

theorem pairKernel_nonneg (q : ℝ) (p : Velocity × Velocity) : 0 ≤ pairKernel q p :=
  mul_nonneg (mul_nonneg (by positivity) (H_nonneg q p.1)) (H_nonneg q p.2)

theorem pairKernel_measurable (q : ℝ) : Measurable (pairKernel q) := by
  unfold pairKernel H singularity
  fun_prop

theorem pairKernel_integrable {q : ℝ} (hq : q < 2) : Integrable (pairKernel q) := by
  have hm : Measurable (H q) := by unfold H singularity; fun_prop
  have hh : VelocityMoment.moment (H q) = ENNReal.ofReal (VelocityMoment.hotConstant q) := by
    simpa only [one_mul] using VelocityMoment.hot_moment hq zero_le_one
  have hb := VelocityMoment.pairMoment_le_square hm (H_nonneg q)
    (VelocityMoment.hotConstant_nonneg q) hh.le
  refine ⟨(pairKernel_measurable q).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (pairKernel_nonneg q))).mpr
    (hb.trans_lt ENNReal.ofReal_lt_top)

variable {X : Type*} [MeasurableSpace X]

def pairDensity (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (1+‖z.2.1‖+‖z.2.2‖)*f (z.1,z.2.1)*f (z.1,z.2.2)

theorem pairDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairDensity f) := by unfold pairDensity; fun_prop

omit [MeasurableSpace X] in
theorem pairDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : 0 ≤ pairDensity f z :=
  mul_nonneg (mul_nonneg (by positivity) (hf _)) (hf _)

omit [MeasurableSpace X] in
theorem pairDensity_bound {q A : ℝ} (hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hf : ∀ z, 0 ≤ f z) (z : X × (Velocity × Velocity))
    (h₁ : f (z.1,z.2.1) ≤ A*H q z.2.1) (h₂ : f (z.1,z.2.2) ≤ A*H q z.2.2) :
    pairDensity f z ≤ A^2*pairKernel q z.2 := by
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left h₁
    (by positivity : 0 ≤ 1+‖z.2.1‖+‖z.2.2‖)) h₂ (hf _)
      (mul_nonneg (by positivity) (mul_nonneg hA (H_nonneg q _)))
  unfold pairDensity pairKernel
  nlinarith [hh]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Fixed outer-annulus majorants give uniform integrability of collision pairs -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem pair_ae_bound {f : X × Velocity → ℝ} (hfm : Measurable f)
    {S : Set X} (hS : MeasurableSet S) (A q : ℝ)
    (h : ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f (x,v) ≤ A*H q v) :
    ∀ᵐ z ∂μ.prod (volume : Measure (Velocity × Velocity)), z.1 ∉ S →
      f (z.1,z.2.1) ≤ A*H q z.2.1 ∧ f (z.1,z.2.2) ≤ A*H q z.2.2 := by
  have h₁ : Measurable (fun z : X × (Velocity × Velocity) => f (z.1,z.2.1)) := by fun_prop
  have h₂ : Measurable (fun z : X × (Velocity × Velocity) => f (z.1,z.2.2)) := by fun_prop
  have hH₁ : Measurable (fun z : X × (Velocity × Velocity) => A*H q z.2.1) := by
    unfold H singularity; fun_prop
  have hH₂ : Measurable (fun z : X × (Velocity × Velocity) => A*H q z.2.2) := by
    unfold H singularity; fun_prop
  have hp : MeasurableSet {z : X × (Velocity × Velocity) | z.1 ∉ S →
      f (z.1,z.2.1) ≤ A*H q z.2.1 ∧ f (z.1,z.2.2) ≤ A*H q z.2.2} := by
    convert (hS.preimage measurable_fst).union ((measurableSet_le h₁ hH₁).inter
      (measurableSet_le h₂ hH₂)) using 1
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_preimage,mem_inter_iff,not_not,imp_iff_not_or]
  apply (Measure.ae_prod_iff_ae_ae hp).mpr
  filter_upwards [h] with x hx
  change ∀ᵐ p : Velocity × Velocity ∂(volume : Measure Velocity).prod volume,
    x ∉ S → f (x,p.1) ≤ A*H q p.1 ∧ f (x,p.2) ≤ A*H q p.2
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Velocity))
    (ν := (volume : Measure Velocity))).ae hx
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Velocity))
    (ν := (volume : Measure Velocity))).ae hx
  filter_upwards [hfst,hsnd] with p hp₁ hp₂
  exact fun hxs => ⟨hp₁ hxs,hp₂ hxs⟩

theorem outer_pairs_uniformIntegrable [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {S : Set X} (hS : MeasurableSet S)
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UniformIntegrable (fun n => outerCutoff S (pairDensity (f n))) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  let g : X × (Velocity × Velocity) → ℝ := fun z => A^2*pairKernel q z.2
  have hg : Integrable g (μ.prod (volume : Measure (Velocity × Velocity))) := by
    have hi := (integrable_const (1:ℝ) : Integrable (fun _ : X => (1:ℝ)) μ).mul_prod
      ((pairKernel_integrable hq).const_mul (A^2))
    simpa only [one_mul] using hi
  have hgn (z) : 0 ≤ g z := mul_nonneg (sq_nonneg A) (pairKernel_nonneg q z.2)
  have hm (n) : AEStronglyMeasurable (outerCutoff S (pairDensity (f n)))
      (μ.prod (volume : Measure (Velocity × Velocity))) :=
    ((pairDensity_measurable (hfm n)).indicator (hS.compl.preimage measurable_fst)).aestronglyMeasurable
  have hb (n) : ∀ᵐ z ∂μ.prod (volume : Measure (Velocity × Velocity)),
      ‖outerCutoff S (pairDensity (f n)) z‖ₑ ≤ ‖g z‖ₑ := by
    filter_upwards [pair_ae_bound (hfm n) hS A q (hdom n)] with z hz
    apply enorm_le_iff_norm_le.mpr
    have hnonneg : 0 ≤ outerCutoff S (pairDensity (f n)) z :=
      indicator_nonneg (fun z _ => pairDensity_nonneg (hf n) z) z
    rw [Real.norm_of_nonneg hnonneg,Real.norm_of_nonneg (hgn z)]
    by_cases hx : z.1 ∈ S
    · rw [outerCutoff,indicator_of_notMem (show z ∉ Prod.fst ⁻¹' Sᶜ from fun hz => hz hx)]
      exact hgn z
    · rw [outerCutoff,indicator_of_mem (show z ∈ Prod.fst ⁻¹' Sᶜ from hx)]
      exact pairDensity_bound hA (hf n) z (hz hx).1 (hz hx).2
  obtain ⟨hui,C,hC⟩ := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (memLp_one_iff_integrable.mpr hg)
  exact ⟨hui.ae_mono hm hb,C,fun n => (eLpNorm_mono_enorm_ae (hm n) (hb n)).trans (hC n)⟩


theorem collision_pairs_uniformIntegrable [IsFiniteMeasure μ] {q : ℝ} (hq : q < 2)
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {M : X → ℝ} (hM : ∀ x, 0 ≤ M x)
    (hmoment : ∀ n, ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => f n (x,v)) ≤ ENNReal.ofReal (M x))
    {S : ℕ → Set X} (hS : ∀ j, MeasurableSet (S j))
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    (houter : ∀ j n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S j → f n (x,v) ≤ A j*H q v)
    (hsmall : Filter.Tendsto (fun j => ∫⁻ x in S j, ENNReal.ofReal (3*(M x)^2) ∂μ)
      Filter.atTop (nhds 0)) :
    UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  apply Compactness.uniformIntegrable_of_spatial_cutoffs
    (fun n => pairDensity_measurable (hfm n)) (fun n => pairDensity_nonneg (hf n)) hS
  · intro n
    filter_upwards [hmoment n] with x hx
    exact VelocityMoment.pairMoment_le_square
      ((hfm n).comp (measurable_const.prodMk measurable_id)) (fun v => hf n (x,v)) (hM x) hx
  · intro j
    exact outer_pairs_uniformIntegrable hq (hA j) (hS j) hfm hf (houter j)
  · exact hsmall

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def scatterTriple (z : (X × (Velocity × Velocity)) × Sphere) :
    (X × (Velocity × Velocity)) × Sphere :=
  ((z.1.1,scatterPair z.2 z.1.2),z.2)

theorem scatterTriple_measurable : Measurable (scatterTriple (X := X)) := by
  unfold scatterTriple scatterPair scatterLeft scatterRight normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem scatterTriple_involutive : Function.Involutive (scatterTriple (X := X)) := by
  intro z
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have hi := scatterPair_involutive (z.2 : Velocity) hw z.1.2
  change ((z.1.1,scatterPair z.2 (scatterPair z.2 z.1.2)),z.2) = z
  rw [hi]

def scatterTripleEquiv : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × (Velocity × Velocity)) × Sphere) where
  toFun := scatterTriple
  invFun := scatterTriple
  left_inv := scatterTriple_involutive
  right_inv := scatterTriple_involutive
  measurable_toFun := scatterTriple_measurable
  measurable_invFun := scatterTriple_measurable

theorem scatterTriple_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (scatterTriple (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ν := μ.prod (volume : Measure (Velocity × Velocity))
  have hf (ω : Sphere) : MeasurePreserving
      (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) ν ν := by
    have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    have hh := (MeasurePreserving.id μ).prod (scatterPair_measurePreserving (ω : Velocity) hω)
    have he : (Prod.map id (scatterPair (ω : Velocity))) =
        (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) := by
      funext p
      rfl
    rw [he] at hh
    simpa only [ν,Measure.volume_eq_prod] using hh
  have hm : Measurable (fun z : Sphere × (X × (Velocity × Velocity)) =>
      (z.2.1,scatterPair z.1 z.2.2)) := by
    unfold scatterPair scatterLeft scatterRight normalComponent
    fun_prop
  have hh := (MeasurePreserving.id sphereArea).skew_product (μc := ν) (μd := ν)
    (g := fun (ω : Sphere) (p : X × (Velocity × Velocity)) => (p.1,scatterPair ω p.2)) hm
    (ae_of_all _ (fun ω => (hf ω).map_eq))
  have h₁ : MeasurePreserving Prod.swap (ν.prod sphereArea) (sphereArea.prod ν) :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving Prod.swap (sphereArea.prod ν) (ν.prod sphereArea) :=
    Measure.measurePreserving_swap
  exact h₂.comp (hh.comp h₁)

def preRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)

def postRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  preRate f (scatterTriple z)


omit [MeasurableSpace X] in
theorem postRate_formula (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change collisionKernel (scatterLeft z.1.2.1 z.1.2.2 z.2) (scatterRight z.1.2.1 z.1.2.2 z.2) z.2*
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [collisionKernel_scatter _ _ _ hw]

theorem preRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) : Measurable (preRate f) := by
  unfold preRate collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem preRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ preRate f z :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

omit [MeasurableSpace X] in
theorem preRate_le_pairDensity {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f z ≤ pairDensity f z.1 := by
  have hk : collisionKernel z.1.2.1 z.1.2.2 z.2 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖ :=
    (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hf _)) (hf _)

theorem preRate_integrable {μ : Measure X} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (preRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (hpair.comp_fst sphereArea).mono' (preRate_measurable hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (preRate_nonneg hf z)]
  exact preRate_le_pairDensity hf z

theorem postRate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (postRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (preRate_integrable hfm hf hpair)

theorem integral_postRate (μ : Measure X) [SFinite μ] (f : X × Velocity → ℝ) :
    (∫ z, postRate f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      ∫ z, preRate f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
  (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding (preRate f)


theorem rates_integrable_of_uniformIntegrable {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hUI : UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) (n : ℕ) :
    Integrable (preRate (f n)) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (postRate (f n)) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  obtain ⟨C,hC⟩ := hUI.2
  have hm : MemLp (pairDensity (f n)) 1 (μ.prod (volume : Measure (Velocity × Velocity))) :=
    (hC n).trans_lt (by finiteness)
  have hi := memLp_one_iff_integrable.mp hm
  exact ⟨preRate_integrable (hfm n) (hf n) hi,postRate_integrable (hfm n) (hf n) hi⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

def collisionGrouping : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × Velocity) × (Velocity × Sphere)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.prodAssoc.symm) (MeasurableEquiv.refl Sphere)).trans
    MeasurableEquiv.prodAssoc

theorem collisionGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := by
  have ha := (measurePreserving_prodAssoc μ (volume : Measure Velocity) (volume : Measure Velocity)).symm.prod
    (MeasurePreserving.id sphereArea)
  have hb := measurePreserving_prodAssoc (μ.prod (volume : Measure Velocity))
    (volume : Measure Velocity) sphereArea
  have he : (⇑(collisionGrouping (X := X))) =
      MeasurableEquiv.prodAssoc ∘ Prod.map (MeasurableEquiv.prodAssoc.symm)
        (id : Sphere → Sphere) := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using hb.comp ha

def gainDensity (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, postRate f (collisionGrouping.symm (p,q)) ∂((volume : Measure Velocity).prod sphereArea)

def lossDensity (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, preRate f (collisionGrouping.symm (p,q)) ∂((volume : Measure Velocity).prod sphereArea)

theorem gainDensity_formula (f : X × Velocity → ℝ) (p : X × Velocity) :
    gainDensity f p = ∫ q : Velocity × Sphere,
      collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*f (p.1,scatterRight p.2 q.1 q.2)
        ∂((volume : Measure Velocity).prod sphereArea) := by
  unfold gainDensity
  congr 1
  funext q
  exact postRate_formula f _

theorem lossDensity_formula (f : X × Velocity → ℝ) (p : X × Velocity) :
    lossDensity f p = ∫ q : Velocity × Sphere,
      collisionKernel p.2 q.1 q.2*f (p.1,p.2)*f (p.1,q.1)
        ∂((volume : Measure Velocity).prod sphereArea) := rfl

theorem gainDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z) (p : X × Velocity) :
    0 ≤ gainDensity f p := integral_nonneg (fun _ => preRate_nonneg hf _)

theorem lossDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z) (p : X × Velocity) :
    0 ≤ lossDensity f p := integral_nonneg (fun _ => preRate_nonneg hf _)

theorem gainLoss_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (gainDensity f) (μ.prod (volume : Measure Velocity)) ∧
      Integrable (lossDensity f) (μ.prod (volume : Measure Velocity)) := by
  have hpost : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => postRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (postRate_integrable hfm hf hpair)
  have hpre : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  exact ⟨hpost.integral_prod_left,hpre.integral_prod_left⟩

theorem gainLoss_integral_eq {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    (∫ p, gainDensity f p ∂μ.prod (volume : Measure Velocity)) =
      ∫ p, lossDensity f p ∂μ.prod (volume : Measure Velocity) := by
  have hpost : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => postRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (postRate_integrable hfm hf hpair)
  have hpre : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  calc
    _ = ∫ z, postRate f (collisionGrouping.symm z)
        ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
      (integral_prod _ hpost).symm
    _ = ∫ z, postRate f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
      (collisionGrouping_measurePreserving μ).symm.integral_comp collisionGrouping.symm.measurableEmbedding _
    _ = ∫ z, preRate f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
      integral_postRate μ f
    _ = ∫ z, preRate f (collisionGrouping.symm z)
        ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
      ((collisionGrouping_measurePreserving μ).symm.integral_comp collisionGrouping.symm.measurableEmbedding _).symm
    _ = _ := integral_prod _ hpre

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Slice mass bounds for the physical gain and loss -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem gainDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gainDensity f) :=
  ((preRate_measurable hf).comp (scatterTriple_measurable.comp
    collisionGrouping.symm.measurable)).stronglyMeasurable.integral_prod_right'.measurable

theorem lossDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (lossDensity f) :=
  ((preRate_measurable hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

private theorem slice_lintegral [MeasurableSingletonClass X]
    (x : X) {g : ((X × (Velocity × Velocity)) × Sphere) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z ∂((Measure.dirac x).prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      ∫⁻ p : Velocity × Velocity, ∫⁻ ω : Sphere, g ((x,p),ω) ∂sphereArea := by
  rw [lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hg.lintegral_prod_right'.aemeasurable]
  simp only [lintegral_dirac]

theorem slice_postRate_mass [MeasurableSingletonClass X]
    {f : X × Velocity → ℝ} (hf : Measurable f) (x : X) :
    (∫⁻ p : Velocity × Velocity, ∫⁻ ω : Sphere,
      ENNReal.ofReal (postRate f ((x,p),ω)) ∂sphereArea) =
    ∫⁻ p : Velocity × Velocity, ∫⁻ ω : Sphere,
      ENNReal.ofReal (preRate f ((x,p),ω)) ∂sphereArea := by
  have hm := (preRate_measurable hf).ennreal_ofReal
  have he := (scatterTriple_measurePreserving (Measure.dirac x)).lintegral_comp hm
  change (∫⁻ z, ENNReal.ofReal (postRate f z) ∂
    ((Measure.dirac x).prod (volume : Measure (Velocity × Velocity))).prod sphereArea) = _ at he
  have hpostm : Measurable (fun z => ENNReal.ofReal (postRate f z)) :=
    hm.comp scatterTriple_measurable
  rw [slice_lintegral x hpostm,slice_lintegral x hm] at he
  exact he

private theorem marginal_mass_le
    {g : ((X × Velocity) × (Velocity × Sphere)) → ℝ}
    (hg : Measurable g) (hn : ∀ z, 0 ≤ g z) (x : X) :
    (∫⁻ v : Velocity, ENNReal.ofReal (∫ q, g ((x,v),q)
      ∂((volume : Measure Velocity).prod sphereArea))) ≤
    ∫⁻ p : Velocity × Velocity, ∫⁻ ω : Sphere, ENNReal.ofReal (g ((x,p.1),(p.2,ω))) ∂sphereArea := by
  calc
    _ ≤ ∫⁻ v : Velocity, ∫⁻ q, ENNReal.ofReal (g ((x,v),q))
        ∂((volume : Measure Velocity).prod sphereArea) := by
      apply lintegral_mono
      intro v
      have hh := enorm_integral_le_lintegral_enorm
        (μ := (volume : Measure Velocity).prod sphereArea) (fun q => g ((x,v),q))
      simpa only [Real.enorm_eq_ofReal (integral_nonneg (fun q => hn _)),
        Real.enorm_eq_ofReal (hn _)] using hh
    _ = ∫⁻ v : Velocity, ∫⁻ w : Velocity, ∫⁻ ω : Sphere,
        ENNReal.ofReal (g ((x,v),(w,ω))) ∂sphereArea := by
      apply lintegral_congr
      intro v
      exact lintegral_prod _ (((hg.ennreal_ofReal).comp
        (measurable_const.prodMk measurable_id)).aemeasurable)
    _ = _ := by
      rw [Measure.volume_eq_prod]
      symm
      apply lintegral_prod
      exact (((hg.ennreal_ofReal).comp
        ((measurable_const.prodMk measurable_fst.fst).prodMk
          (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right').aemeasurable

theorem gainLoss_slice_mass_le [MeasurableSingletonClass X]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (x : X) :
    (∫⁻ v : Velocity, ENNReal.ofReal (gainDensity f (x,v))) ≤
        ENNReal.ofReal (4*Real.pi)*VelocityMoment.pairMoment (fun v => f (x,v)) ∧
    (∫⁻ v : Velocity, ENNReal.ofReal (lossDensity f (x,v))) ≤
        ENNReal.ofReal (4*Real.pi)*VelocityMoment.pairMoment (fun v => f (x,v)) := by
  have hp : (∫⁻ p : Velocity × Velocity, ∫⁻ ω : Sphere,
      ENNReal.ofReal (preRate f ((x,p),ω)) ∂sphereArea) ≤
      ENNReal.ofReal (4*Real.pi)*VelocityMoment.pairMoment (fun v => f (x,v)) := by
    calc
      _ ≤ ∫⁻ p : Velocity × Velocity, ∫⁻ _ω : Sphere,
          ENNReal.ofReal (pairDensity f (x,p)) ∂sphereArea :=
        lintegral_mono (fun p => lintegral_mono (fun ω =>
          ENNReal.ofReal_le_ofReal (preRate_le_pairDensity hf ((x,p),ω))))
      _ = _ := by
        simp only [lintegral_const,sphereArea_univ]
        rw [lintegral_mul_const]
        · exact mul_comm _ _
        · exact ((pairDensity_measurable hfm).comp
            (measurable_const.prodMk measurable_id)).ennreal_ofReal
  constructor
  · exact (marginal_mass_le ((preRate_measurable hfm).comp
      (scatterTriple_measurable.comp collisionGrouping.symm.measurable))
      (fun z => preRate_nonneg hf _) x).trans ((slice_postRate_mass hfm x).trans_le hp)
  · exact (marginal_mass_le ((preRate_measurable hfm).comp collisionGrouping.symm.measurable)
      (fun z => preRate_nonneg hf _) x).trans hp

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The physical collision marginals inherit outer-annulus domination -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem integral_order_outside [SFinite μ]
    {g h : (X × Velocity) × (Velocity × Sphere) → ℝ}
    (hg : ∀ z, 0 ≤ g z)
    (hh : Integrable h ((μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea))) {S : Set X}
    (hle : ∀ᵐ z ∂(μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea), z.1.1 ∉ S → g z ≤ h z) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity), p.1 ∉ S →
      (∫ q, g (p,q) ∂((volume : Measure Velocity).prod sphereArea)) ≤
      ∫ q, h (p,q) ∂((volume : Measure Velocity).prod sphereArea) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hle,hh.prod_right_ae] with p hp hi hs
  apply integral_mono_of_nonneg (ae_of_all _ (fun q => hg _)) hi
  exact hp.mono (fun q hq => hq hs)

theorem gainLoss_order_outside [SFinite μ]
    {f g : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (hgm : Measurable g) (hg : ∀ z, 0 ≤ g z)
    (hpair : Integrable (pairDensity g) (μ.prod (volume : Measure (Velocity × Velocity))))
    {S : Set X}
    (hle : ∀ᵐ z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea,
      z.1.1 ∉ S → preRate f z ≤ preRate g z) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity), p.1 ∉ S →
      gainDensity f p ≤ gainDensity g p ∧ lossDensity f p ≤ lossDensity g p := by
  have hpost := (scatterTriple_measurePreserving μ).quasiMeasurePreserving.ae hle
  have hpost' : ∀ᵐ z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea,
      z.1.1 ∉ S → postRate f z ≤ postRate g z := hpost
  have hp := (collisionGrouping_measurePreserving μ).symm
  have hgp := hp.integrable_comp_of_integrable (postRate_integrable hgm hg hpair)
  have hgl := hp.integrable_comp_of_integrable (preRate_integrable hgm hg hpair)
  have hpostGrouped := hp.quasiMeasurePreserving.ae hpost'
  have hpreGrouped := hp.quasiMeasurePreserving.ae hle
  have h₁ := integral_order_outside (fun z => preRate_nonneg hf _) hgp hpostGrouped
  have h₂ := integral_order_outside (fun z => preRate_nonneg hf _) hgl hpreGrouped
  filter_upwards [h₁,h₂] with p hp₁ hp₂ hs
  exact ⟨hp₁ hs,hp₂ hs⟩

theorem hot_pairDensity_integrable [IsFiniteMeasure μ] {q : ℝ} (hq : q < 2) (A : ℝ) :
    Integrable (pairDensity (fun p : X × Velocity => A*H q p.2))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hi := ((pairKernel_integrable hq).const_mul (A^2)).comp_snd μ
  convert hi using 1
  funext z
  unfold pairDensity pairKernel
  ring

theorem gainLoss_outer_bound [IsFiniteMeasure μ] {q A : ℝ} (hq : q < 2) (hA : 0 ≤ A)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f (x,v) ≤ A*H q v) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity), p.1 ∉ S →
      gainDensity f p ≤ gainDensity (fun z => A*H q z.2) p ∧
      lossDensity f p ≤ lossDensity (fun z => A*H q z.2) p := by
  have hpair := (Measure.quasiMeasurePreserving_fst
    (μ := μ.prod (volume : Measure (Velocity × Velocity))) (ν := sphereArea)).ae
    (pair_ae_bound hfm hS A q hdom)
  apply gainLoss_order_outside hf (by unfold H singularity; fun_prop)
    (fun z => mul_nonneg hA (H_nonneg q z.2)) (hot_pairDensity_integrable hq A)
  filter_upwards [hpair] with z hz hs
  obtain ⟨hv,hw⟩ := hz hs
  exact mul_le_mul (mul_le_mul_of_nonneg_left hv (collisionKernel_nonneg _ _ _)) hw
    (hf _) (mul_nonneg (collisionKernel_nonneg _ _ _) (mul_nonneg hA (H_nonneg q _)))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Uniform integrability of both physical collision terms -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniformIntegrable_mono_nonneg {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {f g : ℕ → Y → ℝ} (hgm : UniformIntegrable g 1 ν)
    (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : ∀ n, ∀ᵐ y ∂ν, 0 ≤ f n y)
    (hle : ∀ n, ∀ᵐ y ∂ν, f n y ≤ g n y) : UniformIntegrable f 1 ν := by
  have hb (n) : ∀ᵐ y ∂ν, ‖f n y‖ₑ ≤ ‖g n y‖ₑ := by
    filter_upwards [hf n,hle n] with y hy hly
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg hy,Real.norm_of_nonneg (hy.trans hly)]
    exact hly
  obtain ⟨hu,C,hC⟩ := hgm
  exact ⟨hu.ae_mono hfm hb,C,fun n =>
    (eLpNorm_mono_enorm_ae (hfm n) (hb n)).trans (hC n)⟩

private theorem outer_uniformIntegrable {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {g : X × Velocity → ℝ} (hg : Integrable g (μ.prod (volume : Measure Velocity)))
    (hgn : ∀ z, 0 ≤ g z) {S : Set X} (hS : MeasurableSet S)
    (hle : ∀ n, ∀ᵐ p ∂μ.prod (volume : Measure Velocity), p.1 ∉ S → f n p ≤ g p) :
    UniformIntegrable (fun n => outerCutoff S (f n)) 1 (μ.prod (volume : Measure Velocity)) := by
  apply uniformIntegrable_mono_nonneg
    (uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hg))
    (fun n => ((hfm n).indicator (hS.compl.preimage measurable_fst)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun p => indicator_nonneg (fun p _ => hf n p) p))
  intro n
  filter_upwards [hle n] with p hp
  change outerCutoff S (f n) p ≤ g p
  by_cases hs : p.1 ∈ S
  · rw [outerCutoff,indicator_of_notMem (show p ∉ Prod.fst ⁻¹' Sᶜ from fun h => h hs)]
    exact hgn p
  · rw [outerCutoff,indicator_of_mem (show p ∈ Prod.fst ⁻¹' Sᶜ from hs)]
    exact hp hs

theorem outer_gainLoss_uniformIntegrable [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UniformIntegrable (fun n => outerCutoff S (gainDensity (f n))) 1
      (μ.prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun n => outerCutoff S (lossDensity (f n))) 1
      (μ.prod (volume : Measure Velocity)) := by
  have hgn (z : X × Velocity) : 0 ≤ A*H q z.2 := mul_nonneg hA (H_nonneg q z.2)
  have hgm : Measurable (fun z : X × Velocity => A*H q z.2) := by
    unfold H singularity
    fun_prop
  have hi := gainLoss_integrable (μ := μ) hgm hgn (hot_pairDensity_integrable (μ := μ) hq A)
  have hb (n) := gainLoss_outer_bound hq hA (hfm n) (hf n) hS (hdom n)
  exact ⟨outer_uniformIntegrable (fun n => gainDensity_measurable (hfm n))
      (fun n => gainDensity_nonneg (hf n)) hi.1 (gainDensity_nonneg hgn) hS
      (fun n => (hb n).mono (fun p hp hs => (hp hs).1)),
    outer_uniformIntegrable (fun n => lossDensity_measurable (hfm n))
      (fun n => lossDensity_nonneg (hf n)) hi.2 (lossDensity_nonneg hgn) hS
      (fun n => (hb n).mono (fun p hp hs => (hp hs).2))⟩

theorem collision_gainLoss_uniformIntegrable [IsFiniteMeasure μ] [MeasurableSingletonClass X]
    {q : ℝ} (hq : q < 2) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {M : X → ℝ} (hM : ∀ x, 0 ≤ M x)
    (hmoment : ∀ n, ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => f n (x,v)) ≤ ENNReal.ofReal (M x))
    {S : ℕ → Set X} (hS : ∀ j, MeasurableSet (S j))
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    (houter : ∀ j n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S j → f n (x,v) ≤ A j*H q v)
    (hsmall : Tendsto (fun j => ∫⁻ x in S j,
      ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(M x)^2) ∂μ) atTop (𝓝 0)) :
    UniformIntegrable (fun n => gainDensity (f n)) 1 (μ.prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun n => lossDensity (f n)) 1 (μ.prod (volume : Measure Velocity)) := by
  have hb (n) : ∀ᵐ x ∂μ,
      (∫⁻ v : Velocity, ENNReal.ofReal (gainDensity (f n) (x,v))) ≤
        ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(M x)^2) ∧
      (∫⁻ v : Velocity, ENNReal.ofReal (lossDensity (f n) (x,v))) ≤
        ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(M x)^2) := by
    filter_upwards [hmoment n] with x hx
    have hp := VelocityMoment.pairMoment_le_square
      ((hfm n).comp (measurable_const.prodMk measurable_id)) (fun v => hf n (x,v)) (hM x) hx
    have hg := gainLoss_slice_mass_le (hfm n) (hf n) x
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (4*Real.pi))) hp
    exact ⟨hg.1.trans hh,hg.2.trans hh⟩
  have hout (j) := outer_gainLoss_uniformIntegrable hq (hA j) hfm hf (hS j) (houter j)
  exact ⟨uniformIntegrable_of_spatial_cutoffs
      (fun n => gainDensity_measurable (hfm n)) (fun n => gainDensity_nonneg (hf n)) hS
      (fun n => (hb n).mono (fun _ h => h.1)) (fun j => (hout j).1) hsmall,
    uniformIntegrable_of_spatial_cutoffs
      (fun n => lossDensity_measurable (hfm n)) (fun n => lossDensity_nonneg (hf n)) hS
      (fun n => (hb n).mono (fun _ h => h.2)) (fun j => (hout j).2) hsmall⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Weak convergence of the actual full collision rates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def normalizedKernel (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2/(1+‖z.1.2.1‖+‖z.1.2.2‖)

theorem normalizedKernel_measurable : Measurable (normalizedKernel (X := X)) := by
  unfold normalizedKernel collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedKernel_bound (z : (X × (Velocity × Velocity)) × Sphere) :
    |normalizedKernel z| ≤ 1 := by
  unfold normalizedKernel
  have hw : 0 < 1+‖z.1.2.1‖+‖z.1.2.2‖ := by positivity
  rw [abs_of_nonneg (div_nonneg (collisionKernel_nonneg _ _ _) hw.le),div_le_one₀ hw]
  exact (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))

omit [MeasurableSpace X] in
theorem preRate_eq_normalized (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    preRate f z = normalizedKernel z*pairDensity f z.1 := by
  have hw : 1+‖z.1.2.1‖+‖z.1.2.2‖ ≠ 0 := ne_of_gt (by positivity)
  unfold preRate normalizedKernel pairDensity
  field_simp

theorem weak_preRate {μ : Measure X} [SFinite μ] {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => preRate (f n)) (preRate g) := by
  have hh := (h.prod_constant (ν := sphereArea) hf).bounded_mul normalizedKernel_measurable
    1 normalizedKernel_bound
  simpa only [← preRate_eq_normalized] using hh

theorem weak_postRate {μ : Measure X} [SFinite μ] {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => postRate (f n)) (postRate g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (scatterTriple_measurePreserving μ)
    (fun n => (preRate_measurable (hfm n)).comp scatterTriple_measurable)
    ((preRate_measurable hgm).comp scatterTriple_measurable)
  have hs (z : (X × (Velocity × Velocity)) × Sphere) :
      scatterTriple (scatterTriple z) = z := scatterTriple_involutive z
  simpa only [postRate, Function.comp_def, hs] using weak_preRate h hf

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Weak convergence of the physical gain and loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem weak_grouped_rate {μ : Measure X} [SFinite μ]
    {r : ℕ → ((X × (Velocity × Velocity)) × Sphere) → ℝ}
    {s : ((X × (Velocity × Velocity)) × Sphere) → ℝ}
    (hr : ∀ n, Measurable (r n)) (hs : Measurable s)
    (h : Published.WeakL1Converges
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) r s) :
    Published.WeakL1Converges
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (fun n z => r n (collisionGrouping.symm z)) (fun z => s (collisionGrouping.symm z)) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (collisionGrouping_measurePreserving μ)
    (fun n => (hr n).comp collisionGrouping.symm.measurable)
    (hs.comp collisionGrouping.symm.measurable)
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using h

theorem weak_gainLoss {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n z, 0 ≤ f n z) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges (μ.prod volume) (fun n => gainDensity (f n)) (gainDensity g) ∧
      Published.WeakL1Converges (μ.prod volume) (fun n => lossDensity (f n)) (lossDensity g) := by
  have hpost := weak_grouped_rate
    (fun n => (preRate_measurable (hfm n)).comp scatterTriple_measurable)
    ((preRate_measurable hgm).comp scatterTriple_measurable)
    (weak_postRate hfm hgm h hf)
  have hpre := weak_grouped_rate (fun n => preRate_measurable (hfm n))
    (preRate_measurable hgm) (weak_preRate h hf)
  have hpostInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (postRate_integrable (hfm n) (hfn n) (hf n))
  have hpreInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (preRate_integrable (hfm n) (hfn n) (hf n))
  have hp := hpost.marginal hpostInt (k := fun _ => 1) measurable_const 1
    (fun _ => by norm_num)
  have hl := hpre.marginal hpreInt (k := fun _ => 1) measurable_const 1
    (fun _ => by norm_num)
  simp only [one_mul] at hp hl
  exact ⟨hp,hl⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
