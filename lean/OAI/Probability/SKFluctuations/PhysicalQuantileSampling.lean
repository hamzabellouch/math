import Mathlib
import OAI.Probability.SKFluctuations.PhysicalLayerSum

namespace OAI

/-! Physical Quantile Sampling. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

variable {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
variable (hr : r₀≤1) (hu : u₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
  (hkc : ∀ t ∈ Icc r₀ 1, c≤k t) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
  (α : inverseIntegralConstraints r₀ u₀ k M)

 theorem physicalQuantileGrid_coord_of_radius {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (j : Fin (steps.length+2))
    (hj : r₀<physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j) :
    physicalCutMass 0 steps j.val=
      α.val.val (physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j) := by
  have hsp := physicalQuantileGrid_spec hr hu hc hk hkc hm hM α steps ha j
  have hlt := inverseConstraint_strictMonoOn hc hk hkc α.property ⟨le_rfl,hr⟩
    (physicalQuantileGrid_mem hr hu hc hk hkc hm hM α steps ha j) hj
  rw [α.property.1,hsp] at hlt
  have hum : u₀<physicalCutMass 0 steps j.val := (lt_max_iff.mp hlt).resolve_left (lt_irrefl _)
  exact physicalQuantileGrid_coord hr hu hc hk hkc hm hM α steps ha j hum.le

 theorem physicalQuantileSample_coord {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) {s ε : ℝ}
    (hlo : r₀<s-ε) (hi : s≤1)
    (hmesh : ∀ j : Fin (steps.length+1),
      physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.succ-
        physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.castSucc ≤ ε)
    (hε : 0≤ε) (hu₀ : 0≤u₀) :
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha
    physicalCutMass 0 steps (radiusGridCut r s)=α.val.val (radiusGridPoint r s) := by
  dsimp only
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha
  have h₀ : r 0<s := by dsimp only [r]; rw [physicalQuantileGrid_first hr hu hc hk hkc hm hM α steps ha hu₀]; linarith
  have h₁ : s≤r (Fin.last (steps.length+1)) := by dsimp only [r]; rw [physicalQuantileGrid_last]; exact hi
  have hb := radiusGridPoint_bounds r (physicalQuantileGrid_mono hr hu hc hk hkc hm hM α steps ha) h₀ h₁ hmesh
  exact physicalQuantileGrid_coord_of_radius hr hu hc hk hkc hm hM α steps ha
    ⟨radiusGridCut r s,lt_of_le_of_lt (radiusGridCut_le r s) (by omega)⟩ (hlo.trans_le hb.1)

 theorem physicalQuantileSample_regular {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) {a T ε cl cu : ℝ}
    (hε : 0≤ε) (hea : ε≤a/2) (hr₀ : r₀<a/2) (hT : T≤1)
    (hcl : 0≤cl) (hcu : 0≤cu) (hu₀ : 0≤u₀)
    (hmesh : ∀ j : Fin (steps.length+1),
      physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.succ-
        physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha j.castSucc ≤ ε)
    (hreg : ∀ t ∈ Icc (a/2) T, cl*t≤α.val.val t ∧ α.val.val t≤cu*t) :
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha
    ∀ s ∈ Icc a T, (cl/2)*s≤physicalCutMass 0 steps (radiusGridCut r s) ∧
      physicalCutMass 0 steps (radiusGridCut r s)≤cu*s := by
  dsimp only
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps ha
  have hrm := physicalQuantileGrid_mono hr hu hc hk hkc hm hM α steps ha
  intro s hs
  have hlo : r₀<s-ε := by linarith [hs.1]
  have h₀ : r 0<s := by dsimp only [r]; rw [physicalQuantileGrid_first hr hu hc hk hkc hm hM α steps ha hu₀]; linarith
  have h₁ : s≤r (Fin.last (steps.length+1)) := by dsimp only [r]; rw [physicalQuantileGrid_last]; exact hs.2.trans hT
  have hb := radiusGridPoint_bounds r hrm h₀ h₁ hmesh
  rw [physicalQuantileSample_coord hr hu hc hk hkc hm hM α steps ha hlo (hs.2.trans hT) hmesh hε hu₀]
  have hh := hreg (radiusGridPoint r s) ⟨by linarith [hb.1,hs.1],hb.2.le.trans hs.2⟩
  constructor
  · have hd : s/2≤radiusGridPoint r s := by linarith [hs.1,hb.1]
    have hm := mul_le_mul_of_nonneg_left hd hcl
    nlinarith
  · exact hh.2.trans (mul_le_mul_of_nonneg_left hb.2.le hcu)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators

 def radiusCellMeasure {I : Type} [Fintype I] (a b w : I → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (w i/(b i-a i)) • volume.restrict (Ioc (a i) (b i))

 instance radiusCellMeasure_finite {I : Type} [Fintype I] (a b w : I → ℝ) :
    IsFiniteMeasure (radiusCellMeasure a b w) := by
  refine ⟨?_⟩
  simp only [radiusCellMeasure,Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  simp only [Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

 theorem integral_radiusCellMeasure {I : Type} [Fintype I] (a b w : I → ℝ)
    (hab : ∀ i, a i < b i) (hw : ∀ i, 0 ≤ w i)
    (f : ℝ → ℝ) (v : I → ℝ) (hf : ∀ i, ∀ s ∈ Ioc (a i) (b i), f s=v i) :
    ∫ s, f s ∂radiusCellMeasure a b w = ∑ i, w i*v i := by
  have hfe i : f =ᵐ[volume.restrict (Ioc (a i) (b i))] fun _ => v i :=
    (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hf i s hs
  have hi i : Integrable f (ENNReal.ofReal (w i/(b i-a i)) • volume.restrict (Ioc (a i) (b i))) :=
    ((integrable_const (v i)).congr (hfe i).symm).smul_measure ENNReal.ofReal_ne_top
  rw [radiusCellMeasure,integral_sum_measure (integrable_sum_measure hi ((hasSum_fintype _).summable)),tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_congr_ae (hfe i),integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_pos.mpr (hab i)).le,
    ENNReal.toReal_ofReal (div_nonneg (hw i) (sub_pos.mpr (hab i)).le),smul_eq_mul]
  field_simp [ne_of_gt (sub_pos.mpr (hab i))]

 theorem radiusCellMeasure_le {I : Type} [Fintype I] (a b w : I → ℝ)
    (hab : ∀ i, a i < b i) {A l r : ℝ} (hA : 0 ≤ A)
    (hw : ∀ i, w i ≤ A*(b i-a i))
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (hband : ∀ i, Ioc (a i) (b i) ⊆ Ioc l r) :
    radiusCellMeasure a b w ≤ ENNReal.ofReal A • volume.restrict (Ioc l r) := by
  have hcoeff i : ENNReal.ofReal (w i/(b i-a i)) ≤ ENNReal.ofReal A :=
    (ENNReal.ofReal_le_ofReal_iff hA).mpr ((div_le_iff₀ (sub_pos.mpr (hab i))).mpr (hw i))
  have hsum : radiusCellMeasure a b w ≤
      ENNReal.ofReal A • volume.restrict (⋃ i, Ioc (a i) (b i)) := by
    rw [Measure.restrict_iUnion hd (fun _ => measurableSet_Ioc)]
    apply Measure.le_iff.mpr
    intro s hs
    simp only [radiusCellMeasure,Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun i => mul_le_mul' (hcoeff i) le_rfl
  apply hsum.trans
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' le_rfl (Measure.restrict_mono_set volume (iUnion_subset hband) s)

 theorem integral_radiusCellMeasure_allow_zero {I : Type} [Fintype I] (a b w : I → ℝ)
    (hab : ∀ i, w i = 0 ∨ a i < b i) (hw : ∀ i, 0 ≤ w i)
    (f : ℝ → ℝ) (v : I → ℝ) (hf : ∀ i, ∀ s ∈ Ioc (a i) (b i), f s=v i) :
    ∫ s, f s ∂radiusCellMeasure a b w = ∑ i, w i*v i := by
  have hfe i : f =ᵐ[volume.restrict (Ioc (a i) (b i))] fun _ => v i :=
    (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hf i s hs
  have hi i : Integrable f (ENNReal.ofReal (w i/(b i-a i)) • volume.restrict (Ioc (a i) (b i))) :=
    ((integrable_const (v i)).congr (hfe i).symm).smul_measure ENNReal.ofReal_ne_top
  rw [radiusCellMeasure,integral_sum_measure (integrable_sum_measure hi ((hasSum_fintype _).summable)),tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rcases hab i with hz|hp
  · simp [hz]
  rw [integral_smul_measure,integral_congr_ae (hfe i),integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_pos.mpr hp).le,
    ENNReal.toReal_ofReal (div_nonneg (hw i) (sub_pos.mpr hp).le),smul_eq_mul]
  field_simp [ne_of_gt (sub_pos.mpr hp)]

 theorem radiusCellMeasure_le_allow_zero {I : Type} [Fintype I] (a b w : I → ℝ)
    (hab : ∀ i, w i = 0 ∨ a i < b i) {A l r : ℝ} (hA : 0 ≤ A)
    (hw : ∀ i, w i ≤ A*(b i-a i))
    (hd : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))))
    (hband : ∀ i, w i ≠ 0 → Ioc (a i) (b i) ⊆ Ioc l r) :
    radiusCellMeasure a b w ≤ ENNReal.ofReal A • volume.restrict (Ioc l r) := by
  let μ i := volume.restrict (if w i=0 then ∅ else Ioc (a i) (b i))
  have hcoeff i : ENNReal.ofReal (w i/(b i-a i)) ≤ ENNReal.ofReal A := by
    rcases hab i with hz|hp
    · simp [hz]
    exact (ENNReal.ofReal_le_ofReal_iff hA).mpr ((div_le_iff₀ (sub_pos.mpr hp)).mpr (hw i))
  have hd' : Pairwise (fun i j => Disjoint (if w i=0 then ∅ else Ioc (a i) (b i))
      (if w j=0 then ∅ else Ioc (a j) (b j))) := by
    intro i j hij
    split_ifs <;> simp_all [hd hij]
  have hm i : MeasurableSet (if w i=0 then ∅ else Ioc (a i) (b i)) := by
    split_ifs <;> simp
  have hsum : radiusCellMeasure a b w ≤
      ENNReal.ofReal A • volume.restrict (⋃ i, if w i=0 then ∅ else Ioc (a i) (b i)) := by
    rw [Measure.restrict_iUnion hd' hm]
    apply Measure.le_iff.mpr
    intro s hs
    simp only [radiusCellMeasure,Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hz : w i=0
    · simp [hz]
    · simp only [ite_eq_right hz]
      exact mul_le_mul' (hcoeff i) le_rfl
  apply hsum.trans
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul]
  apply mul_le_mul' le_rfl
  apply Measure.restrict_mono_set
  apply iUnion_subset
  intro i
  by_cases hz : w i=0
  · simp [hz]
  · simpa [hz] using hband i hz

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

 

def realizeHierarchyPath : (steps : List (GaussianStep ι)) →
    (Fin steps.length → (ι → ℝ)) → S → ForwardPath (ι → ℝ) S steps.length
  | [], _, σ => σ
  | (_,q)::tail, p, σ => (scaleDriver q (p 0), realizeHierarchyPath tail (Fin.tail p) σ)

omit [Fintype S] [Nonempty S] [MeasurableSingletonClass S] in
theorem measurable_realizeHierarchyPath [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (steps : List (GaussianStep ι)) :
    Measurable (Function.uncurry (realizeHierarchyPath (S := S) steps)) := by
  induction steps with
  | nil => exact measurable_snd
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact (((scaleDriver q).continuous.measurable.comp ((measurable_pi_apply 0).comp
      measurable_fst))).prodMk (ih.comp ((Measurable.of_eval (fun i =>
      (measurable_pi_apply i.succ).comp measurable_fst)).prodMk measurable_snd))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem measurable_hierarchyJointDensity [MeasurableSpace S] [MeasurableSingletonClass S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (x : ι → ℝ) (σ : S) :
    Measurable (fun p => ENNReal.ofReal (hierarchyJointDensity w φ steps x p σ)) := by
  have he : (fun p => ENNReal.ofReal (hierarchyJointDensity w φ steps x p σ)) =
      fun p => forwardWeight steps.length (hierarchyIncrements steps)
        (hierarchyTransitions w φ steps) x p *
        ENNReal.ofReal (spinWeight w φ
          (forwardEnd steps.length (hierarchyIncrements steps) x p) σ) := by
    funext p
    rw [hierarchyJointDensity, ENNReal.ofReal_mul (Real.exp_nonneg _), hierarchyPathWeight_eq]
  rw [he]
  refine ((measurable_forwardWeight _ (hierarchyIncrements_measurable steps)
    (hierarchyTransitions_measurable hw φ steps ha)).comp
      (measurable_const.prodMk measurable_id)).mul ?_
  exact ((continuous_spinWeight hw φ σ).measurable.ennreal_ofReal).comp
    ((measurable_forwardEnd _ (hierarchyIncrements_measurable steps)).comp
      (measurable_const.prodMk measurable_id))

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem hierarchyJointDensity_cons [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (m : ℝ) (q : ι → ℝ≥0) (tail : List (GaussianStep ι)) (x : ι → ℝ)
    (p : Fin (tail.length+1) → (ι → ℝ)) (σ : S) :
    ENNReal.ofReal (hierarchyJointDensity w φ ((m,q)::tail) x p σ) =
      hierarchyTransitions w φ ((m,q)::tail) 0 x (p 0) *
      ENNReal.ofReal (hierarchyJointDensity w φ tail (x+scaleDriver q (p 0))
        (Fin.tail p) σ) := by
  simp only [hierarchyJointDensity, hierarchyPathLog, List.length_cons, forwardEnd,
    hierarchyIncrements, Fin.cons_zero, Fin.cons_succ, Real.exp_add,
    hierarchyTransitions, mul_assoc, ENNReal.ofReal_mul (Real.exp_nonneg _)]

 

theorem lintegral_hierarchyPathKernel_density {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (x : ι → ℝ)
    (f : ForwardPath (ι → ℝ) S steps.length → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂hierarchyPathKernel w φ steps x) =
      ∑ σ, ∫⁻ p, ENNReal.ofReal (hierarchyJointDensity w φ steps x p σ) *
        f (realizeHierarchyPath steps p σ)
        ∂Measure.pi (fun _ : Fin steps.length => standardDrivers ι) := by
  induction steps generalizing a x with
  | nil =>
    change S → ℝ≥0∞ at f
    change (∫⁻ p : S, f p ∂terminalSpinKernel w φ x) =
      ∑ σ, ∫⁻ p : Fin 0 → (ι → ℝ),
        ENNReal.ofReal (Real.exp 0 * spinWeight w φ x σ) * f σ
        ∂Measure.pi (fun _ : Fin 0 => standardDrivers ι)
    rw [terminalSpinKernel_apply hw φ,
      lintegral_withDensity_eq_lintegral_mul _
        (measurable_of_countable (fun σ : S => ENNReal.ofReal (spinWeight w φ x σ)))
        (measurable_of_countable f), lintegral_count, tsum_fintype]
    simp [Pi.mul_apply]
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    change ((ι → ℝ) × ForwardPath (ι → ℝ) S tail.length) → ℝ≥0∞ at f
    have hm := plantedStepKernel_markov hw φ m q tail ha
    have ht := hierarchyPathKernel_markov hw φ tail ha.2.2.2
    let T : (ι → ℝ) → ℝ≥0∞ := fun z =>
      hierarchyTransitions w φ ((m,q)::tail) 0 x z
    let F (σ : S) (p : Fin (tail.length+1) → (ι → ℝ)) :=
      ENNReal.ofReal (hierarchyJointDensity w φ ((m,q)::tail) x p σ) *
        f (realizeHierarchyPath ((m,q)::tail) p σ)
    let G (σ : S) (z : ι → ℝ) (p : Fin tail.length → (ι → ℝ)) :=
      ENNReal.ofReal (hierarchyJointDensity w φ tail (x+scaleDriver q z) p σ) *
        f (scaleDriver q z, realizeHierarchyPath tail p σ)
    have hF (σ : S) : Measurable (F σ) :=
      (measurable_hierarchyJointDensity hw φ _ ha x σ).mul
        (hf.comp ((measurable_realizeHierarchyPath _).comp
          (measurable_id.prodMk measurable_const)))
    have hG (σ : S) (z : ι → ℝ) : Measurable (G σ z) :=
      (measurable_hierarchyJointDensity hw φ tail ha.2.2.2 _ σ).mul
        (hf.comp (measurable_const.prodMk
          ((measurable_realizeHierarchyPath tail).comp
            (measurable_id.prodMk measurable_const))))
    have hFG (σ : S) (z : ι → ℝ) (p : Fin tail.length → (ι → ℝ)) :
        F σ (Fin.cons z p) = T z * G σ z p := by
      dsimp only [F, G, T]
      rw [hierarchyJointDensity_cons]
      simp only [Fin.cons_zero, Fin.tail_cons, realizeHierarchyPath, mul_assoc]
    have hpiece (σ : S) : Measurable (fun z => T z * ∫⁻ p, G σ z p
        ∂Measure.pi (fun _ : Fin tail.length => standardDrivers ι)) := by
      have hh0 : Measurable (Function.uncurry
          (fun (z : ι → ℝ) (p : Fin tail.length → (ι → ℝ)) => F σ (Fin.cons z p))) :=
        (hF σ).comp measurable_finCons
      have hh := hh0.lintegral_prod_right
        (ν := Measure.pi (fun _ : Fin tail.length => standardDrivers ι))
      have he : (fun z => T z * ∫⁻ p, G σ z p
          ∂Measure.pi (fun _ : Fin tail.length => standardDrivers ι)) =
          (fun z => ∫⁻ p, F σ (Fin.cons z p)
          ∂Measure.pi (fun _ : Fin tail.length => standardDrivers ι)) := by
        funext z
        simp_rw [hFG]
        exact (lintegral_const_mul _ (hG σ z)).symm
      rw [he]
      exact hh
    have hsplit (σ : S) : (∫⁻ p, F σ p
        ∂Measure.pi (fun _ : Fin (tail.length+1) => standardDrivers ι)) =
        ∫⁻ z, T z * ∫⁻ p, G σ z p
          ∂Measure.pi (fun _ : Fin tail.length => standardDrivers ι)
          ∂standardDrivers ι := by
      rw [lintegral_fin_cons _ (hF σ)]
      simp_rw [hFG]
      exact lintegral_congr fun z => lintegral_const_mul _ (hG σ z)
    change (∫⁻ p : (ι → ℝ) × ForwardPath (ι → ℝ) S tail.length,
      f p ∂(plantedStepKernel w φ m q tail ⊗ₖ
      (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
        (measurable_fst.add measurable_snd)) x) =
      ∑ σ, ∫⁻ p, F σ p ∂Measure.pi (fun _ : Fin (tail.length+1) => standardDrivers ι)
    simp_rw [hsplit]
    rw [← lintegral_finsetSum _ (fun σ _ => hpiece σ),
      Kernel.lintegral_compProd _ _ _ hf]
    simp only [Kernel.comap_apply]
    have hg : Measurable (fun z => ∫⁻ p, f (z,p)
        ∂hierarchyPathKernel w φ tail (x+z)) := by
      let κ := (hierarchyPathKernel w φ tail).comap (fun z => x+z)
        (measurable_const.add measurable_id)
      exact hf.lintegral_kernel_prod_right' (κ := κ)
    have hd : Measurable (fun z => ENNReal.ofReal (plantedTransitionDensity
        (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail) x z)) :=
      (plantedStepDensity_measurable hw φ m q tail ha).comp
        (measurable_const.prodMk measurable_id)
    rw [plantedStepKernel, Kernel.withDensity_apply _
      (plantedStepDensity_measurable hw φ m q tail ha), Kernel.const_apply,
      lintegral_withDensity_eq_lintegral_mul _ hd hg]
    rw [← (scaleDriver_gaussian q).lintegral_comp (hd.mul hg)]
    apply lintegral_congr
    intro z
    simp only [Pi.mul_apply]
    rw [ih ha.2.2.2 (x+scaleDriver q z) (fun p => f (scaleDriver q z,p))
      (hf.comp (measurable_const.prodMk measurable_id)), Finset.mul_sum]
    rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem measurable_hierarchyJointDensity_joint [MeasurableSpace S] [MeasurableSingletonClass S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (σ : S) :
    Measurable (fun p : (ι → ℝ) × (Fin steps.length → (ι → ℝ)) =>
      ENNReal.ofReal (hierarchyJointDensity w φ steps p.1 p.2 σ)) := by
  have he : (fun p : (ι → ℝ) × (Fin steps.length → (ι → ℝ)) =>
      ENNReal.ofReal (hierarchyJointDensity w φ steps p.1 p.2 σ)) =
      fun p => forwardWeight steps.length (hierarchyIncrements steps)
        (hierarchyTransitions w φ steps) p.1 p.2 *
        ENNReal.ofReal (spinWeight w φ
          (forwardEnd steps.length (hierarchyIncrements steps) p.1 p.2) σ) := by
    funext p
    rw [hierarchyJointDensity, ENNReal.ofReal_mul (Real.exp_nonneg _), hierarchyPathWeight_eq]
  rw [he]
  exact (measurable_forwardWeight _ (hierarchyIncrements_measurable steps)
    (hierarchyTransitions_measurable hw φ steps ha)).mul
    (((continuous_spinWeight hw φ σ).measurable.ennreal_ofReal).comp
      (measurable_forwardEnd _ (hierarchyIncrements_measurable steps)))

 theorem measurable_rootedJointDensity {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (σ : S) :
    Measurable (fun p => ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ)) := by
  exact (measurable_hierarchyJointDensity_joint hw φ steps ha σ).comp
    ((((scaleDriver q₀).continuous.measurable).comp (measurable_pi_apply 0)).prodMk
      (Measurable.of_eval (fun i => measurable_pi_apply i.succ)))

 

def rootedHierarchyPathLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι)) :
    Measure ((ι → ℝ) × ForwardPath (ι → ℝ) S steps.length) :=
  (Measure.pi (fun i => gaussianReal 0 (q₀ i))) ⊗ₘ hierarchyPathKernel w φ steps

 theorem rootedHierarchyPathLaw_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    IsProbabilityMeasure (rootedHierarchyPathLaw w φ q₀ steps) := by
  have := hierarchyPathKernel_markov hw φ steps ha
  unfold rootedHierarchyPathLaw
  infer_instance

def realizeRootedPath (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (p : Fin (steps.length+1) → (ι → ℝ)) (σ : S) :
    (ι → ℝ) × ForwardPath (ι → ℝ) S steps.length :=
  (scaleDriver q₀ (p 0), realizeHierarchyPath steps (Fin.tail p) σ)

 theorem measurable_realizeRootedPath (q₀ : ι → ℝ≥0) (steps : List (GaussianStep ι))
    (σ : S) : Measurable (fun p => realizeRootedPath q₀ steps p σ) := by
  exact (((scaleDriver q₀).continuous.measurable).comp (measurable_pi_apply 0)).prodMk
    ((measurable_realizeHierarchyPath steps).comp
      ((Measurable.of_eval (fun i => measurable_pi_apply i.succ)).prodMk measurable_const))

 theorem lintegral_rootedHierarchyPathLaw {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (f : ((ι → ℝ) × ForwardPath (ι → ℝ) S steps.length) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ p, f p ∂rootedHierarchyPathLaw w φ q₀ steps) =
      ∑ σ, ∫⁻ p, ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ) *
        f (realizeRootedPath q₀ steps p σ)
        ∂Measure.pi (fun _ : Fin (steps.length+1) => standardDrivers ι) := by
  have := hierarchyPathKernel_markov hw φ steps ha
  let F (σ : S) (p : Fin (steps.length+1) → (ι → ℝ)) :=
    ENNReal.ofReal (rootedJointDensity w φ q₀ steps p σ) *
      f (realizeRootedPath q₀ steps p σ)
  have hF (σ : S) : Measurable (F σ) :=
    (measurable_rootedJointDensity hw φ q₀ steps ha σ).mul
      (hf.comp (measurable_realizeRootedPath q₀ steps σ))
  have hpiece (σ : S) : Measurable (fun z => ∫⁻ p, F σ (Fin.cons z p)
      ∂Measure.pi (fun _ : Fin steps.length => standardDrivers ι)) := by
    have hh : Measurable (Function.uncurry
        (fun (z : ι → ℝ) (p : Fin steps.length → (ι → ℝ)) => F σ (Fin.cons z p))) :=
      (hF σ).comp measurable_finCons
    exact hh.lintegral_prod_right
  change _ = ∑ σ, ∫⁻ p, F σ p ∂Measure.pi (fun _ => standardDrivers ι)
  simp_rw [lintegral_fin_cons _ (hF _)]
  rw [←lintegral_finsetSum _ (fun σ _ => hpiece σ), rootedHierarchyPathLaw,
    Measure.lintegral_compProd hf]
  rw [← (scaleDriver_gaussian q₀).lintegral_comp
    (hf.lintegral_kernel_prod_right' (κ := hierarchyPathKernel w φ steps))]
  apply lintegral_congr
  intro z
  rw [lintegral_hierarchyPathKernel_density hw φ steps ha (scaleDriver q₀ z)
    (fun p => f (scaleDriver q₀ z,p))
    (hf.comp (measurable_const.prodMk measurable_id))]
  rfl

 theorem rootedHierarchyPathLaw_eq_flat {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    {d : ℕ} (e : Fin d ≃ Fin (steps.length+1) × ι) :
    rootedHierarchyPathLaw w φ q₀ steps =
      ∑ σ, (flatPlantedPinLaw w φ q₀ steps e σ).map
        (fun z => realizeRootedPath q₀ steps ((flattenDrivers e).symm z) σ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_rootedHierarchyPathLaw hw φ q₀ steps ha f hf,
    lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro σ _
  have hmap : Measurable (fun z => realizeRootedPath q₀ steps ((flattenDrivers e).symm z) σ) :=
    (measurable_realizeRootedPath q₀ steps σ).comp (flattenDrivers e).symm.continuous.measurable
  have hd : Measurable (fun z => ENNReal.ofReal
      (rootedJointDensity w φ q₀ steps ((flattenDrivers e).symm z) σ)) :=
    (measurable_rootedJointDensity hw φ q₀ steps ha σ).comp
      (flattenDrivers e).symm.continuous.measurable
  have hfm : Measurable (fun z => f (realizeRootedPath q₀ steps ((flattenDrivers e).symm z) σ)) :=
    hf.comp hmap
  rw [lintegral_map hf hmap, flatPlantedPinLaw,
    lintegral_withDensity_eq_lintegral_mul _ hd hfm]
  rw [← (flattenDrivers_standard e).lintegral_comp_emb
    (flattenDrivers e).toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  simp only [Pi.mul_apply, ContinuousLinearEquiv.symm_apply_apply]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {ι S κ : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype κ]
  [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype ι] [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem ForwardPath.spin_realize [Fintype ι] [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (steps : List (GaussianStep ι))
    (p : Fin steps.length → (ι → ℝ)) (σ : S) :
    ForwardPath.spin steps.length (realizeHierarchyPath steps p σ) = σ := by
  induction steps with
  | nil => rfl
  | cons st tail ih => exact ih (Fin.tail p)

 

def physicalNodePair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (V : κ → ι → ℝ) (steps : List (GaussianStep ι)) (k : ℝ)
    (x : ι → ℝ) (σ : S) : ℝ × ℝ :=
  (k * driverObservable w φ steps (ContinuousLinearMap.id ℝ _) V σ x,
    k^2 * driverEnergy w φ steps (ContinuousLinearMap.id ℝ _) V σ x)

 

def physicalPinnedPair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (V : κ → ι → ℝ) : (steps : List (GaussianStep ι)) → ℝ →
    (Fin (steps.length+1) → ℝ) → (ι → ℝ) →
    ForwardPath (ι → ℝ) S steps.length → ℝ × ℝ
  | [], a, k, x, σ => (1-a) • physicalNodePair w φ V [] (k 0) x σ
  | (m,q)::tail, a, k, x, p =>
    (m-a) • physicalNodePair w φ V ((m,q)::tail) (k 0) x
      (ForwardPath.spin tail.length p.2) +
    physicalPinnedPair w φ V tail m (Fin.tail k) (x+p.1) p.2

 theorem physicalNodePair_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (V : κ → ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (k : ℝ) :
    Measurable (Function.uncurry (physicalNodePair w φ V steps k)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (((driverObservable_smooth hw φ steps ha (.id ℝ _) V σ 0).continuous.measurable).const_mul k).prodMk
    (((driverEnergy_smooth hw φ steps ha (.id ℝ _) V σ 0).continuous.measurable).const_mul (k^2))

 theorem physicalPinnedPair_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (V : κ → ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (k : Fin (steps.length+1) → ℝ) :
    Measurable (Function.uncurry (physicalPinnedPair w φ V steps a k)) := by
  induction steps generalizing a with
  | nil => exact (physicalNodePair_measurable hw φ V [] ha (k 0)).const_smul (1-a)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact (((physicalNodePair_measurable hw φ V ((m,q)::tail) ha (k 0)).comp
      (measurable_fst.prodMk ((ForwardPath.spin_measurable tail.length).comp
        (measurable_snd.comp measurable_snd)))).const_smul (m-a)).add
      ((ih ha.2.2.2 (Fin.tail k)).comp
        ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem physicalNodePair_driver [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (V : κ → ι → ℝ) (steps : List (GaussianStep ι)) {d : ℕ}
    (D : (Fin d → ℝ) →L[ℝ] (ι → ℝ)) (k : ℝ) (x : Fin d → ℝ) (σ : S) :
    physicalNodePair w φ V steps k (D x) σ =
      (k*driverObservable w φ steps D V σ x, k^2*driverEnergy w φ steps D V σ x) := rfl

 theorem physicalPinnedPair_eq_frames (w : S → ℝ) (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (V : κ → ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) {d : ℕ}
    (D : (Fin d → ℝ) →L[ℝ] (ι → ℝ))
    (P : Fin steps.length → (Fin d → ℝ) →L[ℝ] (ι → ℝ))
    (k : Fin (steps.length+1) → ℝ) (x : Fin d → ℝ) (σ : S) :
    physicalPinnedPair w φ V steps a k (D x)
      (realizeHierarchyPath steps (fun j => P j x) σ) =
      (pinnedObservable (pathFrames w hw φ V steps a ha D P) (pathMassDifferences steps a) k σ x,
       pinnedEnergy (pathFrames w hw φ V steps a ha D P) (pathMassDifferences steps a) k σ x) := by
  induction steps generalizing a D with
  | nil =>
    simp [physicalPinnedPair, realizeHierarchyPath, physicalNodePair_driver,
      pinnedObservable, pinnedEnergy, pathFrames, pathMassDifferences,
      PinFrame.observable, PinFrame.energy, smul_eq_mul, mul_assoc]
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    simp only [physicalPinnedPair, realizeHierarchyPath, ForwardPath.spin_realize]
    have hie := ih ha.2.2.2 (D+(scaleDriver q).comp (P 0))
      (fun j => P j.succ) (Fin.tail k)
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply] at hie
    erw [hie]
    apply Prod.ext
    · simp only [physicalNodePair_driver, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        pinnedObservable, Fin.sum_univ_succ, pathFrames, pathMassDifferences,
        Fin.cons_zero, Fin.cons_succ, PinFrame.observable, Fin.tail]
      congr 1
      ring
      erw [Fin.sum_univ_succ]
    · simp only [physicalNodePair_driver, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        pinnedEnergy, Fin.sum_univ_succ, pathFrames, pathMassDifferences,
        Fin.cons_zero, Fin.cons_succ, PinFrame.energy, Fin.tail]
      congr 1
      ring
      erw [Fin.sum_univ_succ]

end SKFluctuations.Hierarchy

end

end OAI
