import OAI.Analysis.PlaneSpectrum.Basic
import OAI.MeasureTheory.CompactFactors.Centers

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

namespace EuclideanFiveColor.UniformFibers

variable {X Q : Type*} [MeasurableSpace X]

 theorem finite_uniform_fibers (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Q) (hm : ∀ y : Q, MeasurableSet (q ⁻¹' {y}))
    {a : ℝ≥0∞} (ha : 0 < a)
    (hs : ∀ᵐ x ∂μ, μ (q ⁻¹' {q x}) = a) :
    ∃ S : Finset Q, S.Nonempty ∧
      (∀ y ∈ S, μ (q ⁻¹' {y}) = a) ∧
      (∀ᵐ x ∂μ, q x ∈ S) ∧ (S.card : ℝ≥0∞) * a = 1 := by
  classical
  have hd : Pairwise (Function.onFun Disjoint (fun y : Q => q ⁻¹' {y})) := by
    intro y z hyz
    change Disjoint (q ⁻¹' {y}) (q ⁻¹' {z})
    rw [Set.disjoint_left]
    intro x hx hy
    exact hyz (hx.symm.trans hy)
  have hf := Measure.finite_const_le_meas_of_disjoint_iUnion μ ha hm hd (measure_ne_top μ _)
  have hf' : {y : Q | μ (q ⁻¹' {y}) = a}.Finite :=
    hf.subset (fun _ h => le_of_eq h.symm)
  let S := hf'.toFinset
  have hS (y : Q) : y ∈ S ↔ μ (q ⁻¹' {y}) = a := hf'.mem_toFinset
  have hsample : ∀ᵐ x ∂μ, q x ∈ S := hs.mono fun x hx => (hS _).mpr hx
  have hcover : (⋃ y ∈ S, q ⁻¹' {y}) =ᵐ[μ] Set.univ := by
    filter_upwards [hsample] with x hx
    have hmem : x ∈ ⋃ y ∈ S, q ⁻¹' {y} :=
      Set.mem_iUnion.mpr ⟨q x, Set.mem_iUnion.mpr ⟨hx, rfl⟩⟩
    exact propext (iff_of_true hmem (Set.mem_univ x))
  have hsum : (S.card : ℝ≥0∞) * a = 1 := by
    have h := measure_congr hcover
    rw [measure_biUnion_finset (fun _ _ _ _ h => hd h) (fun y _ => hm y),
      measure_univ] at h
    calc
      (S.card : ℝ≥0∞) * a = ∑ _y ∈ S, a := by simp
      _ = ∑ y ∈ S, μ (q ⁻¹' {y}) := Finset.sum_congr rfl fun y hy => ((hS y).mp hy).symm
      _ = 1 := h
  refine ⟨S, ?_, (fun y hy => (hS y).mp hy), hsample, hsum⟩
  by_contra h
  have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [hS0] at hsum

end EuclideanFiveColor.UniformFibers

namespace EuclideanFiveColor.CosetCenter.Embedding
open MeasureTheory
open scoped ENNReal
variable {G : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSingletonClass G]
  (e : CosetCenter.Embedding G)

/-- The conditional center law has finitely many, equally weighted atoms.
The original cosets need not form a standard Borel quotient. -/
theorem finite_uniform_centers (μ : ProbabilityMeasure G) {a : ℝ≥0∞}
    (ha : 0 < a) (hs : ∀ᵐ z ∂(μ : Measure G), (μ : Measure G) (e.coset z) = a) :
    ∃ S : Finset G, S.Nonempty ∧
      (∀ b ∈ S, (μ : Measure G) ((e.center μ) ⁻¹' {b}) = a) ∧
      (∀ᵐ z ∂(μ : Measure G), e.center μ z ∈ S) ∧
      (S.card : ℝ≥0∞) * a = 1 := by
  apply UniformFibers.finite_uniform_fibers (μ : Measure G) (e.center μ)
    (fun b => e.measurable_center_fixed μ (measurableSet_singleton b)) ha
  filter_upwards [hs] with z hz
  rw [e.preimage_center_singleton μ (by rw [hz]; exact ha.ne'), hz]

omit [MeasurableSingletonClass G] in
/-- Wildness survives the measurable recentering construction. -/
theorem center_law_ordinary (μ : ProbabilityMeasure G) :
    (μ.map (e.center μ) : Measure G) e.ordinary =
      (μ : Measure G) e.ordinary := by
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (e.measurable_center_fixed μ) e.measurableSet_ordinary]
  congr 1
  ext z
  exact e.center_mem_ordinary_iff μ z

end EuclideanFiveColor.CosetCenter.Embedding

namespace EuclideanFiveColor.ErgodicSupport
open MeasureTheory Filter
variable {K X V : Type*} [SMul K X] [MeasurableSpace X]
  {μ : Measure X} [ErgodicSMul K X μ] [MeasurableSpace V]
  [MeasurableSpace.CountablySeparated V] [Nonempty V]

/-- The invariant-function consequence of group-action ergodicity,
with an individual almost-everywhere identity for each group element. -/
theorem ae_eq_const_of_invariant {f : X → V} (hf : Measurable f)
    (hi : ∀ k : K, ∀ᵐ x ∂μ, f (k • x) = f x) :
    ∃ v : V, f =ᵐ[μ] (fun _ => v) := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have h := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := K)
    (hf hA) (fun k => (hi k).mono (fun x hx => by
      exact propext (show f (k • x) ∈ A ↔ f x ∈ A by rw [hx])))
  exact eventuallyEmptyOrUniv_iff.mp h

end EuclideanFiveColor.ErgodicSupport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.KernelSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_map_base (ν : Measure Y) [SFinite ν] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (R : Y ≃ᵐ Y) :
    (ν.map R) ⊗ₘ (κ.comap R.symm R.symm.measurable) =
      (ν ⊗ₘ κ).map (Prod.map R id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (R.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply ((R.measurable.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) R.measurable]
  apply lintegral_congr
  intro y
  simp only [Kernel.comap_apply, R.symm_apply_apply]
  rfl

lemma condDistrib_comp_equiv [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (R : Y ≃ᵐ Y) :
    condDistrib f (R ∘ p) μ =ᵐ[μ.map (R ∘ p)]
      (condDistrib f p μ).comap R.symm R.symm.measurable := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (R.measurable.comp hp) hf
  rw [← Measure.map_map R.measurable hp, compProd_map_base,
    compProd_map_condDistrib hp.aemeasurable hf.aemeasurable,
    Measure.map_map (R.measurable.prodMap measurable_id) (hp.prodMk hf)]
  rfl

/-- Changing both coordinates of a conditional law by invertible measurable
maps commutes with conditional sampling. -/
lemma condDistrib_equivariant [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (S : X ≃ᵐ X) (R : Y ≃ᵐ Y) (T : Z → Z) (hT : Measurable T)
    (hS : MeasurePreserving S μ μ)
    (hRp : p ∘ S =ᵐ[μ] R ∘ p) (hTf : f ∘ S =ᵐ[μ] T ∘ f) :
    ∀ᵐ y ∂μ.map p, condDistrib f p μ (R y) = (condDistrib f p μ y).map T := by
  have hR : (μ.map p).map R = μ.map p := by
    rw [Measure.map_map R.measurable hp, ← Measure.map_congr hRp,
      ← Measure.map_map hp S.measurable, hS.map_eq]
  have hRS : μ.map (p ∘ S) = μ.map p := by
    rw [← Measure.map_map hp S.measurable, hS.map_eq]
  have hm := condDistrib_map (X := p) (Y := f) (ν := μ) (f := S)
    (hp.aemeasurable) (hf.aemeasurable) S.measurable.aemeasurable
  simp only [hS.map_eq, hRS] at hm
  rw [condDistrib_congr hTf hRp] at hm
  have hc := condDistrib_comp_equiv μ (T ∘ f) p (hT.comp hf) hp R
  have hh : μ.map (R ∘ p) = μ.map p := by
    rw [← Measure.map_map R.measurable hp, hR]
  rw [hh] at hc
  have he := condDistrib_comp (μ := μ) hp.aemeasurable hf.aemeasurable hT
  have hcomp : ∀ᵐ y ∂μ.map p,
      condDistrib f p μ y = (condDistrib f p μ (R.symm y)).map T := by
    have he' : ∀ᵐ y ∂μ.map p,
        condDistrib (T ∘ f) p μ (R.symm y) =
          (condDistrib f p μ (R.symm y)).map T := by
      have hRinv : MeasurePreserving R.symm (μ.map p) (μ.map p) := by
        refine ⟨R.symm.measurable, ?_⟩
        calc
          (μ.map p).map R.symm = ((μ.map p).map R).map R.symm := by rw [hR]
          _ = μ.map p := R.map_symm_map
      exact hRinv.quasiMeasurePreserving.ae <| he.mono fun y hy => by
        simpa only [Kernel.map_apply _ hT] using hy
    filter_upwards [hm, hc, he'] with y h₁ h₂ h₃
    simpa only [Kernel.comap_apply] using h₁.trans (h₂.trans h₃)
  have hRpres : MeasurePreserving R (μ.map p) (μ.map p) := ⟨R.measurable, hR⟩
  have hfinal := hRpres.quasiMeasurePreserving.ae hcomp
  filter_upwards [hfinal] with y hy
  simpa only [R.symm_apply_apply] using hy

end EuclideanFiveColor.KernelSupport

namespace EuclideanFiveColor.RelativeCenters
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Y G : Type*} [MeasurableSpace Y] [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (e : CosetCenter.Embedding G)

noncomputable def probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ]
    (y : Y) : ProbabilityMeasure G := ⟨κ y, inferInstance⟩

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (probabilityKernel κ) := κ.measurable.subtype_mk

noncomputable def cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] (p : Y × G) : ℝ≥0∞ :=
  κ p.1 (e.coset p.2)

lemma measurable_cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (cosetMass e κ) :=
  e.measurable_mass.comp ((measurable_probabilityKernel κ).comp measurable_fst |>.prodMk
    measurable_snd)

/-- The relative difference law uses two independent samples of the same
conditional probability law; it is not an independent marginal difference. -/
noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

lemma differenceLaw_ordinary (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    differenceLaw ν κ e.ordinary = ∫⁻ p : Y × G, cosetMass e κ p ∂ν ⊗ₘ κ := by
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, Measure.map_apply hdiv
    e.measurableSet_ordinary,
    Measure.bind_apply (hdiv e.measurableSet_ordinary)
      (κ ×ₖ κ).aemeasurable,
    Measure.lintegral_compProd (measurable_cosetMass e κ)]
  apply lintegral_congr
  intro y
  rw [Kernel.prod_apply,
    Measure.prod_apply_symm (hdiv e.measurableSet_ordinary)]
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma sampledMass_integral [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary =
      ∫⁻ x, cosetMass e (condDistrib d p μ) (p x, d x) ∂μ := by
  rw [differenceLaw_ordinary, compProd_map_condDistrib hp.aemeasurable hd.aemeasurable,
    lintegral_map (measurable_cosetMass e _) (hp.prodMk hd)]

/-- Positive relative mass and ergodicity force a fixed positive mass for almost
all sampled cosets. The finite-center conclusion follows without a quotient
measurable space for the ordinary-character subgroup. -/
theorem positive_mass_finite_centers [StandardBorelSpace G]
    [MeasurableSingletonClass G]
    {K : Type*} [SMul K X]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hi : ∀ k : K, ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      (∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) = a) ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib d p μ y
          ((e.center (probabilityKernel (condDistrib d p μ) y)) ⁻¹' {b}) = a) ∧
        (∀ᵐ z ∂condDistrib d p μ y,
          e.center (probabilityKernel (condDistrib d p μ) y) z ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 := by
  have hm : Measurable (fun x => cosetMass e (condDistrib d p μ) (p x, d x)) :=
    (measurable_cosetMass e (condDistrib d p μ)).comp (hp.prodMk hd)
  obtain ⟨a, ha⟩ := ErgodicSupport.ae_eq_const_of_invariant hm hi
  have hapos : 0 < a := by
    rw [sampledMass_integral e μ d p hd hp, lintegral_congr_ae ha] at hpos
    simpa using hpos
  refine ⟨a, hapos, ha, ?_⟩
  have hpair : ∀ᵐ q ∂(μ.map p) ⊗ₘ condDistrib d p μ,
      cosetMass e (condDistrib d p μ) q = a := by
    rw [compProd_map_condDistrib hp.aemeasurable hd.aemeasurable]
    exact (ae_map_iff (hp.prodMk hd).aemeasurable
      (measurableSet_eq_fun (measurable_cosetMass e _) measurable_const)).mpr ha
  have hany := Measure.ae_ae_of_ae_compProd hpair
  filter_upwards [hany] with y hy
  exact e.finite_uniform_centers (probabilityKernel (condDistrib d p μ) y) hapos hy

section Actions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma sampledMass_invariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hC : ∀ (k : K) (z : G), k • z ∈ e.ordinary ↔ z ∈ e.ordinary)
    (k : K) :
    ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x) := by
  have heq := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxeq := ae_of_ae_map hp.aemeasurable heq
  filter_upwards [hxeq, hde k, hpe k] with x hx hd' hp'
  change condDistrib d p μ (p (k • x)) (e.coset (d (k • x))) =
    condDistrib d p μ (p x) (e.coset (d x))
  change condDistrib d p μ (k • p x) = _ at hx
  rw [hp', hd', hx, Measure.map_apply (measurable_const_smul k) (e.measurableSet_coset _)]
  congr 1
  ext z
  change k • z / k • d x ∈ e.ordinary ↔ z / d x ∈ e.ordinary
  rw [← smul_div']
  exact hC k _

end Actions

noncomputable def centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) : G :=
  e.center (probabilityKernel (condDistrib d p μ) (p x)) (d x)

lemma measurable_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    Measurable (centerMap e μ d p) :=
  e.measurable_center.comp (((measurable_probabilityKernel _).comp hp).prodMk hd)

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma centerMap_mem_ordinary_iff [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) :
    centerMap e μ d p x ∈ e.ordinary ↔ d x ∈ e.ordinary :=
  e.center_mem_ordinary_iff _ _

lemma centerMap_law_ordinary [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    (μ.map (centerMap e μ d p)) e.ordinary = (μ.map d) e.ordinary := by
  rw [Measure.map_apply (measurable_centerMap e μ d p hd hp) e.measurableSet_ordinary,
    Measure.map_apply hd e.measurableSet_ordinary]
  congr 1
  ext x
  exact centerMap_mem_ordinary_iff e μ d p x

section CenterActions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma centerMap_equivariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (ha : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0)
    (k : K) :
    ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x := by
  have hk := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxk := ae_of_ae_map hp.aemeasurable hk
  filter_upwards [hxk, hde k, hpe k, ha] with x hx hd' hp' ha'
  have hprob : probabilityKernel (condDistrib d p μ) (k • p x) =
      (probabilityKernel (condDistrib d p μ) (p x)).map
        (fun point : G => k • point) := by
    apply Subtype.ext
    exact hx
  change e.center (probabilityKernel (condDistrib d p μ) (p (k • x))) (d (k • x)) = _
  rw [hp', hd', hprob]
  exact e.center_equivariant (MulDistribMulAction.toMulEquiv G k) (O k)
    (measurable_const_smul k) (he k) _ _ ha'

end CenterActions

section ConditionalLaw
variable {H : Type*} [MeasurableSpace H]

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma dependentMapKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) (y : Y) :
    ((Kernel.id ×ₖ κ).map f) y = (κ y).map (fun z => f (y, z)) := by
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma compProd_dependentMap (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) :
    ν ⊗ₘ ((Kernel.id ×ₖ κ).map f) =
      (ν ⊗ₘ κ).map (fun q : Y × G => (q.1, f q)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.compProd_apply ((measurable_fst.prodMk hf) hs)]
  apply lintegral_congr
  intro y
  have hfy : Measurable (fun z : G => f (y, z)) := hf.comp measurable_prodMk_left
  rw [dependentMapKernel_apply κ f hf y,
    Measure.map_apply hfy (measurable_prodMk_left hs)]
  rfl

noncomputable def centerKernel (κ : Kernel Y G) [IsMarkovKernel κ] : Kernel Y G :=
  (Kernel.id ×ₖ κ).map (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2)

lemma measurable_fiberCenter (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2) :=
  e.measurable_center.comp (((measurable_probabilityKernel κ).comp measurable_fst).prodMk
    measurable_snd)

instance centerKernel_markov (κ : Kernel Y G) [IsMarkovKernel κ] :
    IsMarkovKernel (centerKernel e κ) :=
  Kernel.IsMarkovKernel.map _ (measurable_fiberCenter e κ)

lemma centerKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ] (y : Y) :
    centerKernel e κ y = (κ y).map (e.center (probabilityKernel κ y)) :=
  dependentMapKernel_apply κ _ (measurable_fiberCenter e κ) y

lemma condDistrib_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    condDistrib (centerMap e μ d p) p μ =ᵐ[μ.map p]
      centerKernel e (condDistrib d p μ) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hp (measurable_centerMap e μ d p hd hp)
  rw [centerKernel, compProd_dependentMap (μ.map p) (condDistrib d p μ) _
    (measurable_fiberCenter e _), compProd_map_condDistrib hp.aemeasurable hd.aemeasurable,
    Measure.map_map (measurable_fst.prodMk (measurable_fiberCenter e _)) (hp.prodMk hd)]
  rfl

end ConditionalLaw

lemma centerKernel_comp_map [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    centerKernel e (condDistrib d p μ) ∘ₘ (μ.map p) = μ.map (centerMap e μ d p) := by
  rw [← Measure.comp_congr (condDistrib_centerMap e μ d p hd hp)]
  exact condDistrib_comp_map hp.aemeasurable (measurable_centerMap e μ d p hd hp).aemeasurable

variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G] [MeasurableSingletonClass G]

theorem finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (hwild : (μ.map d) e.ordinary = 0)
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    Measurable (centerMap e μ d p) ∧
    (∀ k : K, ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x) ∧
    (μ.map (centerMap e μ d p)) e.ordinary = 0 ∧
    ∃ a : ℝ≥0∞, 0 < a ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib (centerMap e μ d p) p μ y {b} = a) ∧
        (∀ᵐ b ∂condDistrib (centerMap e μ d p) p μ y, b ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 ∧
        (∀ b ∈ S, b ∉ e.ordinary) := by
  have hC (k : K) (z : G) : k • z ∈ e.ordinary ↔ z ∈ e.ordinary :=
    e.equiv_mem_ordinary_iff (MulDistribMulAction.toMulEquiv G k) (O k) (he k) z
  obtain ⟨a, ha, hmass, hfib⟩ := positive_mass_finite_centers e μ d p hd hp
    (sampledMass_invariant e μ d p hd hp hde hpe hC) hpos
  have ha' : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0 :=
    hmass.mono fun _ h => by rw [h]; exact ha.ne'
  have hbzero : (μ.map (centerMap e μ d p)) e.ordinary = 0 := by
    rw [centerMap_law_ordinary e μ d p hd hp, hwild]
  refine ⟨measurable_centerMap e μ d p hd hp,
    centerMap_equivariant e μ d p hd hp hde hpe O he ha', hbzero, a, ha, ?_⟩
  have hz : ∀ᵐ y ∂μ.map p, centerKernel e (condDistrib d p μ) y e.ordinary = 0 := by
    rw [← centerKernel_comp_map e μ d p hd hp,
      Measure.bind_apply e.measurableSet_ordinary (centerKernel e _).aemeasurable] at hbzero
    exact (lintegral_eq_zero_iff ((centerKernel e _).measurable_coe e.measurableSet_ordinary)).mp
      hbzero
  have hcd := condDistrib_centerMap e μ d p hd hp
  filter_upwards [hfib, hz, hcd] with y hy hyzero hycd
  obtain ⟨S, hS, hSa, hSm, hSc⟩ := hy
  have hSa' (b : G) (hb : b ∈ S) : centerKernel e (condDistrib d p μ) y {b} = a := by
    rw [centerKernel_apply, Measure.map_apply (e.measurable_center_fixed _)
      (measurableSet_singleton b)]
    exact hSa b hb
  refine ⟨S, hS, ?_, ?_, hSc, ?_⟩
  · intro b hb
    rw [hycd]
    exact hSa' b hb
  · rw [hycd, centerKernel_apply]
    exact (ae_map_iff (e.measurable_center_fixed _).aemeasurable S.measurableSet).mpr hSm
  · intro b hb hbC
    have hle : centerKernel e (condDistrib d p μ) y {b} ≤
        centerKernel e (condDistrib d p μ) y e.ordinary :=
      measure_mono (Set.singleton_subset_iff.mpr hbC)
    rw [hSa' b hb, hyzero] at hle
    exact (not_le_of_gt ha) hle

end EuclideanFiveColor.RelativeCenters

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor.RelativeCenters

instance dualStandardBorelSpace : StandardBorelSpace D := by
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  have : PolishSpace D := ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace
  infer_instance

instance dualMulDistribAction : MulDistribMulAction K D where
  smul_one u := (scalarHom (kCoeff u)).map_one
  smul_mul u d e := (scalarHom (kCoeff u)).map_mul d e

instance dualMeasurableConstSMul : MeasurableConstSMul K D where
  measurable_const_smul u := (continuous_scalar (kCoeff u)).measurable

noncomputable def ordinaryEmbedding : EuclideanFiveColor.CosetCenter.Embedding D :=
  ⟨jHom, j_measurableEmbedding⟩

@[simp] theorem ordinaryEmbedding_j (t : ℂ) : ordinaryEmbedding.j t = j t := rfl
@[simp] theorem ordinaryEmbedding_ordinary : ordinaryEmbedding.ordinary = C := rfl

noncomputable def frequencyIsometry (u : K) : ℂ →ₗᵢ[ℝ] ℂ where
  toFun z := conj (u.val : ℂ) * z
  map_add' _ _ := mul_add _ _ _
  map_smul' a z := by simp only [RingHom.id_apply, mul_smul_comm]
  norm_map' z := by
    change ‖conj (u.val : ℂ) * z‖ = ‖z‖
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]

noncomputable def frequencyRotation (u : K) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  (frequencyIsometry u).toLinearIsometryEquiv rfl

@[simp] theorem frequencyRotation_apply (u : K) (z : ℂ) :
    frequencyRotation u z = conj (u.val : ℂ) * z := rfl

theorem action_ordinaryEmbedding (u : K) (t : ℂ) :
    u • ordinaryEmbedding.j t = ordinaryEmbedding.j (frequencyRotation u t) :=
  scalar_j (kCoeff u) t

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

theorem wild_map_of_equivariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (hb : Measurable b)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hC : (μ.map b) C = 0) : IsWild (μ.map b) := by
  refine ⟨fun k => ⟨measurable_const_smul k, ?_⟩, hC⟩
  rw [Measure.map_map (measurable_const_smul k) hb]
  calc
    μ.map ((fun z : D => k • z) ∘ b) = μ.map (b ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hbe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map b :=
      (Measure.map_map hb (measurable_const_smul k)).symm
    _ = μ.map b := by rw [measurePreserving_smul k μ |>.map_eq]

theorem exact_finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hwild : IsWild (μ.map d))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) C) :
    ∃ b : X → D, Measurable b ∧
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) ∧
      IsWild (μ.map b) ∧
      ∃ a : ℝ≥0∞, 0 < a ∧
        ∀ᵐ y ∂μ.map p, ∃ S : Finset D, S.Nonempty ∧
          (∀ c ∈ S, condDistrib b p μ y {c} = a) ∧
          (∀ᵐ c ∂condDistrib b p μ y, c ∈ S) ∧
          (S.card : ℝ≥0∞) * a = 1 ∧
          (∀ c ∈ S, c ∉ C) := by
  obtain ⟨hbm, hbe, hbw, hfin⟩ := finite_center_reduction ordinaryEmbedding μ d p hd hp
    hde hpe frequencyRotation action_ordinaryEmbedding hwild.2 hpos
  exact ⟨centerMap ordinaryEmbedding μ d p, hbm, hbe,
    wild_map_of_equivariant μ _ hbm hbe hbw, hfin⟩

end PlaneFiveColor.Spectral

end

end OAI
