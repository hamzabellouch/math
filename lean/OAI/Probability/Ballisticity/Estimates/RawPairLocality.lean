import Mathlib
import OAI.Probability.Ballisticity.Walk.RawPairKernel

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def variableHitKernel {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    Kernel (Environment d × Lattice d) (Lattice d) where
  toFun p := hitKernel (Strip ℓ p.2 H) (Upper ℓ p.2 H) p
  measurable' := measurable_from_prod_countable_left fun x =>
    (hitKernel (Strip ℓ x H) (Upper ℓ x H)).measurable.comp (measurable_id.prodMk measurable_const)

instance variableHitKernel_finite {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    IsFiniteKernel (variableHitKernel ℓ H) where
  exists_univ_le := by
    refine ⟨1,ENNReal.one_lt_top,fun p => ?_⟩
    change hitKernel (Strip ℓ p.2 H) (Upper ℓ p.2 H) p Set.univ ≤ 1
    exact hitKernel_total_le_one (disjoint_strip_upper ℓ p.2 H) p

noncomputable def variablePairHitKernel {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    Kernel (Environment d × (Lattice d × Lattice d)) (Lattice d × Lattice d) :=
  ((variableHitKernel ℓ H).comap (fun p => (p.1,p.2.1)) (by fun_prop)).prod
    ((variableHitKernel ℓ H).comap (fun p => (p.1,p.2.2)) (by fun_prop))

instance variablePairHitKernel_finite {d : ℕ} (ℓ : Vector d) (H : ℕ) :
    IsFiniteKernel (variablePairHitKernel ℓ H) := by unfold variablePairHitKernel; infer_instance

lemma variablePairHitKernel_apply {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    variablePairHitKernel ℓ H (ω,x) = rawPairEndpointLaw ℓ H ω x := by
  simp only [variablePairHitKernel,Kernel.prod_apply,Kernel.comap_apply]
  rfl

lemma rawPairEndpointLaw_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) {S : Set (Lattice d)}
    (h₁ : Strip ℓ x.1 H ⊆ S) (h₂ : Strip ℓ x.2 H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => rawPairEndpointLaw ℓ H ω x) := by
  have hx (y : Lattice d) : y ∈ Strip ℓ y H := ⟨le_rfl,by exact lt_add_of_pos_right _ (by exact_mod_cast hH)⟩
  let : MeasurableSpace (Environment d) := rowSigma S
  let κ₁ : Kernel (Environment d) (Lattice d) :=
    ⟨fun ω => hitKernel (Strip ℓ x.1 H) (Upper ℓ x.1 H) (ω,x.1),
      (measurable_hitKernel_rows _ _ _ (hx x.1)).mono (rowSigma_mono h₁) le_rfl⟩
  let κ₂ : Kernel (Environment d) (Lattice d) :=
    ⟨fun ω => hitKernel (Strip ℓ x.2 H) (Upper ℓ x.2 H) (ω,x.2),
      (measurable_hitKernel_rows _ _ _ (hx x.2)).mono (rowSigma_mono h₂) le_rfl⟩
  have : @IsFiniteKernel (Environment d) (Lattice d) (rowSigma S) _ κ₁ :=
    ⟨⟨1,ENNReal.one_lt_top,fun ω => hitKernel_total_le_one (disjoint_strip_upper ℓ x.1 H) (ω,x.1)⟩⟩
  have : @IsFiniteKernel (Environment d) (Lattice d) (rowSigma S) _ κ₂ :=
    ⟨⟨1,ENNReal.one_lt_top,fun ω => hitKernel_total_le_one (disjoint_strip_upper ℓ x.2 H) (ω,x.2)⟩⟩
  have hm := (κ₁.prod κ₂).measurable
  change @Measurable _ _ (rowSigma S) _ (fun ω => (κ₁ ω).prod (κ₂ ω))
  convert hm using 1
  funext ω
  exact (Kernel.prod_apply κ₁ κ₂ ω).symm

lemma rawPairEndpointLaw_total_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    rawPairEndpointLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawPairEndpointLaw,←Set.univ_prod_univ,Measure.prod_prod]
  exact (mul_le_of_le_one_left (by positivity)
    (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)).trans
      (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)

noncomputable def pairKernelMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ≥0∞ :=
  ∫⁻ x, rawPairEndpointLaw ℓ H ω x {y | z ≤ signedCoordinate f (y.2-y.1)} ∂π

lemma measurable_pairKernelMass {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ) (z : ℝ) :
    Measurable (fun p : Measure (Lattice d × Lattice d) × Environment d => pairKernelMass ℓ f H z p.1 p.2) := by
  simp only [pairKernelMass,lintegral_countable']
  apply Measurable.tsum
  intro x
  have harg : Measurable (fun p : Measure (Lattice d × Lattice d) × Environment d => (p.2,x)) :=
    measurable_snd.prodMk measurable_const
  have hset : MeasurableSet {y : Lattice d × Lattice d | z ≤ signedCoordinate f (y.2-y.1)} :=
    (Set.to_countable _).measurableSet
  have hbase : Measurable (fun q : Environment d × (Lattice d × Lattice d) =>
      variablePairHitKernel ℓ H q {y | z ≤ signedCoordinate f (y.2-y.1)}) :=
    Kernel.measurable_coe (variablePairHitKernel ℓ H) hset
  have hm := hbase.comp harg
  simp only [Function.comp_def,variablePairHitKernel_apply] at hm
  exact hm.mul ((Measure.measurable_coe (measurableSet_singleton x)).comp measurable_fst)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma pairKernelMass_le_one {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) : pairKernelMass ℓ f H z π ω ≤ 1 := by
  calc
    pairKernelMass ℓ f H z π ω ≤ ∫⁻ _ : Lattice d × Lattice d, (1:ℝ≥0∞) ∂π := by
      apply lintegral_mono
      intro x
      exact (measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one ℓ H ω x)
    _ = 1 := by simp

lemma pairKernelMass_toReal {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    (pairKernelMass (realPosition (step e)) f H z π ω).toReal =
      rawPairEndpointMass (realPosition (step e)) f H z π ω := by
  unfold pairKernelMass
  rw [←integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun x => lt_of_le_of_lt
      ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ x)) ENNReal.one_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rawPairEndpointLaw_eq e f x hH]
  rfl

lemma pairKernelMass_lower_iff {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) {g : ℝ} (_ : 0 ≤ g) :
    ENNReal.ofReal g ≤ pairKernelMass (realPosition (step e)) f H z π ω ↔
      g ≤ rawPairEndpointMass (realPosition (step e)) f H z π ω := by
  have hn := ne_top_of_le_ne_top ENNReal.one_ne_top (pairKernelMass_le_one (realPosition (step e)) f H z π ω)
  rw [←pairKernelMass_toReal e f hH z π ω]
  exact ENNReal.ofReal_le_iff_le_toReal hn

abbrev SupportedPairMeasures {d : ℕ} (C : Set (Lattice d × Lattice d)) :=
  {π : Measure (Lattice d × Lattice d) // π Cᶜ = 0}

lemma supportedPairMeasures_singleton {d : ℕ} (C : Set (Lattice d × Lattice d))
    (π : SupportedPairMeasures C) {x : Lattice d × Lattice d} (hx : x ∉ C) : π.val {x} = 0 := by
  apply le_antisymm _ (by positivity)
  calc
    π.val {x} ≤ π.val Cᶜ := measure_mono (Set.singleton_subset_iff.mpr hx)
    _ = 0 := π.property

lemma pairKernelMass_joint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (C : Set (Lattice d × Lattice d))
    (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => pairKernelMass ℓ f H z p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [pairKernelMass,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm : @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞ _ _
        (fun p => rawPairEndpointLaw ℓ H p.2 x {y | z ≤ signedCoordinate f (y.2-y.1)}) :=
      ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
        (rawPairEndpointLaw_rows ℓ x hH (hC x hx).1 (hC x hx).2)).comp measurable_snd
    exact hm.mul ((Measure.measurable_coe (measurableSet_singleton x)).comp
      (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedPairMeasures C × Environment d =>
        rawPairEndpointLaw ℓ H p.2 x {y | z ≤ signedCoordinate f (y.2-y.1)}*p.1.val {x}) =
        fun _ => 0 := by
      funext p
      rw [supportedPairMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const
end DirectionalTransience

end

end

end OAI
