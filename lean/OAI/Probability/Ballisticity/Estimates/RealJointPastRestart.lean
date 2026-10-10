import Mathlib
import OAI.Probability.Ballisticity.Estimates.JointPastRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma integral_partition_countable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] (μ : Measure Ω) (D : Ω → I) (hD : Measurable D)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ a, f a ∂μ) = ∑' i, ∫ a in D ⁻¹' {i}, f a ∂μ := by
  have hu : (⋃ i, D ⁻¹' {i}) = Set.univ := by ext a; simp
  have hd : Pairwise (fun i j : I => Disjoint (D ⁻¹' {i}) (D ⁻¹' {j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (hi.symm.trans hj)
  have hh := integral_iUnion (μ := μ) (fun i => hD (measurableSet_singleton i)) hd
    (show IntegrableOn f (⋃ i, D ⁻¹' {i}) μ by simpa only [hu,IntegrableOn,Measure.restrict_univ] using hf)
  simpa only [hu,Measure.restrict_univ] using hh

lemma integral_countable_restart {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (D : Ω → I) (Y : Ω → S) (κ : I → Measure S)
    [∀ i, IsProbabilityMeasure (κ i)]
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ i, (μ.restrict (D ⁻¹' {i})).map Y = μ (D ⁻¹' {i}) • κ i)
    (g : I → S → ℝ) (hg : ∀ i, Measurable (g i))
    (C : ℝ) (hC : ∀ i z, ‖g i z‖ ≤ C) :
    (∫ a, g (D a) (Y a) ∂μ) = ∫ a, (∫ z, g (D a) z ∂κ (D a)) ∂μ := by
  have hgm : Measurable (fun p : S × I => g p.2 p.1) :=
    measurable_from_prod_countable_left hg
  have hm : Measurable (fun a => g (D a) (Y a)) := hgm.comp (hY.prodMk hD)
  have hmb : ∀ i, ‖∫ z, g i z ∂κ i‖ ≤ C := fun i => by
    simpa using norm_integral_le_of_norm_le_const (μ := κ i) (Filter.Eventually.of_forall (hC i))
  have hri : Integrable (fun a => ∫ z, g (D a) z ∂κ (D a)) μ :=
    Integrable.of_bound ((measurable_of_countable (fun i => ∫ z, g i z ∂κ i)).comp hD).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun a => hmb (D a))
  rw [integral_partition_countable μ D hD _ (Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a => hC (D a) (Y a))),integral_partition_countable μ D hD _ hri]
  apply tsum_congr
  intro i
  have ha : ∀ᵐ a ∂μ.restrict (D ⁻¹' {i}), D a = i :=
    ae_restrict_mem (hD (measurableSet_singleton i))
  calc
    (∫ a in D ⁻¹' {i}, g (D a) (Y a) ∂μ) = ∫ a in D ⁻¹' {i}, g i (Y a) ∂μ :=
      integral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])
    _ = ∫ z, g i z ∂(μ.restrict (D ⁻¹' {i})).map Y := by
      rw [integral_map hY.aemeasurable (hg i).aestronglyMeasurable]
    _ = (μ (D ⁻¹' {i})).toReal * ∫ z, g i z ∂κ i := by
      rw [hrestart i,integral_smul_measure,smul_eq_mul]
    _ = ∫ a in D ⁻¹' {i}, (∫ z, g i z ∂κ i) ∂μ := by
      rw [integral_const,Measure.real,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,smul_eq_mul]
    _ = ∫ a in D ⁻¹' {i}, (∫ z, g (D a) z ∂κ (D a)) ∂μ :=
      integral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])

def boundaryTerminal {d : ℕ} (F : BoundaryData d) : Lattice d × Lattice d :=
  (extendPrefix F.1.1 F.2.1 F.1.1,extendPrefix F.1.2 F.2.2 F.1.2)

lemma boundaryTerminal_data {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    boundaryTerminal (boundaryData ℓ H P) =
      (P.1 (boundaryTimes ℓ H P).1,P.2 (boundaryTimes ℓ H P).2) := by
  simp [boundaryTerminal,boundaryData,pairPrefix,extendPrefix]

theorem shared_jointPast_real_restart {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (g : BoundaryData d → (Path d × Path d) → ℝ) (hg : ∀ i, Measurable (g i))
    (C : ℝ) (hC : ∀ i z, ‖g i z‖ ≤ C) :
    let D := boundaryData ℓ ((height x+H : ℤ) : ℝ)
    let Y := boundarySuffix ℓ ((height x+H : ℤ) : ℝ)
    (∫ P, g (D P) (Y P) ∂sharedConditionedPairLaw ν ℓ x y) =
      ∫ P, (∫ Q, g (D P) Q ∂sharedConditionedPairLaw ν ℓ
        (boundaryTerminal (D P)).1 (boundaryTerminal (D P)).2)
        ∂sharedConditionedPairLaw ν ℓ x y := by
  dsimp only
  let : IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ x y) :=
    sharedConditionedPairLaw_probability ν ℓ x y (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans x y))
  let : ∀ F : BoundaryData d, IsProbabilityMeasure
      (sharedConditionedPairLaw ν ℓ (boundaryTerminal F).1 (boundaryTerminal F).2) := fun F =>
    sharedConditionedPairLaw_probability ν ℓ _ _ (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans _ _))
  exact integral_countable_restart _ _ _ (fun F : BoundaryData d =>
      sharedConditionedPairLaw ν ℓ (boundaryTerminal F).1 (boundaryTerminal F).2) (measurable_boundaryData ℓ _)
    (measurable_boundarySuffix ℓ _)
    (shared_boundaryData_map ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH) g hg C hC

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma countable_restart_decorrelation {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (D : ℕ → Ω → I) (Y : ℕ → Ω → S) (κ : ℕ → I → Measure S)
    [∀ i j, IsProbabilityMeasure (κ i j)]
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y i))
    (hrestart : ∀ i j, ((μ i).restrict (D i ⁻¹' {j})).map (Y i) = (μ i) (D i ⁻¹' {j}) • κ i j)
    (V : ℕ → I → Prop) (hV : ∀ i, ∀ᵐ a ∂μ i, V i (D i a))
    (f : ℕ → I → ℝ) (g : ℕ → I → S → ℝ) (hg : ∀ i j, Measurable (g i j))
    (C M : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i j, ‖f i j‖ ≤ C) (hM : ∀ i j z, ‖g i j z‖ ≤ M)
    (hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ j, V i j → |∫ z, g i j z ∂κ i j| < ε) :
    Tendsto (fun i => ∫ a, f i (D i a) * g i (D i a) (Y i a) ∂μ i) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/(C+1) := div_pos hε (by positivity)
  filter_upwards [hunif (ε/(C+1)) he] with i hi
  have hr := integral_countable_restart (μ i) (D i) (Y i) (κ i) (hD i) (hY i) (hrestart i)
    (fun j z => f i j*g i j z) (fun j => (hg i j).const_mul _) (C*M)
    (fun j z => by rw [norm_mul]; exact mul_le_mul (hf i j) (hM i j z) (norm_nonneg _) hC)
  rw [hr]
  simp only [integral_const_mul]
  have hb : ‖∫ a, f i (D i a)*(∫ z, g i (D i a) z ∂κ i (D i a)) ∂μ i‖ ≤ C*(ε/(C+1)) := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ i)
      (f := fun a => f i (D i a)*(∫ z, g i (D i a) z ∂κ i (D i a)))
      (C := C*(ε/(C+1))) (hV i |>.mono fun a ha => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (hf i _) (le_of_lt (hi _ ha)) (abs_nonneg _) hC)
  rw [Real.dist_eq,sub_zero,← Real.norm_eq_abs]
  exact hb.trans_lt (by have := div_mul_cancel₀ ε (show C+1 ≠ 0 by positivity); nlinarith [div_pos hε (show 0 < C+1 by positivity)])

end DirectionalTransience

end

end

end OAI
