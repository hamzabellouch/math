import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.OuterJoinConfiguration
import OAI.Analysis.CoulombRadii.FieldAnalysis.SliceExpectation

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_add {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x)) :
    sliceExpectation ψ (fun s x => f s x+g s x) = sliceExpectation ψ f + sliceExpectation ψ g := by
  simp only [sliceExpectation, mul_add, integral_add (hf _) (hg _), Finset.sum_add_distrib]
lemma sliceExpectation_sub {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x)) :
    sliceExpectation ψ (fun s x => f s x-g s x) = sliceExpectation ψ f - sliceExpectation ψ g := by
  simp only [sliceExpectation, mul_sub, integral_sub (hf _) (hg _), Finset.sum_sub_distrib]
lemma sliceExpectation_const_mul {m k : ℕ} (ψ : H1Vector (m+k))
    (c : ℝ) (f : Spins m → Configuration m → ℝ) :
    sliceExpectation ψ (fun s x => c*f s x) = c*sliceExpectation ψ f := by
  simp only [sliceExpectation, mul_left_comm (mass _) c, integral_const_mul, Finset.mul_sum]
lemma sliceExpectation_mono_ae {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x))
    (h : ∀ s, ∀ᵐ x, f s x ≤ g s x) : sliceExpectation ψ f ≤ sliceExpectation ψ g := by
  exact Finset.sum_le_sum fun s _ => integral_mono_ae (hf s) (hg s)
    ((h s).mono fun x hx => mul_le_mul_of_nonneg_left hx (mass_nonneg _))

lemma normalized_coreForm_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*form S (ψ.coreSlice s x).normalized) := by
  simp only [form_normalized_weight]
  exact form_coreSlice_integrable S ψ s

lemma retainedFinePower_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*retainedFinePower b r x) := by
  apply slice_weight_integrable_const ψ
  simpa only [outerJoinConfiguration_symm_snd] using outer_finePower_integrable hb r hr ψ
lemma retainedFineCoulomb_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*retainedFineCoulomb b r x) := by
  apply slice_weight_integrable_const ψ
  simpa only [outerJoinConfiguration_symm_snd] using outer_fineCoulomb_integrable hb r hr ψ
lemma outerPair_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*pairPotential x) :=
  slice_weight_integrable_const ψ pairPotential ψ.outer_pair_integrable s

def deletedLabels {m : ℕ} (r : Configuration m → Finset (Fin m)) (x : Configuration m) : Finset (Fin m) :=
  Finset.univ \ r x
lemma deletedLabels_measurable {m : ℕ} (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (i : Fin m) :
    MeasurableSet {x | i ∈ deletedLabels r x} := by
  have he : {x | i ∈ deletedLabels r x} = {x | i ∈ r x}ᶜ := by ext x; simp [deletedLabels]
  rw [he]; exact (hr i).compl
lemma retained_deleted_sum {m : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (f : Fin m → ℝ) :
    (∑ i ∈ r x, f i) + (∑ i ∈ deletedLabels r x, f i) = ∑ i : Fin m, f i := by
  simpa only [add_comm, deletedLabels] using Finset.sum_sdiff (f:=f) (Finset.subset_univ (r x))

def discreteFineTF {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (b : ℝ) (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m) : ℝ :=
  thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x -
    ∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)

def fineLocalizationError (m : ℕ) (b : ℝ) : ℝ :=
  (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (m:ℝ)^(4/3:ℝ) + ((2*Real.pi+1)/(2*b))*m

lemma discreteFineTF_weight_integrable {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*discreteFineTF S ψ b r s x) := by
  simp only [discreteFineTF, mul_sub, mul_add, mul_left_comm (mass _) thomasFermiCoefficient]
  exact (((retainedFinePower_weight_integrable ψ hb r hr s).const_mul _).add
    (retainedFineCoulomb_weight_integrable ψ hb r hr s)).sub
    (retained_field_weight_integrable S ψ r hr s)

lemma fine_energy_expectation_lower {m k : ℕ} (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    sliceExpectation ψ (fun _ x => thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x) -
      fineLocalizationError m b*mass ψ ≤ outerKinetic ψ + sliceExpectation ψ (fun _ x => pairPotential x) := by
  rw [sliceExpectation_add ψ _ _
      (fun s => by simpa only [mul_left_comm (mass _) thomasFermiCoefficient] using
        (retainedFinePower_weight_integrable ψ hb r hr s).const_mul thomasFermiCoefficient)
      (retainedFineCoulomb_weight_integrable ψ hb r hr), sliceExpectation_const_mul]
  rw [sliceExpectation_const ψ _ (by simpa only [outerJoinConfiguration_symm_snd] using outer_finePower_integrable hb r hr ψ),
    sliceExpectation_const ψ _ (by simpa only [outerJoinConfiguration_symm_snd] using outer_fineCoulomb_integrable hb r hr ψ),
    sliceExpectation_const ψ _ ψ.outer_pair_integrable]
  simpa only [outerJoinConfiguration_symm_snd, fineLocalizationError] using
    outer_block_retained_fine_energy_lower ψ hψ hb r hr

theorem conditional_fine_lower {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x) :
    sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) -
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) - fineLocalizationError m b*mass ψ ≤ form S ψ := by
  let P := fun s x => ∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)
  let D := fun s x => ∑ i ∈ deletedLabels r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)
  let A := fun (_ : Spins m) x => thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x
  let e := fun s x => form S (ψ.coreSlice s x).normalized
  have hPi := retained_field_weight_integrable S ψ r hr
  have hDi := retained_field_weight_integrable S ψ (deletedLabels r) (deletedLabels_measurable r hr)
  have hAi (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*A s x) := by
    dsimp only [A]; simp only [mul_add, mul_left_comm (mass _) thomasFermiCoefficient]
    exact ((retainedFinePower_weight_integrable ψ hb r hr s).const_mul _).add
      (retainedFineCoulomb_weight_integrable ψ hb r hr s)
  have hei := normalized_coreForm_weight_integrable S ψ
  have heq (s : Spins m) (x : Configuration m) : conditionalEnergy S ψ s x =
      (e s x-P s x)+pairPotential x-D s x := by
    rw [conditionalEnergy_eq_screened, ←retained_deleted_sum r x]
    dsimp only [e, P, D]; ring
  have hE : form S ψ = outerKinetic ψ +
      (sliceExpectation ψ e-sliceExpectation ψ P)+sliceExpectation ψ (fun _ x => pairPotential x)-sliceExpectation ψ D := by
    rw [conditional_energy_identity]
    change outerKinetic ψ + sliceExpectation ψ (conditionalEnergy S ψ) = _
    conv_lhs => rw [show conditionalEnergy S ψ = (fun s x => (e s x-P s x)+pairPotential x-D s x) by funext s x; exact heq s x]
    rw [sliceExpectation_sub ψ _ _
        (fun s => by
          apply ((hei s |>.sub (hPi s)).add (outerPair_weight_integrable ψ s)).congr
          exact Eventually.of_forall (fun x => by dsimp [e,P]; ring)) hDi,
      sliceExpectation_add ψ _ _ (fun s => by
        apply ((hei s).sub (hPi s)).congr
        exact Eventually.of_forall (fun x => by dsimp [e,P]; ring))
        (outerPair_weight_integrable ψ), sliceExpectation_sub ψ e P hei hPi]
    ring
  have hD : sliceExpectation ψ D ≤ sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) := by
    apply sliceExpectation_mono_ae ψ _ _ hDi hFi
    intro s
    filter_upwards [hcap s] with x hx
    calc D s x ≤ ∑ i ∈ deletedLabels r x, F s x := Finset.sum_le_sum hx
      _ = F s x*(deletedLabels r x).card := by simp; ring
  have hL := fine_energy_expectation_lower ψ hψ hb r hr
  have hT : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) =
      sliceExpectation ψ e + (sliceExpectation ψ A-sliceExpectation ψ P) := by
    change sliceExpectation ψ (fun s x => e s x+(A s x-P s x)) = _
    rw [sliceExpectation_add ψ e _ hei (fun s => by
        apply ((hAi s).sub (hPi s)).congr
        exact Eventually.of_forall (fun x => by dsimp [A,P]; ring)),
      sliceExpectation_sub ψ A P hAi hPi]
  rw [hT, hE]
  change sliceExpectation ψ A -fineLocalizationError m b*mass ψ ≤ _ at hL
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
