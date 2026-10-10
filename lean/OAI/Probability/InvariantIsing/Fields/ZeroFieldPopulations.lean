import OAI.Probability.InvariantIsing.Magnetic.MagneticGeneralSpectrum
import OAI.Probability.InvariantIsing.Fields.PhysicalFieldPopulationComparison

namespace OAI

/-! Vanishing field populations can be relabeled into a positive population. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

lemma spectralLabelCount_eq_spinGroupSize {N : ℕ} {A : Type*} [DecidableEq A]
    (g : Fin N → A) (a : A) : spectralLabelCount g a=spinGroupSize g a := by
  unfold spectralLabelCount spinGroupSize
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

def positiveFieldProjection {A : Type*} (γ : A → ℝ) (fallback : {a // 0 < γ a}) (a : A) : A :=
  (positiveSpectralLabel γ fallback a).val

lemma positiveFieldProjection_weight {A : Type*} [Fintype A]
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (fallback : {a // 0 < γ a}) (b : A) :
    (∑ a : {a // positiveFieldProjection γ fallback a=b}, γ a)=γ b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => positiveFieldProjection γ fallback a=b))
    (by simp) γ,Finset.sum_filter]
  have hi a : (if positiveFieldProjection γ fallback a=b then γ a else 0)=
      (if a=b then γ a else 0) := by
    by_cases hp : 0 < γ a
    · simp only [positiveFieldProjection,positiveSpectralLabel,dite_eq_left hp]
    · have hz : γ a=0 := le_antisymm (le_of_not_gt hp) (hγ a)
      simp only [hz,ite_self]
  simp_rw [hi]
  simp

lemma positiveFieldProjection_counts {A : Type*} [Fintype A]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → A)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (fallback : {a // 0 < γ a})
    (hg : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 γ)) :
    Tendsto (fun k a => (spectralLabelCount (positiveFieldProjection γ fallback ∘ g k) a : ℝ)/N k)
      atTop (𝓝 γ) := by
  have hh := spectral_label_counts_relabel N g γ hg (positiveFieldProjection γ fallback)
  simpa only [positiveFieldProjection_weight γ hγ fallback] using hh

lemma physical_mean_zero_field_populations {A : Type*} [Fintype A] [DecidableEq A]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (g : (N : ℕ) → Fin N → A) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (fallback : {a // 0 < γ a})
    (hg : Tendsto (fun N a => (spinGroupSize (g N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => (∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹) (fun i => c (g N i)) ∂μ N)-
      ∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹)
        (fun i => c (positiveFieldProjection γ fallback (g N i))) ∂μ N) atTop (𝓝 0) := by
  let h := fun N => positiveFieldProjection γ fallback ∘ g N
  have hh : Tendsto (fun N a => (spinGroupSize (h N) a : ℝ)/N) atTop (𝓝 γ) := by
    have hh := positiveFieldProjection_counts id g γ hγ fallback
      (by simpa only [spectralLabelCount_eq_spinGroupSize,id_eq] using hg)
    simpa only [spectralLabelCount,spinGroupSize,id_eq,h] using hh
  let B := ∑ a, |c a|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hc a : |c a| ≤ B := Finset.single_le_sum (f := fun a => |c a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have ht := ((tendsto_finsetSum Finset.univ (fun a _ =>
    (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs)).const_mul (2*B))
  simp only [sub_self,abs_zero,Finset.sum_const_zero,mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa only [Real.norm_eq_abs,h,Function.comp_apply] using physical_mean_field_counts_le (by omega) (μ N)
    (eig N) (g N) (h N) c hB hc

end InvariantIsing

end

end OAI
