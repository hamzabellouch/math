import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift2

namespace OAI

/-! Measures and the conditional distance-set completion. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped Classical Topology ENNReal NNReal

noncomputable def assemblyPositiveEnergy (μ : Measure ℝ) (R : ℝ) : ℝ :=
  ∫ r in Icc (R/2) (2*R), ‖charFun μ r‖^2

lemma assemblyEnergy_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) :
    IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc (R/2) (2*R)) :=
  (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc

lemma assembly_norm_weighted_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) (z : ι → ℂ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ ∑ i ∈ s, (c i : ℝ) * ‖z i‖^2 := by
  have hn : ‖∑ i ∈ s, (c i : ℝ) • z i‖ ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      norm_sum_le s (fun i => (c i : ℝ) • z i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => (c i : ℝ)) (g := fun i => (c i : ℝ)*‖z i‖^2)
    (r := fun i => (c i : ℝ)*‖z i‖)
    (fun _ _ => NNReal.coe_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => by nlinarith)
  have hg : 0 ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖^2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsq : ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ (∑ i ∈ s, (c i : ℝ)*‖z i‖)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (hs.trans (by nlinarith))

lemma assembly_charFun_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (r : ℝ) :
    charFun (∑ i ∈ s, c i • τ i) r = ∑ i ∈ s, (c i : ℝ) • charFun (τ i) r := by
  simp only [charFun_eq_integral_innerProbChar]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_smul_nnreal_measure _ _
  · intro i hi
    exact (BoundedContinuousFunction.innerProbChar r).integrable _

lemma assemblyPositiveEnergy_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (R : ℝ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hτ : ∀ i∈s, assemblyPositiveEnergy (τ i) R ≤ C) :
    assemblyPositiveEnergy (∑ i∈s, c i • τ i) R ≤ C := by
  have hi : IntegrableOn (fun r => ∑ i∈s, (c i:ℝ)*‖charFun (τ i) r‖^2) (Icc (R/2) (2*R)) :=
    integrable_finsetSum s (fun i _ => (assemblyEnergy_integrable (τ i) R).const_mul _)
  have hpoint (r : ℝ) : ‖charFun (∑ i∈s,c i • τ i) r‖^2 ≤
      ∑ i∈s, (c i:ℝ)*‖charFun (τ i) r‖^2 := by
    rw [assembly_charFun_weighted_sum]
    exact assembly_norm_weighted_sum_sq_le s c _ hc
  calc
    _ ≤ ∫ r in Icc (R/2) (2*R), ∑ i∈s, (c i:ℝ)*‖charFun (τ i) r‖^2 :=
      integral_mono (assemblyEnergy_integrable _ R) hi hpoint
    _ = ∑ i∈s, (c i:ℝ)*assemblyPositiveEnergy (τ i) R := by
      rw [integral_finsetSum s (fun i _ => (assemblyEnergy_integrable (τ i) R).const_mul _)]
      simp only [integral_const_mul,assemblyPositiveEnergy]
    _ ≤ ∑ i∈s,(c i:ℝ)*C := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hτ i hi) (NNReal.coe_nonneg _))
    _ = (∑ i∈s,(c i:ℝ))*C := (Finset.sum_mul ..).symm
    _ ≤ C := by nlinarith

lemma assemblyPositiveEnergy_sum {ι : Type*} [Fintype ι]
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (R C : ℝ)
    (hτ : ∀ i, assemblyPositiveEnergy (τ i) R ≤ C) :
    assemblyPositiveEnergy (∑ i,τ i) R ≤ (Fintype.card ι:ℝ)^2*C := by
  have hi : IntegrableOn (fun r => (Fintype.card ι:ℝ)*∑ i,‖charFun (τ i) r‖^2)
      (Icc (R/2) (2*R)) :=
    (integrable_finsetSum _ (fun i _ => assemblyEnergy_integrable (τ i) R)).const_mul _
  have he (r : ℝ) : charFun (∑ i,τ i) r = ∑ i,charFun (τ i) r := by
    simpa only [one_smul,NNReal.coe_one] using
      assembly_charFun_weighted_sum Finset.univ (fun _ => 1) τ r
  have hp (r : ℝ) : ‖charFun (∑ i,τ i) r‖^2 ≤
      (Fintype.card ι:ℝ)*∑ i,‖charFun (τ i) r‖^2 := by
    rw [he]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ:Finset ι)
      (f:=fun _ => (1:ℝ)) (g:=fun i => ‖charFun (τ i) r‖^2)
      (r:=fun i => ‖charFun (τ i) r‖) (fun _ _ => zero_le_one)
      (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh
  calc
    _ ≤ ∫ r in Icc (R/2) (2*R), (Fintype.card ι:ℝ)*∑ i,‖charFun (τ i) r‖^2 :=
      integral_mono (assemblyEnergy_integrable _ R) hi hp
    _ = (Fintype.card ι:ℝ)*∑ i,assemblyPositiveEnergy (τ i) R := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => assemblyEnergy_integrable (τ i) R)]
      rfl
    _ ≤ (Fintype.card ι:ℝ)*∑ _ : ι,C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hτ i)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma assemblyEnergy_two_sided (μ : Measure ℝ) [IsFiniteMeasure μ] {R : ℝ} (hR : 0<R) :
    (∫ r in {r : ℝ | R/2≤|r| ∧ |r|≤2*R}, ‖charFun μ r‖^2) =
      2*assemblyPositiveEnergy μ R := by
  let a := R/2
  let b := 2*R
  have ha : 0<a := by dsimp[a]; positivity
  have hsets : {r : ℝ | R/2≤|r| ∧ |r|≤2*R}=Icc a b ∪ Icc (-b) (-a) := by
    ext r
    change (a≤|r| ∧ |r|≤b) ↔ (a≤r ∧ r≤b) ∨ (-b≤r ∧ r≤-a)
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · rintro (h|h)
        · exact h
        · exfalso; linarith
    · rw [abs_of_nonpos h]
      constructor
      · intro h; right; constructor <;> linarith
      · rintro(h|h)
        · exfalso; linarith
        · constructor <;> linarith
  have hdis : Disjoint (Icc a b) (Icc (-b) (-a)) := by
    apply Set.disjoint_left.mpr
    intro r h₀ h₁
    have := h₀.1
    have := h₁.2
    linarith
  have hi (c d : ℝ) : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc c d) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hneg : (∫ r in Icc (-b) (-a), ‖charFun μ r‖^2) = ∫ r in Icc a b, ‖charFun μ r‖^2 := by
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    have h := hemb.setIntegral_map (μ := (volume : Measure ℝ))
      (fun r => ‖charFun μ r‖^2) (Icc (-b) (-a))
    rw [Measure.map_neg_eq_self] at h
    have hp : (fun x : ℝ => -x) ⁻¹' Icc (-b) (-a) = Icc a b := by
      ext x
      simp only [mem_preimage,mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith
    simpa only [hp,charFun_neg,Complex.norm_conj] using h
  rw [hsets,setIntegral_union hdis measurableSet_Icc (hi a b) (hi (-b) (-a)),hneg]
  unfold assemblyPositiveEnergy
  dsimp only [a,b]
  ring
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
