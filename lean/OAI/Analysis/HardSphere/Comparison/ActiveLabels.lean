import Mathlib
import OAI.Analysis.HardSphere.Geometry.ParticleGradSq

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def activeLabels {α ι : Type*} [Fintype α] (σ : α → ι) : Finset α := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ j, j≠i ∧ σ j=σ i)

lemma mem_activeLabels {α ι : Type*} [Fintype α] (σ : α → ι) (i : α) :
    i∈activeLabels σ ↔ ∃ j, j≠i ∧ σ j=σ i := by
  classical
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma inactive_card_le {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (σ : α → ι) :
    (activeLabels σ)ᶜ.card≤Fintype.card ι := by
  classical
  apply Finset.card_le_card_of_injOn σ (by simp)
  intro a ha b _ hab
  by_contra hne
  have ha' : a∉activeLabels σ := Finset.mem_compl.mp ha
  apply ha'
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨b,(fun h ↦ hne h.symm),hab.symm⟩

lemma active_card_lower {α ι : Type*} [Fintype α] [Fintype ι] (σ : α → ι) :
    Fintype.card α-Fintype.card ι≤(activeLabels σ).card := by
  classical
  have h := inactive_card_le σ
  rw [Finset.card_compl] at h
  have hc := (activeLabels σ).card_le_univ
  omega

lemma sector_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) {ι : Type*} [Fintype ι]
    (b : ι → Point) (σ : Fin (n+1) → ι)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ((n+1-Fintype.card ι : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  classical
  let μ := Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))
  let M := ∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂μ
  let G := fun i ↦ ∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂μ
  let C := ENNReal.ofReal (Real.sqrt 3*l^3/r)
  have hi (i : Fin (n+1)) (hi : i∈activeLabels σ) : M≤C*G i := by
    obtain ⟨j,hji,hs⟩ := (mem_activeLabels σ i).mp hi
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
    exact sector_coordinate_capacity hF hr hl (fun a ↦ b (σ a)) i k (congrArg b hs) hz
  have hs := Finset.sum_le_sum hi
  have hcard := active_card_lower σ
  rw [Fintype.card_fin] at hcard
  calc
    _ ≤ ((activeLabels σ).card : ℝ≥0∞)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = ∑ _ ∈ activeLabels σ, M := by simp
    _ ≤ ∑ i ∈ activeLabels σ, C*G i := hs
    _ = C*∑ i ∈ activeLabels σ, G i := (Finset.mul_sum _ _ _).symm
    _ ≤ C*∑ i, G i := by gcongr; exact Finset.subset_univ _
    _ = _ := rfl

end HardSphere.SphericalCoordinates

end

end OAI
