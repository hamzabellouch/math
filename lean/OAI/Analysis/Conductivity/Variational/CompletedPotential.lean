import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
namespace ScalarConductivity

def completedPotential {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (D : E →L[ℝ] F) (Q : F →L[ℝ] E) (y : E) : E :=
  Q (u y) + y - Q (D y)

lemma completedPotential_pairing {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (D : E →L[ℝ] F) (Q : F →L[ℝ] E)
    (hQ : Function.RightInverse Q D) (y : E) :
    D (completedPotential u D Q y) = u y := by
  simp only [completedPotential, map_sub, map_add, hQ (u y), hQ (D y)]
  abel

lemma completedPotential_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (D : E →L[ℝ] F) (Q : F →L[ℝ] E) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (completedPotential u D Q) :=
  ((Q.contDiff.comp hu).add contDiff_id).sub (Q.contDiff.comp D.contDiff)

lemma completedPotential_derivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {D : E →L[ℝ] F} {a : E} (hu : HasFDerivAt u D a)
    (Q : F →L[ℝ] E) :
    HasFDerivAt (completedPotential u D Q) (ContinuousLinearMap.id ℝ E) a := by
  convert ((Q.hasFDerivAt.comp a hu).add (hasFDerivAt_id a)).sub
    (Q.hasFDerivAt.comp a D.hasFDerivAt) using 1
  · rfl
  · abel

theorem exists_potential_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : E → F} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (a : E)
    (hD : Function.Surjective (fderiv ℝ u a)) {U : Set E} (hU : IsOpen U) (ha : a ∈ U) :
    ∃ X : OpenPartialHomeomorph E E,
      a ∈ X.source ∧ X.source ⊆ U ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      (∀ y, (fderiv ℝ u a) (X y) = u y) ∧
      fderiv ℝ X a = ContinuousLinearMap.id ℝ E := by
  let D := fderiv ℝ u a
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let f := completedPotential u D Q
  have hf := completedPotential_smooth hu D Q
  have hfa : HasFDerivAt f (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) a :=
    completedPotential_derivative ((hu.differentiable (by simp) a).hasFDerivAt) Q
  let X₀ := hf.contDiffAt.toOpenPartialHomeomorph f hfa (by simp)
  let V := U ∩ {y | IsUnit (fderiv ℝ f y)}
  have hV : IsOpen V := hU.inter (Units.isOpen.preimage (hf.continuous_fderiv (by simp)))
  have haV : a ∈ V := ⟨ha, by change IsUnit (fderiv ℝ f a); rw [hfa.fderiv]; exact isUnit_one⟩
  let X := X₀.restr V
  have hXeq : (X : E → E) = f := rfl
  have hsource : X.source = X₀.source ∩ V := by
    simp only [X, OpenPartialHomeomorph.restr_source, hV.interior_eq]
  have hinv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target := by
    intro y hy
    have hx : X.symm y ∈ V := (hsource ▸ X.map_target hy).2
    obtain ⟨v, hv⟩ := hx.2
    let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit v
    have he : (e : E →L[ℝ] E) = fderiv ℝ X (X.symm y) := by
      change (v : E →L[ℝ] E) = _
      simpa only [hXeq] using hv
    have hd : HasFDerivAt X (e : E →L[ℝ] E) (X.symm y) := by
      rw [he, hXeq]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    exact (X.contDiffAt_symm hy hd (hXeq ▸ hf.contDiffAt)).contDiffWithinAt
  refine ⟨X, ?_, ?_, ?_, hinv, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfa (by simp), haV⟩
  · rw [hsource]
    exact fun _ hx => hx.2.1
  · rw [hXeq]
    exact hf
  · intro y
    exact completedPotential_pairing u D Q hQ y
  · exact hfa.fderiv

end ScalarConductivity

end

end OAI
