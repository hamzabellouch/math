import Mathlib
import OAI.Analysis.Conductivity.Branching.MeasurableDisjointGluing
import OAI.Analysis.Conductivity.Variational.CompactDepthReductionRegular

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
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem assemble_compatible_tensors
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hA : Measurable A)
    (R : ∀ i, CompactCompatibleReplacement μ (O i) u A) :
    ∃ (du : Coord3 → Fin 2 → ℝ) (dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
      (T : Coord3 → Symmetric3),
      ContDiff ℝ (↑(⊤ : ℕ∞)) du ∧ HasCompactSupport du ∧ tsupport du ⊆ ⋃ i, O i ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) dF ∧ HasCompactSupport dF ∧ tsupport dF ⊆ ⋃ i, O i ∧
      (∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0) ∧ Measurable T ∧
      (∀ i, EqOn du (R i).du (O i) ∧ EqOn dF (R i).dF (O i) ∧
        EqOn T (R i).tensor (O i)) ∧ EqOn T A (⋃ i, O i)ᶜ ∧
      (∀ x, conductivityFlux (fun y => u y+du y) T x = conductivityFlux u A x+dF x) := by
  obtain ⟨du, dF, hus, huc, hUs, hFs, hFc, hFS, hpair, heq, hoff⟩ :=
    assemble_compatible_replacements μ O hO hd u A R
  have hB (i : I) : ContinuousOn (R i).tensor (O i) :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (R i).smooth_tensor.continuousOn
  obtain ⟨T, hT, hTon, hToff⟩ := exists_measurable_disjoint_gluing O hO hd A hA
    (fun i => (R i).tensor) hB (A 0)
  refine ⟨du, dF, T, hus, huc, hUs, hFs, hFc, hFS, hpair, hT,
    fun i => ⟨(heq i).1, (heq i).2.1, hTon i⟩, hToff, ?_⟩
  intro x
  by_cases hx : x ∈ ⋃ i, O i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    simp only [conductivityFlux, hTon i hxi, (heq i).2.2 x hxi, (heq i).2.1 hxi]
    exact (R i).constitutive x hxi
  · have hxu : x ∉ tsupport du := fun hu => hx (hUs hu)
    have hder : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ u x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [(isClosed_tsupport du).isOpen_compl.mem_nhds hxu] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, add_zero]
    simp only [conductivityFlux, hToff hx, hder, (hoff x hx).2, add_zero]

end ScalarConductivity

end

end OAI
