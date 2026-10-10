import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

abbrev SmoothRealTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {φ : E → ℝ // ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}

lemma countable_weak_derivative_tests (v : E) :
    ∃ S : Set (SmoothRealTest E), S.Countable ∧
      ∀ (f g : E → ℂ), MemLp f 2 → MemLp g 2 →
      (∀ φ ∈ S, (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ.val x v)) =
        -(∫ x, g x * (φ.val x : ℂ))) → IsWeakDerivative v f g := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let V := WeakGraphAmbient E Unit
  let L : SmoothRealTest E → V →L[ℂ] ℂ := fun φ =>
    weakGraphTest (fun _ : Unit => v) () φ.val φ.property.1 φ.property.2
  obtain ⟨S, hS, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun φ : SmoothRealTest E => ((L φ).ker : Set V)ᶜ) (fun φ => (L φ).isClosed_ker.isOpen_compl)
  refine ⟨S, hS, ?_⟩
  intro f g hf hg htest
  let A : V := WithLp.toLp 2 (fun j : Option Unit =>
    match j with | none => hf.toLp f | some _ => hg.toLp g)
  have hAS (φ : SmoothRealTest E) (hφ : φ ∈ S) : A ∈ (L φ).ker := by
    change l2Test _ _ (hf.toLp f) + l2Test _ _ (hg.toLp g) = 0
    rw [l2Test_apply, l2Test_apply]
    have h1 := integral_congr_ae (hf.coeFn_toLp.mono fun x hx =>
      congrArg (· * Complex.ofReal (lineDeriv ℝ φ.val x v)) hx)
    have h2 := integral_congr_ae (hg.coeFn_toLp.mono fun x hx =>
      congrArg (· * (φ.val x : ℂ)) hx)
    rw [h1, h2, htest φ hφ, neg_add_cancel]
  have hAll (φ : SmoothRealTest E) : A ∈ (L φ).ker := by
    by_contra hn
    have hm : A ∈ ⋃ φ : SmoothRealTest E, ((L φ).ker : Set V)ᶜ := Set.mem_iUnion.mpr ⟨φ, hn⟩
    rw [← hcover] at hm
    obtain ⟨ψ, hψ⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hψS, hψA⟩ := Set.mem_iUnion.mp hψ
    exact hψA (hAS ψ hψS)
  intro φ hφ hcφ
  have hh := hAll ⟨φ, hφ, hcφ⟩
  change l2Test _ _ (hf.toLp f) + l2Test _ _ (hg.toLp g) = 0 at hh
  rw [l2Test_apply, l2Test_apply] at hh
  have h1 := integral_congr_ae (hf.coeFn_toLp.mono fun x hx =>
    congrArg (· * Complex.ofReal (lineDeriv ℝ φ x v)) hx)
  have h2 := integral_congr_ae (hg.coeFn_toLp.mono fun x hx =>
    congrArg (· * (φ x : ℂ)) hx)
  rw [h1, h2] at hh
  exact eq_neg_of_add_eq_zero_left hh

end CoulombAtom

end

end OAI
