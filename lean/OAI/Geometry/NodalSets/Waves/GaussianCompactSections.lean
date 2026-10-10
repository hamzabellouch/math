import Mathlib.Topology.ContinuousMap.Compact
import OAI.Geometry.NodalSets.Elliptic.RescaledDerivativeMoments

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X] [CompactSpace X]

def pairSection (seed : C(X,ℝ)) (Z : ι → C(X,ℂ)) (a : ι × Fin 2 → ℝ) : C(X,ℝ) :=
  seed + ∑ p : ι × Fin 2, a p •
    (if p.2 = 0 then ⟨fun x ↦ (Z p.1 x).re, Complex.continuous_re.comp (Z p.1).continuous⟩
    else ⟨fun x ↦ -(Z p.1 x).im, (Complex.continuous_im.comp (Z p.1).continuous).neg⟩)

omit [CompactSpace X] in
lemma pairSection_apply (seed : C(X,ℝ)) (Z : ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) (x : X) :
    pairSection seed Z a x = seed x+pairLinearSum (fun i ↦ Z i x) a := by
  classical
  simp only [pairSection,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,pairLinearSum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [smul_eq_mul,mul_comm]

lemma pairSection_continuous (seed : C(X,ℝ)) (Z : ι → C(X,ℂ)) :
    Continuous (pairSection seed Z) := by
  unfold pairSection
  exact continuous_const.add (continuous_finsetSum _ (fun p _ ↦
    (continuous_apply p).smul continuous_const))

lemma pairSection_integrable (seed : C(X,ℝ)) (Z : ι → C(X,ℂ)) :
    Integrable (pairSection seed Z) gaussianPairs := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  unfold pairSection
  apply (integrable_const (μ := gaussianPairs (ι := ι)) seed).add
  apply integrable_finsetSum
  intro p _
  exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
    (i := p) IsGaussian.integrable_id).smul_const _

lemma pairSection_sup_integrable (seed : C(X,ℝ)) (Z : ι → C(X,ℂ)) :
    Integrable (fun a ↦ ‖pairSection seed Z a‖) gaussianPairs :=
  (pairSection_integrable seed Z).norm

lemma pairSection_norm_le_iff (seed : C(X,ℝ)) (Z : ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ‖pairSection seed Z a‖ ≤ C ↔ ∀ x, |seed x+pairLinearSum (fun i ↦ Z i x) a| ≤ C := by
  rw [ContinuousMap.norm_le _ hC]
  simp only [pairSection_apply,Real.norm_eq_abs]

def derivativeSection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Coord → F) (hf : ContDiff ℝ ∞ f) (K : Set Coord)
    (k : ℕ) (dirs : Fin k → Coord) : C(K,F) :=
  ⟨fun x ↦ iteratedFDeriv ℝ k f x dirs,
    ((hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).comp continuous_subtype_val).eval
        continuous_const⟩

lemma seeded_derivative_section_apply (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (K : Set Coord) [CompactSpace K] (k : ℕ) (dirs : Fin k → Coord)
    (a : ι × Fin 2 → ℝ) (x : K) :
    pairSection (derivativeSection seed hs K k dirs)
      (fun i ↦ derivativeSection (V i) (hV i) K k dirs) a x =
      iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x dirs := by
  rw [pairSection_apply,seeded_gaussian_iterated_apply V seed hV hs]
  rfl

end
end Yau.Geometry

end OAI
