import OAI.Geometry.Immersion.ClosedSurface.AssembledMean
import OAI.Geometry.Immersion.ClosedSurface.FreeAmplitude

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set


def phaseFreeFamily {ι : Type*} (U : ι → Set Base) (δ τ : ℝ)
    (F : ι → RField 4) (ψ : ι → Base → ℝ) (Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ)
    (χ e : ι → Base → Base) (q : ℕ) (A : Base → PhaseMean.Tensor) : ι → Field 4 :=
  fun i => (U i).indicator (chartFreeAmplitude δ τ (F i)
    (phaseAmplitude (ψ i) (coefficient (Q i) (e i) A)) q (χ i))



lemma finite_free_mean {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r ρ R : ℝ} {reference A : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (hρ : 0 < ρ) (hA : ContDiff ℝ ∞ A) (hball : InTrialBall univ reference r A)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    (hdecomp : ∀ p, (∑ i ∈ a, (U i).indicator
      (chartLeadingTensor (phaseAmplitude (ψ i) (coefficient (Q i) (e i) A)) (χ i)) p) = A p)
    {δ η : ℝ} (hδ : δ ≠ 0) (hηs : η * s ≠ 0) (q : ℕ) :
    (fun p => ∑ i ∈ a, phaseZeroTensor (η * s) (fun p => (χ i p).1)
        (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) p) =
      fun p => δ ^ 2 • (A p + assembledMean a U δ s F ψ Q χ e q η A p) := by
  classical
  have he (i : ι) (hi : i ∈ a) := extended_free_mean (h i hi).openU
    (hS i hi) (hSU i hi) (h i hi).smoothF (h i hi).domain
    ((h i hi).amplitude_smooth hρ hA.contDiffOn (fun p _ => hball p (mem_univ p)))
    (h i hi).smoothChi (h i hi).chiInto (hsp i hi) hδ hηs q
  funext p
  calc
    _ = ∑ i ∈ a, (δ ^ 2 • (U i).indicator
          (chartLeadingTensor (phaseAmplitude (ψ i) (coefficient (Q i) (e i) A)) (χ i)) p +
        δ ^ 2 • extendedMeanTerm (U i) δ s (F i) (ψ i) (Q i) (χ i) (e i) q η A p) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrFun (he i hi) p
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hdecomp p, ← smul_add]
      rfl


lemma phaseFreeFamily_smooth {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r ρ R : ℝ} {reference A : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (hρ : 0 < ρ) (hA : ContDiff ℝ ∞ A) (hball : InTrialBall univ reference r A)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    (δ τ : ℝ) (q : ℕ) :
    ∀ i ∈ a, ContDiff ℝ ∞ (phaseFreeFamily U δ τ F ψ Q χ e q A i) ∧
      tsupport (phaseFreeFamily U δ τ F ψ Q χ e q A i) ⊆ S i := by
  intro i hi
  have hz := chartFree_vanishes (hsp i hi) δ τ (F i) (coefficient (Q i) (e i) A) q
  constructor
  · exact contDiff_indicator_of_support (h i hi).openU (hS i hi) (hSU i hi)
      (contDiffOn_chartFreeAmplitude (h i hi).smoothF (h i hi).domain
        ((h i hi).amplitude_smooth hρ hA.contDiffOn (fun p _ => hball p (mem_univ p)))
        (h i hi).smoothChi (h i hi).chiInto δ τ q) hz
  · exact tsupport_indicator_subset (hS i hi) hz

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set




theorem finite_free_mean_adjustment {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r₀ r₁ ρ R : ℝ} {reference H : Base → PhaseMean.Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → PhaseMean.Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r₁ ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (d : ∀ i ∈ a, Budgets (U i) (V i) s (F i) (ψ i) (Q i) (χ i) (e i))
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (hgap : r₀ < r₁)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    (hdecomp : ∀ A : Base → PhaseMean.Tensor, InTrialBall univ reference r₁ A →
      ∀ p, (∑ i ∈ a, (U i).indicator
        (chartLeadingTensor (phaseAmplitude (ψ i) (coefficient (Q i) (e i) A)) (χ i)) p) = A p)
    {δ : ℝ} (hδ : 0 < δ) (q n : ℕ) {C : ℕ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ p, ‖H p - reference p‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound univ s m (C m) H) :
    ∃ B K : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ η, 0 < η → η ≤ η₀ → ∀ j ≤ n, ∃ A : Base → PhaseMean.Tensor,
        ContDiff ℝ ∞ A ∧ InTrialBall univ reference r₁ A ∧
        (∀ i ∈ a, ContDiff ℝ ∞ (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) ∧
          tsupport (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) ⊆ S i) ∧
        (∀ m, WeightedBound univ s m (sizeBound (q + 2) C B j m) A) ∧
        (∀ m, WeightedBound univ s m (differenceBound (q + 2) C B K j m * η ^ (j + 1))
          (fun p => (δ ^ 2)⁻¹ • (∑ i ∈ a, phaseZeroTensor (η * s) (fun p => (χ i p).1)
            (phaseFreeFamily U δ (η * s) F ψ Q χ e q A i) p) - H p)) := by
  obtain ⟨B, K, η₀, hη₀, hη₁, ht⟩ := assembledMean_finite_adjustment a h d hs hs1 hρ hgap
    hS hSU hsp hδ q n hC hH hH0 hbH
  refine ⟨B, K, η₀, hη₀, hη₁, ?_⟩
  intro η hη hηsmall j hj
  obtain ⟨hA, hball, hsize, hres⟩ := ht η hη hηsmall j hj
  let A := trial H (assembledMean a U δ s F ψ Q χ e q) η j
  have he := finite_free_mean a h hρ hA hball hS hSU hsp (hdecomp A hball)
    hδ.ne' (mul_ne_zero hη.ne' hs.ne') q
  refine ⟨A, hA, hball, phaseFreeFamily_smooth a h hρ hA hball hS hSU hsp δ (η * s) q,
    hsize, ?_⟩
  intro m
  apply (hres m).congr
  intro p _
  dsimp only [A]
  rw [congrFun he p, inv_smul_smul₀ (pow_ne_zero 2 hδ.ne')]
  rfl

end ClosedSurfaceR4.RealModes

end

end OAI
