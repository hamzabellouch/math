import OAI.Analysis.Mahler.HalfspaceStokes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem extDeriv_zero_off_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) {x : E} (hx : x ∉ tsupport ω) :
    extDeriv ω x = 0 := by
  rw [extDeriv, fderiv_of_notMem_tsupport ℝ hx]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)

 theorem integral_partial_univ {n : ℕ} (i : Fin (n+1))
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x, fderiv ℝ f x (Pi.single i 1)) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single i 1))
  rw [← setIntegral_univ, setIntegral_slice i MeasurableSet.univ _ hi.integrableOn]
  simp only [mem_univ, ofPred_true, setIntegral_univ]
  simp_rw [integral_partial_slice_zero i _ hf hc]
  simp

/-- Stokes for a compactly supported form in the whole ambient space. -/
theorem integral_extDeriv_univ {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    (∫ x, extDeriv ω x (coordinateBasis (n+1))) = 0 := by
  have hs (i : Fin (n+1)) : HasCompactSupport (orientedCoefficient ω i) :=
    hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ =>
      (-1 : ℝ)^i.val * A (i.removeNth (coordinateBasis (n+1)))) (by simp)
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) :=
    (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hs i).fderiv_apply ℝ (Pi.single i 1))
  simp_rw [extDeriv_eq_divergence (hω.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_partial_univ _ (contDiff_orientedCoefficient hω _) (hs _)]
  simp

/-- The actual interior patch contributes zero, since the support of the
localized form stays strictly inside the domain. -/
theorem integral_extDeriv_interior_support {n : ℕ} {s : Set (Fin (n+1) → ℝ)}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ s) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_extDeriv_univ ω hω hc
  · intro x hx
    rw [extDeriv_zero_off_tsupport ω (fun h => hx (hs h))]
    simp

/-- Remove the interior term from the volume partition. All remaining
terms are supported in boundary charts, before oriented chart transport. -/
theorem integral_extDeriv_boundary_patches {n : ℕ} {ι : Type*} [Fintype ι]
    {K W s : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option ι) 𝓘(ℝ, Fin (n+1) → ℝ) (Fin (n+1) → ℝ) K)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hsW : s ⊆ W) (hs : MeasurableSet s)
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hω : ∀ i, ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x)
    (hinterior : tsupport (ρ none) ⊆ s) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : ι, ∫ x in s,
        extDeriv (fun z => ρ (some i) z • ω z) x (coordinateBasis (n+1)) := by
  rw [integral_extDeriv_partition ρ ω hW hsW hs hsum hρ hω, Fintype.sum_option]
  have hz := integral_extDeriv_interior_support (fun z => ρ none z • ω z)
    (contDiff_localized_form ρ ω none (hω none))
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω none (hρ none))
    ((tsupport_smul_subset_left _ _).trans hinterior)
  rw [hz, zero_add]

end MahlerStokes

end

end OAI
