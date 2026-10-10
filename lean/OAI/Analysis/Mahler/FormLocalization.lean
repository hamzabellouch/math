import OAI.Analysis.Mahler.RegularPartition
import OAI.Analysis.Mahler.ChartStokes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem extDeriv_finsetSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ι : Type*} (t : Finset ι)
    (ω : ι → E → E [⋀^Fin n]→L[ℝ] ℝ) (x : E)
    (hω : ∀ i ∈ t, DifferentiableAt ℝ (ω i) x) :
    extDeriv (fun z => ∑ i ∈ t, ω i z) x = ∑ i ∈ t, extDeriv (ω i) x := by
  simp only [extDeriv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    fderiv_fun_sum hω, map_sum]

/-- The cutoff derivatives cancel because the actual localized forms sum to
ω on a neighborhood; no boundary or Stokes equation is assumed. -/
theorem extDeriv_partition_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {ι : Type*} [Fintype ι] {W : Set E} {x : E}
    (ρ : ι → E → ℝ) (ω : E → E [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hx : x ∈ W) (hsum : ∀ z ∈ W, ∑ i, ρ i z = 1)
    (hω : ∀ i, DifferentiableAt ℝ (fun z => ρ i z • ω z) x) :
    extDeriv ω x = ∑ i, extDeriv (fun z => ρ i z • ω z) x := by
  have he : ω =ᶠ[𝓝 x] (fun z => ∑ i, ρ i z • ω z) := by
    filter_upwards [hW.mem_nhds hx] with z hz
    rw [← Finset.sum_smul, hsum z hz, one_smul]
  rw [he.extDeriv_eq]
  exact extDeriv_finsetSum Finset.univ _ x (fun i _ => hω i)

 theorem contDiff_localized_form {d n : ℕ} {ι : Type*} {K : Set (Fin d → ℝ)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) K)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : ι)
    (hω : ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x) :
    ContDiff ℝ 1 (fun x => ρ i x • ω x) := by
  exact (ρ.contMDiff_smul (fun x hx => (hω x hx).contMDiffAt)).contDiff

 theorem hasCompactSupport_localized_form {d n : ℕ} {ι : Type*}
    (ρ : ι → (Fin d → ℝ) → ℝ)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : ι)
    (hρ : HasCompactSupport (ρ i)) : HasCompactSupport (fun x => ρ i x • ω x) := by
  exact hρ.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)

/-- Every localized C1 compactly supported form has an integrable actual
exterior-derivative coefficient on the whole coordinate space. -/
theorem integrable_extDeriv_coefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    Integrable (fun x => extDeriv ω x (coordinateBasis (n+1))) := by
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) := by
    have hs : HasCompactSupport (orientedCoefficient ω i) :=
      hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ => (-1 : ℝ)^i.val *
        A (i.removeNth (coordinateBasis (n+1)))) (by simp)
    exact (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (Pi.single i 1))
  have he (x) := extDeriv_eq_divergence (hω.differentiable one_ne_zero x)
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => hi i)

/-- Actual volume integral localization for a finite smooth partition, on
any measurable set contained in its sum-one neighborhood. -/
theorem integral_extDeriv_partition {n : ℕ} {ι : Type*} [Fintype ι]
    {K W s : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin (n+1) → ℝ) (Fin (n+1) → ℝ) K)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hW : IsOpen W) (hsW : s ⊆ W) (hs : MeasurableSet s)
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hω : ∀ i, ∀ x ∈ tsupport (ρ i), ContDiffAt ℝ 1 ω x) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i, ∫ x in s, extDeriv (fun z => ρ i z • ω z) x (coordinateBasis (n+1)) := by
  have hd (i) := contDiff_localized_form ρ ω i (hω i)
  have hi (i) := integrable_extDeriv_coefficient _ (hd i)
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω i (hρ i))
  calc
    _ = ∫ x in s, ∑ i, extDeriv (fun z => ρ i z • ω z) x (coordinateBasis (n+1)) := by
      apply setIntegral_congr_fun hs
      intro x hx
      dsimp only
      rw [extDeriv_partition_sum (fun i x => ρ i x) ω hW (hsW hx) hsum
        (fun i => (hd i).differentiable one_ne_zero x)]
      simp
    _ = _ := integral_finsetSum _ (fun i _ => (hi i).integrableOn)

end MahlerStokes

end

end OAI
