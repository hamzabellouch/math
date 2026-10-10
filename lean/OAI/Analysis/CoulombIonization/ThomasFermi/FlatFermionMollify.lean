import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.FlatFermionGradient

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators Topology Convolution ContDiff

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

theorem exists_flatFermion_smooth_approx
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x * Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x * (φ x:ℂ))) :
    ∃ u : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ,
      (∀ n s, ContDiff ℝ ∞ (u n s)) ∧
      (∀ n, FlatAntisymmetric (u n)) ∧
      (∀ n s, MemLp (u n s) 2) ∧
      (∀ n s q, MemLp (fun x => fderiv ℝ (u n s) x (Pi.single q 1)) 2) ∧
      (∀ n, (∑ s, ∫ x, ‖u n s x‖^2) ≤ ∑ s, ∫ x, ‖f s x‖^2) ∧
      (∀ n, (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) ≤
        ∑ s, ∑ q, ∫ x, ‖g s q x‖^2) ∧
      (∀ s, ∀ᵐ x, Tendsto (fun n => u n s x) atTop (𝓝 (f s x))) := by
  let k : ℕ → ((Fin N × Fin 3) → ℝ) → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let v : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ := fun n s => k n ⋆[L] f s
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hlocal (s : Fin N → Fin 2) := (hm s).locallyIntegrable (by norm_num : (1:ENNReal) ≤ 2)
  have hv (n : ℕ) (s : Fin N → Fin 2) : ContDiff ℝ ∞ (v n s) :=
    (hkc n).contDiff_convolution_left L (hk n) (hlocal s)
  have hv1 (n : ℕ) (s : Fin N → Fin 2) : ContDiff ℝ 1 (v n s) := (hv n s).of_le (by simp)
  have hv2 (n : ℕ) (s : Fin N → Fin 2) : MemLp (v n s) 2 ∧
      (∫ x, ‖v n s x‖^2) ≤ ∫ x, ‖f s x‖^2 :=
    convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hm s)
  have hdv (n : ℕ) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
      (fun x => fderiv ℝ (v n s) x (Pi.single q 1)) = k n ⋆[L] g s q := by
    funext x
    exact mollified_weak_derivative (hk n) (hkc n) (hlocal s) (Pi.single q 1) (hw s q) x
  have hdv2 (n : ℕ) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
      MemLp (fun x => fderiv ℝ (v n s) x (Pi.single q 1)) 2 ∧
      (∫ x, ‖fderiv ℝ (v n s) x (Pi.single q 1)‖^2) ≤ ∫ x, ‖g s q x‖^2 := by
    have hh := convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hg s q)
    change MemLp (k n ⋆[L] g s q) 2 ∧
      (∫ x, ‖(k n ⋆[L] g s q) x‖^2) ≤ ∫ x, ‖g s q x‖^2 at hh
    simpa only [← hdv n s q] using hh
  have ht (s : Fin N → Fin 2) : ∀ᵐ x, Tendsto (fun n => v n s x) atTop (𝓝 (f s x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2*(shrinkingBump (E := (Fin N × Fin 3) → ℝ) n).rIn))
      (hlocal s)
  refine ⟨fun n => flatFermionAverage (v n), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n s => flatFermionAverage_contDiff (hv n) s
  · exact fun n => flatFermionAverage_anti (v n)
  · exact fun n s => flatFermionAverage_memLp (fun s => (hv2 n s).1) s
  · exact fun n s q => flatFermionAverage_gradient_memLp (hv1 n) (fun s q => (hdv2 n s q).1) s q
  · intro n
    exact (flatFermionAverage_mass_le (fun s => (hv2 n s).1)).trans
      (Finset.sum_le_sum fun s _ => (hv2 n s).2)
  · intro n
    exact (flatFermionAverage_kinetic_le (hv1 n) (fun s q => (hdv2 n s q).1)).trans
      (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun q _ => (hdv2 n s q).2)
  · exact flatFermionAverage_ae_tendsto ha ht

end CoulombNeumann

end

end OAI
