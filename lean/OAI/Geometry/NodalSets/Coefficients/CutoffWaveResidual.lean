import OAI.Geometry.NodalSets.Coefficients.CutoffResidualProductLemmas
import OAI.Geometry.NodalSets.Coefficients.SmoothFiniteResidual
import OAI.Geometry.NodalSets.Elliptic.CommutatorBounds

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_residual_split (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (N : ℝ) (y x : Coord) (lam : ℂ) :
    smoothSecondOrder g b (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) x +
      lam * (Yau.Waves.scaledCutoff N y x • u x) =
    Yau.Waves.scaledCutoff N y x • (smoothSecondOrder g b u x + lam*u x) +
      cutoffCommutator g b u N y x := by
  simp only [cutoffCommutator, smul_add, mul_smul_comm]
  abel

theorem cutoff_wave_residual_bound (k : ℕ) (c K p : ℝ) (hc : 0 < c) :
    ∃ B₁ > 0, ∃ B₂ > 0, ∀ᶠ N : ℝ in atTop,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
      (u phi core : Coord → ℂ) (lam : ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ phi → ContDiff ℝ ∞ core →
    (∀ z, smoothSecondOrder g b u z + lam*u z = core z * waveExp phi N z) →
    ∀ (x y : Coord) (C D G A S : ℝ), 0 ≤ C → 1 ≤ D → 0 ≤ G → 0 ≤ A →
    DerivativeBound k core x (C*N^(-K-k)) → DerivativeBound k phi x D →
    (phi x).re ≤ S →
    (∀ i j, DerivativeBound k (g i j) x G) →
    (∀ i, DerivativeBound k (b i) x G) →
    DerivativeBound (k+2) u x (A*N^p*Real.exp (N*S-c*N*‖x-y‖^2)) →
    ‖iteratedFDeriv ℝ k (fun z ↦
      smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N y w • u w) z +
      lam * (Yau.Waves.scaledCutoff N y z • u z)) x‖ ≤
      (B₁*C*(k.factorial:ℝ)*D^k + B₂*G*A)*N^(-K)*Real.exp (N*S) := by
  obtain ⟨B₁, hB₁, hprod⟩ := cutoff_residual_times_exponential_bound k
  obtain ⟨B₂, hB₂, hcomm⟩ := cutoffCommutator_gaussian_bound k c p K hc
  refine ⟨B₁, hB₁, B₂, hB₂, ?_⟩
  filter_upwards [hcomm, eventually_ge_atTop (1:ℝ)] with N hcommN hN
  intro g b u phi core lam hg hb hu hp hcore heq x y C D G A S hC hD hG hA
    hcoreB hphiB hgap hgb hbb hub
  have h1 := hprod phi core hp hcore x y C D N K S hC hD hN hcoreB hphiB hgap
  have h2 := hcommN g b u hg hb hu y x G A S hG hA hgb hbb hub
  have he : (fun z ↦ smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N y w • u w) z +
      lam*(Yau.Waves.scaledCutoff N y z • u z)) =
      (fun z ↦ Yau.Waves.scaledCutoff N y z • (core z * waveExp phi N z)) +
      cutoffCommutator g b u N y := by
    funext z
    rw [cutoff_residual_split, heq z]
    rfl
  rw [he, iteratedFDeriv_add_apply
    (f := fun z ↦ Yau.Waves.scaledCutoff N y z • (core z * waveExp phi N z))
    (((Yau.Waves.scaledCutoff_contDiff N y).smul (hcore.mul (waveExp_contDiff hp N))).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((cutoffCommutator_contDiff g b u hg hb hu N y).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

end
end Yau.Jets

end OAI
