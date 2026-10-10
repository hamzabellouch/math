import OAI.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem geometricScale_cutoff {p c e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hScale : S = allocatedSiteScale (G := G) B U b hR hσ (allocatedGeometryInput m p c 0 E) e E)
    {M : ℕ} (hM : (M : ℝ) ≤ Real.exp p) : M ≤ S.value := by
  obtain ⟨hq, hpq, _, _, _, _⟩ := allocatedGeometryInput_bounds m hp hc (le_refl 0) hE
  have hnum := (allocatedSiteScaleNumeric_bounds m hq).2.1
  have hS := allocatedSiteScale_lower (G := G) B U b hR hσ hq he hE
  rw [← hScale] at hS
  exact_mod_cast hM.trans ((Real.exp_le_exp.mpr (hpq.trans hnum)).trans hS)

theorem geometricScale_affine_bad_probability [DecidableEq G]
    {dim : ℕ} [Nonempty (Fin dim)] {p c e E Ebad : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hScale : S = allocatedSiteScale (G := G) B U b hR hσ (allocatedGeometryInput m p c 0 E) e E)
    (hG : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    (M D : ℕ) (hM : 0 < M) (hD : 0 < D)
    (hcutoff : (scalarKernelCutoff (Fin dim) G M D (Real.exp (-(Ebad + 1))) : ℝ) ≤ Real.exp p) :
    let cutoff := scalarKernelCutoff (Fin dim) G M D (Real.exp (-(Ebad + 1)))
    let hlarge := geometricScale_cutoff B U b hR hσ S hp hc he hE hScale hcutoff
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value) (hDwindow : ∀ g, S.value ≤ D * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M D (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDwindow g)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x) ≤ Real.exp (-(Ebad + 1)) := by
  intro cutoff hlarge window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  exact affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hG) selection hM hD (Real.exp_pos _) S.positive
    hlarge window hwindow hDwindow shift moduli residues hmoduli hmoduliM

end Erdos3.VectorPolynomial

end

end OAI
