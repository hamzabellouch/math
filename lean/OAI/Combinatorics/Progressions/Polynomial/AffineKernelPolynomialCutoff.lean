import OAI.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound

namespace OAI

section

namespace Erdos3

theorem exists_affine_kernel_polynomial_cutoff (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) (s : I ↪ J)
    {M D : ℕ} {η R : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hR : 0 ≤ R)
    (hMR : (M : ℝ) ≤ Real.exp R) (hDR : (D : ℝ) ≤ Real.exp R) (hηR : η⁻¹ ≤ Real.exp R) :
    ∃ B : ℕ, 0 < B ∧ (B : ℝ) ≤ Real.exp (scalarKernelLogarithmicBudget I J R) ∧
      ∃ hsize : D * ((Fintype.card I + 1) * M) ≤ B,
      ∀ (L : ℕ) (hL : 0 < L) (hlarge : B ≤ L) (K : J → ℕ)
        (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j) (c : J → ℤ)
        (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
        (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M),
        (FiniteProbabilityWeights.pi (fun j =>
          affineScalarCubeWindowWeights I L (K j) M D (c j) hL (hKL j) (hDK j)
            (m j) (r j) (hm j) (hmM j)
            (scalarCubeWindow_size hD (hsize.trans hlarge) (hDK j)))).eventProbability
              (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) ≤ η := by
  have hb := scalarKernelCutoff_bounds I J hM hD hη
  refine ⟨scalarKernelCutoff I J M D η, hb.1,
    scalarKernelCutoff_le_exp I J hM hD hη hR hMR hDR hηR, hb.2.2.1, ?_⟩
  intro L hL hlarge K hKL hDK c m r hm hmM
  exact affineKernel_explicit_probability_le I J hJ s hM hD hη hL hlarge K hKL hDK c m r hm hmM

end Erdos3

end

end OAI
