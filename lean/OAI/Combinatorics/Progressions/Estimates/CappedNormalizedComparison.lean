import OAI.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw

namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityPMF_le_of_normalized_comparison {K I : Type*}
    [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D g φ : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    {M ε : ℝ} (hg : ∀ z, g z ≤ M) (hφ : ∀ z, 0 ≤ φ z)
    (he : ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ) * (φ z : ℂ)) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) * ((φ z : ℂ) * (g z : ℂ)))‖ ≤ ε) :
    (∑' z, (selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal * φ z) ≤
      M * (∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal * φ z) + ε := by
  have he' : |(∑' z, (selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal * φ z) -
      (∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal * (φ z * g z))| ≤ ε := by
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using he
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have hb : p.mean (fun z => φ z.val * g z.val) ≤ p.mean (fun z => M * φ z.val) :=
    p.mean_mono (fun z => (mul_le_mul_of_nonneg_left (hg z.val) (hφ z.val)).trans_eq (mul_comm _ _))
  rw [p.mean_const_mul] at hb
  dsimp only [p] at hb
  rw [selectedResidueFiniteLaw_mean modulus T W hW hZ (fun z => φ z * g z),
    selectedResidueFiniteLaw_mean modulus T W hW hZ φ] at hb
  linarith [(abs_le.mp he').2]

end Erdos3

end

end OAI
