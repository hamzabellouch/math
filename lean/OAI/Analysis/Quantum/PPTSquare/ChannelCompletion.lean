import OAI.Analysis.Quantum.PPTSquare.Compression

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype n] in
lemma compress_ad (V : Matrix p n ℂ) (W : Matrix p m ℂ) (X : Mat m) :
    Vᴴ * ad W X * V = (Vᴴ * W) * X * (Wᴴ * V) := by
  simp only [ad_apply, Matrix.mul_assoc]

lemma theta_first (d : ℕ) (F G : Map (Fin d) (Fin d)) (X : Mat (Space d)) :
    (W0 d)ᴴ * theta d F G X * W0 d =
      (coefficient G : ℂ) • G ((W1 d)ᴴ * X * W1 d) := by
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, compress_ad,
    W0_isometry, W0_W1, W1_W0, W0_flag, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]

lemma theta_second (d : ℕ) (F G : Map (Fin d) (Fin d)) (X : Mat (Space d)) :
    (W1 d)ᴴ * theta d F G X * W1 d =
      (coefficient F : ℂ) • F ((W0 d)ᴴ * X * W0 d) := by
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, compress_ad,
    W1_isometry, W0_W1, W1_W0, W1_flag, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero]

lemma square_corner (d : ℕ) (F G : Map (Fin d) (Fin d)) (B : Mat (Fin d)) :
    (W0 d)ᴴ * theta d F G (theta d F G (ad (W0 d) B)) * W0 d =
      ((coefficient F * coefficient G : ℝ) : ℂ) • G (F B) := by
  rw [theta_first, theta_second, compress_ad, W0_isometry, Matrix.one_mul,
    Matrix.mul_one, map_smul, smul_smul]
  simp [mul_comm]

omit [Fintype p] in
lemma choi_coord_compress [DecidableEq n] [DecidableEq m] [DecidableEq p]
    {s : Type} [Fintype s] [DecidableEq s]
    (e : n → m) (f : p → s) (F : Map m s) :
    (coord e ⊗ₖ coord f)ᴴ * choi F * (coord e ⊗ₖ coord f) =
      choi ((ad (coord f)ᴴ).comp (F.comp (ad (coord e)))) := by
  rw [coord_kronecker, coord_compress]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [choi, Matrix.submatrix_apply, LinearMap.comp_apply]
  rw [ad_apply, Matrix.conjTranspose_conjTranspose, coord_compress, coord_single]
  rfl

omit [Fintype n] [Fintype m] in
lemma choi_smul [DecidableEq n] (F : Map n m) (c : ℂ) : choi (c • F) = c • choi F := rfl

lemma choi_corner (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    (W0 d ⊗ₖ W0 d)ᴴ * choi ((theta d F G).comp (theta d F G)) * (W0 d ⊗ₖ W0 d) =
      ((coefficient F * coefficient G : ℝ) : ℂ) • choi (G.comp F) := by
  rw [W0, choi_coord_compress]
  rw [← choi_smul]
  congr 1
  apply LinearMap.ext
  intro B
  simpa only [LinearMap.comp_apply, ad_apply, Matrix.conjTranspose_conjTranspose,
    LinearMap.smul_apply, W0] using square_corner d F G B

end ChannelCompletion

namespace ChannelCompletion
variable {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]

omit [Fintype n] [Fintype m] [Fintype p] [Fintype q] in
lemma separable_submatrix {Z : Mat (n × m)} (hZ : Separable Z) (e : p → n) (f : q → m) :
    Separable (Z.submatrix (Prod.map e f) (Prod.map e f)) := by
  obtain ⟨r, A, B, hA, hB, rfl⟩ := hZ
  refine ⟨r, (fun i => (A i).submatrix e e), (fun i => (B i).submatrix f f),
    (fun i => (hA i).submatrix e), (fun i => (hB i).submatrix f), ?_⟩
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

omit [Fintype p] [Fintype q] in
lemma separable_coord_compress [DecidableEq n] [DecidableEq m]
    {Z : Mat (n × m)} (hZ : Separable Z) (e : p → n) (f : q → m) :
    Separable ((coord e ⊗ₖ coord f)ᴴ * Z * (coord e ⊗ₖ coord f)) := by
  rw [coord_kronecker, coord_compress]
  exact separable_submatrix hZ e f

omit [Fintype n] [Fintype m] in
lemma separable_smul {Z : Mat (n × m)} (hZ : Separable Z) {c : ℝ} (hc : 0 ≤ c) :
    Separable ((c : ℂ) • Z) := by
  obtain ⟨r, A, B, hA, hB, rfl⟩ := hZ
  refine ⟨r, (fun i => (c : ℂ) • A i), B,
    (fun i => (hA i).smul (show (0 : ℂ) ≤ c by exact_mod_cast hc)), hB, ?_⟩
  simp [Finset.smul_sum, Matrix.smul_kronecker]

omit [Fintype n] [Fintype m] in
lemma separable_of_smul {Z : Mat (n × m)} {c : ℝ} (hc : 0 < c)
    (hZ : Separable ((c : ℂ) • Z)) : Separable Z := by
  have h := separable_smul hZ (inv_nonneg.mpr hc.le)
  rw [Complex.ofReal_inv, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'),
    one_smul] at h
  exact h

theorem channel_completion (d : ℕ) (F G : Map (Fin d) (Fin d)) (hF : PPT F) (hG : PPT G) :
    0 < coefficient F ∧ 0 < coefficient G ∧
    Fintype.card (Space d) = 2 * d + 1 ∧
    (W0 d)ᴴ * W0 d = 1 ∧ (∀ i j, (W0 d i j).im = 0) ∧
    PPT (theta d F G) ∧ TracePreserving (theta d F G) ∧
    (W0 d ⊗ₖ W0 d)ᴴ * choi ((theta d F G).comp (theta d F G)) *
      (W0 d ⊗ₖ W0 d) =
      ((coefficient F * coefficient G : ℝ) : ℂ) • choi (G.comp F) ∧
    (¬ Separable (choi (G.comp F)) →
      ¬ EntanglementBreaking ((theta d F G).comp (theta d F G))) := by
  refine ⟨coefficient_pos hF.1, coefficient_pos hG.1, dimension d, W0_isometry d,
    coord_real _, theta_ppt d hF hG, theta_tracePreserving d F G, choi_corner d F G, ?_⟩
  intro hn he
  apply hn
  have hs := separable_coord_compress (eb_choi he) (first d) (first d)
  change Separable ((W0 d ⊗ₖ W0 d)ᴴ * choi ((theta d F G).comp (theta d F G)) *
    (W0 d ⊗ₖ W0 d)) at hs
  rw [choi_corner] at hs
  exact separable_of_smul (mul_pos (coefficient_pos hF.1) (coefficient_pos hG.1)) hs

end ChannelCompletion

end

end OAI
