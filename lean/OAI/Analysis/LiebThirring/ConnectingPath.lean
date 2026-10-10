import OAI.Analysis.LiebThirring.FieldFlow

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.MatrixFlow
open ODEProof MatrixProof ScalarProof Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {N : ℕ}

lemma state_diagonal_le (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    (f : Fin N → ℝ) (b : ℝ) (hf : ∀ i, f i ≤ b) :
    φ (complexify (diagonal f)) ≤ b := by
  have hp := hφ (diagonal (fun i ↦ ((b-f i : ℝ) : ℂ)))
    (diagonal_real_posSemidef _ (fun i ↦ sub_nonneg.mpr (hf i)))
  have he : diagonal (fun i ↦ ((b-f i : ℝ) : ℂ)) = b • (1 : Matrix (Fin N) (Fin N) ℂ) - complexify (diagonal f) := by
    rw [complexify_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · simp [diagonal_apply_ne _ hij,one_apply_ne hij]
  rw [he,map_sub,map_smul,hφ₁,smul_eq_mul,mul_one] at hp
  linarith

lemma sourceField_state_nonpos {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (A : Sym N)
    (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    (h : ‖k‖ < |φ (complexify A.val)|) :
    φ (complexify (sourceField σ δ hσ₁ hδ k A).val) ≤ 0 := by
  have hC : φ (complexify (diagonal (fun i ↦ k i^2))) ≤ ‖k‖^2 :=
    state_diagonal_le φ hφ hφ₁ _ _ (fun i ↦ by
      have hh : |k i| ≤ ‖k‖ := norm_le_pi_norm k i
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hh)
  have hj := hermitianField_state_jensen hσ₀ hσ₁ hδ φ hφ hφ₁
    (realK2SelfAdjoint k).prop (complexify_hermitian A.prop)
  change φ (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A.val)) ≤ _ at hj
  rw [← complexify_matrixField hσ₁ hδ k A.prop] at hj
  apply hj.trans
  have hz : φ (complexify (diagonal (fun i ↦ k i^2))) - (φ (complexify A.val))^2 ≤ 0 := by
    nlinarith [sq_abs (φ (complexify A.val)),norm_nonneg k]
  exact (mu_strictMono hσ₀ hσ₁ hδ).monotone hz |>.trans_eq (mu_zero σ δ)

lemma source_path_state_barrier {σ δ ε l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hε : 0 < ε) (k : Fin N → ℝ) (a : ℝ → Fin N → ℝ)
    (q : Sym N → ℝ) (hq : ∀ A, 0 ≤ q A) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X
      (ε⁻¹ • (q (X t) • sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))) (Icc l r) t)
    (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1) :
    ∀ t ∈ Icc l r, |φ (complexify (X t).val)| ≤ ‖k‖ := by
  let ψ := φ.comp (complexifyCLM.comp symInclude.toContinuousLinearMap)
  have hψ (A : Sym N) : ψ A = φ (complexify A.val) := rfl
  have hK : ψ (symDiag k) ≤ ‖k‖ := state_diagonal_le φ hφ hφ₁ _ _
    (fun i ↦ (le_abs_self _).trans (norm_le_pi_norm k i))
  apply two_sided_barrier (h := fun t ↦ ψ (X t))
    (h' := fun t ↦ ψ (ε⁻¹ • (q (X t) • sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))))
  · intro t ht
    exact ψ.hasFDerivAt.comp_hasDerivWithinAt t (hXd t ht)
  · rw [hXi]; exact hK
  · rw [hXf,map_neg]; exact neg_le_neg hK
  · intro t ht h
    have hF := sourceField_state_nonpos hσ₀ hσ₁ hδ k (X t) φ hφ hφ₁ h
    have hA : 0 ≤ ψ (symOuter (a t)) := by
      change 0 ≤ φ (complexify (vecMulVec (a t) (a t)))
      rw [complexify_vecMulVec]
      exact hφ _ (posSemidef_vecMulVec_self_star _)
    rw [map_smul,map_sub,map_smul,smul_eq_mul,smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε.le)
      (sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (hq _) hF) hA))

lemma sym_norm_le_of_states (A : Sym N) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ),
      (∀ B, B.PosSemidef → 0 ≤ φ B) → φ 1 = 1 → |φ (complexify A.val)| ≤ R) :
    ‖A‖ ≤ R := by
  have hA : A.val.IsHermitian := A.prop
  have he (i : Fin N) : |hA.eigenvalues i| ≤ R := by
    have hh := h (unitaryState (complexUnitary (star hA.eigenvectorUnitary)) i)
      (fun B hB ↦ unitaryState_positive _ _ hB) (unitaryState_one _ _)
    rw [unitaryState_apply,← complexify_conj,hA.conjStarAlgAut_star_eigenvectorUnitary] at hh
    simpa only [complexify_apply,Function.comp_apply,RCLike.ofReal_real_eq_id,id_eq,
      diagonal_apply_eq,Complex.ofReal_re] using hh
  have hd := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hn := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ ↦ ‖B‖) hd
  simp only [Unitary.conjStarAlgAut_apply,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,Matrix.l2_opNorm_diagonal,
    RCLike.ofReal_real_eq_id,Function.id_comp] at hn
  change ‖A.val‖ ≤ R
  rw [hn]
  exact (pi_norm_le_iff_of_nonneg hR).mpr he

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof MatrixProof ScalarProof Matrix Set ContinuationGap
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The connecting path, with one coefficient box for all small penalties.
The radial cutoff has been removed by the two endpoint barriers. -/
lemma source_connecting_path {σ δ l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    ∃ R : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (C : LowerSpace N) (X : ℝ → Sym N),
        (∀ i j, |C.val i j| ≤ R) ∧ X l = symDiag k ∧ X r = -symDiag k ∧
        (∀ t ∈ Icc l r, ‖X t‖ ≤ ‖k‖) ∧
        (∀ t ∈ Icc l r, HasDerivWithinAt X
          (ε⁻¹ • (sourceField σ δ hσ₁ hδ k (X t) - symOuter (C.val *ᵥ u t))) (Icc l r) t) := by
  let χ : Sym N → ℝ := radialCutoff ‖k‖
  let M := fun A ↦ χ A • sourceField σ δ hσ₁ hδ k A
  obtain ⟨L,B,hL,hB⟩ := bounded_lipschitz_radial_cutoff
    (sourceField σ δ hσ₁ hδ k) (sourceField_locallyLipschitz hσ₁ hδ k) ‖k‖
  refine ⟨max (2*‖k‖+(r-l)*B) 0+1,?_⟩
  intro ε hε hε₁
  have hχ (A : Sym N) : |χ A| ≤ (1 : ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have hg (i : Fin N) : LocallyLipschitz (fun x ↦ scalarMu σ δ (k i^2-x^2)) :=
    coordinate_mu_locallyLipschitz hσ₁ hδ k i
  have hc (i : Fin N) (A : Sym N) (hi : ∀ j, i ≠ j → A.val i j = 0) :
      (M A).val i i = χ A * scalarMu σ δ (k i^2-A.val i i^2) := by
    change χ A * (sourceField σ δ hσ₁ hδ k A).val i i = _
    rw [matrixField_isolated_coordinate hσ₁ hδ k A i hi]
  have he (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
      M (symConj s A) = symConj s (M A) := by
    dsimp only [M]
    rw [sourceField_equivariant hσ₁ hδ k s hs,map_smul]
    congr 1
    unfold χ radialCutoff
    rw [norm_symConj s hs]
  obtain ⟨C,X,hXi,hXf,hXd,hC⟩ := terminal_matching hlr hε M L B 1 hL hB χ hχ
    (fun i x ↦ scalarMu σ δ (k i^2-x^2)) hg k hk
    (fun i ↦ by simp only [sub_self,mu_zero]) hc he u hu ho
  have hX (t : ℝ) (ht : t ∈ Icc l r) : ‖X t‖ ≤ ‖k‖ := by
    apply sym_norm_le_of_states (X t) (norm_nonneg _)
    intro φ hφ hφ₁
    exact source_path_state_barrier hσ₀ hσ₁ hδ hε k (fun t ↦ C.val *ᵥ u t) χ
      (radialCutoff_nonneg _) X hXi hXf hXd φ hφ hφ₁ t ht
  refine ⟨C,X,?_,hXi,hXf,hX,?_⟩
  · apply gram_entry_bound
    apply hC.trans
    rw [abs_of_pos hε]
    nlinarith [norm_nonneg k]
  · intro t ht
    have hh := hXd t ht
    change HasDerivWithinAt X (ε⁻¹ • (χ (X t) • sourceField σ δ hσ₁ hδ k (X t) - _)) _ t at hh
    rw [show χ (X t) = 1 from radialCutoff_eq_one (hX t ht),one_smul] at hh
    exact hh

end SharpLiebThirring.MatrixFlow

end
end
end
end
end
end
end

end OAI
