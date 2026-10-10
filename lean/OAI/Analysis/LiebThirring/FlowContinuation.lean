import OAI.Analysis.LiebThirring.MatrixFlow

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

namespace SharpLiebThirring.ODEProof
open Set Metric Filter

lemma scalar_stationary_unique {l r k : ℝ} (hlr : l ≤ r)
    {b q g : ℝ → ℝ} (hg : LocallyLipschitz g) (hgk : g k = 0)
    (A : ℝ≥0) (hq : ∀ t ∈ Icc l r, |q t| ≤ A)
    (hb : ∀ t ∈ Icc l r, HasDerivWithinAt b (q t * g (b t)) (Icc l r) t)
    (hbl : b l = k) : EqOn b (fun _ ↦ k) (Icc l r) := by
  have hc := HasDerivWithinAt.continuousOn hb
  obtain ⟨L,hL⟩ := hg.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.image_of_continuousOn hc)
  have hk : k ∈ b '' Icc l r := hbl ▸ mem_image_of_mem b ⟨le_refl _,hlr⟩
  apply ODE_solution_unique_of_mem_Icc_right (K := A*L)
    (v := fun t x ↦ q t * g x) (s := fun _ ↦ b '' Icc l r) _ hc
    (fun t ht ↦ derivative_right_of_Icc ht (hb t (Ico_subset_Icc_self ht)))
    (fun t ht ↦ mem_image_of_mem b (Ico_subset_Icc_self ht)) continuousOn_const
    (fun t _ ↦ by simpa only [hgk,mul_zero] using hasDerivWithinAt_const t (Ici t) k)
    (fun _ _ ↦ hk) hbl
  intro t ht
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  rw [← mul_sub,norm_mul]
  calc
    _ ≤ (A : ℝ) * ((L : ℝ)*‖x-y‖) :=
      mul_le_mul (hq t (Ico_subset_Icc_self ht))
        (lipschitzOnWith_iff_norm_sub_le.mp hL hx hy) (norm_nonneg _) A.prop
    _ = _ := by push_cast; ring

/-- An upper barrier needs the derivative sign only strictly outside the barrier. -/
lemma upper_barrier {l r κ : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt h (h' t) (Icc l r) t)
    (hi : h l ≤ κ)
    (hs : ∀ t ∈ Icc l r, κ < h t → h' t ≤ 0) :
    ∀ t ∈ Icc l r, h t ≤ κ := by
  intro t ht
  have hη : ∀ η > (0 : ℝ), h t ≤ κ + η*(1+t-l) := by
    intro η hη
    apply image_le_of_deriv_right_lt_deriv_boundary
      (HasDerivWithinAt.continuousOn hd)
      (fun x hx ↦ derivative_right_of_Icc hx (hd x (Ico_subset_Icc_self hx)))
      (B := fun x ↦ κ + η*(1+x-l)) (B' := fun _ ↦ η)
    · simpa only [add_sub_cancel_right,mul_one] using hi.trans (le_add_of_nonneg_right hη.le)
    · intro x
      simpa only [mul_one,id_eq] using
        (((hasDerivAt_id x).const_add 1).sub_const l |>.const_mul η |>.const_add κ)
    · intro x hx he
      have hpos : κ < h x := by rw [he]; have := hx.1; nlinarith
      exact (hs x (Ico_subset_Icc_self hx) hpos).trans_lt hη
    · exact ht
  have hc : ContinuousWithinAt (fun η : ℝ ↦ κ + η*(1+t-l)) (Ioi 0) 0 := by fun_prop
  have hh := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0)) hc hη
  simpa only [zero_mul,add_zero] using hh

lemma two_sided_barrier {l r κ : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt h (h' t) (Icc l r) t)
    (hi : h l ≤ κ) (hf : -κ ≤ h r)
    (hs : ∀ t ∈ Icc l r, κ < |h t| → h' t ≤ 0) :
    ∀ t ∈ Icc l r, |h t| ≤ κ := by
  have hup := upper_barrier hd hi (fun t ht h ↦ hs t ht (h.trans_le (le_abs_self _)))
  have hrev : ∀ t ∈ Icc (-r) (-l), HasDerivWithinAt (fun t ↦ -h (-t)) (h' (-t))
      (Icc (-r) (-l)) t := by
    intro t ht
    have hm : -t ∈ Icc l r := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hh := (hd (-t) hm).comp t (hasDerivWithinAt_id t (Icc (-r) (-l)) |>.neg)
      (fun x hx ↦ ⟨by linarith [hx.2],by linarith [hx.1]⟩)
    convert! hh.neg using 1
    simp
  have hlo := upper_barrier hrev (by simpa only [neg_neg] using neg_le_neg hf)
    (fun t ht h ↦ hs (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      (h.trans_le (neg_le_abs _)))
  intro t ht
  apply abs_le.mpr
  constructor
  · have hh := hlo (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    simp only [neg_neg] at hh
    linarith
  · exact hup t ht

end SharpLiebThirring.ODEProof
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix
variable {N : ℕ}

lemma vanishing_row_stationary {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (L Q : ℝ≥0) (hL : LipschitzWith L M)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (i : Fin N) (hi : ∀ j, C i j = 0) :
    ∀ t ∈ Icc l r, (X (C,θ) t).val i i = k i := by
  let s : Fin N → ℝ := fun j ↦ if j=i then -1 else 1
  have hs := zero_row_sign i
  have hC : (fun j a ↦ s j * C j a) = C := by
    ext j a
    by_cases hj : j=i
    · subst j; simp only [s,ite_true,hi,mul_zero]
    · simp only [s,ite_eq_right hj,one_mul]
  have hfixed : ∀ t ∈ Icc l r, symConj s (X (C,θ) t) = X (C,θ) t := by
    have hh := matrix_flow_equivariant hL k u X hXi hXd s hs (he s hs) C θ
    rw [hC] at hh
    exact fun t ht ↦ (hh ht).symm
  have hoff : ∀ t ∈ Icc l r, ∀ j, i ≠ j → (X (C,θ) t).val i j = 0 :=
    fun t ht ↦ fixed_reflection_offdiag i _ (hfixed t ht)
  have hCu (t : ℝ) : (C *ᵥ u t) i = 0 := by simp [mulVec,dotProduct,hi]
  have hd : ∀ t ∈ Icc l r, HasDerivWithinAt (fun x ↦ (X (C,θ) x).val i i)
      ((ε⁻¹*θ*q (X (C,θ) t))*g i ((X (C,θ) t).val i i)) (Icc l r) t := by
    intro t ht
    have hh := (symEntry i i).hasFDerivAt.comp_hasDerivWithinAt t (hXd (C,θ) t ht)
    change HasDerivWithinAt (fun x ↦ (X (C,θ) x).val i i)
      ((ε⁻¹*θ)*(M (X (C,θ) t)).val i i - ε⁻¹*((C*ᵥu t) i*(C*ᵥu t) i)) (Icc l r) t at hh
    simp only [hCu,mul_zero,sub_zero,hc i _ (hoff t ht)] at hh
    convert hh using 1
    ring
  have hinit : (X (C,θ) l).val i i = k i := by rw [hXi]; exact diagonal_apply_eq _ _
  let A : ℝ≥0 := ⟨|ε⁻¹*θ| * Q,mul_nonneg (abs_nonneg _) Q.prop⟩
  apply scalar_stationary_unique hlr (hg i) (hgk i) A _ hd hinit
  intro t _
  exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hq _) (abs_nonneg _))

lemma matching_nonzero_rows {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (L Q : ℝ≥0) (hL : LipschitzWith L M)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (hXf : X (C,θ) r = -symDiag k) :
    ∀ i, ∃ j, C i j ≠ 0 := by
  intro i
  by_contra hn
  push Not at hn
  have hh := vanishing_row_stationary hlr M L Q hL q hq g hg k hgk hc he u X hXi hXd C θ i hn r ⟨hlr,le_refl _⟩
  rw [hXf] at hh
  change -diagonal k i i = k i at hh
  rw [diagonal_apply_eq] at hh
  linarith [hk i]

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set ContinuationGap
variable {N : ℕ}

lemma isClosed_lower : IsClosed {C : Matrix (Fin N) (Fin N) ℝ | ∀ i j, i < j → C i j = 0} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

lemma compact_lower_box (R : ℝ) : IsCompact {C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} := by
  have hh := (isClosed_lower (N := N)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin N ↦ -R) (fun _ _ : Fin N ↦ R)))
  convert! hh using 1
  ext C
  change (∀ i j, |C.val i j| ≤ R) ↔ ((∀ i j, -R ≤ C.val i j) ∧ (∀ i j, C.val i j ≤ R))
  constructor
  · intro h
    exact ⟨fun i j ↦ (abs_le.mp (h i j)).1,fun i j ↦ (abs_le.mp (h i j)).2⟩
  · rintro ⟨hl,hu⟩ i j
    exact abs_le.mpr ⟨hl i j,hu i j⟩

lemma compact_matching_zeros (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hc : Continuous (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1))
    (R : ℝ) (hb : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ C, Φ θ C = 0 → ∀ i j, |C.val i j| ≤ R) :
    IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0} := by
  apply ((compact_lower_box R).prod isCompact_Icc).of_isClosed_subset
    ((isClosed_Icc.preimage continuous_snd).inter (isClosed_eq hc continuous_const))
  intro z hz
  exact ⟨hb z.2 hz.1 z.1 hz.2,hz.1⟩

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix ContinuationGap
variable {N : ℕ}

lemma terminal_zero_parameter {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (hM : Continuous M) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) (X : ℝ → Sym N)
    (hXi : X l = symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,0) t (X t)) (Icc l r) t) :
    (X r + symDiag k).val = 2 • diagonal k - ε⁻¹ • (C*C.transpose) := by
  have hh := flow_integral_sub hlr M hM u hu C X hXd
  simp only [mul_zero,zero_smul,zero_sub,hXi] at hh
  have he := congrArg (fun A : Sym N ↦ A.val) hh
  change -(ε⁻¹ • (∫ t in l..r, symOuter (C*ᵥu t)).val) = (X r).val - diagonal k at he
  rw [integral_outer_mulVec hlr u hu ho C] at he
  have he' := sub_eq_iff_eq_add.mp he.symm
  change (X r).val + diagonal k = _
  rw [he']
  simp only [two_smul]
  abel

lemma terminal_matching {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε)
    (M : Sym N → Sym N) (L B Q : ℝ≥0) (hL : LipschitzWith L M) (hB : ∀ A, ‖M A‖ ≤ B)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    ∃ (C : LowerSpace N) (X : ℝ → Sym N), X l = symDiag k ∧ X r = -symDiag k ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt X (ε⁻¹ • (M (X t) - symOuter (C.val *ᵥ u t))) (Icc l r) t) ∧
      ‖C.val * C.val.transpose‖ ≤ |ε| * (2*‖k‖) + (r-l)*B := by
  obtain ⟨Y,hYi,hYd,hYc⟩ := matrix_flow_exists hlr ε k u hu M L B hL hB
  let Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ := fun θ C ↦ (Y (C.val,θ) r + symDiag k).val
  have hΦc : Continuous (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) := by
    have hYr : Continuous (fun p ↦ Y p r) := hYc.comp
      (continuous_id.prodMk (continuous_const (y := (⟨r,hlr,le_refl r⟩ : Icc l r))))
    exact ((hYr.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).add continuous_const).subtype_val
  have hzero (θ : ℝ) (C : LowerSpace N) (h : Φ θ C = 0) : Y (C.val,θ) r = -symDiag k := by
    apply eq_neg_iff_add_eq_zero.mpr
    apply Subtype.ext
    exact h
  have hsym (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N) : (Φ θ C).IsHermitian :=
    (Y (C.val,θ) r + symDiag k).prop
  have heq (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N)
      (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
      Φ θ (rowSign s C) = signConjugate s (Φ θ C) := by
    have hh := matrix_flow_equivariant hL k u Y hYi hYd s hs (he s hs) C.val θ ⟨hlr,le_refl r⟩
    change (Y ((rowSign s C).val,θ) r + symDiag k).val = (symConj s (Y (C.val,θ) r + symDiag k)).val
    rw [map_add,symConj_diag s hs]
    exact congrArg (fun A : Sym N ↦ (A + symDiag k).val) hh
  have hinit (C : LowerSpace N) : Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val*C.val.transpose) :=
    terminal_zero_parameter hlr M hL.continuous k u hu ho C.val (Y (C.val,0)) (hYi _) (hYd _)
  have hcomp : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0} := by
    apply compact_matching_zeros Φ hΦc (max (|ε| * (2*‖k‖) + (r-l)*B) 0 + 1)
    intro θ hθ C hC
    exact gram_entry_bound C.val (matching_gram_norm hlr (ne_of_gt hε) M hL.continuous B hB k u hu ho C.val
      hθ (Y (C.val,θ)) (hYi _) (hzero θ C hC) (hYd _))
  have hn (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N) (hC : Φ θ C = 0) : NonzeroRows C :=
    matching_nonzero_rows hlr M L Q hL q hq g hg k hk hgk hc he u Y hYi hYd C.val θ (hzero θ C hC)
  obtain ⟨C,hC⟩ := PathTopology.equivariant_continuation N ε k hε hk Φ hΦc.continuousOn hsym heq hinit hcomp hn
  refine ⟨C,Y (C.val,1),hYi _,hzero 1 C hC,?_,?_⟩
  · intro t ht
    simpa only [flowRhs,mul_one,smul_sub] using hYd (C.val,1) t ht
  · exact matching_gram_norm hlr (ne_of_gt hε) M hL.continuous B hB k u hu ho C.val
      ⟨zero_le_one,le_refl _⟩ (Y (C.val,1)) (hYi _) (hzero 1 C hC) (hYd _)

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
