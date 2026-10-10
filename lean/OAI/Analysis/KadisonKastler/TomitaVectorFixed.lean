import OAI.Analysis.KadisonKastler.TomitaVectorProjection

namespace OAI

/-! # The polar conjugation fixes the cyclic separating vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
private theorem positive_square_eigenvector (S : H →L[ℂ] H) (hS : S.IsPositive)
    (k : ℝ) (hk : 0 < k) (x : H) (hx : S (S x) = (k : ℂ) ^ 2 • x) :
    S x = (k : ℂ) • x := by
  let v := S x - (k : ℂ) • x
  have hSv : S v = (-k : ℂ) • v := by
    change S (S x - (k : ℂ) • x) = (-k : ℂ) • (S x - (k : ℂ) • x)
    rw [map_sub, map_smul, hx]
    module
  have hp0 := hS.re_inner_nonneg_left v
  rw [hSv] at hp0
  rw [← Complex.ofReal_neg, Complex.coe_smul, inner_smul_left_eq_smul] at hp0
  have hp : 0 ≤ -k * ‖v‖ ^ 2 := by
    change 0 ≤ (-k • inner ℂ v v).re at hp0
    rw [Complex.smul_re] at hp0
    change 0 ≤ -k * RCLike.re (inner ℂ v v) at hp0
    rwa [inner_self_eq_norm_sq] at hp0
  have hmul : k * ‖v‖ ^ 2 ≤ 0 := by linarith
  have hsq : ‖v‖ ^ 2 ≤ 0 := by
    by_contra hs
    exact (not_lt_of_ge hmul) (mul_pos hk (lt_of_not_ge hs))
  have hv : v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp hv

/-- Positive eigenvalues of the graph resolvent pass to its positive square root. -/
theorem tomitaGraphRoot_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H)
    {t : ℝ} (ht : 0 < t)
    (hx : graphResolvent M J Ω 1 x = (t : ℂ) • x) :
    tomitaGraphRoot (M := M) J Ω x = (Real.sqrt t : ℂ) • x := by
  have hpos : (tomitaGraphRoot (M := M) J Ω).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp
      (CFC.sqrt_nonneg (graphResolvent M J Ω 1))
  apply positive_square_eigenvector (tomitaGraphRoot (M := M) J Ω) hpos
    (Real.sqrt t) (Real.sqrt_pos.2 ht)
  have hs : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  rw [hs]
  exact (congrArg (fun T : H →L[ℂ] H => T x)
    (tomitaGraphRoot_square (M := M) J Ω)).trans hx

theorem tomitaGraphRoot_half_eigen (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H)
    (hx : graphResolvent M J Ω 1 x = (1 / 2 : ℂ) • x) :
    tomitaGraphRoot (M := M) J Ω x = (Real.sqrt (1 / 2) : ℂ) • x := by
  have hpos : (tomitaGraphRoot (M := M) J Ω).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp
      (CFC.sqrt_nonneg (graphResolvent M J Ω 1))
  apply positive_square_eigenvector (tomitaGraphRoot (M := M) J Ω) hpos
    (Real.sqrt (1 / 2)) (Real.sqrt_pos.2 (by norm_num))
  have hs : (Real.sqrt (1 / 2) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    have hsReal : Real.sqrt (1 / 2) ^ 2 = (1 / 2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    calc
      _ = ((Real.sqrt (1 / 2) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal hsReal
      _ = (1 / 2 : ℂ) := by norm_num
  rw [hs]
  have h := congrArg (fun T : H →L[ℂ] H => T x) (tomitaGraphRoot_square (M := M) J Ω)
  exact h.trans hx

theorem tomitaGraphRoot_state (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    tomitaGraphRoot (M := M) J Ω Ω = (Real.sqrt (1 / 2) : ℂ) • Ω :=
  tomitaGraphRoot_half_eigen J Ω Ω (graphResolvent_state J Ω)

theorem tomitaPolarConjugation_fixes_vector (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc Ω = Ω := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  let F := tomitaGraphAntiunitary (M := M) J Ω
  let k : ℂ := Real.sqrt (1 / 2)
  have hk : k ≠ 0 := by
    change (Real.sqrt (1 / 2) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1 / 2)))
  have hroot : k • U Ω = (tomitaGraphFirst (M := M) J Ω).adjoint Ω := by
    have h := tomitaPolarCoordinates_root J Ω hsep hcyc Ω
    rw [tomitaGraphRoot_state, map_smul] at h
    exact h
  have hfixed : F ((tomitaGraphFirst (M := M) J Ω).adjoint Ω) =
      (tomitaGraphFirst (M := M) J Ω).adjoint Ω := by
    apply Subtype.ext
    change tomitaGraphFlip J ((tomitaGraphFirst (M := M) J Ω).adjoint Ω).val = _
    rw [tomitaGraphFirst_adjoint_apply, rescaledGraphProjection_state]
    rw [(tomitaGraphFlip J).map_smulₛₗ]
    have hg := tomitaGraphFlip_vector J Ω (1 : Algebra M)
    have hhalf : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
      change star (1 / 2 : ℂ) = _
      simp
    rw [hhalf]
    change tomitaGraphFlip J (rescaledGraphVector J Ω 1 1) =
      rescaledGraphVector J Ω 1 (star (1 : H →L[ℂ] H)) at hg
    rw [star_one] at hg
    exact congrArg (fun v : TomitaGraphHilbert H => (1 / 2 : ℂ) • v) hg
  have hFU : F (U Ω) = U Ω := by
    apply smul_right_injective (M := rescaledGraphSubspace M J Ω 1) hk
    have h := congrArg F hroot
    rw [F.map_smulₛₗ, hfixed] at h
    have hstar : (starRingEnd ℂ) k = k := Complex.conj_ofReal _
    rw [hstar] at h
    exact h.trans hroot.symm
  change U.symm (F (U Ω)) = Ω
  rw [hFU, U.symm_apply_apply]

end

end KadisonKastler

end OAI
