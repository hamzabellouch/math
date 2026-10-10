import OAI.Combinatorics.Sidorenko.Normalization

namespace OAI


section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Count
variable {I K V : Type*} [Fintype I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem uniformMean_mul_card (f : I → ℝ) :
    (Fintype.card I : ℝ)*uniformMean f=∑ i, f i := by
  by_cases h : Fintype.card I=0
  · have := Fintype.card_eq_zero_iff.mp h
    simp [uniformMean]
  · unfold uniformMean
    field_simp

theorem restrictionSign_count (U : I → Submodule K V) (Q : SymForm K V) (ξ : ℤ) :
    (Nat.card {i : I // (Q.val.restrict (U i)).Nondegenerate ∧
      discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ} : ℝ) =
    (Fintype.card I : ℝ)*uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q)) := by
  classical
  rw [uniformMean_mul_card,Nat.card_eq_fintype_card,Fintype.card_subtype,←Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  change (if (Q.val.restrict (U i)).Nondegenerate ∧
    discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 : ℝ) =
    if (Q.val.restrict (U i)).Nondegenerate then
      if discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 else 0
  split_ifs <;> simp_all
end Count
section Identities
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}

noncomputable def signedProjectorIsotropicEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ)
    (L : LinearMap.BilinForm K (Fin D → K)) :
    {A : SignedProjector Q r ξ // L.restrict A.val.val.toLin'.range=0} ≃
    {U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} //
      (Q.toBilin'.restrict U.val.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val.val)=ξ} where
  toFun A :=
    let U := signedProjectorSubspaceEquiv Q hQ hdet r ξ A.val
    ⟨⟨U.val,by
      change L.restrict (centerSubspaceEquiv Q hQ hdet A.val.val).val=0
      rw [centerSubspaceEquiv_val]; exact A.property⟩,U.property⟩
  invFun U :=
    let A := (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩
    ⟨A,by
      rw [←centerSubspaceEquiv_val Q hQ hdet]
      change L.restrict ((signedProjectorSubspaceEquiv Q hQ hdet r ξ) A).val.val=0
      rw [show (signedProjectorSubspaceEquiv Q hQ hdet r ξ) A=⟨U.val.val,U.property⟩ from
        Equiv.apply_symm_apply _ _]
      exact U.val.property⟩
  left_inv A := by
    apply Subtype.ext
    exact (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((signedProjectorSubspaceEquiv Q hQ hdet r ξ)
      ((signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]

noncomputable def pairRestrictionFraction (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  exact uniformMean (fun U : DimSubspace K (Fin D → K) r =>
    formSignIndicator ξ (symFormPull U.val.subtype (matrixFormEquiv D Q)))

noncomputable def isotropicRestrictionFraction (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  exact uniformMean (fun U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} =>
    formSignIndicator ξ (symFormPull U.val.val.subtype (matrixFormEquiv D Q)))

theorem pairCenter_card (hd : D=2*r) (B : SymMatrix K D) (hB : B.val.det≠0)
    (ξ ζ : ℤ) (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} : ℝ) =
    (Nat.card (DimSubspace K (Fin D → K) r) : ℝ) *
      pairRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D) r ξ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((pairSignedCenterEquiv hd B hB ξ ζ hm).trans
    (signedProjectorSubspaceEquiv B.val⁻¹ B.property.inv hn r ξ))]
  exact (restrictionSign_count (fun U : DimSubspace K (Fin D → K) r => U.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)

theorem tripleCenter_card (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} : ℝ) =
    (Nat.card {U : DimSubspace K (Fin D → K) r //
      (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} : ℝ) *
      isotropicRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D)
        (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0}
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((tripleSignedCenterEquiv hd B C hB hC ξ ζ θ hmB hmC).trans
    (signedProjectorIsotropicEquiv B.val⁻¹ B.property.inv hn r ξ _))]
  exact (restrictionSign_count (fun U : {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} => U.val.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)
end Identities
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairCoefficient (r : ℕ) (ξ ζ : ℤ) : ℝ :=
  (Nat.card (DimSubspace K (Fin (2*r) → K) r) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)
noncomputable def tripleCoefficient (r : ℕ) (ξ ζ θ : ℤ) : ℝ :=
  (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)

theorem pair_exponent_cancel (r : ℕ) :
    r*r+2*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h := triangular_nat_add r r
  have he : r+r+1=2*r+1 := by omega
  rw [he] at h
  omega

theorem triple_exponent_cancel (r : ℕ) :
    r.choose 2+3*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h : (r.choose 2 : ℚ)+3*((r+1).choose 2 : ℚ)=((2*r+1).choose 2 : ℚ) := by
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  exact_mod_cast h

theorem pairCoefficient_normalized (r : ℕ) (ξ ζ : ℤ) :
    pairCoefficient (K := K) r ξ ζ =
      grassmannFactor (2*r) r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  unfold pairCoefficient
  rw [subspace_count_normalized r (by simp; omega),←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card]
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega,Nat.cast_pow]
  rw [←pair_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

theorem tripleCoefficient_normalized (hK : ringChar K≠2) (r : ℕ) (ξ ζ θ : ℤ) :
    tripleCoefficient (K := K) r ξ ζ θ =
      orthogonalFactor r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r θ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  have he := maxOrthogonal_normalized (K := K) hK r
  unfold tripleCoefficient
  rw [←he,←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card,Nat.cast_pow,
    ←triple_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

theorem pairCoefficient_nonneg (r : ℕ) (ξ ζ : ℤ) : 0≤pairCoefficient (K := K) r ξ ζ := by
  unfold pairCoefficient layerMass
  positivity

theorem tripleCoefficient_nonneg (r : ℕ) (ξ ζ θ : ℤ) : 0≤tripleCoefficient (K := K) r ξ ζ θ := by
  unfold tripleCoefficient layerMass
  positivity
end Coeff

theorem pairCoefficient_tendsto (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => pairCoefficient (K := ZMod q.val) r ξ ζ)
      primeInfinity (nhds 4) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have hf := (grassmannFactor_tendsto (2*r) r (by omega)).comp primeInfinity_real_tendsto
  have h := hf.div (hx.mul hz) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  simp_rw [pairCoefficient_normalized,ZMod.card]
  convert h using 1

theorem tripleCoefficient_tendsto (r : ℕ) (hr : 0<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => tripleCoefficient (K := ZMod q.val) r ξ ζ θ)
      primeInfinity (nhds 16) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have ht := layerMass_tendsto (2*r) r hr (by omega) hθ
  have hf := (orthogonalFactor_tendsto r hr).comp primeInfinity_real_tendsto
  have h := hf.div ((hx.mul hz).mul ht) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  have he (q : OddPrime) := tripleCoefficient_normalized (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r ξ ζ θ
  simp only [ZMod.card] at he
  simp_rw [he]
  exact h
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
theorem maxOrthogonal_card_lower (r : ℕ) :
    Fintype.card K ^ r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  classical
  let : Finite (Module.Dual K (Fin r → K)) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (f := graphMaxOrthogonal (K := K) (⊤ : Submodule K (Fin r → K))) (graphMaxOrthogonal_form_injective
    (K := K) (⊤ : Submodule K (Fin r → K)))
  simpa only [altForm_card,finrank_top,Module.finrank_fin_fun] using h

theorem halfIsotropic_card (r : ℕ) (L : LinearMap.BilinForm K (Fin (2*r) → K))
    (hs : L.IsSymm) (hL : L.Nondegenerate) (hK : ringChar K≠2)
    (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  rw [Nat.card_congr (halfIsotropicEquiv L hL r (by simp))]
  exact split_form_card L hs hL hK r (by simp) hc

omit [DecidableEq K] in
theorem pairFamily_card_ge (r : ℕ) (hr : 0<r) :
    (Fintype.card K : ℝ) ≤ Nat.card (DimSubspace K (Fin (2*r) → K) r) := by
  have h := subspace_count_lower (K := K) (V := Fin (2*r) → K) r (by simp; omega)
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega] at h
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (show 1≤r*r from Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

theorem isotropicFamily_card_ge (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    (Fintype.card K : ℝ) ≤ Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} := by
  rw [halfIsotropic_card r L hs hL hK hc]
  have h : (Fintype.card K : ℝ)^r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
    exact_mod_cast maxOrthogonal_card_lower (K := K) r
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (Nat.choose_pos (show 2≤r by omega))
end Sizes
section Bounds
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}

theorem matrix_restriction_family_L1 (U : I → Submodule K (Fin D → K))
    (hinj : Function.Injective U) (hd : ∀ i, finrank K (U i)=r)
    (hc : (Fintype.card K : ℝ)≤Fintype.card I) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K D =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype (matrixFormEquiv D Q)))-1/2|) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  have hq : (0 : ℝ)<Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hi : (0 : ℝ)<Fintype.card I := hq.trans_le hc
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hi)
  have he := uniformMean_equiv (matrixFormEquiv (K := K) D)
    (fun Q => |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|)
  dsimp only [Function.comp_def] at he
  rw [he]
  have h := restriction_family_L1_sq U hinj r hd hK hξ
  have hiq : 1/(Fintype.card I : ℝ)≤1/(Fintype.card K : ℝ) := one_div_le_one_div_of_le hq hc
  have ht : (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) ≤
      ((r : ℝ)+1)/(Fintype.card K : ℝ) := by rw [add_div]; linarith
  exact (Real.le_sqrt (uniformMean_nonneg (fun _ => abs_nonneg _)) (by positivity)).mpr (h.trans ht)

theorem pairRestrictionFraction_L1 (r : ℕ) (hr : 0<r) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |pairRestrictionFraction Q r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin (2*r) → K) r)
  exact matrix_restriction_family_L1 (fun U : DimSubspace K (Fin (2*r) → K) r => U.val)
    Subtype.val_injective (fun U => U.property)
    (by simpa only [Nat.card_eq_fintype_card] using pairFamily_card_ge (K := K) r hr) hK hξ

theorem isotropicRestrictionFraction_L1 (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r))
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |isotropicRestrictionFraction Q L r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0}
  exact matrix_restriction_family_L1 (fun U : {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} => U.val.val)
    (Subtype.val_injective.comp Subtype.val_injective) (fun U => U.val.property)
    (by simpa only [Nat.card_eq_fintype_card] using isotropicFamily_card_ge r hr L hs hL hK hc) hK hξ
end Bounds
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

omit [DecidableEq I] in
theorem uniformMean_sum (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

theorem uniformMean_coordinate [Nonempty A] (i : I) (f : A → ℝ) :
    uniformMean (fun x : I → A => f (x i))=uniformMean f := by
  classical
  rw [←uniformMean_equiv (Equiv.piSplitAt i (fun _ : I => A)).symm,uniformMean_prod]
  simp only [Function.comp_def,Equiv.piSplitAt,Equiv.coe_fn_symm_mk]
  simp [uniformMean_const]

theorem uniformMean_update [Nonempty A] (i : I) (f : (I → A) → ℝ) :
    uniformMean f=uniformMean (fun x : I → A => uniformMean (fun a : A => f (Function.update x i a))) := by
  classical
  let e := Equiv.funSplitAt i A
  have he (x : A × ({j : I // j≠i} → A)) (a : A) :
      Function.update (e.symm x) i a=e.symm (a,x.2) := by
    ext j
    by_cases hj : j=i
    · subst j; simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
    · simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hj]
  rw [←uniformMean_equiv e.symm,uniformMean_prod]
  conv_rhs => rw [←uniformMean_equiv e.symm,uniformMean_prod]
  simp only [Function.comp_def,he]
  rw [uniformMean_const]
  exact uniformMean_swap _

theorem uniformMean_mul_right (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a*c)=uniformMean f*c := by
  simpa only [mul_comm] using uniformMean_mul c f

theorem uniformMean_ite_le [Nonempty A] (P : A → Prop) [DecidablePred P]
    (f : A → ℝ) (b : ℝ) (hf : ∀ a, P a → f a≤b) (hb : 0≤b) :
    uniformMean (fun a => if P a then f a else 0)≤b := by
  apply uniformMean_bound
  intro a
  split_ifs with h
  · exact hf a h
  · exact hb
end Mean
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Inverting
variable {K : Type*} [Field K] [Fintype K]

/-- Extend inversion by fixing singular forms. Unlike the total matrix inverse,
this is a permutation of the entire symmetric-matrix probability space. -/
noncomputable def symmetricInverse (D : ℕ) (M : SymMatrix K D) : SymMatrix K D :=
  by
  classical
  exact if M.val.det = 0 then M else ⟨M.val⁻¹, M.property.inv⟩

omit [Fintype K] in
 theorem symmetricInverse_involutive (D : ℕ) : Function.Involutive (symmetricInverse (K := K) D) := by
  classical
  intro M
  by_cases h : M.val.det = 0
  · have he : symmetricInverse D M = M := by simp only [symmetricInverse, h, ↓reduceIte]
    rw [he, he]
  · let M' : SymMatrix K D := ⟨M.val⁻¹, M.property.inv⟩
    have he : symmetricInverse D M = M' := by simp only [symmetricInverse, h, ↓reduceIte, M']
    have hn : M'.val.det ≠ 0 := (M.val.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr h)).ne_zero
    have he' : symmetricInverse D M' = ⟨M'.val⁻¹, M'.property.inv⟩ := by
      simp only [symmetricInverse, hn, ↓reduceIte]
    rw [he, he']
    exact Subtype.ext (M.val.nonsing_inv_nonsing_inv (isUnit_iff_ne_zero.mpr h))

noncomputable def symmetricInverseEquiv (D : ℕ) : SymMatrix K D ≃ SymMatrix K D :=
  (symmetricInverse_involutive D).toPerm

end Inverting
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairLocal (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B))
noncomputable def tripleLocal (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) *
    rankKernel K (2*r) r θ (A-C))

def pairMatch (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : Prop :=
  quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ

def tripleMatch (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : Prop :=
  pairMatch r ξ ζ B ∧ pairMatch r ξ θ C ∧ pairMatch r ζ θ (C-B)

theorem pairLocal_card (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairLocal r ξ ζ B =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm]
  unfold pairLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl

theorem tripleLocal_card (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    tripleLocal r ξ ζ θ B C =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ ∧ A-C ∈ signedLayer K (2*r) r θ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ ∧
        A-C ∈ signedLayer K (2*r) r θ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm,mul_assoc]
  unfold tripleLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl

theorem pairLocal_match (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : pairMatch r ξ ζ B) :
    pairLocal r ξ ζ B = pairCoefficient (K := K) r ξ ζ *
      pairRestrictionFraction (symmetricInverse (2*r) B) r ξ := by
  rw [pairLocal_card,pairCenter_card rfl B hB ξ ζ hm]
  simp only [symmetricInverse,hB,ite_false]
  unfold pairCoefficient
  ring

theorem pairLocal_mismatch (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : ¬pairMatch r ξ ζ B) : pairLocal r ξ ζ B=0 := by
  unfold pairLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B)=0 := by
    unfold rankKernel
    split_ifs with hx hz
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,ht⟩ := (mem_signedLayer ..).mp hz
      have h := signed_pair_compatibility rfl A B hB ha hb
      rw [hs,ht] at h
      exact (hm h).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0

theorem tripleLocal_mismatch (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    (hm : ¬tripleMatch r ξ ζ θ B C) : tripleLocal r ξ ζ θ B C=0 := by
  unfold tripleLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C)=0 := by
    unfold rankKernel
    split_ifs with hx hz ht
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,hz⟩ := (mem_signedLayer ..).mp hz
      obtain ⟨hc,ht⟩ := (mem_signedLayer ..).mp ht
      have h1 := signed_pair_compatibility rfl A B hB ha hb
      have h2 := signed_pair_compatibility rfl A C hC ha hc
      have h3 := signed_pair_compatibility rfl (A-B) (C-B) hBC hb (by simpa using hc)
      simp only [sub_sub_sub_cancel_right] at h3
      rw [hs,hz] at h1
      rw [hs,ht] at h2
      rw [hz,ht] at h3
      exact (hm ⟨h1,h2,h3⟩).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0
omit [Fintype K] [DecidableEq K] in
theorem inverse_difference_det (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) :
    (B.val⁻¹-C.val⁻¹).det = B.val.det⁻¹ * (C-B).val.det * C.val.det⁻¹ := by
  rw [Matrix.inv_sub_inv (by
    exact iff_of_true ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hC)))]
  simp only [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Submodule.coe_sub]

omit [Fintype K] [DecidableEq K] in
theorem inverse_difference_nondegenerate (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    (B.val⁻¹-C.val⁻¹).toBilin'.Nondegenerate := by
  apply Matrix.nondegenerate_toBilin'_iff.mpr
  apply Matrix.nondegenerate_iff_det_ne_zero.mpr
  rw [inverse_difference_det D B C hB hC]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hB) hBC) (inv_ne_zero hC)

theorem matching_inverse_difference_split (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    discriminantSign (B.val⁻¹-C.val⁻¹).toBilin'
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv)) =
        quadraticChar K ((-1 : K)^r) := by
  rw [discriminantSign_nondegenerate _ _ (inverse_difference_nondegenerate (2*r) B C hB hC hBC)
    (Pi.basisFun K (Fin (2*r)))]
  change quadraticChar K ((B.val⁻¹-C.val⁻¹).toBilin'.toMatrix').det = _
  rw [LinearMap.BilinForm.toMatrix'_toBilin',inverse_difference_det (2*r) B C hB hC,
    map_mul,map_mul,quadraticChar_inverse hB,quadraticChar_inverse hC]
  rw [hm.1,hm.2.1,hm.2.2]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  have hx : ξ^2=1 := by rcases hξ with rfl | rfl <;> norm_num
  have hz : ζ^2=1 := by rcases hζ with rfl | rfl <;> norm_num
  have ht : θ^2=1 := by rcases hθ with rfl | rfl <;> norm_num
  calc
    _ = quadraticChar K ((-1 : K)^r) * (quadraticChar K ((-1 : K)^r))^2 * ξ^2 * ζ^2 * θ^2 := by ring
    _ = _ := by rw [hc,hx,hz,ht]; ring

theorem tripleLocal_match (hK : ringChar K≠2) (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    tripleLocal r ξ ζ θ B C = tripleCoefficient (K := K) r ξ ζ θ *
      isotropicRestrictionFraction (symmetricInverse (2*r) B) (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  rw [tripleLocal_card,tripleCenter_card rfl B C hB hC ξ ζ θ hm.1 hm.2.1,
    halfIsotropic_card r _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv))
      (inverse_difference_nondegenerate (2*r) B C hB hC hBC) hK
      (matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm)]
  simp only [symmetricInverse,hB,ite_false]
  unfold tripleCoefficient
  ring
end Center
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_le_one {f : A → ℝ} (hf : ∀ a, f a ≤ 1) : uniformMean f ≤ 1 := by
  cases isEmpty_or_nonempty A
  · simp [uniformMean]
  · exact uniformMean_bound hf
variable [AddCommGroup A]
theorem uniformMean_subLeft (a : A) (f : A → ℝ) :
    uniformMean (fun x => f (a-x))=uniformMean f :=
  uniformMean_equiv (Equiv.subLeft a) f
end Means
section Range
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
theorem pairRestrictionFraction_range (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) :
    0 ≤ pairRestrictionFraction Q r ξ ∧ pairRestrictionFraction Q r ξ ≤ 1 := by
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  unfold pairRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩
theorem isotropicRestrictionFraction_range (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) :
    0 ≤ isotropicRestrictionFraction Q L r ξ ∧ isotropicRestrictionFraction Q L r ξ ≤ 1 := by
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  unfold isotropicRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩
omit [DecidableEq K] in
theorem uniformMean_inverse (f : SymMatrix K D → ℝ) :
    uniformMean (fun B => f (symmetricInverse D B))=uniformMean f :=
  uniformMean_equiv (symmetricInverseEquiv D) f

omit [DecidableEq K] in
theorem uniformMean_inverse_difference (f : SymMatrix K D → SymMatrix K D → ℝ) :
    uniformMean (fun B => uniformMean fun C =>
      f (symmetricInverse D B) (symmetricInverse D B-symmetricInverse D C)) =
        uniformMean (fun L => uniformMean fun Q => f Q L) := by
  calc
    _ = uniformMean (fun B => uniformMean fun T => f (symmetricInverse D B) (symmetricInverse D B-T)) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_inverse (fun T => f (symmetricInverse D B) (symmetricInverse D B-T))
    _ = uniformMean (fun B => uniformMean fun L => f (symmetricInverse D B) L) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_subLeft (symmetricInverse D B) (f (symmetricInverse D B))
    _ = uniformMean (fun Q => uniformMean fun L => f Q L) :=
      uniformMean_inverse (fun Q => uniformMean fun L => f Q L)
    _ = _ := uniformMean_swap _
end Range
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators

theorem scalar_fraction_error (c f m : ℝ) (hc : 0 ≤ c) :
    |c*f-m| ≤ |c/2-m|+c*|f-1/2| := by
  calc
    _ = |(c/2-m)+c*(f-1/2)| := by congr 1; ring
    _ ≤ |c/2-m|+|c*(f-1/2)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_of_nonneg hc]
section Error
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def matrixSplit (r : ℕ) (L : SymMatrix K (2*r)) : Prop :=
  L.val.det≠0 ∧ discriminantSign L.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)=quadraticChar K ((-1 : K)^r)

noncomputable def pairError (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 then |pairLocal r ξ ζ B-(if pairMatch r ξ ζ B then 2 else 0)| else 0
noncomputable def tripleError (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 ∧ C.val.det≠0 ∧ (C-B).val.det≠0 then
    |tripleLocal r ξ ζ θ B C-(if tripleMatch r ξ ζ θ B C then 8 else 0)| else 0

noncomputable def splitFractionError (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) : ℝ :=
  if matrixSplit r L then |isotropicRestrictionFraction Q L.val.toBilin' r ξ-1/2| else 0

theorem splitFractionError_nonneg (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) :
    0 ≤ splitFractionError r ξ Q L := by unfold splitFractionError; split <;> positivity

theorem pairError_pointwise (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairError r ξ ζ B ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ*|pairRestrictionFraction (symmetricInverse (2*r) B) r ξ-1/2| := by
  have hc := pairCoefficient_nonneg (K := K) r ξ ζ
  unfold pairError
  split_ifs with hB hm
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact scalar_fraction_error _ _ _ hc
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity

theorem tripleError_pointwise (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) :
    tripleError r ξ ζ θ B C ≤ |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
      tripleCoefficient (K := K) r ξ ζ θ * splitFractionError r ξ
        (symmetricInverse (2*r) B) (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
  have hc := tripleCoefficient_nonneg (K := K) r ξ ζ θ
  have hf := splitFractionError_nonneg r ξ (symmetricInverse (2*r) B)
    (symmetricInverse (2*r) B-symmetricInverse (2*r) C)
  unfold tripleError
  split_ifs with ht hm
  · obtain ⟨hB,hC,hBC⟩ := ht
    have hs : matrixSplit r (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
      simp only [matrixSplit,symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
      exact ⟨Matrix.nondegenerate_iff_det_ne_zero.mp
        (Matrix.nondegenerate_toBilin'_iff.mp (inverse_difference_nondegenerate (2*r) B C hB hC hBC)),
        matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm⟩
    rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm,splitFractionError,ite_eq_left hs]
    simp only [symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
    exact scalar_fraction_error _ _ _ hc
  · rw [tripleLocal_mismatch r ξ ζ θ B C ht.1 ht.2.1 ht.2.2 hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity

theorem splitFractionError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (L : SymMatrix K (2*r)) :
    uniformMean (fun Q => splitFractionError r ξ Q L) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  by_cases h : matrixSplit r L
  · simp only [splitFractionError,h,ite_true]
    exact isotropicRestrictionFraction_L1 r hr _
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr h.1))
      hK h.2 hξ
  · simp only [splitFractionError,h,ite_false,uniformMean_const]
    positivity

theorem pairError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (pairError (K := K) r ξ ζ) ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (pairError_pointwise r ξ ζ)).trans
  rw [uniformMean_add,uniformMean_const,uniformMean_mul,
    uniformMean_inverse (fun Q => |pairRestrictionFraction Q r ξ-1/2|)]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (pairRestrictionFraction_L1 r hr hK hξ)
    (pairCoefficient_nonneg (K := K) r ξ ζ))

theorem tripleError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    uniformMean (fun B => uniformMean (fun C => tripleError (K := K) r ξ ζ θ B C)) ≤
      |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
        tripleCoefficient (K := K) r ξ ζ θ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (fun B => uniformMean_mono (tripleError_pointwise hK r hξ hζ hθ B))).trans
  simp_rw [uniformMean_add,uniformMean_const,uniformMean_mul]
  rw [uniformMean_inverse_difference]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (uniformMean_bound (splitFractionError_mean hK r hr hξ)) (tripleCoefficient_nonneg (K := K) r ξ ζ θ))
end Error
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
theorem pairLocal_nonneg (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairLocal r ξ ζ B :=
  uniformMean_nonneg fun _ => mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)
theorem tripleLocal_nonneg (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleLocal r ξ ζ θ B C :=
  uniformMean_nonneg fun _ => mul_nonneg
    (mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)) (rankKernel_nonneg ..)
theorem pairError_nonneg (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairError r ξ ζ B := by
  unfold pairError; split <;> positivity
theorem tripleError_nonneg (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleError r ξ ζ θ B C := by unfold tripleError; split <;> positivity

theorem pairLocal_bound (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairLocal r ξ ζ B ≤ pairCoefficient (K := K) r ξ ζ := by
  by_cases hm : pairMatch r ξ ζ B
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact mul_le_of_le_one_right (pairCoefficient_nonneg ..) (pairRestrictionFraction_range _ _ _).2
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    exact pairCoefficient_nonneg ..

theorem tripleLocal_bound (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    tripleLocal r ξ ζ θ B C ≤ tripleCoefficient (K := K) r ξ ζ θ := by
  by_cases hm : tripleMatch r ξ ζ θ B C
  · rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm]
    exact mul_le_of_le_one_right (tripleCoefficient_nonneg ..) (isotropicRestrictionFraction_range _ _ _ _).2
  · rw [tripleLocal_mismatch r ξ ζ θ B C hB hC hBC hm]
    exact tripleCoefficient_nonneg ..
end Bounds

theorem localFraction_error_tendsto (r : ℕ) :
    Tendsto (fun q : OddPrime => Real.sqrt (((r : ℝ)+1)/(q.val : ℝ))) primeInfinity (nhds 0) := by
  have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul ((r : ℝ)+1)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,←div_eq_mul_inv] using hs

theorem pairError_tendsto (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (pairError (K := ZMod q.val) r ξ ζ)) primeInfinity (nhds 0) := by
  have hc := pairCoefficient_tendsto r hr hξ hζ
  have ha := ((hc.div_const 2).sub_const 2).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg (pairError_nonneg r ξ ζ)) (fun q => ?_) h
  simpa only [ZMod.card] using pairError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ

theorem tripleError_tendsto (r : ℕ) (hr : 1<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (fun B => uniformMean
      (fun C => tripleError (K := ZMod q.val) r ξ ζ θ B C))) primeInfinity (nhds 0) := by
  have hc := tripleCoefficient_tendsto r (by omega) hξ hζ hθ
  have ha := ((hc.div_const 2).sub_const 8).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg fun B => uniformMean_nonneg (tripleError_nonneg r ξ ζ θ B))
    (fun q => ?_) h
  simpa only [ZMod.card] using tripleError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ hζ hθ
end SidorenkoCounterexample

end

end OAI
