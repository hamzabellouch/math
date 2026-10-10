import OAI.Combinatorics.Sidorenko.Restrictions

namespace OAI


section

namespace SidorenkoCounterexample
open scoped BigOperators
open Module Filter

noncomputable def grassmannFactor (D k : ℕ) (q : ℝ) : ℝ :=
  ∏ i : Fin k, (1 - 1 / q^(D-i.val)) / (1 - 1 / q^(k-i.val))

theorem grassmann_single_factor (D k i : ℕ) (hik : i ≤ k) (hkD : k ≤ D)
    (q : ℝ) (hq : q ≠ 0) :
    (q^D - q^i)/(q^k-q^i) = q^(D-k) *
      ((1 - 1/q^(D-i)) / (1 - 1/q^(k-i))) := by
  have hf (n : ℕ) (hi : i ≤ n) : q^n-q^i=q^n*(1-1/q^(n-i)) := by
    rw [mul_sub, mul_one, mul_one_div, div_eq_mul_inv,
      ← pow_sub₀ q hq (Nat.sub_le n i), Nat.sub_sub_self hi]
  rw [hf D (hik.trans hkD), hf k hik, mul_div_mul_comm,
    div_eq_mul_inv (q^D), ← pow_sub₀ q hq hkD]

theorem subspace_count_normalized {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype K] [Finite V] (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) =
      (Fintype.card K : ℝ)^(k*(finrank K V-k)) *
        grassmannFactor (finrank K V) k (Fintype.card K) := by
  rw [subspace_count_real k hk]
  have hf (i : Fin k) := grassmann_single_factor (finrank K V) k i.val i.isLt.le hk
    (Fintype.card K : ℝ) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm (finrank K V-k) k]
  rfl

theorem inverse_power_tendsto_zero (n : ℕ) (hn : 0<n) :
    Tendsto (fun q : ℝ => 1/q^n) atTop (nhds 0) := by
  simpa only [one_div, inv_pow, zero_pow (Nat.ne_zero_of_lt hn)] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n

theorem grassmannFactor_tendsto (D k : ℕ) (hk : k ≤ D) :
    Tendsto (grassmannFactor D k) atTop (nhds 1) := by
  unfold grassmannFactor
  have h (i : Fin k) : Tendsto (fun q : ℝ =>
      (1 - 1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds 1) := by
    have hD := inverse_power_tendsto_zero (D-i.val) (by omega)
    have hk' := inverse_power_tendsto_zero (k-i.val) (by omega)
    have ha : Tendsto (fun q : ℝ => 1-1/q^(D-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hD
    have hb : Tendsto (fun q : ℝ => 1-1/q^(k-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hk'
    have hc : Tendsto (fun q : ℝ =>
        (1-1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds ((1-0:ℝ)/(1-0))) :=
      (ha.div hb (by norm_num)).congr (fun _ => rfl)
    simpa only [sub_zero, div_self (one_ne_zero : (1:ℝ) ≠ 0)] using hc
  simpa using tendsto_finsetProd Finset.univ (fun i _ => h i)

theorem triangular_nat_add (r k : ℕ) :
    (r+k+1).choose 2 = (r+1).choose 2 + (k+1).choose 2 + r*k := by
  have h : (((r+k+1).choose 2 : ℕ) : ℚ) =
      ((r+1).choose 2 : ℚ) + ((k+1).choose 2 : ℚ) + (r:ℚ)*k := by
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
    ring
  exact_mod_cast h

theorem layerMass_normalized {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ * (Fintype.card K : ℝ)^((D-r+1).choose 2) =
      grassmannFactor D (D-r) (Fintype.card K) * symmetricSignProb (K := K) r ξ := by
  rw [layerMass_exact D r hrD hξ, subspace_count_normalized _ (by simp)]
  simp only [Module.finrank_pi, Fintype.card_fin, Nat.sub_sub_self hrD]
  have he : (D+1).choose 2 = (r+1).choose 2 + (D-r+1).choose 2 + (D-r)*r := by
    simpa only [Nat.add_sub_of_le hrD, Nat.mul_comm r (D-r)] using triangular_nat_add r (D-r)
  rw [he, pow_add, pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem primeInfinity_real_tendsto :
    Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop :=
  tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap

theorem symmetricSignProb_tendsto (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => symmetricSignProb (K := ZMod q.val) r ξ)
      primeInfinity (nhds (1/2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun q : OddPrime => (r:ℝ)/q.val) primeInfinity (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (r:ℝ)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro q
  simpa only [Real.norm_eq_abs,ZMod.card] using
    symmetricSignProb_error (K := ZMod q.val) r hr
      (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hξ

theorem layerMass_tendsto (D r : ℕ) (hr : 0<r) (hrD : r ≤ D)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => layerMass (ZMod q.val) D r ξ *
      (q.val:ℝ)^((D-r+1).choose 2)) primeInfinity (nhds (1/2)) := by
  have he (q : OddPrime) := layerMass_normalized (K := ZMod q.val) D r hrD hξ
  simp only [ZMod.card] at he
  simp_rw [he]
  simpa only [one_mul, Function.comp_def] using
    ((grassmannFactor_tendsto D (D-r) (Nat.sub_le ..)).comp
      primeInfinity_real_tendsto).mul (symmetricSignProb_tendsto r hr hξ)

end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Filter Topology
open scoped BigOperators
section CountDimension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [Finite V]
theorem maxOrthogonal_card_by_dimension (hK : ringChar K ≠ 2) :
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ k.val.choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [maxOrthogonal_card_sum hK,← Fintype.sum_fiberwise d]
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]
end CountDimension

noncomputable def orthogonalFactor (r : ℕ) (q : ℝ) : ℝ :=
  ∑ k : Fin (r+1), grassmannFactor r k.val q / q^((r-k.val).choose 2)

theorem choose_two_add (a b : ℕ) : (a+b).choose 2 = a.choose 2+b.choose 2+a*b := by
  have h : (((a+b).choose 2 : ℕ) : ℚ) = (a.choose 2 : ℚ)+(b.choose 2 : ℚ)+(a:ℚ)*b := by
    simp only [Nat.cast_choose_two, Nat.cast_add]
    ring
  exact_mod_cast h

theorem maxOrthogonal_normalized {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (r : ℕ) :
    (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
      (Fintype.card K : ℝ)^r.choose 2 = orthogonalFactor r (Fintype.card K) := by
  classical
  rw [maxOrthogonal_card_by_dimension hK,Module.finrank_fin_fun]
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  rw [Finset.sum_div]
  unfold orthogonalFactor
  apply Finset.sum_congr rfl
  intro k _
  rw [subspace_count_normalized k.val (by simp; omega)]
  simp only [Module.finrank_fin_fun]
  have hr : (k.val+(r-k.val)).choose 2 = r.choose 2 := by rw [Nat.add_sub_of_le (by omega)]
  have he : r.choose 2 = k.val.choose 2 + (r-k.val).choose 2 + k.val*(r-k.val) := by
    rw [←hr,choose_two_add]
  rw [he,pow_add,pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem orthogonalFactor_tendsto (r : ℕ) (hr : 0<r) :
    Tendsto (orthogonalFactor r) atTop (nhds 2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hrest (k : Fin n) : Tendsto (fun q : ℝ =>
      grassmannFactor (n+1) k.val q / q^((n+1-k.val).choose 2)) atTop (nhds 0) := by
    have hp : 0 < (n+1-k.val).choose 2 := Nat.choose_pos (by omega)
    have h := (grassmannFactor_tendsto (n+1) k.val (by omega)).mul
      (inverse_power_tendsto_zero _ hp)
    simpa only [one_mul,div_eq_mul_inv,one_div] using h
  have hsum := tendsto_finsetSum Finset.univ (fun k (_ : k ∈ Finset.univ) => hrest k)
  have hn : Tendsto (fun q : ℝ => grassmannFactor (n+1) n q /
      q^((n+1-n).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) n (Nat.le_succ n)
  have hn1 : Tendsto (fun q : ℝ => grassmannFactor (n+1) (n+1) q /
      q^((n+1-(n+1)).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) (n+1) le_rfl
  have h := (hsum.add hn).add hn1
  simp only [Finset.sum_const_zero,zero_add] at h
  norm_num only [one_add_one_eq_two] at h
  convert h using 1
  funext q
  unfold orthogonalFactor
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl

 theorem split_form_normalized {K E : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hB : B.Nondegenerate)
    (hK : ringChar K ≠ 2) (r : ℕ) (hd : finrank K E=2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    (Nat.card (SymplecticLagrangian B) : ℝ)/(Fintype.card K : ℝ)^r.choose 2 =
      orthogonalFactor r (Fintype.card K) := by
  rw [split_form_card B hs hB hK r hd hc]
  exact maxOrthogonal_normalized hK r
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section PairSigns
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}

theorem signed_pair_compatibility (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) (hb : (A-B).val.rank=r) :
    quadraticChar K B.val.det = quadraticChar K ((-1 : K)^r) *
      matrixSign K D A * matrixSign K D (A-B) := by
  have hba : (B.val-A.val).rank=r := by
    have he : B.val-A.val= -(A-B).val := by simp
    rw [he,matrix_rank_neg,hb]
  have hi := (half_rank_projection r (by simpa using hd) A.val B.val hB ha).mp hba
  have hs := center_complement_sign B.val A.val B.property hB A.property hi
  have he : (⟨B.val-A.val,B.property.sub A.property⟩ : SymMatrix K D)= -(A-B) := by
    apply Subtype.ext; simp
  change quadraticChar K B.val.det = matrixSign K D A *
    matrixSign K D ⟨B.val-A.val,B.property.sub A.property⟩ at hs
  rw [he,matrixSign_neg,hb] at hs
  rw [hs]; ring

theorem signed_second_iff (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) {ξ ζ : ℤ} (hx : matrixSign K D A=ξ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    ((A-B).val.rank=r ∧ matrixSign K D (A-B)=ζ) ↔ A.val*B.val⁻¹*A.val=A.val := by
  have hr : (A-B).val.rank=r ↔ A.val*B.val⁻¹*A.val=A.val := by
    rw [←half_rank_projection r (by simpa using hd) A.val B.val hB ha]
    have he : (A-B).val= -(B.val-A.val) := by simp
    rw [he,matrix_rank_neg]
  constructor
  · exact fun h => hr.mp h.1
  · intro hi
    have hb := hr.mpr hi
    refine ⟨hb,?_⟩
    have hp := signed_pair_compatibility hd A B hB ha hb
    rw [hx,hm] at hp
    have hc : quadraticChar K ((-1 : K)^r)≠0 := by
      exact mt quadraticChar_eq_zero_iff.mp (pow_ne_zero r (neg_ne_zero.mpr (one_ne_zero : (1 : K)≠0)))
    have hn : ξ≠0 := by rw [←hx]; exact discriminantSign_ne_zero _ _
    exact mul_left_cancel₀ (mul_ne_zero hc hn) hp.symm
end PairSigns
section Equiv
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]

omit [Fintype K] [DecidableEq K] in
theorem centerSubspaceEquiv_rank (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : finrank K (centerSubspaceEquiv Q hQ hdet A).val = A.val.rank := by
  rw [centerSubspaceEquiv_val]
  rfl

theorem centerSubspaceEquiv_sign (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) :
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1) =
    discriminantSign (Q.toBilin'.restrict (centerSubspaceEquiv Q hQ hdet A).val)
      ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  rw [centerSubspaceEquiv_val]
  exact center_discriminant Q A.val hQ hdet A.property.1 A.property.2

noncomputable def centerPredicateEquiv (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (P : Submodule K (n → K) → Prop) :
    {A : CenterProjection Q // P A.val.toLin'.range} ≃
    {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate ∧ P U} :=
  ((centerSubspaceEquiv Q hQ hdet).subtypeEquiv (fun A => by
    rw [centerSubspaceEquiv_val])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
end Equiv
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section SignedProjector
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}

def SignedProjector (Q : Matrix (Fin D) (Fin D) K) (r : ℕ) (ξ : ℤ) :=
  {A : CenterProjection Q // A.val.rank=r ∧
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1)=ξ}

noncomputable def pairSignedCenterEquiv (hd : D=2*r) (B : SymMatrix K D)
    (hB : B.val.det≠0) (ξ ζ : ℤ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} ≃
      SignedProjector B.val⁻¹ r ξ where
  toFun A :=
    ⟨⟨A.val.val,A.val.property,
      (signed_second_iff hd A.val B hB ((mem_signedLayer ..).mp A.property.1).1
        ((mem_signedLayer ..).mp A.property.1).2 hm).mp
        ((mem_signedLayer ..).mp A.property.2)⟩,
      ((mem_signedLayer ..).mp A.property.1).1,((mem_signedLayer ..).mp A.property.1).2⟩
  invFun A :=
    ⟨⟨A.val.val,A.val.property.1⟩,
      (mem_signedLayer ..).mpr A.property,
      (mem_signedLayer ..).mpr ((signed_second_iff hd ⟨A.val.val,A.val.property.1⟩ B hB
        A.property.1 A.property.2 hm).mpr A.val.property.2)⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl

noncomputable def signedProjectorSubspaceEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ) :
    SignedProjector Q r ξ ≃
    {U : DimSubspace K (Fin D → K) r // (Q.toBilin'.restrict U.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val)=ξ} where
  toFun A :=
    ⟨⟨(centerSubspaceEquiv Q hQ hdet A.val).val,
      (centerSubspaceEquiv_rank Q hQ hdet A.val).trans A.property.1⟩,
      (centerSubspaceEquiv Q hQ hdet A.val).property,
      (centerSubspaceEquiv_sign Q hQ hdet A.val).symm.trans A.property.2⟩
  invFun U :=
    ⟨(centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩,by
      constructor
      · rw [←centerSubspaceEquiv_rank Q hQ hdet,Equiv.apply_symm_apply]; exact U.val.property
      · rw [centerSubspaceEquiv_sign Q hQ hdet,Equiv.apply_symm_apply]; exact U.property.2⟩
  left_inv A := by
    apply Subtype.ext
    exact (centerSubspaceEquiv Q hQ hdet).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((centerSubspaceEquiv Q hQ hdet)
      ((centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]
end SignedProjector
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Isotropic
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem restrict_eq_zero_iff_isotropic (L : LinearMap.BilinForm K V) (U : Submodule K V) :
    L.restrict U=0 ↔ U ≤ L.orthogonal U := by
  constructor
  · intro h x hx y hy
    have he := congrArg (fun B : LinearMap.BilinForm K U => B ⟨y,hy⟩ ⟨x,hx⟩) h
    exact he
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact h y.property x.val x.property

variable [FiniteDimensional K V]
theorem half_isotropic_iff_self (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) (U : Submodule K V) (hu : finrank K U=r) :
    L.restrict U=0 ↔ L.orthogonal U=U := by
  rw [restrict_eq_zero_iff_isotropic]
  constructor
  · intro h
    symm
    apply Submodule.eq_of_le_of_finrank_eq h
    have hr := L.finrank_orthogonal hL U
    omega
  · intro h; rw [h]

noncomputable def halfIsotropicEquiv (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) :
    {U : DimSubspace K V r // L.restrict U.val=0} ≃ SymplecticLagrangian L where
  toFun U := ⟨U.val.val,(half_isotropic_iff_self L hL r hd U.val.val U.val.property).mp U.property⟩
  invFun U := ⟨⟨U.val,by
    have h := self_orthogonal_twice_finrank L U.val hL U.property
    omega⟩,(restrict_eq_zero_iff_isotropic L U.val).mpr (by rw [U.property])⟩
  left_inv U := by apply Subtype.ext; rfl
  right_inv U := rfl
end Isotropic
section Triple
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}

noncomputable def tripleSignedCenterEquiv (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} ≃
    {A : SignedProjector B.val⁻¹ r ξ // (B.val⁻¹-C.val⁻¹).toBilin'.restrict A.val.val.toLin'.range=0} where
  toFun A := ⟨pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩,by
    apply (center_second_equation B.val⁻¹ C.val⁻¹ A.val.val A.val.property
      ((pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩).val.property.2)).mp
    exact (signed_second_iff hd A.val C hC ((mem_signedLayer ..).mp A.property.1).1
      ((mem_signedLayer ..).mp A.property.1).2 hmC).mp ((mem_signedLayer ..).mp A.property.2.2)⟩
  invFun A :=
    let a := (pairSignedCenterEquiv hd B hB ξ ζ hmB).symm A.val
    ⟨a.val,a.property.1,a.property.2,(mem_signedLayer ..).mpr
      ((signed_second_iff hd a.val C hC ((mem_signedLayer ..).mp a.property.1).1
        ((mem_signedLayer ..).mp a.property.1).2 hmC).mpr
        ((center_second_equation B.val⁻¹ C.val⁻¹ A.val.val.val A.val.val.property.1
          A.val.val.property.2).mpr A.property))⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl
end Triple
end SidorenkoCounterexample

end

end OAI
