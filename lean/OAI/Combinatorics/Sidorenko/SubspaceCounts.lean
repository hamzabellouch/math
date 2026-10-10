import OAI.Combinatorics.Sidorenko.Orbits

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericCounts
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

noncomputable def symplecticLagrangianEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    SymplecticLagrangian ω ≃ SymplecticLagrangian η :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ η.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_isometry_between ω η e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)

variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)

 theorem symplecticLagrangian_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (SymplecticLagrangian ω) ∧
      (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  change Nat.card (Lagrangian (K := K) (V := L)) = _ at hc
  rw [←hc,←hd]
  exact ⟨lagrangian_card_lower,lagrangian_card_upper⟩

omit [Fintype K] in
 theorem symplecticLagrangian_card_pos (ha : ω.IsAlt) :
    0 < Nat.card (SymplecticLagrangian ω) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  let : Nonempty (SymplecticLagrangian ω) := ⟨⟨L,hL⟩⟩
  exact Nat.card_pos

omit [Fintype K] in
 theorem isotropic_finrank_le_half (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) : finrank K S ≤ D := by
  have h := ω.finrank_orthogonal hω S
  have hl := Submodule.finrank_mono hS
  omega

 theorem containingLagrangian_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
        Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-finrank K S) *
          (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) := by
  let e : {L : SymplecticLagrangian ω // S ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he := Nat.card_congr (e.trans (containingLagrangianEquiv ω S ha hS))
  have hc := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  rw [he]
  exact symplecticLagrangian_card_bounds (symplecticReductionForm ω S ha) h2
    (symplecticReductionForm_alt ω S ha) (symplecticReductionForm_nondegenerate ω S ha hω)
    (D-finrank K S) (by omega)

abbrev IsotropicDimspace (c : ℕ) :=
  {S : Submodule K E // S ≤ ω.orthogonal S ∧ finrank K S = c}

noncomputable def isotropicIncidenceEquiv (c : ℕ) :
    (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) ≃
    (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) where
  toFun p := ⟨p.2.val,⟨p.1.val.comap p.2.val.val.subtype,
    (Submodule.comapSubtypeEquivOfLe p.2.property).finrank_eq.trans p.1.property.2⟩⟩
  invFun p := ⟨⟨p.2.val.map p.1.val.subtype,by
      constructor
      · intro x hx y hy
        exact p.1.property.ge (Submodule.map_subtype_le p.1.val _ hx) y
          (Submodule.map_subtype_le p.1.val _ hy)
      · exact (Submodule.equivMapOfInjective p.1.val.subtype p.1.val.injective_subtype p.2.val).finrank_eq.symm.trans p.2.property⟩,
    ⟨p.1,Submodule.map_subtype_le p.1.val _⟩⟩
  left_inv p := by
    have hS : (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype = p.1.val := by
      rw [Submodule.map_comap_subtype,inf_of_le_right p.2.property]
    refine Sigma.ext (Subtype.ext hS) ?_
    apply (Subtype.heq_iff_coe_eq (fun L => ?_)).mpr
    · rfl
    · change (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype ≤ L.val ↔ p.1.val ≤ L.val
      rw [hS]
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact Submodule.comap_map_eq_of_injective p.1.val.injective_subtype p.2.val

omit [Fintype K] [Finite E] in
 theorem isotropic_incidence_card (c : ℕ) :
    Nat.card (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) =
      Nat.card (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) :=
  Nat.card_congr (isotropicIncidenceEquiv ω c)
end GenericCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

/-- The exponent 2Dc-(3c²-c)/2, written without truncated half-integers. -/
def isotropicExponent (D c : ℕ) : ℕ :=
  (D+1).choose 2 + c*(D-c) - (D-c+1).choose 2

 theorem isotropicExponent_add (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c) := by
  have h := symmetric_nullity_exponent D c hc
  exact Nat.sub_add_cancel (by omega)

section IsotropicCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)

 theorem isotropic_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (c : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^(isotropicExponent D c) ≤
        lagrangianConstant (D-c) * Nat.card (IsotropicDimspace ω c) ∧
      (Nat.card (IsotropicDimspace ω c) : ℝ) ≤
        (lagrangianConstant D * 2^c) * (Fintype.card K : ℝ)^(isotropicExponent D c) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := K)
  have hdim (L : SymplecticLagrangian ω) : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hs (S : IsotropicDimspace ω c) :=
    containingLagrangian_card_bounds ω h2 ha hω D hD S.val S.property.1
  have hs' (S : IsotropicDimspace ω c) :
      q^((D-c+1).choose 2) ≤ Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-c)*q^((D-c+1).choose 2) := by
    simpa only [S.property.2] using hs S
  have hsum : (∑ S : IsotropicDimspace ω c,
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ)) =
        ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) := by
    have h := isotropic_incidence_card ω c
    rw [Nat.card_sigma,Nat.card_sigma] at h
    exact_mod_cast h
  have hgrass (L : SymplecticLagrangian ω) :
      q^(c*(D-c)) ≤ Nat.card (DimSubspace K L.val c) ∧
        (Nat.card (DimSubspace K L.val c) : ℝ) ≤ 2^c*q^(c*(D-c)) := by
    have hcL : c ≤ finrank K L.val := (hdim L).symm ▸ hc
    constructor
    · simpa only [hdim L] using subspace_count_lower (K := K) (V := L.val) c hcL
    · simpa only [hdim L] using subspace_count_upper (K := K) (V := L.val) c hcL
  have hu : (Nat.card (IsotropicDimspace ω c) : ℝ)*q^((D-c+1).choose 2) ≤
      (Nat.card (SymplecticLagrangian ω) : ℝ)*(2^c*q^(c*(D-c))) := by
    calc
      _ = ∑ _S : IsotropicDimspace ω c, q^((D-c+1).choose 2) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ S : IsotropicDimspace ω c,
          (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) :=
        Finset.sum_le_sum (fun S _ => (hs' S).1)
      _ = _ := hsum
      _ ≤ ∑ _L : SymplecticLagrangian ω, 2^c*q^(c*(D-c)) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hl : (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ)*(lagrangianConstant (D-c)*q^((D-c+1).choose 2)) := by
    calc
      _ = ∑ _L : SymplecticLagrangian ω, q^(c*(D-c)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).1)
      _ = _ := hsum.symm
      _ ≤ ∑ _S : IsotropicDimspace ω c, lagrangianConstant (D-c)*q^((D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => (hs' S).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hlag := symplecticLagrangian_card_bounds ω h2 ha hω D hD
  have he : q^(isotropicExponent D c)*q^((D-c+1).choose 2) =
      q^((D+1).choose 2)*q^(c*(D-c)) := by
    rw [←pow_add,isotropicExponent_add D c hc,pow_add]
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ = q^((D+1).choose 2)*q^(c*(D-c)) := he
      _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) :=
        mul_le_mul_of_nonneg_right hlag.1 (by positivity)
      _ ≤ _ := hl
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ ≤ _ := hu
      _ ≤ (lagrangianConstant D*q^((D+1).choose 2))*(2^c*q^(c*(D-c))) :=
        mul_le_mul_of_nonneg_right hlag.2 (by positivity)
      _ = (lagrangianConstant D*2^c)*(q^((D+1).choose 2)*q^(c*(D-c))) := by ring
      _ = _ := by rw [←he]; ring
end IsotropicCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

 theorem lagrangianConstant_mono : Monotone lagrangianConstant := by
  intro m n h
  unfold lagrangianConstant
  exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right h 1)
    (pow_le_pow_right₀ (by norm_num) h) (by positivity) (by positivity)

section AvoidanceCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)

/-- The elementary line union bound, expressed before taking probabilities. -/
theorem lagrangian_bad_intersection_card (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (hpos : 0 < finrank K S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) ≤
      (2*(Fintype.card K : ℝ)^(finrank K S-1)) *
        (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
  classical
  let Line := DimSubspace K S 1
  let B := {L : SymplecticLagrangian ω // ¬ Disjoint L.val S}
  let Inc := Σ ℓ : Line, {L : SymplecticLagrangian ω // ℓ.val.map S.subtype ≤ L.val}
  let := Fintype.ofFinite Line
  have hex (L : B) : ∃ ℓ : Line, ℓ.val.map S.subtype ≤ L.val.val := by
    have hne : L.val.val ⊓ S ≠ ⊥ := by simpa only [disjoint_iff] using L.property
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let v : S := ⟨x,hx.2⟩
    have hv : v ≠ 0 := by intro h; exact hx0 (congrArg Subtype.val h)
    refine ⟨⟨K ∙ v, finrank_span_singleton hv⟩,?_⟩
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact L.val.val.smul_mem a hx.1
  let f : B → Inc := fun L => ⟨(hex L).choose,⟨L.val,(hex L).choose_spec⟩⟩
  have hfi : Function.Injective f := by
    intro L M h
    apply Subtype.ext
    exact congrArg (fun i : Inc => i.2.val) h
  have hi (ℓ : Line) : (Nat.card {L : SymplecticLagrangian ω //
      ℓ.val.map S.subtype ≤ L.val} : ℝ) ≤
      lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) := by
    have hle : ℓ.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have hiso : ℓ.val.map S.subtype ≤ ω.orthogonal (ℓ.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (ℓ.val.map S.subtype) = 1 := by
      exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective ℓ.val).finrank_eq.symm.trans ℓ.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD
      (ℓ.val.map S.subtype) hiso).2
  have hinc : (Nat.card Inc : ℝ) ≤ (Nat.card Line : ℝ)*
      (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ℓ : Line, lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) :=
        Finset.sum_le_sum (fun ℓ _ => hi ℓ)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hl : (Nat.card Line : ℝ) ≤ 2*(Fintype.card K : ℝ)^(finrank K S-1) := by
    simpa [Line] using subspace_count_upper (K := K) (V := S) 1 hpos
  calc
    _ ≤ (Nat.card Inc : ℝ) := by exact_mod_cast Nat.card_le_card_of_injective f hfi
    _ ≤ _ := hinc
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (by
      exact mul_nonneg (lagrangianConstant_pos _).le (by positivity))

/-- For fixed dimension, failure of avoiding an isotropic space is O(1/q).
No transversality statement is used as a probabilistic assumption. -/
theorem lagrangian_bad_intersection_scaled (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) *
      Fintype.card K ≤ 2*lagrangianConstant D*Nat.card (SymplecticLagrangian ω) := by
  classical
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  by_cases hp : 0 < finrank K S
  · have hs := isotropic_finrank_le_half ω hω D hD S hS
    have hDpos : 0 < D := lt_of_lt_of_le hp hs
    have he : (D-1+1).choose 2 + D = (D+1).choose 2 := by
      rw [Nat.sub_add_cancel hDpos, Nat.choose_succ_succ,Nat.choose_one_right]
      change D.choose 2 + D = D + D.choose 2
      omega
    have hpow : q^((finrank K S-1)+(D-1+1).choose 2+1) ≤ q^((D+1).choose 2) := by
      apply pow_le_pow_right₀ hq
      omega
    have hc : lagrangianConstant (D-1) ≤ lagrangianConstant D := lagrangianConstant_mono (Nat.sub_le _ _)
    calc
      _ ≤ (2*q^(finrank K S-1))*(lagrangianConstant (D-1)*q^((D-1+1).choose 2))*q :=
        mul_le_mul_of_nonneg_right (lagrangian_bad_intersection_card ω h2 ha hω D hD S hS hp) (by positivity)
      _ = 2*lagrangianConstant (D-1)*q^((finrank K S-1)+(D-1+1).choose 2+1) := by
        simp only [pow_add,pow_one]; ring
      _ ≤ 2*lagrangianConstant D*q^((D+1).choose 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hpow
          (by positivity) (by exact mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
        (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
  · have hfin : finrank K S = 0 := by omega
    have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have he : IsEmpty {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by
      rw [hbot]
      exact ⟨fun L => L.property disjoint_bot_right⟩
    have := he
    simp only [Nat.card_of_isEmpty,Nat.cast_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le) (by positivity)




theorem lagrangian_disjoint_card_lower (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
      2*Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hsum : Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} +
      Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} =
        Nat.card (SymplecticLagrangian ω) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have hsumR := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hsumR
  have hbad := lagrangian_bad_intersection_scaled ω h2 ha hω D hD S hS
  have hC := lagrangianConstant_pos D
  have hbad0 : (0 : ℝ) ≤ Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by positivity
  nlinarith

end AvoidanceCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

 theorem reduceSubspace_isotropic (ha : ω.IsAlt) (A S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    reduceSubspace ω A S ≤ (symplecticReductionForm ω A ha).orthogonal (reduceSubspace ω A S) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
  exact hS hx y.val hy

/-- Containment and exact intersection become ordinary avoidance in the
containment quotient. This is a literal equivalence of finite sample spaces. -/
noncomputable def containmentAvoidanceEquiv (ha : ω.IsAlt)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S) :
    AvoidanceSpace ω S A ≃
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hSP : S ≤ ω.orthogonal A := hS.trans (ω.orthogonal_le hAS)
  let e := containingLagrangianEquiv ω A ha hAP
  let f : AvoidanceSpace ω S A →
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := fun L => by
    have hAL : A ≤ L.val := L.property.2.ge.trans inf_le_left
    refine ⟨e ⟨L.val,L.property.1,hAL⟩,?_⟩
    apply disjoint_iff.mpr
    change reduceSubspace ω A L.val ⊓ reduceSubspace ω A S = ⊥
    rw [← reduceSubspace_inf ω A L.val S hAL,L.property.2,reduceSubspace_self]
  have hfi : Function.Injective f := by
    intro L M hh
    apply Subtype.ext
    have he := e.injective (congrArg Subtype.val hh)
    exact congrArg (fun X : {T : Submodule K E // ω.orthogonal T = T ∧ A ≤ T} => X.val) he
  have hfs : Function.Surjective f := by
    intro L
    let T := e.symm L.val
    have hlast : T.val ⊓ S = A := by
      calc
        T.val ⊓ S = liftReduction ω A L.val.val ⊓ liftReduction ω A (reduceSubspace ω A S) := by
          rw [lift_reduce ω A S hAS hSP]
          rfl
        _ = liftReduction ω A (L.val.val ⊓ reduceSubspace ω A S) :=
          (liftReduction_inf ω A _ _).symm
        _ = A := by rw [L.property.eq_bot,liftReduction_bot ω A hAP]
    refine ⟨⟨T.val,T.property.1,hlast⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply L.val
  exact Equiv.ofBijective f ⟨hfi,hfs⟩

variable [Fintype K] [Finite E]

 theorem avoidance_card_lower (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hdim := reducedSpace_finrank ω A hω hAP
  have hle := isotropic_finrank_le_half ω hω D hD A hAP
  let Ω := symplecticReductionForm ω A ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω A ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω A ha hω
  let : Finite (ReducedSpace ω A) := Module.finite_of_finite K
  have h := lagrangian_disjoint_card_lower Ω h2 hΩa hΩ (D-finrank K A) (by omega)
    (reduceSubspace ω A S) (reduceSubspace_isotropic ω ha A S hS)
    ((mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D _)) (by norm_num)).trans hq)
  have he₁ := Nat.card_congr (containmentAvoidanceEquiv ω ha A S hAS hS)
  have e₂ : {L : SymplecticLagrangian ω // A ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ A ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he₂ := Nat.card_congr (e₂.trans (containingLagrangianEquiv ω A ha hAP))
  rwa [he₁,he₂]

end ContainmentAvoidance
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

/-- An isometry of three containing reductions lifts to a simultaneous
isometry of the actual Lagrangians, fixing their common space pointwise. -/
theorem triple_containing_isometry_lift (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (_hS : S ≤ ω.orthogonal S) (L M N L' M' N' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M') (hN' : ω.orthogonal N' = N')
    (hSL : S ≤ L) (hSM : S ≤ M) (hSN : S ≤ N)
    (hSL' : S ≤ L') (hSM' : S ≤ M') (hSN' : S ≤ N')
    (hres : TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      (reduceSubspace ω S L) (reduceSubspace ω S M) (reduceSubspace ω S N)
      (reduceSubspace ω S L') (reduceSubspace ω S M') (reduceSubspace ω S N')) :
    TripleIsometry ω ω L M N L' M' N' := by
  obtain ⟨f,hf,hfL,hfM,hfN⟩ := hres
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [←orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [←hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,
    hmap M M' hM hM' hSM hSM' hfM,hmap N N' hN hN' hSN hSN' hfN⟩

end CommonSpaceLift
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev PairLinearOrbit (U V : Submodule K E) :=
  {p : Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2}

abbrev PairLinearStabilizer (U V : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V}

def pairLinearOrbitMap (U V : Submodule K E) (e : E ≃ₗ[K] E) : PairLinearOrbit U V :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap),e,rfl,rfl⟩

 theorem submodule_map_trans (U : Submodule K E) (e f : E ≃ₗ[K] E) :
    U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap := by
  exact Submodule.map_comp _ _ _

 theorem submodule_map_symm_cancel (U : Submodule K E) (e : E ≃ₗ[K] E) :
    (U.map e.toLinearMap).map e.symm.toLinearMap = U := by
  rw [←Submodule.map_comp]
  simp

noncomputable def pairLinearOrbitFiberEquiv (U V : Submodule K E) (p : PairLinearOrbit U V) :
    {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} ≃ PairLinearStabilizer U V := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2
  have hm (e : {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2 := by
    exact ⟨congrArg (fun a : PairLinearOrbit U V => a.val.1) e.property,
      congrArg (fun a : PairLinearOrbit U V => a.val.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2,←hV,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.1).trans hU
    · change V.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.2
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.2).trans hV
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp

noncomputable def pairLinearStabilizerRestriction (U V : Submodule K E) :
    PairLinearStabilizer U V → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2)

 theorem pairLinearStabilizerRestriction_bijective (U V : Submodule K E) (hUV : IsCompl U V) :
    Function.Bijective (pairLinearStabilizerRestriction U V) := by
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    have hx : x ∈ U ⊔ V := by rw [hUV.sup_eq_top]; trivial
    obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
    have hU := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.1 ⟨u,hu⟩).val) hh
    have hV := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.2 ⟨v,hv⟩).val) hh
    change e.val u = f.val u at hU
    change e.val v = f.val v at hV
    simp only [map_add,hU,hV]
  · intro g
    let c := Submodule.prodEquivOfIsCompl U V hUV
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr g.2).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,0) = u.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2 v).val := by
      have hc : c (0,v) = v.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have hU : U.map e.toLinearMap = U := by
      ext x
      constructor
      · rintro ⟨u,hu,rfl⟩
        change e u ∈ U
        rw [heU ⟨u,hu⟩]
        exact (g.1 ⟨u,hu⟩).property
      · intro hx
        refine ⟨(g.1.symm ⟨x,hx⟩).val,(g.1.symm ⟨x,hx⟩).property,?_⟩
        exact (heU _).trans (congrArg Subtype.val (g.1.apply_symm_apply ⟨x,hx⟩))
    have hV : V.map e.toLinearMap = V := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        change e v ∈ V
        rw [heV ⟨v,hv⟩]
        exact (g.2 ⟨v,hv⟩).property
      · intro hx
        refine ⟨(g.2.symm ⟨x,hx⟩).val,(g.2.symm ⟨x,hx⟩).property,?_⟩
        exact (heV _).trans (congrArg Subtype.val (g.2.apply_symm_apply ⟨x,hx⟩))
    refine ⟨⟨e,hU,hV⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · ext v
      exact heV v

variable [Fintype K] [Finite E]

 omit [Fintype K] in
 theorem pairLinearOrbit_card_identity (U V : Submodule K E) (hUV : IsCompl U V) :
    Nat.card (PairLinearOrbit U V) *
      (Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (PairLinearOrbit U V)
  have hc : Nat.card (PairLinearStabilizer U V) =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (pairLinearStabilizerRestriction_bijective U V hUV)),Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (pairLinearOrbitMap U V))).symm
  rw [Nat.card_sigma] at he
  have hf (p : PairLinearOrbit U V) : Nat.card {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) :=
    (Nat.card_congr (pairLinearOrbitFiberEquiv U V p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm

 theorem linearAut_card_upper : Nat.card (E ≃ₗ[K] E) ≤
    Fintype.card K ^ (finrank K E * finrank K E) := by
  rw [linearAut_card]
  calc
    _ ≤ ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E :=
      Finset.prod_le_prod (fun i _ => Nat.sub_le _ _)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]

/-- Ordered complementary decompositions have q^(2uv) choices up to a
positive fixed-dimension constant; proved from their exact stabilizer. -/
theorem pairLinearOrbit_card_bounds (U V : Submodule K E) (hUV : IsCompl U V) :
    (Fintype.card K : ℝ)^(2*finrank K U*finrank K V) ≤
      2^(finrank K E)*(Nat.card (PairLinearOrbit U V) : ℝ) ∧
    (Nat.card (PairLinearOrbit U V) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*finrank K U*finrank K V) := by
  let u := finrank K U
  let v := finrank K V
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+v = n := Submodule.finrank_add_eq_of_isCompl hUV
  have he : n*n = 2*u*v + (u*u+v*v) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (PairLinearOrbit U V) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast pairLinearOrbit_card_identity U V hUV
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v))) := by gcongr
      _ = _ := by rw [←pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = (Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v)) := by rw [pow_add]
      _ ≤ (Nat.card (PairLinearOrbit U V) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*(2^v*Nat.card (V ≃ₗ[K] V))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn,pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring

end Decompositions
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Literal coordinates for an ordered direct sum of three subspaces. -/
noncomputable def tripleSumEquiv (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) : (U × (V × W)) ≃ₗ[K] E := by
  let f := V.subtype.coprod W.subtype
  have hr : LinearMap.range f = V ⊔ W := by
    rw [LinearMap.range_coprod,Submodule.range_subtype,Submodule.range_subtype]
  have hk : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range,Submodule.ker_subtype,Submodule.ker_subtype,Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using hVW
  apply LinearEquiv.ofBijective (U.subtype.coprod f)
  constructor
  · rw [←LinearMap.ker_eq_bot,LinearMap.ker_coprod_of_disjoint_range,
      Submodule.ker_subtype,hk,Submodule.prod_bot]
    simpa only [Submodule.range_subtype,hr] using hU.disjoint
  · rw [←LinearMap.range_eq_top,LinearMap.range_coprod,Submodule.range_subtype,hr,hU.sup_eq_top]

@[simp] theorem tripleSumEquiv_apply (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) (u : U) (v : V) (w : W) :
    tripleSumEquiv U V W hU hVW (u,(v,w)) = u.val+(v.val+w.val) := rfl

abbrev TripleLinearOrbit (U V W : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2.1 ∧ W.map e.toLinearMap = p.2.2}

abbrev TripleLinearStabilizer (U V W : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V ∧ W.map e.toLinearMap = W}

def tripleLinearOrbitMap (U V W : Submodule K E) (e : E ≃ₗ[K] E) : TripleLinearOrbit U V W :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap,W.map e.toLinearMap),e,rfl,rfl,rfl⟩

noncomputable def tripleLinearOrbitFiberEquiv (U V W : Submodule K E) (p : TripleLinearOrbit U V W) :
    {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} ≃ TripleLinearStabilizer U V W := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2.1
  have hW := p.property.choose_spec.2.2
  have hm (e : {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2.1 ∧
        W.map e.val.toLinearMap = p.val.2.2 := by
    exact ⟨congrArg (fun a : TripleLinearOrbit U V W => a.val.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.1,←hV,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.2,←hW,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.1).trans hU
    · apply Prod.ext
      · change V.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.1
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.1).trans hV
      · change W.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.2
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.2).trans hW
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp

noncomputable def tripleLinearStabilizerRestriction (U V W : Submodule K E) :
    TripleLinearStabilizer U V W → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2.1,
    e.val.ofSubmodules W W e.property.2.2)

 theorem map_eq_of_restriction_aut (U : Submodule K E) (e : E ≃ₗ[K] E) (g : U ≃ₗ[K] U)
    (h : ∀ u : U, e u.val = (g u).val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    change e u ∈ U
    rw [h ⟨u,hu⟩]
    exact (g ⟨u,hu⟩).property
  · intro hx
    refine ⟨(g.symm ⟨x,hx⟩).val,(g.symm ⟨x,hx⟩).property,?_⟩
    exact (h _).trans (congrArg Subtype.val (g.apply_symm_apply ⟨x,hx⟩))

 theorem tripleLinearStabilizerRestriction_bijective (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Function.Bijective (tripleLinearStabilizerRestriction U V W) := by
  let c := tripleSumEquiv U V W hU hVW
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    obtain ⟨⟨u,v,w⟩,rfl⟩ := c.surjective x
    have h₁ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.1 u).val) hh
    have h₂ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.1 v).val) hh
    have h₃ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.2 w).val) hh
    change e.val u.val = f.val u.val at h₁
    change e.val v.val = f.val v.val at h₂
    change e.val w.val = f.val w.val at h₃
    change e.val (u.val+(v.val+w.val)) = f.val (u.val+(v.val+w.val))
    simp only [map_add,h₁,h₂,h₃]
  · intro g
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr (g.2.1.prodCongr g.2.2)).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,(0,0)) = u.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2.1 v).val := by
      have hc : c (0,(v,0)) = v.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heW (w : W) : e w.val = (g.2.2 w).val := by
      have hc : c (0,(0,w)) = w.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm w.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    refine ⟨⟨e,map_eq_of_restriction_aut U e g.1 heU,
      map_eq_of_restriction_aut V e g.2.1 heV,map_eq_of_restriction_aut W e g.2.2 heW⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · apply Prod.ext
      · ext v
        exact heV v
      · ext w
        exact heW w

variable [Finite E]

 theorem tripleLinearOrbit_card_identity (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Nat.card (TripleLinearOrbit U V W) *
      (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (TripleLinearOrbit U V W)
  have hc : Nat.card (TripleLinearStabilizer U V W) =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (tripleLinearStabilizerRestriction_bijective U V W hU hVW)),
      Nat.card_prod,Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleLinearOrbitMap U V W))).symm
  rw [Nat.card_sigma] at he
  have hf (p : TripleLinearOrbit U V W) : Nat.card {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) :=
    (Nat.card_congr (tripleLinearOrbitFiberEquiv U V W p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm

variable [Fintype K]

 theorem tripleLinearOrbit_card_bounds (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      2^(finrank K E)*(Nat.card (TripleLinearOrbit U V W) : ℝ) ∧
    (Nat.card (TripleLinearOrbit U V W) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  let u := finrank K U
  let v := finrank K V
  let w := finrank K W
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+(v+w) = n := by
    simpa only [Module.finrank_prod] using (tripleSumEquiv U V W hU hVW).finrank_eq
  have he : n*n = 2*(u*v+u*w+v*w) + (u*u+(v*v+w*w)) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (TripleLinearOrbit U V W) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast tripleLinearOrbit_card_identity U V W hU hVW
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,v]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hw : (Nat.card (W ≃ₗ[K] W) : ℝ) ≤ q^(w*w) := by dsimp [q,w]; exact_mod_cast linearAut_card_upper (K := K) (E := W)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,v]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hw' : q^(w*w) ≤ 2^w*(Nat.card (W ≃ₗ[K] W) : ℝ) := by dsimp [q,w]; exact_mod_cast linearAut_card_lower (K := K) (E := W)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w)))) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = (Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w))) := by simp only [pow_add]
      _ ≤ (Nat.card (TripleLinearOrbit U V W) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*((2^v*Nat.card (V ≃ₗ[K] V))*(2^w*Nat.card (W ≃ₗ[K] W)))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn]; simp only [pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring

end TripleDecompositions
end SidorenkoCounterexample


namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type*}

noncomputable def prodFiberEquiv (f : A → B) (g : C → D) (b : B) (d : D) :
    {x : A × C // (f x.1,g x.2) = (b,d)} ≃
      {a : A // f a = b} × {c : C // g c = d} where
  toFun x := (⟨x.val.1,congrArg Prod.fst x.property⟩,⟨x.val.2,congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val,x.2.val),Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem uniform_prod_card [Finite A] [Finite B] [Finite C] [Finite D]
    (f : A → B) (g : C → D)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)
    (hg : ∀ d, Nat.card {c : C // g c = d} * Nat.card D = Nat.card C)
    (p : B × D) :
    Nat.card {x : A × C // (f x.1,g x.2) = p} * Nat.card (B × D) = Nat.card (A × C) := by
  rcases p with ⟨b,d⟩
  rw [Nat.card_congr (prodFiberEquiv f g b d),Nat.card_prod,Nat.card_prod,Nat.card_prod]
  calc
    _ = (Nat.card {a : A // f a = b} * Nat.card B) *
      (Nat.card {c : C // g c = d} * Nat.card D) := by ring
    _ = _ := by rw [hf,hg]

 theorem uniform_preimage_card [Finite A] [Finite B] (f : A → B)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A) (P : B → Prop) :
    Nat.card {a : A // P (f a)} * Nat.card B = Nat.card {b : B // P b} * Nat.card A := by
  classical
  let := Fintype.ofFinite {b : B // P b}
  let e : {a : A // P (f a)} ≃ Σ b : {b : B // P b}, {a : A // f a = b.val} :=
    { toFun := fun a => ⟨⟨f a.val,a.property⟩,⟨a.val,rfl⟩⟩
      invFun := fun b => ⟨b.2.val,by rw [b.2.property]; exact b.1.property⟩
      left_inv := fun a => rfl
      right_inv := by rintro ⟨⟨b,hb⟩,a,ha⟩; dsimp at ha; subst b; rfl }
  rw [Nat.card_congr e,Nat.card_sigma,Finset.sum_mul]
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
end UniformCounts

section ExactPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)



 theorem avoidance_exact_intersection
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLA : L ⊓ S = A) (hMB : M ⊓ S = B) (hAB : A ⊔ B = S)
    (hr : reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥) :
    L ⊓ M = A ⊓ B := by
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ ω.orthogonal S := by
      intro y hy
      rw [←hAB] at hy
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hy
      have haL : a ∈ L := (hLA.symm ▸ ha : a ∈ L ⊓ S).1
      have hbM : b ∈ M := (hMB.symm ▸ hb : b ∈ M ⊓ S).1
      rw [map_add,LinearMap.add_apply,(hL.ge hx.1) a haL,(hM.ge hx.2) b hbM,add_zero]
    have hxq : (reductionKernel ω S).mkQ ⟨x,hxP⟩ = 0 := by
      have hmem : (reductionKernel ω S).mkQ ⟨x,hxP⟩ ∈
          reduceSubspace ω S L ⊓ reduceSubspace ω S M :=
        ⟨⟨⟨x,hxP⟩,hx.1,rfl⟩,⟨⟨x,hxP⟩,hx.2,rfl⟩⟩
      simpa only [hr,Submodule.mem_bot] using hmem
    have hxS : x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxq
    exact ⟨hLA ▸ (⟨hx.1,hxS⟩ : x ∈ L ⊓ S),hMB ▸ (⟨hx.2,hxS⟩ : x ∈ M ⊓ S)⟩
  · intro x hx
    exact ⟨(hLA.symm ▸ hx.1 : x ∈ L ⊓ S).1,(hMB.symm ▸ hx.2 : x ∈ M ⊓ S).1⟩
end ExactPairs
end SidorenkoCounterexample

end OAI
