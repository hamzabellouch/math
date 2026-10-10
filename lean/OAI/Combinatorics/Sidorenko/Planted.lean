import OAI.Combinatorics.Sidorenko.OrbitBounds

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

 theorem reduceSubspace_finrank_general (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K ↥(S ⊓ A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = (S ⊓ A).comap A.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨(Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx,x.property⟩
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx.1
  have hr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe (inf_le_right : S ⊓ A ≤ A)).finrank_eq] at hh
  exact hh



 theorem reduce_center_intersection_finrank (L Y : Submodule K E)
    (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    finrank K ↥(reduceSubspace ω S L ⊓ reduceSubspace ω S Y) + finrank K ↥(S ⊓ Y) =
      finrank K ↥(L ⊓ Y) := by
  rw [←reduceSubspace_inf ω S L Y hSL]
  have hh := reduceSubspace_finrank_general ω S (L ⊓ Y) (inf_le_left.trans hLP)
  have he : S ⊓ (L ⊓ Y) = S ⊓ Y := by rw [←inf_assoc,inf_eq_left.mpr hSL]
  rwa [he] at hh
end PlantedQuotient

section CenterDisintegration
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

abbrev TripleCenterSet (r : ℕ) (L M N : Submodule K E) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val) = r ∧
    finrank K ↥(M ⊓ Y.val) = r ∧ finrank K ↥(N ⊓ Y.val) = r}

noncomputable def tripleCenterIsometryEquiv (r : ℕ) (L M N : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y) :
    TripleCenterSet ω r L M N ≃
    TripleCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) (N.map e.toLinearMap) := by
  let f := lagrangianIsometryEquiv ω e he
  refine f.subtypeEquiv ?_
  intro Y
  change (_ ∧ _ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(N.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r)
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,
    ←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq,e.finrank_map_eq,e.finrank_map_eq]

 theorem tripleCenter_orbit_card (r : ℕ) (L M N : Submodule K E)
    (P : OrderedTripleOrbit ω L M N) :
    Nat.card (TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (TripleCenterSet ω r L M N) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  exact (Nat.card_congr (tripleCenterIsometryEquiv ω r L M N e he)).symm

/-- A literal finite disintegration over an ACTUAL ordered orbit, the exact
density-ratio identity behind the local planted bound. -/
 theorem tripleCenterOrbit_card [Finite E] (r : ℕ) (L M N : Submodule K E) :
    Nat.card (Σ P : OrderedTripleOrbit ω L M N, TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (OrderedTripleOrbit ω L M N) * Nat.card (TripleCenterSet ω r L M N) := by
  classical
  let := Fintype.ofFinite (OrderedTripleOrbit ω L M N)
  rw [Nat.card_sigma]
  simp_rw [tripleCenter_orbit_card ω r L M N]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end CenterDisintegration
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)

abbrev SymplecticCenterStratum (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ Y.val) = r}
abbrev SymplecticCenterProfile (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}

 theorem exists_center_coordinates [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : SymplecticLagrangian ω) :
    ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) ∧
      (verticalSpace (K := K) (V := Y.val)).map e.toLinearMap = Y.val := by
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω Y.val h2 ha hω Y.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
  let A := f.symm Y
  have hm : A.val.map e.toLinearMap = Y.val := congrArg Subtype.val (f.apply_symm_apply Y)
  obtain ⟨a,ha,hA⟩ := lagrangian_transitivity canonicalSymplectic verticalLagrangian.val h2
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate verticalLagrangian.property A.val A.property
  refine ⟨a.trans e,?_,?_⟩
  · intro x y
    change ω (e (a x)) (e (a y)) = _
    rw [he,ha]
  · change verticalSpace.map (e.toLinearMap.comp a.toLinearMap) = _
    rw [Submodule.map_comp]
    change (verticalLagrangian.val.map a.toLinearMap).map e.toLinearMap = _
    rw [hA,hm]

 theorem map_pair_finrank (e : V ≃ₗ[K] E) (A B : Submodule K V) :
    finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
  rw [←Submodule.map_inf e.toLinearMap e.injective]
  exact e.finrank_map_eq _

 theorem map_common_zero_iff (e : V ≃ₗ[K] E) (A B C : Submodule K V) :
    (A.map e.toLinearMap ⊓ B.map e.toLinearMap) ⊓ C.map e.toLinearMap = ⊥ ↔ (A ⊓ B) ⊓ C = ⊥ := by
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective]
  constructor
  · intro h
    apply (Submodule.orderIsoMapComap e).injective
    simpa only [Submodule.orderIsoMapComap_apply,Submodule.map_bot] using h
  · intro h
    rw [h,Submodule.map_bot]

noncomputable def symplecticCenterStratumEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r : ℕ) :
    CenterStratum (K := K) (V := V) r ≃ SymplecticCenterStratum ω Y r :=
  (symplecticLagrangianEquiv canonicalSymplectic ω e he).subtypeEquiv (by
    intro L
    change finrank K ↥(L.val ⊓ verticalSpace) = r ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ Y.val) = r
    rw [←hY,map_pair_finrank])

noncomputable def symplecticCenterProfileEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r s₀ s₁ s₂ : ℕ) :
    CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ SymplecticCenterProfile ω Y r s₀ s₁ s₂ :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr (f.prodCongr f)).subtypeEquiv (by
    intro L
    change (_ ∧ _ ∧ _ ∧ _) ↔
      ((L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) ⊓ L.2.2.val.val.map e.toLinearMap = ⊥ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) = s₀ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₁ ∧
      finrank K ↥(L.2.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₂)
    rw [map_common_zero_iff,map_pair_finrank,map_pair_finrank,map_pair_finrank])

 theorem symplectic_center_profile_probability_bound [Fintype K] [Finite E]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val) :
    (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
      (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K Y.val) r s₀ s₁ s₂ θ.val) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterProfileEquiv ω Y e he hY r s₀ s₁ s₂),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  exact canonical_center_profile_probability_bound r s₀ s₁ s₂ hr

 theorem symplectic_profile_pair_sum_le [Fintype K] [Finite E]
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D := by
  rw [←triplePairSum_finrank _ _ _ h0]
  exact isotropic_finrank_le_half ω hω D hD _ (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)

end GenericReducedCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonCenterSet (S : Submodule K E) (u : ℕ) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(S ⊓ Y.val) = u}

 theorem commonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
      2^u * lagrangianConstant (D-u) *
        (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2) := by
  classical
  let B := CommonCenterSet ω S u
  let Inc := Σ U : DimSubspace K S u, {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val}
  let f (Y : B) : Inc :=
    ⟨⟨(S ⊓ Y.val.val).comap S.subtype,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ Y.val.val ≤ S)).finrank_eq.trans Y.property⟩,
      ⟨Y.val,by rintro x ⟨y,hy,rfl⟩; exact hy.2⟩⟩
  have hf : Function.Injective f := by
    intro Y Z h
    exact Subtype.ext (congrArg (fun i : Inc => i.2.val) h)
  have hb (U : DimSubspace K S u) :
      (Nat.card {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val} : ℝ) ≤
      lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) := by
    have hle : U.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have his : U.val.map S.subtype ≤ ω.orthogonal (U.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (U.val.map S.subtype) = u :=
      (Submodule.equivMapOfInjective S.subtype S.subtype_injective U.val).finrank_eq.symm.trans U.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD _ his).2
  let := Fintype.ofFinite (DimSubspace K S u)
  have hi : (Nat.card Inc : ℝ) ≤ (Nat.card (DimSubspace K S u) : ℝ)*
      (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ U : DimSubspace K S u, lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) :=
        Finset.sum_le_sum (fun U _ => hb U)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ (Nat.card Inc : ℝ) := Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ ≤ _ := hi
    _ ≤ (2^u*(Fintype.card K : ℝ)^(u*(finrank K S-u))) *
        (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper u hu)
        (mul_nonneg (lagrangianConstant_pos (D-u)).le (by positivity))
    _ = _ := by rw [pow_add]; ring

 theorem commonCenter_cost_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) *
      (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
      2^D * lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hc := isotropic_finrank_le_half ω hω D hD S hS
  have hud : u ≤ D := hu.trans hc
  have he : u*(D-finrank K S)+(u+1).choose 2+
      (u*(finrank K S-u)+(D-u+1).choose 2) = (D+1).choose 2 := by
    have hh := symmetric_nullity_exponent D u hud
    have hmul : u*(D-finrank K S)+u*(finrank K S-u) = u*(D-u) := by
      rw [←Nat.mul_add]; congr 1; omega
    omega
  have hh := mul_le_mul_of_nonneg_left (commonCenter_card_upper ω h2 ha hω D hD S hS u hu)
    (show 0 ≤ (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) by positivity)
  calc
    _ ≤ _ := hh
    _ = (2^u*lagrangianConstant (D-u))*(Fintype.card K : ℝ)^((D+1).choose 2) := by
      rw [←he,pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hud)
        (lagrangianConstant_mono (Nat.sub_le D u))
        (lagrangianConstant_pos (D-u)).le (by positivity)) (by positivity)
end CommonCenterCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev FixedCommonCenterProfile (c h₀ h₁ h₂ : ℕ) (S : IsotropicDimspace ω c)
    (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {p : TripleDimProfile ω c h₀ h₁ h₂ // tripleProfileCommon ω p = S ∧
    finrank K ↥(p.val.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.2.val ⊓ Y.val) = r}
noncomputable def generalReductionLagrangian (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (Y : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S Y.val,general_lagrangian_reduction ω S ha hω hS Y.val Y.property⟩

 theorem fixedCommonCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    {c h₀ h₁ h₂ r u : ℕ} (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) :
    ∃ f : FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r →
      SymplecticCenterProfile (symplecticReductionForm ω S.val ha)
        (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
        (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f := by
  let F := FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r
  let Y' := generalReductionLagrangian ω ha hω S.val S.property.1 Y.val
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property.1
  have hL (p : F) : S.val ≤ p.val.val.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_left)
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_right)
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (le_of_eq (heq p).symm).trans inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hd (P : SymplecticLagrangian ω) (hSP : S.val ≤ P.val)
      (hPr : finrank K ↥(P.val ⊓ Y.val.val) = r) :
      finrank K ↥((commonReductionLagrangian ω S.val ha S.property.1 P hSP).val ⊓ Y'.val) = r-u := by
    have hh := reduce_center_intersection_finrank ω S.val P.val Y.val.val hSP
      (lagrangian_le_orthogonal ω S.val P.val P.property hSP)
    rw [Y.property,hPr] at hh
    change finrank K ↥(reduceSubspace ω S.val P.val ⊓ reduceSubspace ω S.val Y.val.val) = _
    omega
  let L' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨L p,hd _ _ p.property.2.1⟩
  let M' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨M p,hd _ _ p.property.2.2.1⟩
  let N' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨N p,hd _ _ p.property.2.2.2⟩
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hp0 (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = h₀-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hp1 (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = h₁-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hp2 (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = h₂-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : SymplecticCenterProfile (symplecticReductionForm ω S.val ha) Y'
      (r-u) (h₀-c) (h₁-c) (h₂-c) :=
    ⟨(L' p,M' p,N' p),hzero p,hp0 p,hp1 p,hp2 p⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))
end ReducedCenterInjection
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def reducedPlantedSum (d r s₀ s₁ s₂ : ℕ) (q : ℝ) : ℝ :=
  ∑ θ : BaseParameters d r s₀ s₁ s₂,
    reducedPlantedConstant r s₀ s₁ s₂ θ.val * q^(reducedPlantedExponent d r s₀ s₁ s₂ θ.val)
 theorem reducedPlantedSum_nonneg (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ reducedPlantedSum d r s₀ s₁ s₂ q := by
  unfold reducedPlantedSum
  apply Finset.sum_nonneg
  intro θ _
  unfold reducedPlantedConstant
  positivity

section ReducedCardBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_center_profile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (Y : SymplecticLagrangian ω)
    (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D) :
    (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
      (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
      2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
  have hd : finrank K Y.val = D := by
    have hh := self_orthogonal_twice_finrank ω Y.val hω Y.property
    omega
  have hp := symplectic_pair_card_bounds ω h2 ha hω D hD Y r hr
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0:ℝ) < Nat.card (SymplecticCenterStratum ω Y r) := by
    have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp.1
    exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
  have hb := symplectic_center_profile_probability_bound ω h2 ha hω Y r s₀ s₁ s₂ (by omega)
  rw [hd] at hb
  change (_ / _) ≤ reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) at hb
  have hcount := (div_le_iff₀ (pow_pos hc 3)).mp hb
  have hpair : ((Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r))^3 ≤
      (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 := by
    exact pow_le_pow_left₀ (by positivity) hp.2 3
  calc
    _ ≤ (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
        (reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K)*
          (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card K : ℝ)^((r+1).choose 2) *
        Nat.card (SymplecticCenterStratum ω Y r))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm 3]; ring
    _ ≤ (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) :=
      mul_le_mul_of_nonneg_right hpair (reducedPlantedSum_nonneg _ _ _ _ _ _ (by positivity))
    _ = _ := by rw [mul_pow,←pow_mul,←pow_mul]; congr 2 <;> rw [Nat.mul_comm]

 theorem fixedCommonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
      (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  let := Module.finite_of_finite K (M := ReducedSpace ω S.val)
  have hc := isotropic_finrank_le_half ω hω D hD S.val S.property.1
  rw [S.property.2] at hc
  have hd := reducedSpace_finrank ω S.val hω S.property.1
  rw [S.property.2] at hd
  obtain ⟨f,hf⟩ := fixedCommonCenter_injection ω ha hω (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (r := r) S Y
  have hh := symplectic_center_profile_card_upper (symplecticReductionForm ω S.val ha) h2
    (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
    (D-c) (by omega) (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
    (r-u) (h₀-c) (h₁-c) (h₂-c) hr
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)) (by positivity)).trans hh
end ReducedCardBound
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonParameters (D r c : ℕ) := {u : Fin (c+1) // u.val ≤ r ∧ r-u.val ≤ D-c}
noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
abbrev ProfileCenterSet (c h₀ h₁ h₂ r : ℕ) :=
  Σ p : TripleDimProfile ω c h₀ h₁ h₂, TripleCenterSet ω r p.val.1.val p.val.2.1.val p.val.2.2.val
abbrev PlantedCommonData (D c h₀ h₁ h₂ r : ℕ) :=
  Σ S : IsotropicDimspace ω c, Σ u : CommonParameters D r c,
    Σ Y : CommonCenterSet ω S.val u.val.val, FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r

 theorem profileCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) :
    ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
      Function.Injective f := by
  let F := ProfileCenterSet ω c h₀ h₁ h₂ r
  let S (p : F) := tripleProfileCommon ω p.1
  let u (p : F) := finrank K ↥((S p).val ⊓ p.2.val.val)
  have hS (p : F) : (S p).val ≤ p.1.val.1.val := inf_le_left.trans inf_le_left
  have hu (p : F) : u p ≤ c :=
    (Submodule.finrank_mono (inf_le_left : (S p).val ⊓ p.2.val.val ≤ (S p).val)).trans_eq (S p).property.2
  have hur (p : F) : u p ≤ r :=
    (Submodule.finrank_mono (inf_le_inf_right p.2.val.val (hS p))).trans_eq p.2.property.1
  have hdr (p : F) : r-u p ≤ D-c := by
    have hi := (S p).property.1
    have hc := isotropic_finrank_le_half ω hω D hD (S p).val hi
    have hd := reducedSpace_finrank ω (S p).val hω hi
    rw [(S p).property.2,hD.symm] at hd
    rw [(S p).property.2] at hc
    let Y' := generalReductionLagrangian ω ha hω (S p).val hi p.2.val
    let := Module.finite_of_finite K (M := ReducedSpace ω (S p).val)
    have hy := self_orthogonal_twice_finrank (symplecticReductionForm ω (S p).val ha) Y'.val
      (symplecticReductionForm_nondegenerate ω (S p).val ha hω) Y'.property
    have he := reduce_center_intersection_finrank ω (S p).val p.1.val.1.val p.2.val.val
      (hS p) (lagrangian_le_orthogonal ω (S p).val p.1.val.1.val p.1.val.1.property (hS p))
    rw [p.2.property.1] at he
    have hm := Submodule.finrank_mono (inf_le_right :
      reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val ≤ Y'.val)
    change finrank K ↥(reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val) + u p = r at he
    omega
  let f (p : F) : PlantedCommonData ω D c h₀ h₁ h₂ r :=
    ⟨S p,⟨⟨u p,by have := hu p; omega⟩,hur p,hdr p⟩,⟨p.2.val,rfl⟩,
      ⟨p.1,rfl,p.2.property⟩⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have hprofile : p.1 = q.1 := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.2.val) hpq
  have hcenter : p.2.val = q.2.val := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.1.val) hpq
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at hprofile hcenter
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hcenter)
end FullCenterCoding
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem unweight_count_bound {q x C y : ℝ} (hq : 0 < q) (a b : ℕ)
    (h : q^a*x ≤ C*q^b*y) : x ≤ C*q^((b:ℝ)-a)*y := by
  apply le_of_mul_le_mul_left (a := q^a) ?_ (pow_pos hq _)
  refine h.trans_eq ?_
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  field_simp

section CommonCountSummation
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedCommonCenter_card_rpow_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) :=
by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    unweight_count_bound (Nat.cast_pos.mpr Fintype.card_pos) _ _
      (fixedCommonCenter_card_upper ω h2 ha hω D hD (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) S Y hr)

 theorem commonData_fixed_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
    (S : IsotropicDimspace ω c) (u : CommonParameters D r c) :
    (Nat.card (Σ Y : CommonCenterSet ω S.val u.val.val,
      FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
        (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
          (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (CommonCenterSet ω S.val u.val.val)
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  let A : ℝ := 2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq.le _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq.le)
  have hu : u.val.val ≤ finrank K S.val := by rw [S.property.2]; exact Nat.le_of_lt_succ u.val.isLt
  have hc := commonCenter_card_upper ω h2 ha hω D hD S.val S.property.1 u.val.val hu
  rw [S.property.2] at hc
  calc
    _ = ∑ Y : CommonCenterSet ω S.val u.val.val,
        (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Y : CommonCenterSet ω S.val u.val.val, A :=
      Finset.sum_le_sum (fun Y _ => fixedCommonCenter_card_rpow_upper ω h2 ha hω D hD S Y u.property.2)
    _ = (Nat.card (CommonCenterSet ω S.val u.val.val) : ℝ)*A := by simp [Nat.card_eq_fintype_card]
    _ ≤ (2^u.val.val*lagrangianConstant (D-u.val.val)*
        (Fintype.card K : ℝ)^(u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2))*A :=
      mul_le_mul_of_nonneg_right hc hA
    _ = _ := by
      let a := u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2
      let b := 3*((D-c+1).choose 2)
      let e : ℝ := 3*((r-u.val.val+1).choose 2:ℝ)
      change (_*(Fintype.card K : ℝ)^a)*A = _*(Fintype.card K : ℝ)^((a:ℝ)+b-e)*_
      rw [show (a:ℝ)+b-e = a+((b:ℝ)-e) by ring,Real.rpow_add hq,Real.rpow_natCast]
      dsimp [A,a,b,e]
      ring
end CommonCountSummation
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def commonPlantedTerm (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ) : ℝ :=
  (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
    q^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
      (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
    reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) q
 theorem commonPlantedTerm_nonneg (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ)
    (hq : 0 ≤ q) : 0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q := by
  unfold commonPlantedTerm
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (lagrangianConstant_pos _).le) (by positivity)) (Real.rpow_nonneg hq _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq)

section FullProfileCenterBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem profileCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D) :
    (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
      (lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  obtain ⟨f,hf⟩ := profileCenter_injection ω ha hω D hD c h₀ h₁ h₂ r
  have hs (S : IsotropicDimspace ω c) :
      (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
        FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    exact Finset.sum_le_sum (fun u _ => commonData_fixed_card_upper ω h2 ha hω D hD S u)
  calc
    _ ≤ (Nat.card (PlantedCommonData ω D c h₀ h₁ h₂ r) : ℝ) :=
      Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ = ∑ S : IsotropicDimspace ω c,
        (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
          FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _S : IsotropicDimspace ω c,
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) :=
      Finset.sum_le_sum (fun S _ => hs S)
    _ = (Nat.card (IsotropicDimspace ω c) : ℝ)*
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right (isotropic_card_bounds ω h2 ha hω D hD c hc).2
      (Finset.sum_nonneg (fun u _ => commonPlantedTerm_nonneg _ _ _ _ _ _ _ _ (by positivity)))
end FullProfileCenterBound
end SidorenkoCounterexample

namespace SidorenkoCounterexample
 theorem normalized_count_ratio_bound {p t s O Z T A L C B : ℝ}
    (hp : 0 < p) (hA : 0 < A) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (_hO : 0 ≤ O)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hs : 0 ≤ s) (_ht : 0 ≤ t)
    (hOrbit : p^3 ≤ C*s*O) (hCenter : O*Z ≤ T)
    (hPair : p ≤ t*A) (hLag : L ≤ B*p) :
    Z*L^2/A^3 ≤ C*B^2*s*t^3*T/p^4 := by
  have hbar : p^3*Z ≤ C*s*T := by
    calc
      _ ≤ (C*s*O)*Z := mul_le_mul_of_nonneg_right hOrbit hZ
      _ = (C*s)*(O*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCenter (mul_nonneg hC hs)
  have hl : L^2 ≤ (B*p)^2 := pow_le_pow_left₀ hL hLag 2
  have htt : p^3 ≤ (t*A)^3 := pow_le_pow_left₀ hp.le hPair 3
  apply (div_le_div_iff₀ (pow_pos hA 3) (pow_pos hp 4)).mpr
  calc
    Z*L^2*p^4 ≤ Z*(B*p)^2*p^4 := by gcongr
    _ = (p^3*Z)*B^2*p^3 := by ring
    _ ≤ (C*s*T)*B^2*(t*A)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hbar (sq_nonneg B)) htt
        (by positivity) (by positivity)
    _ = _ := by ring

open Module
section OrbitCenterProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
 omit [FiniteDimensional K E] in
 theorem orbit_member_profile (L M N : SymplecticLagrangian ω)
    (P : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
    ω.orthogonal P.val.2.2 = P.val.2.2 ∧
    finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  refine ⟨(lagrangianIsometryEquiv ω e he L).property,
    (lagrangianIsometryEquiv ω e he M).property,
    (lagrangianIsometryEquiv ω e he N).property,?_,map_pair_finrank e _ _,map_pair_finrank e _ _,map_pair_finrank e _ _⟩
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]

omit [FiniteDimensional K E] in
 theorem orbitCenter_profile_injection (L M N : SymplecticLagrangian ω) (r : ℕ) :
    ∃ f : (Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) →
      ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
      Function.Injective f := by
  let F := Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2
  let G := ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r
  let f (p : F) : G :=
    let hp := orbit_member_profile ω L M N p.1
    ⟨⟨(⟨p.1.val.1,hp.1⟩,⟨p.1.val.2.1,hp.2.1⟩,⟨p.1.val.2.2,hp.2.2.1⟩),hp.2.2.2⟩,p.2⟩
  refine ⟨f,?_⟩
  intro p q h
  have he : p.1 = q.1 := Subtype.ext (congrArg (fun s : G => (s.1.val.1.val,s.1.val.2.1.val,s.1.val.2.2.val)) h)
  have hy : p.2.val = q.2.val := congrArg (fun s : G => s.2.val) h
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at he hy
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hy)

 omit [FiniteDimensional K E] in
 theorem orbit_center_count_le_profile [Finite E] (L M N : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (OrderedTripleOrbit ω L.val M.val N.val) * Nat.card (TripleCenterSet ω r L.val M.val N.val) ≤
      Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) := by
  rw [←tripleCenterOrbit_card]
  obtain ⟨f,hf⟩ := orbitCenter_profile_injection ω L M N r
  exact Nat.card_le_card_of_injective f hf
end OrbitCenterProfile
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def tripleFaceDensity (r : ℕ) (A L M N : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (TripleCenterSet ω r L.val M.val N.val) : ℝ)*
    (Nat.card (SymplecticLagrangian ω) : ℝ)^2 /
    (Nat.card (SymplecticCenterStratum ω A r) : ℝ)^3

 omit [Fintype K] [Finite E] in
 theorem tripleFaceDensity_nonneg (r : ℕ) (A L M N : SymplecticLagrangian ω) :
    0 ≤ tripleFaceDensity ω r A L M N := by unfold tripleFaceDensity; positivity

 theorem symplectic_center_stratum_card_pos (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (r : ℕ) (hr : r ≤ D) :
    (0:ℝ) < Nat.card (SymplecticCenterStratum ω A r) := by
  have hp := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω A r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn

 theorem tripleFaceDensity_profile_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq0 : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hOrbit := tripleOrbit_card_lower ω ha hω D hD hq L M N
  have hCenter := orbit_center_count_le_profile ω L M N r
  have hPair := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hLag := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).2
  have hi := normalized_count_ratio_bound
    (p := q^((D+1).choose 2)) (t := q^((r+1).choose 2))
    (s := q^(tripleDefect D L.val M.val N.val))
    (O := Nat.card (OrderedTripleOrbit ω L.val M.val N.val))
    (Z := Nat.card (TripleCenterSet ω r L.val M.val N.val))
    (T := Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
      (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r))
    (A := Nat.card (SymplecticCenterStratum ω A r)) (L := Nat.card (SymplecticLagrangian ω))
    (C := orbitMassConstant D) (B := lagrangianConstant D)
    (pow_pos hq0 _) (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (orbitMassConstant_pos D).le (lagrangianConstant_pos D).le (by positivity) (by positivity)
    (by simpa only [←pow_mul,Nat.mul_comm] using hOrbit)
    (by exact_mod_cast hCenter) hPair hLag
  refine hi.trans_eq ?_
  change _ = _*q^((tripleDefect D L.val M.val N.val : ℝ)+(3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ))*_
  rw [Real.rpow_sub hq0,Real.rpow_add hq0,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast]
  simp only [pow_mul,pow_succ]
  ring

 theorem tripleFaceDensity_full_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
    let h₀ := finrank K ↥(L.val ⊓ M.val)
    let h₁ := finrank K ↥(L.val ⊓ N.val)
    let h₂ := finrank K ↥(M.val ⊓ N.val)
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        ((lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
          ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)) := by
  dsimp only
  have hc : finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ≤ D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hh := profileCenter_card_upper ω h2 ha hω D hD
    (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
    (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r hc
  have hq0 : (0:ℝ) ≤ Fintype.card K := by positivity
  exact (tripleFaceDensity_profile_bound ω h2 ha hω D hD hq r hr A L M N).trans
    (mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (orbitMassConstant_pos D).le (sq_nonneg _))
      (Real.rpow_nonneg hq0 _)))
end PointwisePlanted
end SidorenkoCounterexample

end OAI
