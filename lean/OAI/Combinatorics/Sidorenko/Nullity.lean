import OAI.Combinatorics.Sidorenko.FormGluing

namespace OAI

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Bounds
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
/-- The elementary matching lower Grassmann bound. -/
theorem subspace_count_lower (k : ℕ) (hk : k ≤ finrank K V) :
    (Fintype.card K : ℝ)^(k*(finrank K V-k)) ≤ Nat.card (DimSubspace K V k) := by
  rw [subspace_count_real k hk]
  let q : ℝ := Fintype.card K
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hq0 : 0 < q := by linarith
  have hfac (i : Fin k) : q^(finrank K V-k) ≤
      (q^finrank K V-q^i.val)/(q^k-q^i.val) := by
    have hd : 0 < q^k-q^i.val := sub_pos.mpr (pow_lt_pow_right₀ hq i.isLt)
    have hid : q^finrank K V = q^(finrank K V-k)*q^k := by
      rw [←pow_add,Nat.sub_add_cancel hk]
    apply (le_div_iff₀ hd).mpr
    rw [hid]
    have hp : 1 ≤ q^(finrank K V-k) := one_le_pow₀ hq.le
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hq0.le i.val)
    nlinarith
  calc
    q^(k*(finrank K V-k)) = ∏ _i : Fin k, q^(finrank K V-k) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
      rw [Nat.mul_comm]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hq0.le _) (fun i _ => hfac i)

end Bounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainingSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem containment_quotient_finrank (S U : Submodule K V) (hS : S ≤ U) :
    finrank K (U.map S.mkQ) + finrank K S = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.comp U.subtype)
  rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,Submodule.ker_mkQ] at h
  rw [(Submodule.comapSubtypeEquivOfLe hS).finrank_eq] at h
  exact h

noncomputable def containingSubspaceEquiv (S : Submodule K V) (r : ℕ) (hr : finrank K S ≤ r) :
    {U : DimSubspace K V r // S ≤ U.val} ≃ DimSubspace K (V ⧸ S) (r-finrank K S) where
  toFun U := ⟨U.val.val.map S.mkQ,by
    have h := containment_quotient_finrank S U.val.val U.property
    rw [U.val.property] at h
    omega⟩
  invFun Q := ⟨⟨Q.val.comap S.mkQ,by
    have h := containment_quotient_finrank S (Q.val.comap S.mkQ) (Submodule.le_comap_mkQ _ _)
    rw [Submodule.map_comap_eq_self (by simp),Q.property] at h
    omega⟩,Submodule.le_comap_mkQ _ _⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change (U.val.val.map S.mkQ).comap S.mkQ = U.val.val
    simp only [Submodule.comap_map_mkQ, sup_eq_right.mpr U.property]
  right_inv Q := by
    apply Subtype.ext
    exact (S.comapMkQRelIso).symm_apply_apply Q.val

variable [Fintype K] [Finite V]
 omit [Finite V] in
 theorem containingSubspace_card_bounds (S : Submodule K V) (r : ℕ)
    (hr : finrank K S ≤ r) (hrD : r ≤ finrank K V) :
    (Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) ≤
        Nat.card {U : DimSubspace K V r // S ≤ U.val} ∧
    (Nat.card {U : DimSubspace K V r // S ≤ U.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) := by
  let : Finite (V ⧸ S) := Module.finite_of_finite K
  have hD := S.finrank_quotient_add_finrank
  have hle : r-finrank K S ≤ finrank K (V ⧸ S) := by omega
  have he : finrank K (V ⧸ S)-(r-finrank K S) = finrank K V-r := by omega
  rw [Nat.card_congr (containingSubspaceEquiv S r hr)]
  constructor
  · simpa only [he] using (subspace_count_lower (K := K) (V := V ⧸ S) (r-finrank K S) hle)
  · have h := subspace_count_upper (K := K) (V := V ⧸ S) (r-finrank K S) hle
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le r _)) (by positivity))
end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev SubspaceTripleProfile (r p₀ p₁ p₂ : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r × DimSubspace K V r //
    (R.1.val ⊓ R.2.1.val) ⊓ R.2.2.val = ⊥ ∧
    finrank K ↥(R.1.val ⊓ R.2.1.val) = p₀ ∧
    finrank K ↥(R.1.val ⊓ R.2.2.val) = p₁ ∧
    finrank K ↥(R.2.1.val ⊓ R.2.2.val) = p₂}
abbrev PairSubspaceConfig (p₀ p₁ p₂ : ℕ) :=
  {P : DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂ //
    Disjoint P.1.val P.2.1.val ∧ Disjoint P.1.val P.2.2.val ∧ Disjoint P.2.1.val P.2.2.val}
abbrev SubspaceTripleCompletion {p₀ p₁ p₂ : ℕ} (r : ℕ) (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) :=
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.1.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.2.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.2.1.val ⊔ P.val.2.2.val ≤ R.val}

 theorem triple_pairwise_disjoint (L M N : Submodule K V) (hc : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) (L ⊓ N) ∧ Disjoint (L ⊓ M) (M ⊓ N) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  refine ⟨disjoint_iff.mpr (le_antisymm ?_ bot_le),disjoint_iff.mpr (le_antisymm ?_ bot_le),
    disjoint_iff.mpr (le_antisymm ?_ bot_le)⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩

noncomputable def subspaceProfile_to_config {r p₀ p₁ p₂ : ℕ}
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) :
    Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P :=
  ⟨⟨(⟨R.val.1.val ⊓ R.val.2.1.val,R.property.2.1⟩,
    ⟨R.val.1.val ⊓ R.val.2.2.val,R.property.2.2.1⟩,
    ⟨R.val.2.1.val ⊓ R.val.2.2.val,R.property.2.2.2⟩),
    triple_pairwise_disjoint _ _ _ R.property.1⟩,
   ⟨R.val.1,sup_le inf_le_left inf_le_left⟩,
   ⟨R.val.2.1,sup_le inf_le_right inf_le_left⟩,
   ⟨R.val.2.2,sup_le inf_le_right inf_le_right⟩⟩
 theorem subspaceProfile_to_config_injective (r p₀ p₁ p₂ : ℕ) :
    Function.Injective (subspaceProfile_to_config (K := K) (V := V) (r := r) (p₀ := p₀) (p₁ := p₁) (p₂ := p₂)) := by
  intro R S h
  let f : (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) →
      DimSubspace K V r × DimSubspace K V r × DimSubspace K V r := fun p => (p.2.1.val,p.2.2.1.val,p.2.2.2.val)
  exact Subtype.ext (congrArg f h)

variable [FiniteDimensional K V]
 theorem disjoint_sup_finrank (U W : Submodule K V) (h : Disjoint U W) :
    finrank K ↥(U ⊔ W) = finrank K U + finrank K W := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [h.eq_bot,finrank_bot,add_zero] at hh
  exact hh

variable [Fintype K]
 theorem pairSubspaceConfig_card_upper (p₀ p₁ p₂ : ℕ)
    (h₀ : p₀ ≤ finrank K V) (h₁ : p₁ ≤ finrank K V) (h₂ : p₂ ≤ finrank K V) :
    (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂)) := by
  let : Finite V := Module.finite_of_finite K
  have hc : Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) ≤
      Nat.card (DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh : (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      (Nat.card (DimSubspace K V p₀) : ℝ) * Nat.card (DimSubspace K V p₁) * Nat.card (DimSubspace K V p₂) := by
    rw [Nat.card_prod, Nat.card_prod] at hc
    exact_mod_cast (hc.trans_eq (Nat.mul_assoc _ _ _).symm)
  calc
    _ ≤ _ := hh
    _ ≤ (2^p₀*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀))) *
      (2^p₁*(Fintype.card K : ℝ)^(p₁*(finrank K V-p₁))) *
      (2^p₂*(Fintype.card K : ℝ)^(p₂*(finrank K V-p₂))) := by
      exact mul_le_mul (mul_le_mul (subspace_count_upper p₀ h₀) (subspace_count_upper p₁ h₁)
        (by positivity) (by positivity)) (subspace_count_upper p₂ h₂) (by positivity) (by positivity)
    _ = _ := by simp only [pow_add]; ring

 theorem subspaceTripleCompletion_card_upper {p₀ p₁ p₂ : ℕ} (r : ℕ)
    (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleCompletion r P) : ℝ) ≤
      2^(3*r)*(Fintype.card K : ℝ)^((r-(p₀+p₁))*(finrank K V-r)+
        (r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)) := by
  let : Finite V := Module.finite_of_finite K
  have d₀ : finrank K ↥(P.val.1.val ⊔ P.val.2.1.val) = p₀+p₁ := by
    rw [disjoint_sup_finrank _ _ P.property.1,P.val.1.property,P.val.2.1.property]
  have d₁ : finrank K ↥(P.val.1.val ⊔ P.val.2.2.val) = p₀+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.1,P.val.1.property,P.val.2.2.property]
  have d₂ : finrank K ↥(P.val.2.1.val ⊔ P.val.2.2.val) = p₁+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.2,P.val.2.1.property,P.val.2.2.property]
  have a₀ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.1.val) r (by omega) hr).2
  have a₁ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  have a₂ := (containingSubspace_card_bounds (P.val.2.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  rw [d₀] at a₀
  rw [d₁] at a₁
  rw [d₂] at a₂
  have h := mul_le_mul (mul_le_mul a₀ a₁ (by positivity) (by positivity)) a₂ (by positivity) (by positivity)
  simpa only [SubspaceTripleCompletion,Nat.card_prod,Nat.cast_mul,pow_add,pow_mul,show 3*r=r+r+r by omega,
    mul_assoc,mul_left_comm,mul_comm] using h

noncomputable def subspaceTripleExponent (n r p₀ p₁ p₂ : ℕ) : ℕ :=
  p₀*(n-p₀)+p₁*(n-p₁)+p₂*(n-p₂) +
  ((r-(p₀+p₁))*(n-r)+(r-(p₀+p₂))*(n-r)+(r-(p₁+p₂))*(n-r))

 theorem subspaceTripleProfile_card_upper (r p₀ p₁ p₂ : ℕ)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent (finrank K V) r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
  have hc : (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      Nat.card (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (subspaceProfile_to_config_injective (K := K) (V := V) r p₀ p₁ p₂)
  let e := (r-(p₀+p₁))*(finrank K V-r)+(r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)
  calc
    _ ≤ _ := hc
    _ = ∑ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, (Nat.card (SubspaceTripleCompletion r P) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, 2^(3*r)*(Fintype.card K : ℝ)^e :=
      Finset.sum_le_sum (fun P _ => subspaceTripleCompletion_card_upper r P hr h₀ h₁ h₂)
    _ = (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ)*(2^(3*r)*(Fintype.card K : ℝ)^e) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂))) *
      (2^(3*r)*(Fintype.card K : ℝ)^e) := mul_le_mul_of_nonneg_right
        (pairSubspaceConfig_card_upper p₀ p₁ p₂ (by omega) (by omega) (by omega)) (by positivity)
    _ = _ := by dsimp [e,subspaceTripleExponent]; simp only [pow_add]; ring
end TripleSubspaces
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def restrictDimSubspace (Z : Submodule K V) {r : ℕ} (R : DimSubspace K V r) (h : R.val ≤ Z) :
    DimSubspace K Z r :=
  ⟨R.val.comap Z.subtype, (Submodule.comapSubtypeEquivOfLe h).finrank_eq.trans R.property⟩

noncomputable def restrictTripleProfile (Z : Submodule K V) {r p₀ p₁ p₂ : ℕ}
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂)
    (h : R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val ≤ Z) :
    SubspaceTripleProfile (K := K) (V := Z) r p₀ p₁ p₂ := by
  have h₀ : R.val.1.val ≤ Z := le_trans (le_trans le_sup_left le_sup_left) h
  have h₁ : R.val.2.1.val ≤ Z := le_trans (le_trans le_sup_right le_sup_left) h
  have h₂ : R.val.2.2.val ≤ Z := le_trans le_sup_right h
  refine ⟨(restrictDimSubspace Z R.val.1 h₀, restrictDimSubspace Z R.val.2.1 h₁,
    restrictDimSubspace Z R.val.2.2 h₂), ?_, ?_, ?_, ?_⟩
  · change (R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) ⊓ R.val.2.2.val.comap Z.subtype = ⊥
    rw [←Submodule.comap_inf,←Submodule.comap_inf,R.property.1,Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr Z.injective_subtype
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) = p₀
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.1.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.1.val)).finrank_eq]
    exact R.property.2.1
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₁
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.1
  · change finrank K ↥(R.val.2.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₂
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₁) :
      (R.val.2.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.2.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.2

abbrev SubspaceTripleSpanProfile (r p₀ p₁ p₂ n : ℕ) :=
  {R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂ //
    finrank K ↥(R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val) = n}

noncomputable def spanProfileInjection (r p₀ p₁ p₂ n : ℕ)
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
    Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂ :=
  ⟨⟨R.val.val.1.val ⊔ R.val.val.2.1.val ⊔ R.val.val.2.2.val,R.property⟩,
   restrictTripleProfile _ R.val le_rfl⟩

 omit [FiniteDimensional K V] in
 theorem spanProfileInjection_injective (r p₀ p₁ p₂ n : ℕ) :
    Function.Injective (spanProfileInjection (K := K) (V := V) r p₀ p₁ p₂ n) := by
  intro R S h
  let recover : (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) →
      Submodule K V × Submodule K V × Submodule K V := fun ZR =>
    (ZR.2.val.1.val.map ZR.1.val.subtype,ZR.2.val.2.1.val.map ZR.1.val.subtype,
      ZR.2.val.2.2.val.map ZR.1.val.subtype)
  have he (T : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
      recover (spanProfileInjection r p₀ p₁ p₂ n T) =
      (T.val.val.1.val,T.val.val.2.1.val,T.val.val.2.2.val) := by
    let Z := T.val.val.1.val ⊔ T.val.val.2.1.val ⊔ T.val.val.2.2.val
    change ((T.val.val.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.2.val.comap Z.subtype).map Z.subtype) = _
    rw [Submodule.map_comap_subtype,Submodule.map_comap_subtype,Submodule.map_comap_subtype]
    rw [inf_eq_right.mpr (le_trans le_sup_left le_sup_left),
      inf_eq_right.mpr (le_trans le_sup_right le_sup_left),inf_eq_right.mpr le_sup_right]
  have hh := congrArg recover h
  rw [he,he] at hh
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
    (Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) hh)) (Subtype.ext (congrArg (fun z => z.2.2) hh)))

variable [Fintype K]
 theorem subspaceTripleSpanProfile_card_upper (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^
        (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (DimSubspace K V n)
  have hc : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      Nat.card (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (spanProfileInjection_injective (K := K) (V := V) r p₀ p₁ p₂ n)
  calc
    _ ≤ _ := hc
    _ = ∑ Z : DimSubspace K V n, (Nat.card (SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Z : DimSubspace K V n, 2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂) := by
      apply Finset.sum_le_sum
      intro Z _
      simpa only [Z.property] using subspaceTripleProfile_card_upper (K := K) (V := Z.val) r p₀ p₁ p₂
        (by simpa only [Z.property] using hr) h₀ h₁ h₂
    _ = (Nat.card (DimSubspace K V n) : ℝ) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^n*(Fintype.card K : ℝ)^(n*(finrank K V-n))) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper n hn) (by positivity)
    _ = _ := by simp only [pow_add]; ring
end SpanCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]

 theorem subspace_span_cost_identity (d n r p₀ p₁ p₂ : ℕ)
    (hn : n ≤ d) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    ((n*(d-n)+subspaceTripleExponent n r p₀ p₁ p₂ : ℕ) : ℝ) - (3*r*(d-r) : ℕ) =
      -((d:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) - ((d:ℝ)-n)*(3*r-n-(p₀+p₁+p₂)) := by
  have hp₀ : p₀ ≤ n := (Nat.le_add_right p₀ p₁).trans (h₀.trans hr)
  have hp₁ : p₁ ≤ n := (Nat.le_add_left p₁ p₀).trans (h₀.trans hr)
  have hp₂ : p₂ ≤ n := (Nat.le_add_left p₂ p₀).trans (h₁.trans hr)
  simp only [subspaceTripleExponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_sub hn,Nat.cast_sub hr,Nat.cast_sub (hr.trans hn),
    Nat.cast_sub hp₀,Nat.cast_sub hp₁,Nat.cast_sub hp₂,Nat.cast_sub h₀,Nat.cast_sub h₁,Nat.cast_sub h₂]
  ring



 theorem subspace_span_probability_bound (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(
        -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
          ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))) := by
  let : Finite V := Module.finite_of_finite K
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hcount := subspaceTripleSpanProfile_card_upper (K := K) (V := V) r p₀ p₁ p₂ n hn hr h₀ h₁ h₂
  have hden : q^(3*r*(finrank K V-r)) ≤ (Nat.card (DimSubspace K V r) : ℝ)^3 := by
    have hu := subspace_count_lower (K := K) (V := V) r (hr.trans hn)
    have hh := pow_le_pow_left₀ (pow_nonneg hq.le _) hu 3
    simpa only [←pow_mul,Nat.mul_comm 3 r,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
  have hp : 0 < (Nat.card (DimSubspace K V r) : ℝ)^3 := lt_of_lt_of_le (pow_pos hq _) hden
  have hdiv : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
        (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      (2^(n+p₀+p₁+p₂+3*r)*q^(n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂)) /
        q^(3*r*(finrank K V-r)) := by
    exact div_le_div₀ (by positivity) hcount (pow_pos hq _) hden
  refine hdiv.trans_eq ?_
  rw [mul_div_assoc,←Real.rpow_natCast q (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂),
    ←Real.rpow_natCast q (3*r*(finrank K V-r)),←Real.rpow_sub hq,
    subspace_span_cost_identity (finrank K V) n r p₀ p₁ p₂ hn hr h₀ h₁ h₂]
end PlantedSubspaceExponent
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

 theorem coannihilator_finrank (R : Submodule K (Module.Dual K V)) :
    finrank K R.dualCoannihilator + finrank K R = finrank K V := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq R.dualCoannihilator
  rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at h

noncomputable def dualDimSubspaceEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    DimSubspace K V (finrank K V-r) ≃ DimSubspace K (Module.Dual K V) r where
  toFun U := ⟨U.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U.val
    rw [U.property] at h
    omega⟩
  invFun R := ⟨R.val.dualCoannihilator, by
    have h := coannihilator_finrank R.val
    rw [R.property] at h
    omega⟩
  left_inv U := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv R := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

 theorem coannihilator_common_finrank (R₀ R₁ R₂ : Submodule K (Module.Dual K V)) :
    finrank K ↥((R₀.dualCoannihilator ⊓ R₁.dualCoannihilator) ⊓ R₂.dualCoannihilator) =
      finrank K V - finrank K ↥((R₀ ⊔ R₁) ⊔ R₂) := by
  rw [←Submodule.dualCoannihilator_sup_eq,←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank ((R₀ ⊔ R₁) ⊔ R₂)
  omega

noncomputable def dualGraph (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) : Lagrangian (K := K) (V := V) :=
  graphLagrangian R.dualCoannihilator B

 theorem dualGraph_vertical_dim (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) :
    finrank K ↥((dualGraph R B).val ⊓ verticalSpace (K := K) (V := V)) = finrank K R := by
  change finrank K ↥(formGraph R.dualCoannihilator B.val ⊓ verticalSpace (K := K) (V := V)) = _
  rw [graph_vertical_intersection_finrank]
  have h := coannihilator_finrank R
  omega

 theorem dualGraph_vertical_subspace (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) (f : Module.Dual K V) :
    ((0,f) : V × Module.Dual K V) ∈ (dualGraph R B).val ↔ f ∈ R := by
  change (∃ u : R.dualCoannihilator, u.val = 0 ∧ _ = B.val u) ↔ _
  constructor
  · rintro ⟨u,hu,hf⟩
    have hu0 : u = 0 := Subtype.ext hu
    have hf0 : f ∈ R.dualCoannihilator.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator (W := R.dualCoannihilator) f).mpr
      intro x hx
      have h := congrArg (fun l : Module.Dual K R.dualCoannihilator => l ⟨x,hx⟩) hf
      simpa [hu0] using h
    simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using hf0
  · intro hf
    refine ⟨0,rfl,?_⟩
    ext x
    change f x.val = B.val 0 x
    rw [map_zero,LinearMap.zero_apply]
    have hx := (Submodule.mem_dualCoannihilator (Φ := R) x.val).mp x.property
    exact hx f hf

 theorem dualGraph_common_zero (R₀ R₁ R₂ : Submodule K (Module.Dual K V))
    (F : OriginalForms R₀.dualCoannihilator R₁.dualCoannihilator R₂.dualCoannihilator)
    (h : ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val = ⊥) :
    (R₀ ⊓ R₁) ⊓ R₂ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hm : ((0,f) : V × Module.Dual K V) ∈
      ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val :=
    ⟨⟨(dualGraph_vertical_subspace R₀ F.1 f).mpr hf.1.1,
       (dualGraph_vertical_subspace R₁ F.2.1 f).mpr hf.1.2⟩,
       (dualGraph_vertical_subspace R₂ F.2.2 f).mpr hf.2⟩
  have hz := h.le hm
  exact congrArg Prod.snd hz

end DualPlantedBases
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
 theorem symmetric_nullity_probability_bound_all (t : ℕ) :
    (Nat.card {B : SymForm K V // t ≤ finrank K B.val.ker} : ℝ) / Nat.card (SymForm K V) ≤
      2^t / (Fintype.card K : ℝ)^((t+1).choose 2) := by
  by_cases ht : t ≤ finrank K V
  · exact symmetric_nullity_probability_bound t ht
  · have : IsEmpty {B : SymForm K V // t ≤ finrank K B.val.ker} :=
      ⟨fun B => ht (B.property.trans (Submodule.finrank_le B.val.val.ker))⟩
    rw [Nat.card_of_isEmpty,Nat.cast_zero,zero_div]
    positivity
end NullityAll
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)


theorem planted_nullity_probability_bound_all
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (originalCyclicDifference A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₁ ⊓ A₂)) t₀
  have hb₁ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₂ ⊓ A₀)) t₁
  have hb₂ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₀ ⊓ A₁)) t₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)


 theorem lift_pair_profile_probability_bound_all (t₀ t₁ t₂ : ℕ)
 :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have he (F : OriginalForms A₀ A₁ A₂) :
      (finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)) ↔
      (t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker) := by
    change (_ ≤ finrank K ↥(formGraph A₁ F.2.1.val ⊓ formGraph A₂ F.2.2.val) ∧
      _ ≤ finrank K ↥(formGraph A₂ F.2.2.val ⊓ formGraph A₀ F.1.val) ∧
      _ ≤ finrank K ↥(formGraph A₀ F.1.val ⊓ formGraph A₁ F.2.1.val)) ↔ _
    rw [graph_pair_intersection_finrank,graph_pair_intersection_finrank,graph_pair_intersection_finrank]
    simp only [Nat.add_le_add_iff_left]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact planted_nullity_probability_bound_all A₀ A₁ A₂ t₀ t₁ t₂

end NullityAllLift
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
abbrev DualProfileForms (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :=
  OriginalForms R.val.val.1.val.dualCoannihilator R.val.val.2.1.val.dualCoannihilator
    R.val.val.2.2.val.dualCoannihilator
abbrev DualLiftEvent (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :=
  {F : DualProfileForms R //
    p₂+t₂ ≤ finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) ∧
    p₁+t₁ ≤ finrank K ↥((dualGraph R.val.val.2.2.val F.2.2).val ⊓ (dualGraph R.val.val.1.val F.1).val) ∧
    p₀+t₀ ≤ finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val)}

 theorem dualProfileForms_card [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    Nat.card (DualProfileForms R) = (Fintype.card K)^(3*((finrank K V-r+1).choose 2)) := by
  have hdim (S : DimSubspace K (Module.Dual K V) r) : finrank K S.val.dualCoannihilator = finrank K V-r := by
    have h := coannihilator_finrank S.val
    rw [S.property] at h
    omega
  simp only [DualProfileForms,OriginalForms,Nat.card_prod,symForm_card,hdim,←pow_add]
  congr 1
  omega

 theorem dual_lift_probability_bound [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) / Nat.card (DualProfileForms R) ≤
      2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
        (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2) := by
  let A₀ := R.val.val.1.val.dualCoannihilator
  let A₁ := R.val.val.2.1.val.dualCoannihilator
  let A₂ := R.val.val.2.2.val.dualCoannihilator
  have h₀ : finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) = p₂ := by
    dsimp only [A₁,A₂]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.2.2
  have h₁ : finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) = p₁ := by
    dsimp only [A₂,A₀]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq,inf_comm]
    exact R.val.property.2.2.1
  have h₂ : finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) = p₀ := by
    dsimp only [A₀,A₁]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.1
  have hv : finrank K (CommonSpace A₀ A₁ A₂) = finrank K V-n := by
    exact (coannihilator_common_finrank _ _ _).trans (by rw [R.property])
  have hb := lift_pair_profile_probability_bound_all A₀ A₁ A₂ t₂ t₁ t₀
  rw [h₀,h₁,h₂,hv] at hb
  refine hb.trans_eq ?_
  simp only [pow_add]
  ring

end DualProfileLift
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem subspace_profile_constraints {r p₀ p₁ p₂ n : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
    n ≤ finrank K V ∧ r ≤ n ∧ p₀+p₁ ≤ r ∧ p₀+p₂ ≤ r ∧ p₁+p₂ ≤ r ∧
      n+(p₀+p₁+p₂) ≤ 3*r := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdis := triple_pairwise_disjoint A B C R.val.property.1
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have ha : p₀+p₁ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (A ⊓ C) ≤ A from sup_le inf_le_left inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.1,hp₀,hp₁,hdA] at h
  have hb : p₀+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (B ⊓ C) ≤ B from sup_le inf_le_right inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.2.1,hp₀,hp₂,hdB] at h
  have hc : p₁+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ C from sup_le inf_le_right inf_le_right)
    rwa [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂,hdC] at h
  refine ⟨hn ▸ Submodule.finrank_le _,?_,ha,hb,hc,?_⟩
  · have h := Submodule.finrank_mono (show A ≤ (A ⊔ B) ⊔ C from le_trans le_sup_left le_sup_left)
    rwa [hdA,hn] at h
  · have h₁ := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) C
    have h₃ := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ (A ⊔ B) ⊓ C from
      sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl))
    rw [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂] at h₃
    rw [hdA,hdB,hp₀] at h₁
    rw [hn,hdC] at h₂
    omega
end ProfileConstraints

section DualLiftSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]

 theorem center_stratum_cube (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card {L : Lagrangian (K := K) (V := V) //
      finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 =
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3 *
        (Fintype.card K : ℝ)^(3*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 3]

 theorem dual_lift_sum_probability_bound (r p₀ p₁ p₂ n t₀ t₁ t₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n,
      DualLiftEvent R t₀ t₁ t₂) : ℝ) /
      (Nat.card {L : Lagrangian (K := K) (V := V) //
        finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 ≤
    ((Nat.card (SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3) *
    (2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
      (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let RType := SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
  let : Fintype RType := Fintype.ofFinite _
  let q : ℝ := Fintype.card K
  let f := 3*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/
    q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hF : 0 < q^f := pow_pos hq _
  have hb (R : RType) : (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤ b*q^f := by
    have h := dual_lift_probability_bound R t₀ t₁ t₂
    rw [dualProfileForms_card,Nat.cast_pow] at h
    exact (div_le_iff₀ hF).mp h
  have hc : (Nat.card (Σ R : RType, DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤
      (Nat.card RType : ℝ)*b*q^f := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _R : RType, b*q^f := Finset.sum_le_sum (fun R _ => hb R)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Nat.card_eq_fintype_card]; ring
  rw [center_stratum_cube r hr]
  refine (div_le_div_of_nonneg_right hc (by positivity)).trans_eq ?_
  change (Nat.card RType : ℝ)*b*q^f / ((Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3*q^f) = _
  rw [mul_div_mul_right _ _ hF.ne']
  ring

end DualLiftSum
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev CenterStratum (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r}

noncomputable def dualPairStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ≃
      CenterStratum (K := K) (V := V) r :=
  (Equiv.sigmaCongrLeft (β := fun U : DimSubspace K V (finrank K V-r) => SymForm K U.val)
    (dualDimSubspaceEquiv (K := K) (V := V) r hr).symm).trans (pairStratumEquiv r hr)

 theorem dualPairStratumEquiv_apply (r : ℕ) (hr : r ≤ finrank K V)
    (R : DimSubspace K (Module.Dual K V) r) (F : SymForm K R.val.dualCoannihilator) :
    (dualPairStratumEquiv r hr ⟨R,F⟩).val = dualGraph R.val F := rfl

abbrev DualBaseTriple (r : ℕ) := DimSubspace K (Module.Dual K V) r ×
  DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualBaseForms {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r) :=
  OriginalForms R.1.val.dualCoannihilator R.2.1.val.dualCoannihilator R.2.2.val.dualCoannihilator
noncomputable def dualBaseTripleGraph {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r)
    (F : DualBaseForms R) : Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) :=
  (dualGraph R.1.val F.1,dualGraph R.2.1.val F.2.1,dualGraph R.2.2.val F.2.2)

noncomputable def dualTripleStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
  let e : (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) :=
    { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2.1,RF.2.2.1⟩,⟨RF.1.2.2,RF.2.2.2⟩)
      invFun := fun p => ⟨(p.1.1,p.2.1.1,p.2.2.1),(p.1.2,p.2.1.2,p.2.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.trans ((dualPairStratumEquiv r hr).prodCongr ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr)))

 theorem dualTripleStratumEquiv_graph (r : ℕ) (hr : r ≤ finrank K V)
    (RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) :
    ((dualTripleStratumEquiv r hr RF).1.val,(dualTripleStratumEquiv r hr RF).2.1.val,
      (dualTripleStratumEquiv r hr RF).2.2.val) = dualBaseTripleGraph RF.1 RF.2 := rfl

 theorem dualGraph_pair_finrank_ge (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥(R ⊓ S) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  change _ ≤ finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val)
  rw [graph_pair_intersection_finrank,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.le_add_right _ _

abbrev CanonicalLiftProfile (r s₀ s₁ s₂ : ℕ) :=
  {RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R //
    let L := dualBaseTripleGraph RF.1 RF.2
    (L.1.val ⊓ L.2.1.val) ⊓ L.2.2.val = ⊥ ∧
    finrank K ↥(L.1.val ⊓ L.2.1.val) = s₀ ∧
    finrank K ↥(L.1.val ⊓ L.2.2.val) = s₁ ∧
    finrank K ↥(L.2.1.val ⊓ L.2.2.val) = s₂}

end CanonicalCoding
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

 theorem coannihilator_pair_finrank (R S : Submodule K (Module.Dual K V)) :
    finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) + finrank K R + finrank K S =
      finrank K V + finrank K ↥(R ⊓ S) := by
  rw [←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank (R ⊔ S)
  have hg := Submodule.finrank_sup_add_finrank_inf_eq R S
  omega

 theorem dualGraph_pair_finrank_le (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) ≤
      finrank K ↥(R ⊓ S)+finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) := by
  change finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val) ≤ _
  rw [graph_pair_intersection_finrank,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

 theorem dualGraph_pair_extra_feasible {r s : ℕ} (R S : DimSubspace K (Module.Dual K V) r)
    (F : SymForm K R.val.dualCoannihilator) (G : SymForm K S.val.dualCoannihilator)
    (hs : finrank K ↥((dualGraph R.val F).val ⊓ (dualGraph S.val G).val) = s) :
    (s-finrank K ↥(R.val ⊓ S.val))+2*r ≤ finrank K V+finrank K ↥(R.val ⊓ S.val) := by
  have h₁ := dualGraph_pair_finrank_ge R.val S.val F G
  have h₂ := dualGraph_pair_finrank_le R.val S.val F G
  have h₃ := coannihilator_pair_finrank R.val S.val
  rw [hs] at h₁ h₂
  rw [R.property,S.property] at h₃
  omega

 theorem dual_common_pair_extra_feasible {r p₀ p₁ p₂ n : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    (finrank K V-n)+2*r ≤ finrank K V+p₀ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₁ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₂ := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have hv := coannihilator_common_finrank A B C
  rw [hn] at hv
  have h₀ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ B.dualCoannihilator from inf_le_left)
  have h₁ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_left le_rfl)
  have h₂ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    B.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_right le_rfl)
  rw [hv] at h₀ h₁ h₂
  have hc₀ := coannihilator_pair_finrank A B
  have hc₁ := coannihilator_pair_finrank A C
  have hc₂ := coannihilator_pair_finrank B C
  rw [hdA,hdB,hp₀] at hc₀
  rw [hdA,hdC,hp₁] at hc₁
  rw [hdB,hdC,hp₂] at hc₂
  omega

end ExtraFeasibility
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section CanonicalParameterCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

abbrev FourDims (d : ℕ) := Fin (d+1) × Fin (d+1) × Fin (d+1) × Fin (d+1)
def BaseFeasible (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : Prop :=
  r ≤ θ.2.2.2.val ∧ θ.1.val+θ.2.1.val ≤ r ∧ θ.1.val+θ.2.2.1.val ≤ r ∧
  θ.2.1.val+θ.2.2.1.val ≤ r ∧ θ.2.2.2.val+(θ.1.val+θ.2.1.val+θ.2.2.1.val) ≤ 3*r ∧
  θ.1.val ≤ s₀ ∧ θ.2.1.val ≤ s₁ ∧ θ.2.2.1.val ≤ s₂ ∧
  (s₀-θ.1.val)+2*r ≤ d+θ.1.val ∧ (s₁-θ.2.1.val)+2*r ≤ d+θ.2.1.val ∧
  (s₂-θ.2.2.1.val)+2*r ≤ d+θ.2.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.1.val ∧ (d-θ.2.2.2.val)+2*r ≤ d+θ.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.2.2.1.val
abbrev BaseParameters (d r s₀ s₁ s₂ : ℕ) := {θ : FourDims d // BaseFeasible r s₀ s₁ s₂ θ}

noncomputable def canonicalLiftFourDims {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) : FourDims (finrank K V) :=
  let bound (R : Submodule K (Module.Dual K V)) : finrank K R < finrank K V+1 := by
    have h := Submodule.finrank_le R
    rw [Subspace.dual_finrank_eq] at h
    omega
  (⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.1.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.2.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥((P.val.1.1.val ⊔ P.val.1.2.1.val) ⊔ P.val.1.2.2.val),bound _⟩)

noncomputable def canonicalLiftSubspaces {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r
      (canonicalLiftFourDims P).1.val (canonicalLiftFourDims P).2.1.val
      (canonicalLiftFourDims P).2.2.1.val (canonicalLiftFourDims P).2.2.2.val :=
  ⟨⟨P.val.1,dualGraph_common_zero _ _ _ P.val.2 P.property.1,rfl,rfl,rfl⟩,rfl⟩

 theorem canonicalLift_feasible {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    BaseFeasible r s₀ s₁ s₂ (canonicalLiftFourDims P) := by
  have hc := subspace_profile_constraints (canonicalLiftSubspaces P)
  refine ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.1).trans_eq P.property.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.2).trans_eq P.property.2.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.2.1 P.val.2.2.2).trans_eq P.property.2.2.2
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.1 P.val.2.1 P.val.2.2.1 P.property.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.2 P.val.2.1 P.val.2.2.2 P.property.2.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.2.1 P.val.1.2.2 P.val.2.2.1 P.val.2.2.2 P.property.2.2.2
  · exact dual_common_pair_extra_feasible (canonicalLiftSubspaces P)

 theorem dualGraph_pair_gap_bound (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator)
    {p s : ℕ} (hp : finrank K ↥(R ⊓ S) = p)
    (hs : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = s) :
    p+(s-p) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  have h := dualGraph_pair_finrank_ge R S F G
  rw [hp,hs] at h
  rw [hs]
  omega

noncomputable def dualLift_of_exactDims {r p₀ p₁ p₂ n s₀ s₁ s₂ : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (F : DualProfileForms R)
    (hs₀ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val) = s₀)
    (hs₁ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₁)
    (hs₂ : finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₂) :
    DualLiftEvent R (s₀-p₀) (s₁-p₁) (s₂-p₂) :=
  ⟨F,dualGraph_pair_gap_bound _ _ F.2.1 F.2.2 R.val.property.2.2.2 hs₂,
    by
      have h := dualGraph_pair_gap_bound _ _ F.1 F.2.2 R.val.property.2.2.1 hs₁
      rwa [inf_comm] at h,
    dualGraph_pair_gap_bound _ _ F.1 F.2.1 R.val.property.2.1 hs₀⟩

noncomputable def canonicalLiftCoding {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val) :=
  ⟨⟨canonicalLiftFourDims P,canonicalLift_feasible P⟩,canonicalLiftSubspaces P,
    dualLift_of_exactDims (canonicalLiftSubspaces P) P.val.2 P.property.2.1 P.property.2.2.1 P.property.2.2.2⟩

 theorem canonicalLiftCoding_injective (r s₀ s₁ s₂ : ℕ) :
    Function.Injective (canonicalLiftCoding (K := K) (V := V) (r := r) (s₀ := s₀) (s₁ := s₁) (s₂ := s₂)) := by
  let recover : (Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) →
      Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R :=
    fun T => ⟨T.2.1.val.val,T.2.2.val⟩
  intro P Q h
  exact Subtype.ext (congrArg recover h)

abbrev CenterTripleProfile (r s₀ s₁ s₂ : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}

noncomputable def canonicalCenterProfileEquiv (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ :=
  Equiv.subtypeEquiv (dualTripleStratumEquiv r hr) (fun _ => Iff.rfl)

end CanonicalParameterCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
open scoped BigOperators

noncomputable instance baseParametersFintype (d r s₀ s₁ s₂ : ℕ) : Fintype (BaseParameters d r s₀ s₁ s₂) := Fintype.ofFinite _

def reducedPlantedExponent (d r s₀ s₁ s₂ : ℕ) (θ : FourDims d) : ℝ :=
  -((d:ℝ)-2*r)*(θ.1.val+θ.2.1.val+θ.2.2.1.val) -
    ((θ.1.val:ℝ)^2+θ.2.1.val^2+θ.2.2.1.val^2) -
    ((d:ℝ)-θ.2.2.2.val)*(3*r-θ.2.2.2.val-(θ.1.val+θ.2.1.val+θ.2.2.1.val)) +
    ((d-θ.2.2.2.val+1).choose 2 : ℕ) -
    (((s₀-θ.1.val+1).choose 2+(s₁-θ.2.1.val+1).choose 2+(s₂-θ.2.2.1.val+1).choose 2 : ℕ) : ℝ)

def reducedPlantedConstant (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : ℝ :=
  2^(θ.2.2.2.val+θ.1.val+θ.2.1.val+θ.2.2.1.val+3*r+(s₀-θ.1.val)+(s₁-θ.2.1.val)+(s₂-θ.2.2.1.val))

section CanonicalNumericalBound
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]

 theorem reducedPlanted_bound_one (r s₀ s₁ s₂ : ℕ)
    (θ : BaseParameters (finrank K V) r s₀ s₁ s₂) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    reducedPlantedConstant r s₀ s₁ s₂ θ.val *
      (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
  let p₀ := θ.val.1.val
  let p₁ := θ.val.2.1.val
  let p₂ := θ.val.2.2.1.val
  let n := θ.val.2.2.2.val
  let t₀ := s₀-p₀
  let t₁ := s₁-p₁
  let t₂ := s₂-p₂
  have hn : n ≤ finrank K V := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hcon := θ.property
  have hr : r ≤ n := hcon.1
  have hh := dual_lift_sum_probability_bound (K := K) (V := V) r p₀ p₁ p₂ n t₀ t₁ t₂ (hr.trans hn)
  have hp := subspace_span_probability_bound (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
    (by rwa [Subspace.dual_finrank_eq]) hr hcon.2.1 hcon.2.2.1 hcon.2.2.2.1
  rw [Subspace.dual_finrank_eq] at hp
  refine hh.trans ((mul_le_mul_of_nonneg_right hp (by positivity)).trans_eq ?_)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  let e : ℝ := -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
    ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))
  change (2^(n+p₀+p₁+p₂+3*r) * q^e) *
    (2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) = _
  have he : reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val =
      e+((finrank K V-n+1).choose 2 : ℕ)-(((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ) := rfl
  rw [he,Real.rpow_sub hq (e+((finrank K V-n+1).choose 2 : ℕ))
    (((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ),
    Real.rpow_add hq e ((finrank K V-n+1).choose 2 : ℕ),Real.rpow_natCast,Real.rpow_natCast]
  simp only [reducedPlantedConstant, pow_add]
  change _ = 2^n*2^p₀*2^p₁*2^p₂*2^(3*r)*2^t₀*2^t₁*2^t₂ * _
  ring

 theorem canonical_center_profile_probability_bound (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hi := Nat.card_le_card_of_injective _ (canonicalLiftCoding_injective (K := K) (V := V) r s₀ s₁ s₂)
  rw [Nat.card_congr (canonicalCenterProfileEquiv r s₀ s₁ s₂ hr),Nat.card_sigma] at hi
  have hi' := (Nat.cast_le (α := ℝ)).mpr hi
  rw [Nat.cast_sum] at hi'
  refine (div_le_div_of_nonneg_right hi' (by positivity)).trans ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun θ _ => reducedPlanted_bound_one r s₀ s₁ s₂ θ)

end CanonicalNumericalBound
end SidorenkoCounterexample

end OAI
