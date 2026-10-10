import OAI.Combinatorics.Sidorenko.Basic

namespace OAI

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SubspaceCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]

abbrev DimSubspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {U : Submodule K V // finrank K U = k}

abbrev IndependentTuple (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent K s}

omit [Fintype K] in
 theorem tuple_spans (k : ℕ) (U : DimSubspace K V k)
    (s : IndependentTuple K U.val k) :
    Submodule.span K (Set.range (fun i => (s.val i : V))) = U.val := by
  have hs : Submodule.span K (Set.range s.val) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card s.property, Fintype.card_fin, U.property]
  have h := congrArg (Submodule.map U.val.subtype) hs
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using h

noncomputable def tupleForget {k : ℕ}
    (s : Σ U : DimSubspace K V k, IndependentTuple K U.val k) :
    IndependentTuple K V k :=
  ⟨fun i => (s.2.val i : V), s.2.property.map' s.1.val.subtype
    (Submodule.ker_subtype _)⟩

omit [Fintype K] in
 theorem tupleForget_bijective (k : ℕ) :
    Function.Bijective (tupleForget (K := K) (V := V) (k := k)) := by
  constructor
  · rintro ⟨U,s⟩ ⟨W,t⟩ heq
    have hval : (fun i => (s.val i : V)) = (fun i => (t.val i : V)) :=
      congrArg Subtype.val heq
    have hUW : U = W := by
      apply Subtype.ext
      rw [← tuple_spans k U s, ← tuple_spans k W t, hval]
    subst W
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hval i)
  · intro s
    let U : DimSubspace K V k := ⟨Submodule.span K (Set.range s.val), by
      rw [finrank_span_eq_card s.property, Fintype.card_fin]⟩
    let t : Fin k → U.val := fun i => ⟨s.val i, Submodule.subset_span ⟨i,rfl⟩⟩
    have ht : LinearIndependent K t := LinearIndependent.of_comp U.val.subtype s.property
    refine ⟨⟨U,⟨t,ht⟩⟩, ?_⟩
    rfl

/-- Counting independent tuples by their span gives the exact Grassmann
counting identity, with no division and including k=0. -/
 theorem subspace_count_identity (k : ℕ) (hk : k ≤ finrank K V) :
    Nat.card (DimSubspace K V k) *
      (∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val)) =
        ∏ i : Fin k, (Fintype.card K ^ finrank K V - Fintype.card K ^ i.val) := by
  classical
  let : Fintype (DimSubspace K V k) := Fintype.ofFinite _
  have h := Nat.card_congr (Equiv.ofBijective _ (tupleForget_bijective (K := K) (V := V) k))
  rw [Nat.card_sigma] at h
  have hcard (U : DimSubspace K V k) : Nat.card (IndependentTuple K U.val k) =
      ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val) := by
    rw [IndependentTuple, card_linearIndependent (by rw [U.property]), U.property]
  simp only [hcard, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id] at h
  rw [Nat.card_eq_fintype_card, h]
  exact card_linearIndependent hk

 theorem independent_tuple_count_pos (k : ℕ) :
    0 < ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val) := by
  apply Finset.prod_pos
  intro i _
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right Fintype.one_lt_card i.isLt

/-- The exact Gaussian binomial formula stated in the manuscript. -/
 theorem subspace_count_real (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) =
      ∏ i : Fin k, ((Fintype.card K : ℝ) ^ finrank K V - (Fintype.card K : ℝ)^i.val) /
        ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^i.val) := by
  have h := subspace_count_identity (K := K) (V := V) k hk
  have hp := independent_tuple_count_pos (K := K) k
  have hle (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ k :=
    Nat.pow_le_pow_right (by exact Fintype.card_pos) i.isLt.le
  have hle' (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K V :=
    Nat.pow_le_pow_right (by exact Fintype.card_pos) (i.isLt.le.trans hk)
  have hr : (Nat.card (DimSubspace K V k) : ℝ) *
      (∏ i : Fin k, ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^i.val)) =
      ∏ i : Fin k, ((Fintype.card K : ℝ)^finrank K V - (Fintype.card K : ℝ)^i.val) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_sub (hle _),
      Nat.cast_sub (hle' _), Nat.cast_pow] using hc
  have hpr : (0 : ℝ) < ∏ i : Fin k, ((Fintype.card K : ℝ)^k -
      (Fintype.card K : ℝ)^i.val) := by
    have hpc : (0 : ℝ) < ((∏ i : Fin k, (Fintype.card K ^ k -
        Fintype.card K ^ i.val)) : ℕ) := by exact_mod_cast hp
    simpa only [Nat.cast_prod, Nat.cast_sub (hle _), Nat.cast_pow] using hpc
  rw [Finset.prod_div_distrib]
  exact (eq_div_iff hpr.ne').mpr hr

/-- A dimension-uniform explicit Grassmann bound, sufficient for all nullity
union bounds; the constant 2^k is independent of the finite field. -/
 theorem subspace_count_upper (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) ≤
      2^k * (Fintype.card K : ℝ)^(k * (finrank K V - k)) := by
  rw [subspace_count_real k hk]
  let q : ℝ := Fintype.card K
  have hq : 2 ≤ q := by
    have hcard : 2 ≤ Fintype.card K := Fintype.one_lt_card
    change (2 : ℝ) ≤ (Fintype.card K : ℝ)
    exact_mod_cast hcard
  have hq0 : 0 < q := by linarith
  have hpow (i : Fin k) : 2 * q^i.val ≤ q^k := by
    calc
      2 * q^i.val ≤ q * q^i.val := mul_le_mul_of_nonneg_right hq (pow_nonneg hq0.le _)
      _ = q^(i.val+1) := by rw [pow_succ]; ring
      _ ≤ q^k := pow_le_pow_right₀ (by linarith) i.isLt
  have hfac (i : Fin k) : (q^finrank K V - q^i.val)/(q^k-q^i.val) ≤
      2 * q^(finrank K V - k) := by
    have hid : q^finrank K V = q^(finrank K V - k) * q^k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have hp : 0 < q^i.val := pow_pos hq0 _
    have hd : 0 < q^k-q^i.val := by linarith [hpow i]
    apply (div_le_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_left (hpow i) (pow_nonneg hq0.le (finrank K V-k))
    rw [hid]
    nlinarith
  calc
    (∏ i : Fin k, (q^finrank K V - q^i.val)/(q^k-q^i.val)) ≤
        ∏ _i : Fin k, 2 * q^(finrank K V-k) := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply div_nonneg
        · exact sub_nonneg.mpr (pow_le_pow_right₀ (by linarith) (i.isLt.le.trans hk))
        · linarith [hpow i, pow_nonneg hq0.le i.val]
      · intro i _
        exact hfac i
    _ = 2^k * q^(k * (finrank K V-k)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
        Nat.mul_comm (finrank K V-k) k]

end SubspaceCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FormCount
variable (K : Type*) [Field K]

def symmetricSubmodule (D : ℕ) : Submodule K (Matrix (Fin D) (Fin D) K) where
  carrier := {M | M.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hM hN => hM.add hN
  smul_mem' := fun a _ hM => hM.smul a

abbrev SymMatrix (D : ℕ) := symmetricSubmodule K D

/-- A symmetric matrix is exactly a function on unordered pairs with repetition. -/
def symMatrixCoordinates (D : ℕ) : SymMatrix K D ≃ (Sym2 (Fin D) → K) :=
  (Equiv.subtypeEquiv (Equiv.refl (Matrix (Fin D) (Fin D) K)) (fun M => by
    change M.IsSymm ↔ ∀ i j, M i j = M j i
    constructor
    · intro h i j
      exact (h.apply i j).symm
    · intro h
      ext i j
      exact h j i)).trans Sym2.lift

 theorem symMatrix_card [Fintype K] (D : ℕ) :
    Nat.card (SymMatrix K D) = Fintype.card K ^ ((D+1).choose 2) := by
  rw [Nat.card_congr (symMatrixCoordinates K D), Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Sym2.card, Fintype.card_fin]

variable (V : Type*) [AddCommGroup V] [Module K V]

abbrev SymForm := {B : LinearMap.BilinForm K V // B.IsSymm}

noncomputable def symFormMatrix [FiniteDimensional K V] :
    SymForm K V ≃ SymMatrix K (finrank K V) :=
  Equiv.subtypeEquiv (LinearMap.BilinForm.toMatrix (Module.finBasis K V)).toEquiv
    (fun B => (B.isSymm_toMatrix_iff_isSymm (Module.finBasis K V)).symm)

instance symForm_finite [Finite K] [FiniteDimensional K V] : Finite (SymForm K V) :=
  Finite.of_equiv (SymMatrix K (finrank K V)) (symFormMatrix K V).symm

 theorem symForm_card [Fintype K] [FiniteDimensional K V] :
    Nat.card (SymForm K V) = Fintype.card K ^ ((finrank K V + 1).choose 2) := by
  rw [Nat.card_congr (symFormMatrix K V), symMatrix_card]

variable {K V}

/-- Symmetric forms whose radical contains a prescribed subspace descend
bijectively to the quotient. This keeps the actual radical condition. -/
def formRadicalEquiv (U : Submodule K V) :
    {B : SymForm K V // U ≤ B.val.ker} ≃ SymForm K (V ⧸ U) where
  toFun B := ⟨LinearMap.IsRefl.liftQ₂ B.val.val U B.val.property.isRefl B.property, by
    constructor
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact B.val.property.eq x y⟩
  invFun C := ⟨⟨C.val.compl₁₂ U.mkQ U.mkQ, by
    constructor
    intro x y
    exact C.property.eq _ _⟩, by
      intro x hx
      apply LinearMap.mem_ker.mpr
      ext y
      change C.val (U.mkQ x) (U.mkQ y) = 0
      simp [(Submodule.Quotient.mk_eq_zero U).mpr hx]⟩
  left_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    ext x y
    rfl
  right_inv C := by
    apply Subtype.ext
    ext x y
    rfl



 theorem radical_containment_card [Fintype K] [FiniteDimensional K V]
    (U : Submodule K V) :
    Nat.card {B : SymForm K V // U ≤ B.val.ker} =
      Fintype.card K ^ ((finrank K V - finrank K U + 1).choose 2) := by
  rw [Nat.card_congr (formRadicalEquiv U), symForm_card]
  congr 2
  have h := U.finrank_quotient_add_finrank
  omega

/-- Union bound over genuine subspaces of the radical, not a rank heuristic. -/
 theorem nullity_count_bound [Fintype K] [Finite V] (u : ℕ) :
    Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} ≤
      Nat.card (DimSubspace K V u) *
        Fintype.card K ^ ((finrank K V - u + 1).choose 2) := by
  classical
  let : Fintype (DimSubspace K V u) := Fintype.ofFinite _
  let f : (Σ U : DimSubspace K V u, {B : SymForm K V // U.val ≤ B.val.ker}) →
      {B : SymForm K V // u ≤ finrank K B.val.ker} := fun x =>
    ⟨x.2.val, by simpa only [x.1.property] using Submodule.finrank_mono x.2.property⟩
  have hf : Function.Surjective f := by
    intro B
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank B.property
    let w : Fin u → V := fun i => (v i : V)
    have hw : LinearIndependent K w := hv.map' B.val.val.ker.subtype
      (Submodule.ker_subtype _)
    let U : DimSubspace K V u := ⟨Submodule.span K (Set.range w), by
      rw [finrank_span_eq_card hw, Fintype.card_fin]⟩
    have hU : U.val ≤ B.val.val.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (v i).property
    exact ⟨⟨U,⟨B.val,hU⟩⟩, rfl⟩
  calc
    Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} ≤
        Nat.card (Σ U : DimSubspace K V u, {B : SymForm K V // U.val ≤ B.val.ker}) :=
      Nat.card_le_card_of_surjective f hf
    _ = _ := by
      rw [Nat.card_sigma]
      have hdim (U : DimSubspace K V u) : finrank K U.val = u := U.property
      simp only [radical_containment_card, hdim, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]

 theorem symmetric_nullity_exponent (n u : ℕ) (hu : u ≤ n) :
    u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 = (n+1).choose 2 := by
  have h : ((u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 : ℕ) : ℚ) =
      ((n+1).choose 2 : ℚ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_one,
      Nat.cast_sub hu]
    ring
  exact_mod_cast h

/-- An explicit finite-field nullity tail bound. In the manuscript this is
O(q^(-b(u))); here the constant is the concrete field-independent 2^u. -/
 theorem symmetric_nullity_probability_bound [Fintype K] [Finite V]
    (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) /
      Nat.card (SymForm K V) ≤ 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) := by
  have hcount : (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) ≤
      (Nat.card (DimSubspace K V u) : ℝ) *
        (Fintype.card K : ℝ)^((finrank K V-u+1).choose 2) := by
    exact_mod_cast nullity_count_bound (K := K) (V := V) u
  have hspace := subspace_count_upper (K := K) (V := V) u hu
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  rw [symForm_card, Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hq _)).mpr
  calc
    (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) ≤
        2^u * (Fintype.card K : ℝ)^(u*(finrank K V-u)) *
          (Fintype.card K : ℝ)^((finrank K V-u+1).choose 2) :=
      hcount.trans (mul_le_mul_of_nonneg_right hspace (pow_nonneg hq.le _))
    _ = 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) *
        (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
      rw [← symmetric_nullity_exponent (finrank K V) u hu]
      rw [pow_add, pow_add]
      field_simp

end FormCount
end SidorenkoCounterexample

end OAI
