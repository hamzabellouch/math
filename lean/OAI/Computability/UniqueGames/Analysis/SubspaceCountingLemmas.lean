import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Std
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

noncomputable def generators (S : Submodule K V) (k : ℕ)
    (h : finrank K S = k) : Fin k → V :=
  fun i => (Module.finBasisOfFinrankEq K S h i : V)

theorem span_generators (S : Submodule K V) (k : ℕ) (h : finrank K S = k) :
    Submodule.span K (Set.range (generators S k h)) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  change Submodule.span K (Set.range (S.subtype ∘ b)) = S
  rw [Set.range_comp, Submodule.span_image, b.span_eq]
  simp

/-- A k-subspace is determined by a chosen ordered k-tuple of spanning vectors. -/
theorem card_subspaces_rank_le [Finite V] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤ Nat.card V ^ k := by
  classical
  let code : {S : Submodule K V // finrank K S = k} → (Fin k → V) :=
    fun S => generators S.1 k S.2
  have hinj : Function.Injective code := by
    intro S T h
    apply Subtype.ext
    calc
      S.1 = Submodule.span K (Set.range (code S)) := (span_generators S.1 k S.2).symm
      _ = Submodule.span K (Set.range (code T)) :=
        congrArg (fun f : Fin k → V => Submodule.span K (Set.range f)) h
      _ = T.1 := span_generators T.1 k T.2
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hinj

/-- General finite-field form of the image-choice estimate in A.4. -/
theorem card_subspaces_rank_le_field_power [Finite K] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤
      Nat.card K ^ (finrank K V * k) := by
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  have h := card_subspaces_rank_le (K := K) (V := V) k
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_mul] at h

/-- Binary specialization: the ambient dimension is the dimension of Y's image,
not the potentially much larger original vector space. -/
theorem card_binary_subspaces_rank_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (d k : ℕ) (hd : finrank (ZMod 2) V ≤ d) :
    Nat.card {S : Submodule (ZMod 2) V // finrank (ZMod 2) S = k} ≤
      2 ^ (d * k) := by
  calc
    _ ≤ Nat.card (ZMod 2) ^ (finrank (ZMod 2) V * k) :=
      card_subspaces_rank_le_field_power (K := ZMod 2) (V := V) k
    _ = 2 ^ (finrank (ZMod 2) V * k) := by simp
    _ ≤ 2 ^ (d * k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k hd)

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

omit [Module.Finite K V] in
/-- Evaluating on a basis bounds the number of linear maps without counting
arbitrary functions on every vector. -/
theorem card_linearMaps_le [Finite V] :
    Nat.card (U →ₗ[K] V) ≤ Nat.card V ^ finrank K U := by
  let b := Module.finBasis K U
  let code : (U →ₗ[K] V) → (Fin (finrank K U) → V) := fun f i => f (b i)
  have hi : Function.Injective code := by
    intro f g h
    apply b.ext
    exact congrFun h
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hi

omit [Module.Finite K V] in
/-- Every rank-k map factors through the actual coordinate vector space K^k. -/
theorem exists_rank_factorization (f : U →ₗ[K] V) (k : ℕ)
    (hk : finrank K (LinearMap.range f) = k) :
    ∃ (a : (Fin k → K) →ₗ[K] V) (b : U →ₗ[K] (Fin k → K)), a.comp b = f := by
  let e := (Module.finBasisOfFinrankEq K (LinearMap.range f) hk).equivFun
  refine ⟨(LinearMap.range f).subtype.comp e.symm.toLinearMap,
    e.toLinearMap.comp f.rangeRestrict, ?_⟩
  ext x
  simp

/-- Rank-k maps between r- and s-dimensional spaces number at most |K|^((r+s)k).
This is a general finite-field bound, proved by selecting the preceding
factorization and injecting into the pair of factor maps. -/
theorem card_rank_maps_le [Finite K] (k : ℕ) :
    Nat.card {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k} ≤
      Nat.card K ^ ((finrank K U + finrank K V) * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis K U).equivFun
    (Module.finBasis K U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let A := (Fin k → K) →ₗ[K] V
  let B := U →ₗ[K] (Fin k → K)
  let : Finite A := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite B := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hf (f : {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k}) :
      ∃ p : A × B, p.1.comp p.2 = f.1 := by
    obtain ⟨a, b, h⟩ := exists_rank_factorization f.1 k f.2
    exact ⟨(a, b), h⟩
  let code := fun f => Classical.choose (hf f)
  have hi : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    calc
      f.1 = (code f).1.comp (code f).2 := (Classical.choose_spec (hf f)).symm
      _ = (code g).1.comp (code g).2 := congrArg (fun p : A × B => p.1.comp p.2) h
      _ = g.1 := Classical.choose_spec (hf g)
  calc
    _ ≤ Nat.card (A × B) := Nat.card_le_card_of_injective code hi
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _
    _ ≤ Nat.card V ^ k * (Nat.card K ^ k) ^ finrank K U := by
      apply Nat.mul_le_mul
      · simpa [A] using card_linearMaps_le (K := K) (U := Fin k → K) (V := V)
      · simpa [B, Nat.card_fun] using
          card_linearMaps_le (K := K) (U := U) (V := Fin k → K)
    _ = Nat.card K ^ ((finrank K U + finrank K V) * k) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := V)]
      simp only [← pow_mul, ← pow_add]
      congr 1
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

/-- Factor a map whose kernel contains `ker Y` and whose image lies in `range Y`
through the effective domain and codomain. -/
def quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y :=
  let f := (LinearMap.ker Y).liftQ X hker
  f.codRestrict (LinearMap.range Y) (fun q => himage (by
    rw [← Submodule.range_liftQ (LinearMap.ker Y) X hker]
    exact LinearMap.mem_range_self f q))

omit [Module.Finite K V] [Module.Finite K U] in
@[simp] theorem quotientImageMap_mk (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) (u : U) :
    (quotientImageMap Y X hker himage ((LinearMap.ker Y).mkQ u) : V) = X u := rfl

omit [Module.Finite K V] [Module.Finite K U] in
theorem rank_quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    finrank K (LinearMap.range (quotientImageMap Y X hker himage)) =
      finrank K (LinearMap.range X) := by
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range Y), ← LinearMap.range_comp]
  change finrank K (LinearMap.range ((LinearMap.ker Y).liftQ X hker)) = _
  rw [Submodule.range_liftQ]

omit [Module.Finite K V] in
/-- General ambient-independent rank-k bound for maps constrained by the image
and kernel of Y. This counts actual linear maps; neither cardinality nor
rank-additive predecessor estimates are supplied as hypotheses. -/
theorem card_constrained_maps_le [Finite K] (Y : U →ₗ[K] V) (k : ℕ) :
    Nat.card {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} ≤
      Nat.card K ^ (2 * finrank K (LinearMap.range Y) * k) := by
  classical
  let : Finite (LinearMap.range Y) := Finite.of_injective
    (Module.finBasis K (LinearMap.range Y)).equivFun
    (Module.finBasis K (LinearMap.range Y)).equivFun.injective
  let : Finite (U ⧸ LinearMap.ker Y) := Finite.of_injective
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun.injective
  let : Finite ((U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y}) :
      {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} :=
    ⟨quotientImageMap Y X.1 X.2.2.1 X.2.2.2,
      (rank_quotientImageMap Y X.1 X.2.2.1 X.2.2.2).trans X.2.1⟩
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    ext u
    have he := congrArg
      (fun f => ((f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y)
        ((LinearMap.ker Y).mkQ u) : V)) (congrArg Subtype.val h)
    exact he
  have hdim : finrank K (U ⧸ LinearMap.ker Y) = finrank K (LinearMap.range Y) := by
    have hq := (LinearMap.ker Y).finrank_quotient_add_finrank
    have hr := Y.finrank_range_add_finrank_ker
    omega
  calc
    _ ≤ Nat.card {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} := Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card K ^ ((finrank K (U ⧸ LinearMap.ker Y) +
        finrank K (LinearMap.range Y)) * k) :=
      card_rank_maps_le (K := K) (U := U ⧸ LinearMap.ker Y) (V := LinearMap.range Y) k
    _ = _ := by rw [hdim, ← two_mul]

section BinaryPredecessors

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module (ZMod 2) U] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V] in
theorem binary_add_cancel (X Y : U →ₗ[ZMod 2] V) : X + (Y + X) = Y := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hself (x : V) : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, htwo, zero_smul]
  ext u
  change X u + (Y u + X u) = Y u
  rw [add_comm (Y u) (X u), ← add_assoc, hself, zero_add]

theorem card_binary_predecessors_le (Y : U →ₗ[ZMod 2] V) (d k : ℕ)
    (hd : finrank (ZMod 2) (LinearMap.range Y) ≤ d) :
    Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))} ≤ 2 ^ (3 * d * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis (ZMod 2) U).equivFun
    (Module.finBasis (ZMod 2) U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis (ZMod 2) V).equivFun
    (Module.finBasis (ZMod 2) V).equivFun.injective
  let : Finite (U →ₗ[ZMod 2] V) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))}) :
      {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} := by
    have hr : finrank (ZMod 2) (LinearMap.range (X.1 + (Y + X.1))) =
        finrank (ZMod 2) (LinearMap.range X.1) +
        finrank (ZMod 2) (LinearMap.range (Y + X.1)) := by
      rw [binary_add_cancel]
      exact X.2.2
    refine ⟨X.1, X.2.1, ?_, ?_⟩
    · simpa only [binary_add_cancel] using
        RankAdditivity.ker_add_le_ker_left X.1 (Y + X.1) hr
    · simpa only [binary_add_cancel] using
        RankAdditivity.range_left_le_range_add X.1 (Y + X.1) hr
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    change (code X).1 = (code Z).1
    exact congrArg Subtype.val h
  calc
    _ ≤ Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} :=
      Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card (ZMod 2) ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) :=
      card_constrained_maps_le (K := ZMod 2) Y k
    _ = 2 ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) := by simp
    _ ≤ 2 ^ (3 * d * k) := by
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.mul_le_mul_right
      omega

end BinaryPredecessors

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

section

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace UniqueGamesTheorem.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontal (B : Submodule K V) : Submodule K (V × K) := B.prod ⊥
def hKernel (S : Submodule K (V × K)) : Submodule K V := S.comap (LinearMap.inl K V K)

def scalarMap {Q : Type*} [AddCommGroup Q] [Module K Q] (q : Q) : K →ₗ[K] Q where
  toFun t := t • q
  map_add' a b := add_smul a b q
  map_smul' a b := by change (a*b) • q = a • (b • q); exact mul_smul a b q

def extension (B : Submodule K V) (q : V ⧸ B) : Submodule K (V × K) :=
  LinearMap.ker (B.mkQ.comp (LinearMap.fst K V K) -
    (scalarMap q).comp (LinearMap.snd K V K))

theorem extension_mem (B : Submodule K V) (q : V ⧸ B) (x : V) (t : K) :
    (x,t) ∈ extension B q ↔ B.mkQ x = t • q := by
  change B.mkQ x - t • q = 0 ↔ _
  exact sub_eq_zero

theorem mkQ_eq_smul_iff (B : Submodule K V) (x v : V) (t : K) :
    B.mkQ x = t • B.mkQ v ↔ x - t • v ∈ B := by
  have he : B.mkQ (x-t•v) = B.mkQ x - t•B.mkQ v := by simp only [map_sub, map_smul]
  rw [← sub_eq_zero, ← he]
  change (x-t•v ∈ LinearMap.ker B.mkQ) ↔ _
  rw [Submodule.ker_mkQ]

@[simp] theorem hKernel_horizontal (B : Submodule K V) : hKernel (horizontal B) = B := by
  ext x
  change (x ∈ B ∧ (0:K) = 0) ↔ x ∈ B
  simp

@[simp] theorem hKernel_extension (B : Submodule K V) (q : V ⧸ B) : hKernel (extension B q) = B := by
  ext x
  change (x,0) ∈ extension B q ↔ x ∈ B
  rw [extension_mem, zero_smul]
  change (x ∈ LinearMap.ker B.mkQ) ↔ x ∈ B
  rw [Submodule.ker_mkQ]

theorem exists_one_extension (B : Submodule K V) (q : V ⧸ B) : ∃ v, (v,1) ∈ extension B q := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  exact ⟨v, (extension_mem B q v 1).mpr (by simpa only [one_smul] using hv)⟩

theorem eq_extension_of_one_mem (S : Submodule K (V × K)) (v : V)
    (hv : (v,1) ∈ S) : S = extension (hKernel S) ((hKernel S).mkQ v) := by
  ext p
  rcases p with ⟨x,t⟩
  rw [extension_mem, mkQ_eq_smul_iff]
  change (x,t) ∈ S ↔ (x-t•v,0) ∈ S
  have hz : (x-t•v,0) = (x,t)-t•(v,1) := by ext <;> simp
  rw [hz]
  constructor
  · intro hx; exact S.sub_mem hx (S.smul_mem t hv)
  · intro hx
    have h := S.add_mem hx (S.smul_mem t hv)
    simpa only [sub_add_cancel] using h

theorem eq_horizontal_of_no_one (S : Submodule K (V × K))
    (hn : ¬ ∃ v, (v,1) ∈ S) : S = horizontal (hKernel S) := by
  have last_zero : ∀ x t, (x,t) ∈ S → t = 0 := by
    intro x t hxt
    by_contra ht
    have h := S.smul_mem t⁻¹ hxt
    have h' : (t⁻¹ • x,1) ∈ S := by simpa [smul_eq_mul, ht] using h
    exact hn ⟨_,h'⟩
  ext p
  rcases p with ⟨x,t⟩
  change (x,t) ∈ S ↔ (x ∈ hKernel S ∧ t = 0)
  constructor
  · intro hp
    have ht := last_zero x t hp
    subst t
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact hx

theorem horizontal_ne_extension (A B : Submodule K V) (q : V ⧸ B) : horizontal A ≠ extension B q := by
  intro h
  obtain ⟨v,hv⟩ := exists_one_extension B q
  have hv' : (v,1) ∈ horizontal A := h.symm ▸ hv
  change v ∈ A ∧ (1:K) = 0 at hv'
  exact one_ne_zero hv'.2

theorem extension_injective (B : Submodule K V) : Function.Injective (extension B) := by
  intro q r h
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have hp : (v,1) ∈ extension B q := (extension_mem B q v 1).mpr (by simpa using hv)
  have hp' : (v,1) ∈ extension B r := h ▸ hp
  have hr := (extension_mem B r v 1).mp hp'
  simpa only [one_smul, hv] using hr

def encode : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) → Submodule K (V × K)
  | .inl B => horizontal B
  | .inr ⟨B,q⟩ => extension B q

theorem encode_injective : Function.Injective (encode (K:=K) (V:=V)) := by
  intro a b h
  cases a with
  | inl A =>
    cases b with
    | inl B =>
      have hAB : A = B := by simpa only [encode,hKernel_horizontal] using congrArg hKernel h
      subst B
      rfl
    | inr b =>
      rcases b with ⟨B,q⟩
      exact False.elim (horizontal_ne_extension A B q h)
  | inr a =>
    rcases a with ⟨A,q⟩
    cases b with
    | inl B => exact False.elim (horizontal_ne_extension B A q h.symm)
    | inr b =>
      rcases b with ⟨B,r⟩
      have hAB : A = B := by simpa only [encode,hKernel_extension] using congrArg hKernel h
      cases hAB
      have hqr : q = r := extension_injective A h
      cases hqr
      rfl

theorem encode_surjective : Function.Surjective (encode (K:=K) (V:=V)) := by
  intro S
  by_cases h : ∃ v, (v,1) ∈ S
  · obtain ⟨v,hv⟩ := h
    exact ⟨.inr ⟨hKernel S,(hKernel S).mkQ v⟩, (eq_extension_of_one_mem S v hv).symm⟩
  · exact ⟨.inl (hKernel S), (eq_horizontal_of_no_one S h).symm⟩

def splitEquiv : Submodule K (V × K) ≃ (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) :=
  (Equiv.ofBijective encode ⟨encode_injective,encode_surjective⟩).symm

def horizontalEquiv (B : Submodule K V) : B ≃ₗ[K] horizontal B where
  toFun b := ⟨((b:V),0),⟨b.property,rfl⟩⟩
  invFun p := ⟨p.val.1,p.property.1⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp : p.val.2 = 0 := p.property.2
      exact hp.symm
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def extensionEquiv (B : Submodule K V) (q : V ⧸ B) (v : V) (hv : B.mkQ v = q) :
    (B × K) ≃ₗ[K] extension B q where
  toFun p := ⟨((p.1:V)+p.2•v,p.2), by
    apply (extension_mem B q _ _).mpr
    have hb : B.mkQ (p.1:V) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact p.1.property
    simp only [map_add,map_smul,hb,hv,zero_add]⟩
  invFun p := (⟨p.val.1-p.val.2•v, by
    apply (mkQ_eq_smul_iff B _ v _).mp
    rw [hv]
    exact (extension_mem B q _ _).mp p.property⟩,p.val.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((p.1:V)+p.2•v)-p.2•v = (p.1:V)
      exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.val.1-p.val.2•v)+p.val.2•v = p.val.1
      exact sub_add_cancel _ _
    · rfl
  map_add' p r := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1:V)+(r.1:V))+(p.2+r.2)•v =
        ((p.1:V)+p.2•v)+((r.1:V)+r.2•v)
      rw [add_smul]
      abel
    · rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · change c•(p.1:V)+(c*p.2)•v = c•((p.1:V)+p.2•v)
      rw [smul_add,mul_smul]
    · rfl

theorem finrank_horizontal [FiniteDimensional K V] (B : Submodule K V) :
    Module.finrank K (horizontal B) = Module.finrank K B := (horizontalEquiv B).finrank_eq.symm

theorem finrank_extension [FiniteDimensional K V] (B : Submodule K V) (q : V ⧸ B) :
    Module.finrank K (extension B q) = Module.finrank K B + 1 := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have h := (extensionEquiv B q v hv).finrank_eq.symm
  simpa only [Module.finrank_prod,Module.finrank_self] using h

local instance subspaceFintype [Finite V] : Fintype (Submodule K V) := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.ofInjective (fun B : Submodule K V => (B : Set V)) SetLike.coe_injective
local instance quotientFintype [Finite V] (B : Submodule K V) : Fintype (V ⧸ B) := by
  letI : Finite (V ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  exact Fintype.ofFinite _

def weightedTotal [Finite V] (w : Nat → ℤ) : ℤ := ∑ B : Submodule K V, w (Module.finrank K B)

theorem card_eq_pow_finrank [Finite K] [Finite V] [FiniteDimensional K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  have h := Fintype.card_congr (Module.finBasis K V).equivFun.toEquiv
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card] using h

theorem quotient_card_mul_pow [Finite K] [Finite V] [FiniteDimensional K V] (B : Submodule K V) :
    (Nat.card (V ⧸ B) : ℤ) * (Nat.card K : ℤ)^Module.finrank K B =
      (Nat.card K : ℤ)^Module.finrank K V := by
  rw [card_eq_pow_finrank (K:=K) (V:=V ⧸ B)]
  simp only [Nat.cast_pow]
  rw [← pow_add, B.finrank_quotient_add_finrank]

theorem weightedTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V × K) w =
      ∑ B : Submodule K V, (w (Module.finrank K B) +
        (Nat.card (V ⧸ B) : ℤ) * w (Module.finrank K B + 1)) := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ a : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B),
        w (Module.finrank K (encode a)) :=
      (Equiv.sum_comp ((splitEquiv (K:=K) (V:=V)).symm) _).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_sigma,encode,Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro B _
        exact congrArg w (finrank_horizontal B)
      · apply Finset.sum_congr rfl
        intro B _
        calc
          _ = ∑ _q : V ⧸ B, w (Module.finrank K B + 1) := by
            apply Finset.sum_congr rfl
            intro q _
            exact congrArg w (finrank_extension B q)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Nat.card_eq_fintype_card]

def mobiusWeight (q : Nat) : Nat → ℤ
  | 0 => 1
  | n+1 => -(q:ℤ)^n * mobiusWeight q n

def mobiusTotal [Finite K] [Finite V] : ℤ :=
  weightedTotal (K:=K) (V:=V) (mobiusWeight (Nat.card K))

theorem mobiusTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V × K) =
      (1 - (Nat.card K : ℤ)^Module.finrank K V) * mobiusTotal (K:=K) (V:=V) := by
  classical
  unfold mobiusTotal
  rw [weightedTotal_prod]
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, (1-(Nat.card K:ℤ)^Module.finrank K V) *
        mobiusWeight (Nat.card K) (Module.finrank K B) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [mobiusWeight]
      have hcard := quotient_card_mul_pow (K:=K) B
      calc
        _ = mobiusWeight (Nat.card K) (Module.finrank K B) -
            ((Nat.card (V ⧸ B):ℤ)*(Nat.card K:ℤ)^Module.finrank K B) *
              mobiusWeight (Nat.card K) (Module.finrank K B) := by ring
        _ = _ := by rw [hcard]; ring
    _ = _ := by rw [Finset.mul_sum]

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem map_inverse (e : V ≃ₗ[K] W) (B : Submodule K V) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← Submodule.map_comp,hc,Submodule.map_id]

def subspaceEquiv (e : V ≃ₗ[K] W) : Submodule K V ≃ Submodule K W where
  toFun B := B.map e.toLinearMap
  invFun C := C.map e.symm.toLinearMap
  left_inv := map_inverse e
  right_inv := map_inverse e.symm

def subspaceMapEquiv (e : V ≃ₗ[K] W) (B : Submodule K V) : B ≃ₗ[K] B.map e.toLinearMap where
  toFun b := ⟨e b,Submodule.mem_map.mpr ⟨b,b.property,rfl⟩⟩
  invFun c := ⟨e.symm c,by
    rcases Submodule.mem_map.mp c.property with ⟨b,hb,hbc⟩
    rw [← hbc]
    simpa using hb⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

theorem finrank_map_equiv (e : V ≃ₗ[K] W) (B : Submodule K V) :
    Module.finrank K (B.map e.toLinearMap) = Module.finrank K B := (subspaceMapEquiv e B).finrank_eq.symm

theorem weightedTotal_equiv [Finite V] [Finite W] (e : V ≃ₗ[K] W) (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V) w = weightedTotal (K:=K) (V:=W) w := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, w (Module.finrank K (B.map e.toLinearMap)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [finrank_map_equiv]
    _ = _ := by
      change (∑ B : Submodule K V, w (Module.finrank K (subspaceEquiv e B))) = _
      exact Equiv.sum_comp (subspaceEquiv e) (fun B : Submodule K W => w (Module.finrank K B))

theorem mobiusTotal_equiv [Finite K] [Finite V] [Finite W] (e : V ≃ₗ[K] W) :
    mobiusTotal (K:=K) (V:=V) = mobiusTotal (K:=K) (V:=W) :=
  weightedTotal_equiv e _

def coordinateSplit (n : Nat) :
    (Fin (n+1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' f g := rfl
  map_smul' c f := rfl

theorem mobiusTotal_subsingleton [Finite K] [Finite V] [Subsingleton V] :
    mobiusTotal (K:=K) (V:=V) = 1 := by
  classical
  have hB : ∀ B : Submodule K V, B = ⊥ := by
    intro B
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  unfold mobiusTotal weightedTotal
  rw [Finset.sum_eq_single ⊥]
  · simp [mobiusWeight]
  · intro B _ hne
    exact (hne (hB B)).elim
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem coordinate_total_succ [Finite K] (n : Nat) :
    mobiusTotal (K:=K) (V:=Fin (n+1) → K) = 0 := by
  induction n with
  | zero =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) 0),mobiusTotal_prod]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) (n+1)),mobiusTotal_prod,ih,mul_zero]

theorem mobiusTotal_eq_if [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V) = if Module.finrank K V = 0 then 1 else 0 := by
  rw [mobiusTotal_equiv (Module.finBasis K V).equivFun]
  cases hd : Module.finrank K V with
  | zero => simpa [hd] using (mobiusTotal_subsingleton (K:=K) (V:=Fin 0 → K))
  | succ n => simpa [hd] using (coordinate_total_succ (K:=K) n)

theorem mobiusWeight_closed (q n : Nat) :
    mobiusWeight q n = (-1:ℤ)^n * (q:ℤ)^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    rw [mobiusWeight,ih,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,pow_add,pow_succ]
    ring

theorem binary_subspace_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] :
    weightedTotal (K:=ZMod 2) (V:=E) (fun d => (-1:ℤ)^d * 2^(d.choose 2)) =
      if Module.finrank (ZMod 2) E = 0 then 1 else 0 := by
  have h := mobiusTotal_eq_if (K:=ZMod 2) (V:=E)
  have hq : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [mobiusTotal,weightedTotal,mobiusWeight_closed,hq,Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Appendix.SubspaceExtensions

end

section

namespace UniqueGamesTheorem.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalEquiv (I : Submodule 𝕜 V) :
    {A : Submodule 𝕜 V // A ≤ I} ≃ Submodule 𝕜 I where
  toFun A := A.val.comap I.subtype
  invFun B := ⟨B.map I.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact b.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.comap I.subtype).map I.subtype = A.val
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact Submodule.mem_map.mpr ⟨⟨x, A.property hx⟩, hx, rfl⟩
  right_inv B := by
    change (B.map I.subtype).comap I.subtype = B
    ext b
    constructor
    · intro hb
      change (b : V) ∈ B.map I.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨c, hc, hcb⟩
      have h : c = b := Subtype.ext hcb
      simpa only [h] using hc
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩

def lowerIntervalSpaceEquiv (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    A.val ≃ₗ[𝕜] A.val.comap I.subtype where
  toFun a := ⟨⟨a.val, A.property a.property⟩, a.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem lowerInterval_finrank (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    finrank 𝕜 (lowerIntervalEquiv I A) = finrank 𝕜 A.val :=
  (lowerIntervalSpaceEquiv I A).finrank_eq.symm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_lowerInterval {R : Type*} [AddCommMonoid R]
    (I : Submodule 𝕜 V) [Fintype {A : Submodule 𝕜 V // A ≤ I}]
    [Fintype (Submodule 𝕜 I)] (weight : Nat → R) :
    (∑ A : {A : Submodule 𝕜 V // A ≤ I}, weight (finrank 𝕜 A.val)) =
      ∑ B : Submodule 𝕜 I, weight (finrank 𝕜 B) := by
  apply Fintype.sum_equiv (lowerIntervalEquiv I)
  intro A
  rw [lowerInterval_finrank]

local instance submoduleFinite [Finite V] : Finite (Submodule 𝕜 V) :=
  Finite.of_injective (fun S : Submodule 𝕜 V => (S : Set V)) SetLike.coe_injective

noncomputable def lowerWeightedTotal [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  exact ∑ A : {A : Submodule 𝕜 V // A ≤ I}, w (finrank 𝕜 A.val)

theorem lowerWeightedTotal_eq [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) :
    lowerWeightedTotal I w = SubspaceExtensions.weightedTotal (K := 𝕜) (V := I) w := by
  classical
  let := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  let := SubspaceExtensions.subspaceFintype (K := 𝕜) (V := I)
  unfold lowerWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (lowerIntervalEquiv I)
    (fun A : {A : Submodule 𝕜 V // A ≤ I} => w (finrank 𝕜 A.val))
    (fun B : Submodule 𝕜 I => w (finrank 𝕜 B))
    (fun A => congrArg w (lowerInterval_finrank I A).symm)

theorem binary_lower_interval_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] (I : Submodule (ZMod 2) E) :
    lowerWeightedTotal I (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if I = ⊥ then 1 else 0 := by
  rw [lowerWeightedTotal_eq, SubspaceExtensions.binary_subspace_mobius]
  simp only [Submodule.finrank_eq_zero]

end UniqueGamesTheorem.Appendix.SubmoduleInterval

end

section

namespace UniqueGamesTheorem.Fourier.Deletion

universe u v w

/-- The number of entries on which a Boolean function is true. -/
def trueCount {Ω : Type u} (f : Ω → Bool) : List Ω → Nat
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + trueCount f xs

theorem trueCount_mono {Ω : Type u} (f g : Ω → Bool)
    (h : ∀ x, f x = true → g x = true) (xs : List Ω) :
    trueCount f xs ≤ trueCount g xs := by
  induction xs with
  | nil => simp [trueCount]
  | cons x xs ih =>
    have hx : (if f x then 1 else 0 : Nat) ≤ (if g x then 1 else 0) := by
      cases hf : f x with
      | false => simp
      | true => simp [h x hf]
    exact Nat.add_le_add hx ih

theorem trueCount_eq_zero {Ω : Type u} (f : Ω → Bool) (xs : List Ω)
    (h : ∀ x, x ∈ xs → f x = false) : trueCount f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = false := h x (by simp)
    have ht : trueCount f xs = 0 := ih (fun y hy => h y (by simp [hy]))
    simp [trueCount, hx, ht]

/-- A family of admissible restrictions and their containing rows. Rows may
overlap, and there is no requirement that different restrictions share the
same ancillary data. -/
structure RestrictionSystem (Ω : Type u) (Row : Type v) (Witness : Type w) where
  samples : Witness → List Ω
  samples_nonempty : ∀ t, samples t ≠ []
  admissible : Witness → Prop
  row : Row → Ω → Prop
  containingRow : Witness → Row
  contained : ∀ t x, x ∈ samples t → row (containingRow t) x

variable {Ω : Type u} {Row : Type v} {Witness : Type w}

/-- Strict density above the rational threshold `p / q` when `q > 0`. -/
def Dense (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (t : Witness) : Prop :=
  p * (S.samples t).length < q * trueCount H (S.samples t)

/-- A row is bad when it contains a dense admissible restriction. -/
def BadRow (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (r : Row) : Prop :=
  ∃ t, S.admissible t ∧ S.containingRow t = r ∧ Dense S H p q t

/-- All points of every bad row are removed. -/
def DeletedSet (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (x : Ω) : Prop :=
  ∃ r, BadRow S H p q r ∧ S.row r x

/-- The Boolean remainder after deleting the union of bad rows. -/
noncomputable def remainder (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) : Bool := by
  classical
  exact if DeletedSet S H p q x then false else H x

/-- The Boolean part removed from the original function. -/
noncomputable def removed (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) : Bool := by
  classical
  exact if DeletedSet S H p q x then H x else false

theorem remainder_le_original (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω)
    (h : remainder S H p q x = true) : H x = true := by
  classical
  unfold remainder at h
  split at h
  · contradiction
  · exact h

/-- A dense restriction makes its whole row bad, including points that were
not sampled by the restriction. -/
theorem dense_deletes_whole_row (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (t : Witness)
    (ha : S.admissible t) (hd : Dense S H p q t)
    (x : Ω) (hx : S.row (S.containingRow t) x) :
    remainder S H p q x = false := by
  classical
  have hdel : DeletedSet S H p q x :=
    ⟨S.containingRow t, ⟨t, ha, rfl, hd⟩, hx⟩
  simp [remainder, hdel]

theorem dense_restriction_remainder_zero
    (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool) (p q : Nat)
    (t : Witness) (ha : S.admissible t) (hd : Dense S H p q t) :
    trueCount (remainder S H p q) (S.samples t) = 0 := by
  apply trueCount_eq_zero
  intro x hx
  exact dense_deletes_whole_row S H p q t ha hd x (S.contained t x hx)

/-- Rational restriction globality of a Boolean function. -/
def RestrictionGlobal (S : RestrictionSystem Ω Row Witness) (G : Ω → Bool)
    (p q : Nat) : Prop :=
  ∀ t, S.admissible t → q * trueCount G (S.samples t) ≤ p * (S.samples t).length

/-- Whole-row deletion establishes every admissible restriction bound. This
is the first assertion of Lemma 5.2, before applying Fourier estimates. -/
theorem remainder_restrictionGlobal
    (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool) (p q : Nat) :
    RestrictionGlobal S (remainder S H p q) p q := by
  classical
  intro t ha
  by_cases hd : Dense S H p q t
  · rw [dense_restriction_remainder_zero S H p q t ha hd]
    simp
  · have hn : q * trueCount H (S.samples t) ≤ p * (S.samples t).length :=
      Nat.le_of_not_gt hd
    exact Nat.le_trans
      (Nat.mul_le_mul_left q
        (trueCount_mono (remainder S H p q) H
          (remainder_le_original S H p q) (S.samples t))) hn

/-- Retained and removed contributions form a disjoint Boolean partition. -/
theorem boolean_partition (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) :
    (remainder S H p q x || removed S H p q x) = H x ∧
    (remainder S H p q x && removed S H p q x) = false := by
  classical
  by_cases hd : DeletedSet S H p q x <;> simp [remainder, removed, hd]

/-- Exact conservation of retained and removed mass on any sampling list. -/
theorem trueCount_partition (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (xs : List Ω) :
    trueCount H xs = trueCount (remainder S H p q) xs +
      trueCount (removed S H p q) xs := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hd : DeletedSet S H p q x
    · simp only [trueCount, remainder, removed, ite_eq_left hd, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add]
      omega
    · simp only [trueCount, remainder, removed, ite_eq_right hd, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add]
      omega

end UniqueGamesTheorem.Fourier.Deletion

end

end OAI
