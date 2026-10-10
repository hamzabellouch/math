import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Analysis.DerivativeInduction
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Analysis.SubspaceCountingLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

/-!
# Exact antecedents of quotient compression

This is the reverse-map count used in Proposition A.5. The compressed map is
fixed, together with the two removed subspaces; neither a prescribed rank nor
an assumed cardinality is part of the antecedent predicate.
-/

namespace UniqueGamesTheorem.Appendix.AntecedentCount

open UniqueGamesTheorem.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Actual quotient-compression antecedents with the complement conditions
in the passage from (A.15) to (A.16). -/
def IsAntecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) : Prop :=
  compress X Q P = Y ∧ Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev Antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :=
  {X : W →ₗ[F2] V // IsAntecedent P Q Y X}

/-- Maps satisfying the geometric complement conditions, before their
compression is fixed. -/
abbrev Admissible (P : Submodule F2 W) (Q : Submodule F2 V) :=
  {X : W →ₗ[F2] V // Disjoint X.range Q ∧ P ⊔ X.ker = ⊤}

/-- Reindex the actual maps by their actual compressed frequency. -/
def compressionEquiv (P : Submodule F2 W) (Q : Submodule F2 V) :
    Admissible P Q ≃ Σ Y : P →ₗ[F2] (V ⧸ Q), Antecedent P Q Y where
  toFun X := ⟨compress X.val Q P, ⟨X.val, rfl, X.property⟩⟩
  invFun X := ⟨X.2.val, X.2.property.2⟩
  left_inv X := rfl
  right_inv X := by
    rcases X with ⟨Y, ⟨X, hXY, hd, hk⟩⟩
    cases hXY
    rfl

/-- Choosing a codomain complement only changes the coordinates of the fixed
compressed output. -/
theorem isAntecedent_iff_subspace (P : Submodule F2 W)
    (Q D : Submodule F2 V) (hQ : IsCompl Q D)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) :
    IsAntecedent P Q Y X ↔
      DerivativeInduction.IsSubspaceAntecedent P Q D hQ
        ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) X := by
  constructor
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    intro p
    have h := LinearMap.congr_fun hXY p
    exact congrArg (Q.quotientEquivOfIsCompl D hQ) h
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    ext p
    apply (Q.quotientEquivOfIsCompl D hQ).injective
    exact hXY p

/-- The quotient antecedents and the graph-coordinate antecedents are the
same maps, with equivalent predicates. -/
def subspaceEquiv (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Y : P →ₗ[F2] (V ⧸ Q)) :
    Antecedent P Q Y ≃ DerivativeInduction.SubspaceAntecedent P Q D hQ
      ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) where
  toFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mp X.property⟩
  invFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mpr X.property⟩
  left_inv X := Eq.refl X
  right_inv X := Eq.refl X

variable [FiniteDimensional F2 W] [FiniteDimensional F2 V]

omit [FiniteDimensional F2 V] in
/-- Every admissible antecedent has the rank of its fixed compression. -/
theorem rank_eq (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : Antecedent P Q Y) :
    Module.finrank F2 X.val.range = Module.finrank F2 Y.range := by
  have h := compress_rank_preserved X.val Q P X.property.2.1.symm X.property.2.2
  rw [X.property.1] at h
  exact h.symm

/-- Exact number of antecedents of a fixed quotient compression. The graph
and omitted-domain parameters have `rank Y * (dim Q + codim P)` bits. -/
theorem card_antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :
    Nat.card (Antecedent P Q Y) =
      2 ^ (Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P))) := by
  obtain ⟨E, hP⟩ := P.exists_isCompl
  obtain ⟨D, hQ⟩ := Q.exists_isCompl
  rw [Nat.card_congr (subspaceEquiv P Q D hQ Y),
    DerivativeInduction.card_subspaceAntecedent P E Q D hP hQ]
  rw [CoordinateTransport.finrank_comp_equiv]
  rw [← (P.quotientEquivOfIsCompl E hP).finrank_eq]

/-- The actual reverse-map multiplicity fits the two graph-parameter budgets
used in (A.16). No additional isomorphism factor is needed. -/
theorem card_antecedent_le (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hQ : Module.finrank F2 Q ≤ d)
    (hP : Module.finrank F2 (W ⧸ P) ≤ d) :
    Nat.card (Antecedent P Q Y) ≤ 2 ^ (2 * d * k) := by
  rw [card_antecedent]
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  calc
    Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P)) ≤ k * (d + d) :=
      Nat.mul_le_mul hY (Nat.add_le_add hQ hP)
    _ = 2 * d * k := by ring

/-- Exact finite-sum reindexing by compressed maps, with the true fiber
multiplicity. This holds for signed weights as well as nonnegative energies. -/
theorem sum_compression [Fintype (W →ₗ[F2] V)]
    (P : Submodule F2 W) (Q : Submodule F2 V)
    [Fintype (P →ₗ[F2] (V ⧸ Q))]
    {R : Type*} [Semiring R] (weight : (P →ₗ[F2] (V ⧸ Q)) → R) :
    (∑ X : Admissible P Q, weight (compress X.val Q P)) =
      ∑ Y : P →ₗ[F2] (V ⧸ Q),
        (2 : R) ^ (Module.finrank F2 Y.range *
          (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P))) * weight Y := by
  classical
  calc
    (∑ X : Admissible P Q, weight (compress X.val Q P)) =
        ∑ X : Σ Y : P →ₗ[F2] (V ⧸ Q), Antecedent P Q Y, weight X.1 :=
      Fintype.sum_equiv (compressionEquiv P Q) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro Y _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, card_antecedent]
      simp only [Nat.cast_pow, Nat.cast_ofNat]

end

end UniqueGamesTheorem.Appendix.AntecedentCount

end

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

/-- Restrict a dual map to `ker X` and then quotient by `range X`. -/
def compression (X Y : E →ₗ[F2] F) : X.ker →ₗ[F2] (F ⧸ X.range) :=
  X.range.mkQ.comp (Y.comp X.ker.subtype)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
@[simp] theorem compression_apply (X Y : E →ₗ[F2] F) (k : X.ker) :
    compression X Y k = X.range.mkQ (Y k) := rfl

/-- The genuine rank-additive compression fiber. In characteristic two,
`Y - X` and `Y + X` are equal. -/
def Fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :=
  {Y : E →ₗ[F2] F // finrank F2 Y.range =
      finrank F2 X.range + finrank F2 (Y - X).range ∧ compression X Y = Z}

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem fiber_condition_iff (X Y : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    (finrank F2 Y.range = finrank F2 X.range + finrank F2 (Y - X).range ∧
      compression X Y = Z) ↔
    (finrank F2 (toBlocks X P hP C hC Y).range = finrank F2 X.range +
      finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range ∧
      CompressionCount.compress (toBlocks X P hP C hC Y) =
        (X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) := by
  have hy := finrank_toBlocks X Y P hP C hC
  have hd := finrank_toBlocks X (Y - X) P hP C hC
  rw [map_sub, toBlocks_base] at hd
  change finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range =
    finrank F2 (Y - X).range at hd
  rw [hy, hd]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hz
    apply LinearMap.ext
    intro k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k)
    rw [compressed_toBlocks]
    exact congrArg (X.range.quotientEquivOfIsCompl C hC)
      (DFunLike.congr_fun hz k)
  · intro hz
    apply LinearMap.ext
    intro k
    apply (X.range.quotientEquivOfIsCompl C hC).injective
    have h := DFunLike.congr_fun hz k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k) at h
    rw [compressed_toBlocks] at h
    exact h

/-- Coordinate transport is a bijection on the complete rank-additive fibers. -/
def fiberEquiv (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    Fiber X Z ≃ CompressionCount.Fiber (U := X.range)
      ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) :=
  (toBlocks X P hP C hC).toEquiv.subtypeEquiv
    (fun Y => fiber_condition_iff X Y Z P hP C hC)

omit [FiniteDimensional F2 F] in
/-- Lemma A.2: every compressed rank-r map has exactly `2^(2*k*r)`
rank-additive lifts above an arbitrary rank-k map X. -/
theorem card_fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
    Nat.card (Fiber X Z) = 2 ^ (2 * finrank F2 X.range * finrank F2 Z.range) := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  rw [Nat.card_congr (fiberEquiv X Z P hP C hC), CompressionCount.card_fiber,
    finrank_comp_equiv]

omit [FiniteDimensional F2 F] in
/-- Every member of a compression fiber has rank `rank X + rank Z`. -/
theorem fiber_rank (X : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range)) (Y : Fiber X Z) :
    finrank F2 Y.val.range = finrank F2 X.range + finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  have h := CompressionCount.fiber_rank
    ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z)
    ((fiberEquiv X Z P hP C hC) Y)
  change finrank F2 (toBlocks X P hP C hC Y.val).range =
    finrank F2 X.range +
      finrank F2 ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z).range at h
  rw [finrank_toBlocks, finrank_comp_equiv] at h
  exact h

end

end UniqueGamesTheorem.Appendix.FullCompression

end

section

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/
namespace UniqueGamesTheorem.Appendix.DerivativeEnergy

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 F] in
theorem supported_fiber_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (s : Finset (E →ₗ[F2] F)) (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d) :
    (∑ Z, (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y ∈ s, a Y^2 := by
  classical
  apply FiberEnergy.finite_fiber_energy
  intro Z
  let t := s.filter (fun Y => FullCompression.compression X Y = Z)
  by_cases ht : t.Nonempty
  · obtain ⟨Y, hY⟩ := ht
    have hy := Finset.mem_filter.mp hY
    have hys := hs Y hy.1
    let yz : FullCompression.Fiber X Z := ⟨Y, hys.1, hy.2⟩
    have hr := FullCompression.fiber_rank X Z yz
    have hz : finrank F2 Z.range ≤ d - finrank F2 X.range := by
      change finrank F2 Y.range = finrank F2 X.range + finrank F2 Z.range at hr
      omega
    let emb : ↥t → FullCompression.Fiber X Z := fun y =>
      ⟨y.val, (hs y.val (Finset.mem_filter.mp y.property).1).1,
        (Finset.mem_filter.mp y.property).2⟩
    have hemb : Function.Injective emb := by
      intro y y' h
      have hv : y.val = y'.val :=
        congrArg (fun z : FullCompression.Fiber X Z => z.val) h
      exact Subtype.ext hv
    let : Finite (FullCompression.Fiber X Z) :=
      Finite.of_injective (fun z : FullCompression.Fiber X Z => z.val)
        (fun _ _ h => Subtype.ext h)
    have hc : t.card ≤ Nat.card (FullCompression.Fiber X Z) := by
      have h := Nat.card_le_card_of_injective emb hemb
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
    rw [FullCompression.card_fiber X Z] at hc
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (Nat.mul_le_mul_left (2 * finrank F2 X.range) hz)
    have hnat : t.card ≤ 2^(2 * finrank F2 X.range * (d - finrank F2 X.range)) :=
      hc.trans hpow
    exact_mod_cast hnat
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

omit [FiniteDimensional F2 F] in
/-- The precise merged-coefficient form of (A.10). Coefficients are arbitrary
real numbers with the stated degree support, not assumed nonnegative. -/
theorem coefficient_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hdegree : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
      then a Y else 0)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
  classical
  let s := Finset.univ.filter (fun Y : E →ₗ[F2] F =>
    RankBelow X Y ∧ finrank F2 Y.range ≤ d)
  have hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d := by
    intro Y hY
    exact (Finset.mem_filter.mp hY).2
  have hsum (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
      (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y) =
        ∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z then a Y else 0 := by
    simp only [s, Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  have henergy : (∑ Y ∈ s, a Y^2) =
      ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  simpa only [hsum, henergy] using supported_fiber_energy X s a d hs

end UniqueGamesTheorem.Appendix.DerivativeEnergy

end

section

namespace UniqueGamesTheorem.Appendix.TotalPredecessorCount
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

noncomputable def predecessorEnd (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) : Y.range →ₗ[F2] Y.range :=
  let R' : E →ₗ[F2] Y.range := R.val.codRestrict Y.range
    (fun x => range_le_of_rankBelow R.val Y R.property ⟨x,rfl⟩)
  let hker : Y.ker ≤ R'.ker := by
    intro x hx
    exact Subtype.ext (ker_le_of_rankBelow R.val Y R.property hx)
  (Y.ker.liftQ R' hker).comp Y.quotKerEquivRange.symm.toLinearMap

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_recovery (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) (x : E) :
    ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) = R.val x := by
  have hq : Y.quotKerEquivRange.symm (Y.rangeRestrict x) = Y.ker.mkQ x :=
    Y.quotKerEquivRange.symm_apply_apply (Y.ker.mkQ x)
  dsimp only [predecessorEnd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hq]
  rfl

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_injective (Y : E →ₗ[F2] F) :
    Function.Injective (predecessorEnd Y) := by
  intro R S h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  calc
    R.val x = ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) :=
      (predecessorEnd_recovery Y R x).symm
    _ = ((predecessorEnd Y S (Y.rangeRestrict x) : Y.range) : F) :=
      congrArg (fun P : Y.range →ₗ[F2] Y.range => (P (Y.rangeRestrict x) : F)) h
    _ = S.val x := predecessorEnd_recovery Y S x

omit [FiniteDimensional F2 F] in
theorem card_predecessors_le [Finite E] [Finite F] (Y : E →ₗ[F2] F) :
    Nat.card {R : E →ₗ[F2] F // RankBelow R Y} ≤
      2 ^ (finrank F2 Y.range ^ 2) := by
  classical
  let : Finite (Y.range →ₗ[F2] Y.range) :=
    Finite.of_injective (fun f : Y.range →ₗ[F2] Y.range => (f : Y.range → Y.range))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective (predecessorEnd Y)
    (predecessorEnd_injective Y)
  rw [CompressionCount.natCard_linearMap] at h
  simpa only [pow_two] using h
end UniqueGamesTheorem.Appendix.TotalPredecessorCount

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.UpperMobius
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

local instance quotientFinite (K : Submodule F2 W) : Finite (W ⧸ K) :=
  Finite.of_surjective K.mkQ K.mkQ_surjective

local instance dualFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Module.Dual F2 V) :=
  Finite.of_injective (fun f : Module.Dual F2 V => (f : V → F2)) DFunLike.coe_injective

local instance submoduleFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Submodule F2 V) :=
  Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

noncomputable def upperQuotientEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃ Submodule F2 (W ⧸ K) :=
  (Submodule.comapMkQRelIso K).symm.toEquiv

noncomputable def dualSubspaceEquiv (V : Type*) [AddCommGroup V]
    [Module F2 V] [FiniteDimensional F2 V] :
    Submodule F2 V ≃ Submodule F2 (Module.Dual F2 V) :=
  (Subspace.orderIsoFiniteDimensional (K := F2) (V := V)).toEquiv

omit [FiniteDimensional F2 W] [Finite W] in
theorem quotient_comap_codim (K : Submodule F2 W)
    (S : Submodule F2 (W ⧸ K)) :
    Module.finrank F2 (W ⧸ S.comap K.mkQ) =
      Module.finrank F2 ((W ⧸ K) ⧸ S) := by
  let π := S.mkQ.comp K.mkQ
  have hπ : Function.Surjective π := S.mkQ_surjective.comp K.mkQ_surjective
  have hker : π.ker = S.comap K.mkQ := by simp [π, LinearMap.ker_comp]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq.symm.trans
    (π.quotKerEquivOfSurjective hπ).finrank_eq

omit [FiniteDimensional F2 W] [Finite W] in
theorem upperQuotientEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) := by
  have hB : (upperQuotientEquiv K B).comap K.mkQ = B.val :=
    congrArg Subtype.val ((Submodule.comapMkQRelIso K).apply_symm_apply B)
  exact (Submodule.quotEquivOfEq _ _ hB).finrank_eq.symm.trans
    (quotient_comap_codim K (upperQuotientEquiv K B))

noncomputable def upperDualSubspaceEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃
      Submodule F2 (Module.Dual F2 (W ⧸ K)) :=
  (upperQuotientEquiv K).trans (dualSubspaceEquiv (W ⧸ K))

omit [Finite W] in
theorem upperDualSubspaceEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 (upperDualSubspaceEquiv K B) := by
  calc
    _ = Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) :=
      upperQuotientEquiv_codim K B
    _ = Module.finrank F2 (upperQuotientEquiv K B).dualAnnihilator :=
      (Subspace.quotEquivAnnihilator (upperQuotientEquiv K B)).finrank_eq
    _ = _ := rfl

noncomputable def upperWeightedTotal (K : Submodule F2 W) (w : ℕ → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  exact ∑ B : {B : Submodule F2 W // K ≤ B}, w (Module.finrank F2 (W ⧸ B.val))

theorem upperWeightedTotal_eq_dual (K : Submodule F2 W) (w : ℕ → ℤ) :
    upperWeightedTotal K w =
      SubspaceExtensions.weightedTotal
        (K := F2) (V := Module.Dual F2 (W ⧸ K)) w := by
  classical
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  let := SubspaceExtensions.subspaceFintype (K := F2) (V := Module.Dual F2 (W ⧸ K))
  unfold upperWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (upperDualSubspaceEquiv K)
    (fun B : {B : Submodule F2 W // K ≤ B} => w (Module.finrank F2 (W ⧸ B.val)))
    (fun S : Submodule F2 (Module.Dual F2 (W ⧸ K)) => w (Module.finrank F2 S))
    (fun B => congrArg w (upperDualSubspaceEquiv_codim K B))

omit [Finite W] in
theorem quotient_finrank_zero_iff (K : Submodule F2 W) :
    Module.finrank F2 (W ⧸ K) = 0 ↔ K = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := K.finrank_quotient_add_finrank
    omega
  · intro h
    subst K
    have hr := (⊤ : Submodule F2 W).finrank_quotient_add_finrank
    rw [finrank_top] at hr
    omega

theorem binary_upper_interval_mobius (K : Submodule F2 W) :
    upperWeightedTotal K (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if K = ⊤ then 1 else 0 := by
  classical
  rw [upperWeightedTotal_eq_dual]
  rw [SubspaceExtensions.binary_subspace_mobius]
  simp only [Subspace.dual_finrank_eq, quotient_finrank_zero_iff]
end UniqueGamesTheorem.Appendix.UpperMobius

end

end

end OAI
