import Mathlib
import OAI.Computability.DirectedFeedback.Games.UpperMobius

namespace OAI

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.OperatorPartitions
open DFVSGames.Appendix.LinearIdentities

namespace DFVSGames.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

theorem exponent_le (d i j t : ℕ) (hi : i ≤ t) (hj : j ≤ t) (ht : t ≤ d) :
    7 * d * (i + j) + 3 * i * j ≤ 24 * d * t := by
  have hs : i + j ≤ 2 * t := by omega
  have hp : i * j ≤ d * t :=
    (Nat.mul_le_mul hi hj).trans (Nat.mul_le_mul_right t ht)
  have hfirst := Nat.mul_le_mul_left (7 * d) hs
  have hsecond := Nat.mul_le_mul_left 3 hp
  have hdt : 0 ≤ d * t := Nat.zero_le _
  nlinarith

theorem weighted_moment_le (d i j t : ℕ) (e : ℝ)
    (hi : i ≤ t) (hj : j ≤ t) (he : 0 ≤ e) (hz : d < t → e = 0) :
    (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) * e ≤
      (2 : ℝ) ^ (24 * d * t) * e := by
  by_cases ht : t ≤ d
  · have hn := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (exponent_le d i j t hi hj ht)
    have hr : (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) ≤
        (2 : ℝ) ^ (24 * d * t) := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_right hr he
  · rw [hz (Nat.lt_of_not_ge ht)]
    simp

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

def tripleMoment (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 T, 𝔼 N, mapDerivative p.2.2 (hybridDerivative p.1 p.2.1 T f) N ^ 4

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleMoment_nonneg (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleMoment p f := by
  apply Finset.expect_nonneg
  intro T _
  apply Finset.expect_nonneg
  intro N _
  positivity

theorem weak_fourth_le_counted (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
        ∑ p : A4GeometricIndex A B, tripleMoment p.val f := by
  have hnat := Nat.pow_le_pow_left (A4IndexCount.card_index_le A B) 3
  rw [Nat.card_eq_fintype_card, ← pow_mul] at hnat
  have he : (Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * 3 =
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B) := by ring
  rw [he] at hnat
  have hc : (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) := by
    exact_mod_cast hnat
  have hn : 0 ≤ ∑ p : A4GeometricIndex A B, tripleMoment p.val f :=
    Finset.sum_nonneg fun p _ => tripleMoment_nonneg p.val f
  exact (OperatorNorm.a4_fourth_average_le A B f).trans
    (mul_le_mul_of_nonneg_right hc hn)

theorem weighted_weak_fourth_le_counted (d : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
      (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    ∑ p : A4GeometricIndex A B,
      (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
        3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f := by
  calc
    _ ≤ (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
        ((2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
          ∑ p : A4GeometricIndex A B, tripleMoment p.val f) :=
      mul_le_mul_of_nonneg_left (weak_fourth_le_counted A B f) (by positivity)
    _ = _ := by simp only [pow_add, Finset.mul_sum, mul_assoc]

theorem tripleMoment_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleMoment p f = 0 :=
  DerivativeDegree.map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    p.1 p.2.1 p.2.2 f hf h

def tripleTerm (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  (2 : ℝ) ^ (24 * d * A13Index.size p) * tripleMoment p f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleTerm_nonneg (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleTerm d p f :=
  mul_nonneg (by positivity) (tripleMoment_nonneg p f)

theorem tripleTerm_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleTerm d p f = 0 := by
  unfold tripleTerm
  rw [tripleMoment_eq_zero_of_lt_size p f hf h, mul_zero]

theorem weighted_geometric_moment_le {d : ℕ}
    (A : Submodule F2 E) (B : Submodule F2 F)
    (p : A4GeometricIndex A B) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f ≤
      tripleTerm d p.val f := by
  have hi : Module.finrank F2 A ≤ A13Index.size p.val := by
    have h := A13Index.dim_weakA p
    unfold A13Index.size MatrixRestrictions.order
    omega
  have hj : Module.finrank F2 (F ⧸ B) ≤ A13Index.size p.val := by
    have h := A13Index.codim_weakB p
    unfold A13Index.size MatrixRestrictions.order
    omega
  exact weighted_moment_le d _ _ _ _ hi hj (tripleMoment_nonneg p.val f)
    (fun h => tripleMoment_eq_zero_of_lt_size p.val f hf h)

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

def positiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.PositiveTriple (E := E) (F := F), tripleTerm d p.val f

def boundedPositiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d, tripleTerm d p.val f

theorem weakFourthSum_le_positiveTripleSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    A1Reduction.weakFourthSum d f ≤ positiveTripleSum d f := by
  classical
  have heq : A1Reduction.weakFourthSum d f =
      ∑ p : A13Index.WeakPositive (E := E) (F := F),
        (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.val.1 +
          Module.finrank F2 (F ⧸ p.val.2))) *
          (𝔼 M, spectralProjector
            (fun Y => p.val.1 ≤ Y.range ∧ Y.ker ≤ p.val.2) f M ^ 4) := by
    symm
    exact F1Gram.sum_subtype_eq
      (fun p : Submodule F2 E × Submodule F2 F => p ≠ (⊥, ⊤))
      (fun p => (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.1 +
        Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M ^ 4))
  rw [heq]
  calc
    _ ≤ ∑ p : A13Index.WeakPositive (E := E) (F := F),
        ∑ q : A4GeometricIndex p.val.1 p.val.2, tripleTerm d q.val f := by
      apply Finset.sum_le_sum
      intro p _
      exact (weighted_weak_fourth_le_counted d p.val.1 p.val.2 f).trans
        (Finset.sum_le_sum fun q _ => weighted_geometric_moment_le p.val.1 p.val.2 q f hf)
    _ = ∑ w : A13Index.PositiveWitness (E := E) (F := F),
        tripleTerm d w.2.val f := by
      simp only [Fintype.sum_sigma]
    _ ≤ positiveTripleSum d f :=
      F1Gram.sum_comp_le A13Index.positiveMap A13Index.positiveMap_injective
        (fun q : A13Index.PositiveTriple (E := E) (F := F) => tripleTerm d q.val f)
        (fun q => tripleTerm_nonneg d q.val f)

theorem positiveTripleSum_eq_bounded (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    positiveTripleSum d f = boundedPositiveTripleSum d f := by
  classical
  unfold positiveTripleSum boundedPositiveTripleSum
  rw [F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) => 0 < A13Index.size p)
      (fun p => tripleTerm d p f),
    F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) =>
        0 < A13Index.size p ∧ A13Index.size p ≤ d)
      (fun p => tripleTerm d p f)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < A13Index.size p
  · by_cases ht : A13Index.size p ≤ d
    · rw [ite_eq_left hp, ite_eq_left ⟨hp, ht⟩]
    · rw [ite_eq_left hp, ite_eq_right (fun h => ht h.2)]
      exact tripleTerm_eq_zero_of_lt_size p f hf (Nat.lt_of_not_ge ht)
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + positiveTripleSum d f := by
  have hbase := A1Reduction.degree_reduction f d (fun Y hY => hf Y hY)
  exact hbase.trans (add_le_add le_rfl (weakFourthSum_le_positiveTripleSum f d hf))

theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  simpa only [positiveTripleSum_eq_bounded f d hf] using degree_reduction f d hf

end DFVSGames.Appendix.A13Reduction
end

namespace DFVSGames.Appendix.DerivativeInduction

open DFVSGames.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

def IsAntecedent (Z : B →ₗ[F2] C) (X : (B × U) →ₗ[F2] (A × C)) : Prop :=
  (∀ b, (X (b, 0)).2 = Z b) ∧
  Disjoint X.range (LinearMap.inl F2 A C).range ∧
  (LinearMap.inl F2 B U).range ⊔ X.ker = ⊤

abbrev Antecedent (Z : B →ₗ[F2] C) :=
  { X : (B × U) →ₗ[F2] (A × C) // IsAntecedent Z X }

theorem antecedent_image_from_left (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    ∃ b : B, X p = X (b, 0) := by
  have hp : p ∈ (LinearMap.inl F2 B U).range ⊔ X.ker := by
    rw [hX.2.2]
    trivial
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hp
  obtain ⟨b, rfl⟩ := hq
  refine ⟨b, ?_⟩
  rw [← he, map_add]
  have hz : X r = 0 := hr
  simp only [hz, add_zero, LinearMap.inl_apply]

theorem antecedent_bottom_mem_range (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    (X p).2 ∈ Z.range := by
  obtain ⟨b, hb⟩ := antecedent_image_from_left Z X hX p
  exact ⟨b, (hX.1 b).symm.trans (congrArg Prod.snd hb).symm⟩

theorem antecedent_vertical_zero (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X)
    (p : B × U) (hp : (X p).2 = 0) : X p = 0 := by
  apply Submodule.disjoint_def.mp hX.2.1 (X p) (LinearMap.mem_range_self X p)
  exact ⟨(X p).1, Prod.ext rfl hp.symm⟩

private theorem antecedent_kernel_le_inline_DerivativeInduction (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) :
    Z.ker ≤ ((LinearMap.fst F2 A C).comp (X.comp (LinearMap.inl F2 B U))).ker := by
  intro b hb
  have hz : Z b = 0 := hb
  have hx := antecedent_vertical_zero Z X hX (b, 0) ((hX.1 b).trans hz)
  exact congrArg Prod.fst hx

noncomputable def graphParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : Z.range →ₗ[F2] A :=
  (Z.ker.liftQ ((LinearMap.fst F2 A C).comp
    (X.val.comp (LinearMap.inl F2 B U))) (antecedent_kernel_le_inline_DerivativeInduction Z X.val X.property)).comp
    Z.quotKerEquivRange.symm.toLinearMap

theorem graphParameter_apply (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (b : B) :
    graphParameter Z X (Z.rangeRestrict b) = (X.val (b, 0)).1 := by
  rw [show Z.rangeRestrict b = ⟨Z b, LinearMap.mem_range_self Z b⟩ from rfl]
  simp [graphParameter, LinearMap.quotKerEquivRange_symm_apply_image]

noncomputable def complementParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 A C).comp (X.val.comp (LinearMap.inr F2 B U))).codRestrict
    Z.range (fun u => antecedent_bottom_mem_range Z X.val X.property (0, u))

@[simp] theorem complementParameter_val (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (u : U) :
    (complementParameter Z X u : C) = (X.val (0, u)).2 := rfl

def lift (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    (B × U) →ₗ[F2] (A × C) :=
  (F.comp (Z.rangeRestrict.coprod H)).prod
    (Z.range.subtype.comp (Z.rangeRestrict.coprod H))

@[simp] theorem lift_apply (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) (p : B × U) :
    lift Z F H p = (F (Z.rangeRestrict p.1 + H p.2),
      ((Z.rangeRestrict p.1 + H p.2 : Z.range) : C)) := rfl

theorem lift_isAntecedent (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    IsAntecedent Z (lift Z F H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp
  · apply Submodule.disjoint_def.mpr
    intro v hv hw
    obtain ⟨p, rfl⟩ := hv
    obtain ⟨a, ha⟩ := hw
    have hz : Z.rangeRestrict p.1 + H p.2 = 0 := by
      apply Subtype.ext
      exact (congrArg Prod.snd ha).symm
    simp [hz]
  · apply top_unique
    intro p _
    obtain ⟨b, hb⟩ := Z.surjective_rangeRestrict (Z.rangeRestrict p.1 + H p.2)
    have he : lift Z F H p = lift Z F H (b, 0) := by
      simp [hb]
    apply Submodule.mem_sup.mpr
    refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
    · change lift Z F H (p - (b, 0)) = 0
      rw [map_sub, he, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

def intoAntecedent (Z : B →ₗ[F2] C)
    (p : (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range)) :
    Antecedent (U := U) (A := A) Z :=
  ⟨lift Z p.1 p.2, lift_isAntecedent Z p.1 p.2⟩

theorem graphParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    graphParameter Z (intoAntecedent Z (F, H)) = F := by
  ext c
  obtain ⟨b, rfl⟩ := Z.surjective_rangeRestrict c
  rw [graphParameter_apply]
  simp [intoAntecedent]

theorem complementParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    complementParameter Z (intoAntecedent Z (F, H)) = H := by
  ext u
  simp [intoAntecedent]

theorem lift_parameters (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) :
    lift Z (graphParameter Z X) (complementParameter Z X) = X.val := by
  apply LinearMap.ext
  intro p
  have hb : (Z.rangeRestrict p.1 + complementParameter Z X p.2 : C) = (X.val p).2 := by
    have hp : p = (p.1, 0) + (0, p.2) := by simp
    conv_rhs => rw [hp, map_add]
    simp [X.property.1]
  obtain ⟨b, he⟩ := antecedent_image_from_left Z X.val X.property p
  have hr : Z.rangeRestrict p.1 + complementParameter Z X p.2 = Z.rangeRestrict b := by
    apply Subtype.ext
    exact hb.trans ((congrArg Prod.snd he).trans (X.property.1 b))
  apply Prod.ext
  · change graphParameter Z X (Z.rangeRestrict p.1 + complementParameter Z X p.2) = _
    rw [hr, graphParameter_apply]
    exact (congrArg Prod.fst he).symm
  · exact hb

noncomputable def antecedentEquiv (Z : B →ₗ[F2] C) :
    Antecedent (U := U) (A := A) Z ≃
      (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range) where
  toFun X := (graphParameter Z X, complementParameter Z X)
  invFun := intoAntecedent Z
  left_inv X := Subtype.ext (lift_parameters Z X)
  right_inv p := Prod.ext (graphParameter_lift Z p.1 p.2)
    (complementParameter_lift Z p.1 p.2)

def graphEmbedding (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) :
    Z.range →ₗ[F2] (A × C) := F.prod Z.range.subtype

theorem graphEmbedding_injective (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) :
    Function.Injective (graphEmbedding Z F) := by
  intro c d h
  exact Subtype.ext (congrArg Prod.snd h)

theorem range_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    (lift Z F H).range = (graphEmbedding Z F).range := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Z.rangeRestrict p.1 + H p.2, rfl⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨b, hb⟩ := Z.surjective_rangeRestrict c
    refine ⟨(b, 0), ?_⟩
    simp [graphEmbedding, hb]

theorem finrank_range_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    Module.finrank F2 (lift Z F H).range = Module.finrank F2 Z.range := by
  rw [range_lift]
  exact LinearMap.finrank_range_of_inj (graphEmbedding_injective Z F)

theorem finrank_range_antecedent (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) :
    Module.finrank F2 X.val.range = Module.finrank F2 Z.range := by
  rw [← lift_parameters Z X]
  exact finrank_range_lift Z (graphParameter Z X) (complementParameter Z X)

theorem card_antecedent (Z : B →ₗ[F2] C)
    [Module.Finite F2 A] [Module.Finite F2 U] [Module.Finite F2 C] :
    Nat.card (Antecedent (U := U) (A := A) Z) =
      2 ^ (Module.finrank F2 Z.range *
        (Module.finrank F2 A + Module.finrank F2 U)) := by
  rw [Nat.card_congr (antecedentEquiv (U := U) (A := A) Z), Nat.card_prod,
    CompressionCount.natCard_linearMap, CompressionCount.natCard_linearMap, ← pow_add]
  congr 1
  ring

theorem isAntecedent_iff_pointwise (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) :
    IsAntecedent Z X ↔
      (∀ b, (X (b, 0)).2 = Z b) ∧
      (∀ p, (X p).2 = 0 → X p = 0) ∧
      (∀ p, ∃ b, X p = X (b, 0)) := by
  constructor
  · intro h
    exact ⟨h.1, antecedent_vertical_zero Z X h, antecedent_image_from_left Z X h⟩
  · rintro ⟨hc, hv, hs⟩
    refine ⟨hc, Submodule.disjoint_def.mpr ?_, top_unique ?_⟩
    · rintro v ⟨p, rfl⟩ ⟨a, ha⟩
      exact hv p (congrArg Prod.snd ha).symm
    · intro p _
      obtain ⟨b, hb⟩ := hs p
      apply Submodule.mem_sup.mpr
      refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
      · change X (p - (b, 0)) = 0
        rw [map_sub, hb, sub_self]
      · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

theorem disjoint_range_iff_zero (X : W →ₗ[F2] V) (Q : Submodule F2 V) :
    Disjoint X.range Q ↔ ∀ w, X w ∈ Q → X w = 0 := by
  constructor
  · intro h w hw
    exact Submodule.disjoint_def.mp h (X w) (LinearMap.mem_range_self X w) hw
  · intro h
    apply Submodule.disjoint_def.mpr
    rintro v ⟨w, rfl⟩ hw
    exact h w hw

theorem sup_kernel_iff_image (X : W →ₗ[F2] V) (P : Submodule F2 W) :
    P ⊔ X.ker = ⊤ ↔ ∀ w, ∃ p : P, X w = X p := by
  constructor
  · intro h w
    have hw : w ∈ P ⊔ X.ker := by rw [h]; trivial
    obtain ⟨p, hp, r, hr, he⟩ := Submodule.mem_sup.mp hw
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [← he, map_add]
    have hz : X r = 0 := hr
    simp [hz]
  · intro h
    apply top_unique
    intro w _
    obtain ⟨p, hp⟩ := h w
    apply Submodule.mem_sup.mpr
    refine ⟨p, p.property, w - p, ?_, ?_⟩
    · change X (w - p) = 0
      rw [map_sub, hp, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (p : W) w

def IsSubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) : Prop :=
  (∀ p : P, D.projectionOnto Q hQ.symm (X p) = Z p) ∧
  Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev SubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) :=
  { X : W →ₗ[F2] V // IsSubspaceAntecedent P Q D hQ Z X }

noncomputable def coordinateEquiv (P E : Submodule F2 W) (Q D : Submodule F2 V)
    (hP : IsCompl P E) (hQ : IsCompl Q D) :
    (W →ₗ[F2] V) ≃ₗ[F2] ((P × E) →ₗ[F2] (Q × D)) :=
  LinearEquiv.arrowCongr (P.prodEquivOfIsCompl E hP).symm
    (Q.prodEquivOfIsCompl D hQ).symm

@[simp] theorem coordinateEquiv_apply (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (X : W →ₗ[F2] V) (p : P × E) :
    coordinateEquiv P E Q D hP hQ X p =
      (Q.prodEquivOfIsCompl D hQ).symm (X ((p.1 : W) + p.2)) := rfl

theorem coordinate_antecedent_iff (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) :
    IsAntecedent Z (coordinateEquiv P E Q D hP hQ X) ↔
      IsSubspaceAntecedent P Q D hQ Z X := by
  rw [isAntecedent_iff_pointwise]
  unfold IsSubspaceAntecedent
  rw [disjoint_range_iff_zero, sup_kernel_iff_image]
  constructor
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro w hw
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      have hz : (coordinateEquiv P E Q D hP hQ X p).2 = 0 := by
        rw [coordinateEquiv_apply, hp]
        exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mpr hw
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) (hv p hz)
      simpa only [coordinateEquiv_apply, hp, LinearEquiv.apply_symm_apply, map_zero] using hh
    · intro w
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      obtain ⟨b, hb⟩ := hs p
      refine ⟨b, ?_⟩
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) hb
      simpa only [coordinateEquiv_apply, hp, Submodule.coe_zero, add_zero,
        LinearEquiv.apply_symm_apply] using hh
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro p hp
      have hm : X ((p.1 : W) + p.2) ∈ Q :=
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mp hp
      have hz := hv ((p.1 : W) + p.2) hm
      simp [hz]
    · intro p
      obtain ⟨b, hb⟩ := hs ((p.1 : W) + p.2)
      refine ⟨b, ?_⟩
      simpa only [coordinateEquiv_apply, Submodule.coe_zero, add_zero] using
        congrArg (Q.prodEquivOfIsCompl D hQ).symm hb

noncomputable def subspaceAntecedentEquiv (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) :
    SubspaceAntecedent P Q D hQ Z ≃
      (Z.range →ₗ[F2] Q) × (E →ₗ[F2] Z.range) :=
  (Equiv.subtypeEquiv (coordinateEquiv P E Q D hP hQ).toEquiv
    (fun X => (coordinate_antecedent_iff P E Q D hP hQ Z X).symm)).trans
    (antecedentEquiv Z)

theorem card_subspaceAntecedent (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) [Module.Finite F2 W] [Module.Finite F2 V] :
    Nat.card (SubspaceAntecedent P Q D hQ Z) =
      2 ^ (Module.finrank F2 Z.range *
        (Module.finrank F2 Q + Module.finrank F2 E)) := by
  rw [Nat.card_congr (subspaceAntecedentEquiv P E Q D hP hQ Z), Nat.card_prod,
    CompressionCount.natCard_linearMap, CompressionCount.natCard_linearMap, ← pow_add]
  congr 1
  ring

end DFVSGames.Appendix.DerivativeInduction

namespace DFVSGames.Appendix.AntecedentCount

open DFVSGames.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

def IsAntecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) : Prop :=
  compress X Q P = Y ∧ Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev Antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :=
  {X : W →ₗ[F2] V // IsAntecedent P Q Y X}

abbrev Admissible (P : Submodule F2 W) (Q : Submodule F2 V) :=
  {X : W →ₗ[F2] V // Disjoint X.range Q ∧ P ⊔ X.ker = ⊤}

def compressionEquiv (P : Submodule F2 W) (Q : Submodule F2 V) :
    Admissible P Q ≃ Σ Y : P →ₗ[F2] (V ⧸ Q), Antecedent P Q Y where
  toFun X := ⟨compress X.val Q P, ⟨X.val, rfl, X.property⟩⟩
  invFun X := ⟨X.2.val, X.2.property.2⟩
  left_inv X := rfl
  right_inv X := by
    rcases X with ⟨Y, ⟨X, hXY, hd, hk⟩⟩
    cases hXY
    rfl

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

def subspaceEquiv (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Y : P →ₗ[F2] (V ⧸ Q)) :
    Antecedent P Q Y ≃ DerivativeInduction.SubspaceAntecedent P Q D hQ
      ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) where
  toFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mp X.property⟩
  invFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mpr X.property⟩
  left_inv _X := rfl
  right_inv _X := rfl

variable [FiniteDimensional F2 W] [FiniteDimensional F2 V]

omit [FiniteDimensional F2 V] in
theorem rank_eq (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : Antecedent P Q Y) :
    Module.finrank F2 X.val.range = Module.finrank F2 Y.range := by
  have h := compress_rank_preserved X.val Q P X.property.2.1.symm X.property.2.2
  rw [X.property.1] at h
  exact h.symm

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

end DFVSGames.Appendix.AntecedentCount

namespace DFVSGames.Appendix.A5ReverseIndex

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

abbrev EarlierA (A' : Submodule F2 V) (i : ℕ) :=
  {A : Submodule F2 V // A ≤ A' ∧ Module.finrank F2 A = i}

abbrev EarlierB (B' : Submodule F2 W) (j : ℕ) :=
  {B : Submodule F2 W // B' ≤ B ∧ Module.finrank F2 (W ⧸ B) = j}

def frequencyEquiv (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) :
    (B' →ₗ[F2] (V ⧸ A')) ≃ₗ[F2]
      ((B'.comap B.subtype) →ₗ[F2] ((V ⧸ A) ⧸ A'.map A.mkQ)) :=
  LinearEquiv.arrowCongr
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm

def relativeFrequency (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) (Y : B' →ₗ[F2] (V ⧸ A')) :=
  frequencyEquiv A A' B' B hA hB Y

theorem relativeFrequency_rank (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) :
    Module.finrank F2 (relativeFrequency A A' B' B hA hB Y).range =
      Module.finrank F2 Y.range :=
  CoordinateTransport.finrank_range_transport
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm Y

abbrev Ancestor (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (i j : ℕ) :=
  Σ A : EarlierA A' i, Σ B : EarlierB B' j,
    AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
      (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem relative_codomain_dimension (A A' : Submodule F2 V) (hA : A ≤ A') :
    Module.finrank F2 (A'.map A.mkQ) + Module.finrank F2 A =
      Module.finrank F2 A' := by
  have h₁ := (A'.map A.mkQ).finrank_quotient_add_finrank
  have h₂ := A.finrank_quotient_add_finrank
  have h₃ := A'.finrank_quotient_add_finrank
  have h₄ := (Submodule.quotientQuotientEquivQuotient A A' hA).finrank_eq
  omega

theorem relative_domain_codimension_le (B' B : Submodule F2 W) (hB : B' ≤ B) :
    Module.finrank F2 (B ⧸ B'.comap B.subtype) ≤
      Module.finrank F2 (W ⧸ B') := by
  have h₁ := (B'.comap B.subtype).finrank_quotient_add_finrank
  have h₂ := B'.finrank_quotient_add_finrank
  have h₃ := B.finrank_le
  have h₄ := (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).finrank_eq
  change Module.finrank F2 B' = Module.finrank F2 (B'.comap B.subtype) at h₄
  omega

theorem card_local_antecedent_le (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hAd : Module.finrank F2 A' ≤ d)
    (hBd : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (AntecedentCount.Antecedent
      (B'.comap B.subtype) (A'.map A.mkQ)
      (relativeFrequency A A' B' B hA hB Y)) ≤ 2 ^ (2 * d * k) := by
  apply AntecedentCount.card_antecedent_le
  · simpa only [relativeFrequency_rank] using hY
  · have h := relative_codomain_dimension A A' hA
    omega
  · exact (relative_domain_codimension_le B' B hB).trans hBd

local instance quotientFinite {U : Type*} [AddCommGroup U] [Module F2 U]
    [Finite U] (P : Submodule F2 U) : Finite (U ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance linearMapFinite {U Z : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup Z] [Module F2 Z] [Finite U] [Finite Z] :
    Finite (U →ₗ[F2] Z) :=
  Finite.of_injective (fun f : U →ₗ[F2] Z => (f : U → Z)) DFunLike.coe_injective

private theorem card_sigma_le_inline_A5ReverseIndex {I : Type*} [Fintype I]
    (fiber : I → Type*) [∀ i, Finite (fiber i)] (N : ℕ)
    (h : ∀ i, Nat.card (fiber i) ≤ N) :
    Nat.card (Σ i, fiber i) ≤ Nat.card I * N := by
  rw [Nat.card_sigma]
  calc
    (∑ i, Nat.card (fiber i)) ≤ ∑ _i : I, N := Finset.sum_le_sum (fun i _ => h i)
    _ = Nat.card I * N := by simp [Nat.card_eq_fintype_card]

variable [Finite V] [Finite W]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

theorem card_ancestor_le (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (d * (i + j) + 2 * d * k) := by
  have hlocal (A : EarlierA A' i) (B : EarlierB B' j) :=
    card_local_antecedent_le A.val A' B' B.val A.property.1 B.property.1
      Y d k hY hA hB
  have hinner (A : EarlierA A' i) :
      Nat.card (Σ B : EarlierB B' j,
        AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
          (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)) ≤
        Nat.card (EarlierB B' j) * 2 ^ (2 * d * k) :=
    card_sigma_le_inline_A5ReverseIndex _ _ (hlocal A)
  have htotal : Nat.card (Ancestor A' B' Y i j) ≤
      Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) :=
    card_sigma_le_inline_A5ReverseIndex _ _ hinner
  calc
    Nat.card (Ancestor A' B' Y i j) ≤
        Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) := htotal
    _ ≤ 2 ^ (d * i) * (2 ^ (d * j) * 2 ^ (2 * d * k)) :=
      Nat.mul_le_mul (BadConvolution.card_lower_rank_le A' d i hA)
        (Nat.mul_le_mul_right _ (BadConvolution.card_upper_codim_le B' d j hB))
    _ = 2 ^ (d * (i + j) + 2 * d * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem card_ancestor_le_source (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) (ht : i + j + k ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (3 * (d * (i + j + k))) := by
  apply (card_ancestor_le A' B' Y d i j k hY hA hB).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Induction.antecedent_exponent_budget d i j k (i + j + k) rfl ht
  calc
    d * (i + j) + 2 * d * k ≤ d * (i + j) + 2 * d * k + k * k :=
      Nat.le_add_right _ _
    _ ≤ 3 * (d * (i + j + k)) := by simpa only [Nat.mul_assoc] using h

end

end DFVSGames.Appendix.A5ReverseIndex

end OAI
