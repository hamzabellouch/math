import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.DerivativeInduction

open UniqueGamesTheorem.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

/-- The actual complement conditions after choosing domain/codomain splittings. -/
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

private theorem antecedent_kernel_le (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) :
    Z.ker ≤ ((LinearMap.fst F2 A C).comp (X.comp (LinearMap.inl F2 B U))).ker := by
  intro b hb
  have hz : Z b = 0 := hb
  have hx := antecedent_vertical_zero Z X hX (b, 0) ((hX.1 b).trans hz)
  exact congrArg Prod.fst hx

/-- The graph map from the fixed compressed image into the removed summand. -/
noncomputable def graphParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : Z.range →ₗ[F2] A :=
  (Z.ker.liftQ ((LinearMap.fst F2 A C).comp
    (X.val.comp (LinearMap.inl F2 B U))) (antecedent_kernel_le Z X.val X.property)).comp
    Z.quotKerEquivRange.symm.toLinearMap

theorem graphParameter_apply (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (b : B) :
    graphParameter Z X (Z.rangeRestrict b) = (X.val (b, 0)).1 := by
  rw [show Z.rangeRestrict b = ⟨Z b, LinearMap.mem_range_self Z b⟩ from rfl]
  simp [graphParameter, LinearMap.quotKerEquivRange_symm_apply_image]

/-- Values on the omitted domain complement, compressed into `range Z`. -/
noncomputable def complementParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 A C).comp (X.val.comp (LinearMap.inr F2 B U))).codRestrict
    Z.range (fun u => antecedent_bottom_mem_range Z X.val X.property (0, u))

@[simp] theorem complementParameter_val (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (u : U) :
    (complementParameter Z X u : C) = (X.val (0, u)).2 := rfl

/-- The block matrix `[F Z, F H; Z, H]`. -/
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

/-- Exact antecedent bijection; neither direction assumes the desired count. -/
noncomputable def antecedentEquiv (Z : B →ₗ[F2] C) :
    Antecedent (U := U) (A := A) Z ≃
      (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range) where
  toFun X := (graphParameter Z X, complementParameter Z X)
  invFun := intoAntecedent Z
  left_inv X := Subtype.ext (lift_parameters Z X)
  right_inv p := Prod.ext (graphParameter_lift Z p.1 p.2)
    (complementParameter_lift Z p.1 p.2)

/-- The graph of the reconstruction parameter as an injective linear map. -/
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

/-- The reconstructed map has exactly the rank of the fixed compression. -/
theorem finrank_range_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    Module.finrank F2 (lift Z F H).range = Module.finrank F2 Z.range := by
  rw [range_lift]
  exact LinearMap.finrank_range_of_inj (graphEmbedding_injective Z F)

/-- The map rank is preserved for every antecedent, without a rank hypothesis. -/
theorem finrank_range_antecedent (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) :
    Module.finrank F2 X.val.range = Module.finrank F2 Z.range := by
  rw [← lift_parameters Z X]
  exact finrank_range_lift Z (graphParameter Z X) (complementParameter Z X)

/-- The sharp cardinality of the antecedents after the outer subspaces are fixed. -/
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

section Subspaces

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

/-- Antecedents on arbitrary subspaces. Projection onto the chosen complement
is the quotient compression expressed through `quotientEquivOfIsCompl`. -/
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

/-- Transport the canonical antecedent count to arbitrary complementary subspaces. -/
noncomputable def subspaceAntecedentEquiv (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) :
    SubspaceAntecedent P Q D hQ Z ≃
      (Z.range →ₗ[F2] Q) × (E →ₗ[F2] Z.range) :=
  (Equiv.subtypeEquiv (coordinateEquiv P E Q D hP hQ).toEquiv
    (fun X => (coordinate_antecedent_iff P E Q D hP hQ Z X).symm)).trans
    (antecedentEquiv Z)

/-- Exact antecedent cardinality in arbitrary complementary subspaces. -/
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

end Subspaces

end UniqueGamesTheorem.Appendix.DerivativeInduction

end

end OAI
