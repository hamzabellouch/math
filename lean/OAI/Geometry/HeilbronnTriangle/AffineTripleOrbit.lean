import Mathlib

namespace OAI


namespace Problem355.AffineTripleOrbit
open Affine

variable {F V P ι : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_linearEquiv_map [Finite ι] {u v : ι → V}
    (hu : LinearIndependent F u) (hv : LinearIndependent F v) :
    ∃ g : V ≃ₗ[F] V, ∀ i, g (u i) = v i := by
  classical
  let f := hu.linearCombinationEquiv.symm.trans hv.linearCombinationEquiv
  let : FiniteDimensional F (Submodule.span F (Set.range u)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range u)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun i => ?_⟩
  have hi := hg (hu.linearCombinationEquiv (Finsupp.single i 1))
  simpa [f] using hi.symm

instance linearTupleMulAction :
    MulAction (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
  smul g u := ⟨g ∘ u.1, u.2.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem linearTuple_smul_apply
    (g : V ≃ₗ[F] V) (u : {u : ι → V // LinearIndependent F u}) (i : ι) :
    (g • u).1 i = g (u.1 i) := rfl

instance linearTuplePretransitive [Finite ι] :
    MulAction.IsPretransitive (V ≃ₗ[F] V) {u : ι → V // LinearIndependent F u} where
  exists_smul_eq u v := by
    obtain ⟨g, hg⟩ := exists_linearEquiv_map u.2 v.2
    exact ⟨g, Subtype.ext (funext hg)⟩

theorem exists_affineEquiv_map [Finite ι] [AffineSpace V P]
    {p q : ι → P} (hp : AffineIndependent F p) (hq : AffineIndependent F q)
    (i0 : ι) : ∃ g : P ≃ᵃ[F] P, ∀ i, g (p i) = q i := by
  classical
  have hp' := (affineIndependent_iff_linearIndependent_vsub F p i0).mp hp
  have hq' := (affineIndependent_iff_linearIndependent_vsub F q i0).mp hq
  obtain ⟨g, hg⟩ := exists_linearEquiv_map hp' hq'
  refine ⟨AffineEquiv.ofLinearEquiv g (p i0) (q i0), ?_⟩
  intro i
  by_cases hi : i = i0
  · subst i
    simp [AffineEquiv.ofLinearEquiv_apply]
  · rw [AffineEquiv.ofLinearEquiv_apply, hg ⟨i, hi⟩]
    exact vsub_vadd (q i) (q i0)

theorem exists_affineEquiv_map_triple [AffineSpace V P]
    {p q : Fin 3 → P} (hp : AffineIndependent F p) (hq : AffineIndependent F q) :
    ∃ g : P ≃ᵃ[F] P, ∀ i, g (p i) = q i :=
  exists_affineEquiv_map hp hq 0

instance affineTupleMulAction [AffineSpace V P] :
    MulAction (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
  smul g p := ⟨g ∘ p.1, g.affineIndependent_iff.mpr p.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem affineTuple_smul_apply [AffineSpace V P]
    (g : P ≃ᵃ[F] P) (p : {p : ι → P // AffineIndependent F p}) (i : ι) :
    (g • p).1 i = g (p.1 i) := rfl

instance affineTuplePretransitive [Finite ι] [Nonempty ι] [AffineSpace V P] :
    MulAction.IsPretransitive (P ≃ᵃ[F] P) {p : ι → P // AffineIndependent F p} where
  exists_smul_eq p q := by
    classical
    obtain ⟨g, hg⟩ := exists_affineEquiv_map p.2 q.2 (Classical.arbitrary ι)
    exact ⟨g, Subtype.ext (funext hg)⟩

theorem affineIndependent_iff_succ_vsub {n : ℕ} (p : Fin (n + 1) → V) :
    AffineIndependent F p ↔
      LinearIndependent F (fun i : Fin n => p i.succ - p 0) := by
  rw [affineIndependent_iff_linearIndependent_vsub F p 0]
  simpa [Function.comp_def, finSuccAboveEquiv_apply] using
    (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (n + 1)))
      (f := fun i : {i : Fin (n + 1) // i ≠ 0} => p i - p 0)).symm

noncomputable def affineIndependentEquiv (n : ℕ) :
    {p : Fin (n + 1) → V // AffineIndependent F p} ≃
      V × {u : Fin n → V // LinearIndependent F u} where
  toFun p := (p.1 0, ⟨fun i => p.1 i.succ - p.1 0,
    (affineIndependent_iff_succ_vsub p.1).mp p.2⟩)
  invFun u := ⟨Fin.cons u.1 (fun i => u.2.1 i + u.1), by
    rw [affineIndependent_iff_succ_vsub]
    simpa using u.2.2⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv u := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext i
      simp

theorem card_affineIndependent_triple [Fintype F] :
    Nat.card {p : Fin 3 → (Fin 3 → F) // AffineIndependent F p} =
      Fintype.card F ^ 3 * (Fintype.card F ^ 3 - 1) *
        (Fintype.card F ^ 3 - Fintype.card F) := by
  rw [Nat.card_congr (affineIndependentEquiv (F := F) (V := Fin 3 → F) 2),
    Nat.card_prod, card_linearIndependent (by simp)]
  simp [Nat.card_eq_fintype_card, Fin.prod_univ_succ, mul_assoc]

noncomputable def inputShiftEquiv :
    (V ≃ᵃ[F] V) ≃ (V ≃ₗ[F] V) × V where
  toFun e := (e.linear, e.linear.symm (e 0))
  invFun u := AffineEquiv.ofLinearEquiv u.1 0 (u.1 u.2)
  left_inv e := by
    apply AffineEquiv.ext
    intro x
    simp only [AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub, sub_zero,
      vadd_eq_add, LinearEquiv.apply_symm_apply]
    simpa using (e.map_vadd 0 x).symm
  right_inv u := by
    apply Prod.ext
    · rfl
    · simp [AffineEquiv.ofLinearEquiv_apply]

@[simp] theorem inputShiftEquiv_symm_apply (g : V ≃ₗ[F] V) (a x : V) :
    (inputShiftEquiv.symm (g, a)) x = g (a + x) := by
  simp [inputShiftEquiv, AffineEquiv.ofLinearEquiv_apply, map_add, add_comm]

noncomputable def restrictedInputShiftEquiv (A : Set V) :
    {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} ≃ (V ≃ₗ[F] V) × A where
  toFun e := ((inputShiftEquiv e.1).1, ⟨(inputShiftEquiv e.1).2, e.2⟩)
  invFun u := ⟨inputShiftEquiv.symm (u.1, u.2.1), by simp⟩
  left_inv e := by
    apply Subtype.ext
    exact inputShiftEquiv.symm_apply_apply e.1
  right_inv u := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [inputShiftEquiv, AffineEquiv.ofLinearEquiv_apply]

theorem card_restrictedInputShift (A : Set V) :
    Nat.card {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} =
      Nat.card (V ≃ₗ[F] V) * Nat.card A := by
  rw [Nat.card_congr (restrictedInputShiftEquiv A), Nat.card_prod]

theorem card_affineEquiv :
    Nat.card (V ≃ᵃ[F] V) = Nat.card (V ≃ₗ[F] V) * Nat.card V := by
  rw [Nat.card_congr (inputShiftEquiv (F := F) (V := V)), Nat.card_prod]

theorem card_affineEquiv_le_two_restricted (A : Set V)
    (hA : Nat.card V ≤ 2 * Nat.card A) :
    Nat.card (V ≃ᵃ[F] V) ≤
      2 * Nat.card {e : V ≃ᵃ[F] V // (inputShiftEquiv e).2 ∈ A} := by
  rw [card_affineEquiv, card_restrictedInputShift]
  simpa [mul_assoc, mul_left_comm] using Nat.mul_le_mul_left (Nat.card (V ≃ₗ[F] V)) hA

end Problem355.AffineTripleOrbit

end OAI
