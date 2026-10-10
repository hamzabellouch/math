import OAI.NumberTheory.DirichletL.ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain

namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

abbrev UnitInvariant (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : Prop :=
  ∀ u : Aˣ, χ (Ideal.Quotient.mk M u) = 1

theorem residue_eq_of_associated (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {a b : A} (hab : Associated a b) :
    χ (Ideal.Quotient.mk M a) = χ (Ideal.Quotient.mk M b) := by
  obtain ⟨u, rfl⟩ := hab
  rw [map_mul, map_mul, hχ u, mul_one]

theorem isUnit_mk_iff_isCoprime (M : Ideal A) (a : A) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span ({a} : Set A)) M := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton_sup]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hba : b * a - 1 ∈ M :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp (by simpa only [map_mul] using hb)
    refine ⟨b, -(b * a - 1), M.neg_mem hba, ?_⟩
    ring
  · rintro ⟨b, c, hc, hbc⟩
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have h := congrArg (Ideal.Quotient.mk M) hbc
    simpa only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc,
      add_zero, map_one] using h

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

def value (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (I : Ideal A) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.Quotient.mk M (generator I))

omit [IsDomain A] in
theorem value_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : value M χ ⊥ = 0 := by
  simp only [value, ite_true]

theorem value_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    value M χ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) := by
  have hI : Ideal.span ({a} : Set A) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [value, hI, ite_false]
  exact residue_eq_of_associated M χ hχ (associated_generator_span_self a)

def ofResidue (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    Ideal A →*₀ ℂ where
  toFun := value M χ
  map_zero' := value_bot M χ
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, map_one] using
      value_span M χ hχ (one_ne_zero : (1 : A) ≠ 0)
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst I
      simp only [Ideal.bot_mul, value_bot, zero_mul]
    by_cases hJ : J = ⊥
    · subst J
      simp only [Ideal.mul_bot, value_bot, mul_zero]
    let a := generator I
    let b := generator J
    have ha : a ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have hb : b ≠ 0 := fun h => hJ ((eq_bot_iff_generator_eq_zero J).mpr h)
    have hIa : Ideal.span ({a} : Set A) = I := Ideal.span_singleton_generator I
    have hJb : Ideal.span ({b} : Set A) = J := Ideal.span_singleton_generator J
    calc
      value M χ (I * J) = value M χ (Ideal.span ({a * b} : Set A)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, hIa, hJb]
      _ = χ (Ideal.Quotient.mk M (a * b)) := value_span M χ hχ (mul_ne_zero ha hb)
      _ = χ (Ideal.Quotient.mk M a) * χ (Ideal.Quotient.mk M b) := by
        rw [map_mul, map_mul]
      _ = value M χ I * value M χ J := by
        rw [← hIa, ← hJb, value_span M χ hχ ha, value_span M χ hχ hb]

@[simp] theorem ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ

theorem ofResidue_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    ofResidue M χ hχ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) :=
  value_span M χ hχ ha

theorem ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    simpa only [h, Ideal.span_singleton_zero] using ha.symm
  rw [← ha, ofResidue_span M χ hχ ha0]

omit [IsDomain A] [IsPrincipalIdealRing A] in
theorem norm_residue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (a : A ⧸ M) : ‖χ a‖ ≤ 1 := by
  let : Fintype (A ⧸ M)ˣ := Fintype.ofFinite _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn : ‖χ (u : A ⧸ M)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using h
    exact hn.le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem norm_ofResidue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _

omit [IsDomain A] [IsPrincipalIdealRing A] in

theorem one_unitInvariant (M : Ideal A) : UnitInvariant M (1 : MulChar (A ⧸ M) ℂ) := by
  intro u
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk M))

theorem ofResidue_one (M : Ideal A) (I : Ideal A) :
    ofResidue M 1 (one_unitInvariant M) I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have heq := ofResidue_span M 1 (one_unitInvariant M) hg
    rw [Ideal.span_singleton_generator] at heq
    rw [heq]
    simp only [hI, ite_false]
    have hu : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      exact MulChar.one_apply (hu.mpr hc)
    · simp only [hc, ite_false]
      exact MulChar.map_nonunit _ (fun h => hc (hu.mp h))

theorem ofResidue_one_top (I : Ideal A) :
    ofResidue (⊤ : Ideal A) 1 (one_unitInvariant ⊤) I = if I = ⊥ then 0 else 1 := by
  rw [ofResidue_one]
  have h : IsCoprime I (⊤ : Ideal A) := Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq I)
  simp only [h, ite_true]

theorem ofResidue_source_mask (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I = if IsCoprime I M then ofResidue K φ hφ I else 0 := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_self]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have h := hmask (generator I)
    have hcop : IsUnit (Ideal.Quotient.mk M (generator I)) ↔ IsCoprime I M := by
      simpa only [Ideal.span_singleton_generator] using isUnit_mk_iff_isCoprime M (generator I)
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span K φ hφ hg,
      Ideal.span_singleton_generator] at h
    simpa only [hcop] using h

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

theorem ofResidue_product (M N : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) (I : Ideal A) :
    ofResidue (M ⊓ N) (ResidueCharacter.product M N χ ψ)
        (ResidueCharacter.product_global_units M N χ ψ hχ hψ) I =
      ofResidue M χ hχ I * ofResidue N ψ hψ I := by
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, mul_zero]
  · have hg : generator I ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    conv_lhs => rw [← Ideal.span_singleton_generator I]
    rw [ofResidue_span _ _ _ hg, ResidueCharacter.product_mk]
    rw [← ofResidue_span M χ hχ hg, ← ofResidue_span N ψ hψ hg,
      Ideal.span_singleton_generator]

section Primitive

variable [Infinite A]

theorem exists_primitive_associate (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : A)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

theorem exists_primitive_product_associate (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ M.absNorm * N.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (A ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

end OAI
