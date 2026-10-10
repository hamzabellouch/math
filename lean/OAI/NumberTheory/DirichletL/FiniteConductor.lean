import OAI.NumberTheory.DirichletL.FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps

namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

theorem exists_character_factor_iff {G H : Type*} [Group G] [CommGroup H]
    [Finite H] (q : G →* H) (χ : G →* ℂˣ) :
    (∃ φ : H →* ℂˣ, φ.comp q = χ) ↔ q.ker ≤ χ.ker := by
  constructor
  · rintro ⟨φ, rfl⟩ g hg
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hg, map_one]
  · intro hker
    have hker' : q.rangeRestrict.ker ≤ χ.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using hker
    let θ : q.range →* ℂˣ :=
      MonoidHom.liftOfSurjective q.rangeRestrict q.rangeRestrict_surjective ⟨χ, hker'⟩
    have hθ : θ.comp q.rangeRestrict = χ := MonoidHom.liftOfRightInverse_comp ..
    obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective ℂ q.range θ
    refine ⟨φ, ?_⟩
    calc
      φ.comp q = (φ.domRestrict q.range).comp q.rangeRestrict := rfl
      _ = θ.comp q.rangeRestrict := by rw [← hφ]; rfl
      _ = χ := hθ

variable {R : Type*} [CommRing R] [Finite R]

def quotientUnits (I : Ideal R) : Rˣ →* (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

def FactorsThroughIdeal (χ : MulChar R ℂ) (I : Ideal R) : Prop :=
  ∃ φ : MulChar (R ⧸ I) ℂ,
    φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom

omit [Finite R] in
theorem quotientUnits_eq_one_iff (I : Ideal R) (u : Rˣ) :
    quotientUnits I u = 1 ↔ (u : R) - 1 ∈ I := by
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

theorem factorsThroughIdeal_iff (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hfactor : FactorsThroughIdeal χ I ↔
      ∃ φ : (R ⧸ I)ˣ →* ℂˣ, φ.comp (quotientUnits I) = χ.toUnitHom := by
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.toUnitHom, hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨MulChar.ofUnitHom φ, ?_⟩
      simpa only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply] using hφ
  rw [hfactor, exists_character_factor_iff]
  constructor
  · intro h u hu
    have hunit := h ((quotientUnits_eq_one_iff I u).mpr hu)
    exact congrArg Units.val hunit
  · intro h u hu
    apply Units.ext
    exact h u ((quotientUnits_eq_one_iff I u).mp hu)

theorem primitiveOnIdeals_iff_no_descent (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  simp only [IsPrimitiveOnIdeals, factorsThroughIdeal_iff]
  push Not
  rfl

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

theorem FactorsThroughIdeal.inv {χ : MulChar R ℂ} {I : Ideal R}
    (h : FactorsThroughIdeal χ I) : FactorsThroughIdeal χ⁻¹ I := by
  rw [factorsThroughIdeal_iff] at h ⊢
  intro u hu
  rw [← MulChar.star_apply', h u hu, star_one]

omit [Finite R] in

theorem factorization_with_source_mask (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom) (a : R) :
    χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp only [u.isUnit, ite_true]
    exact (congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ).symm
  · simp only [ha, ite_false, MulChar.map_nonunit _ ha]

theorem exists_primitive_quotient (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  classical
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  have hbot : FactorsThroughIdeal χ ⊥ := by
    rw [factorsThroughIdeal_iff]
    intro u hu
    have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
    rw [hu1, map_one]
  obtain ⟨I, hI⟩ := (Set.toFinite {I : Ideal R | FactorsThroughIdeal χ I}).exists_maximal
    ⟨⊥, hbot⟩
  obtain ⟨φ, hφ⟩ := hI.1
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  refine ⟨I, φ, hφ, ?_, hI⟩
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)

theorem exists_primitive_quotient_with_mask (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient χ
  exact ⟨I, φ, hprimitive, hmaximal, factorization_with_source_mask χ I φ hφ⟩

end

end SevenEighths.FiniteConductor

end OAI
