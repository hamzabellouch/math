import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Data.Nat.Init
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Submodule

namespace OAI

noncomputable section

universe w v u

namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian

section ExactDimensionShifting
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_shortExact
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    (hmid : Subsingleton (Ext X S.X₂ n))
    (hleft : Subsingleton (Ext X S.X₁ (n + 1))) :
    Subsingleton (Ext X S.X₃ n) := by
  let := hmid
  let := hleft
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ X hS e rfl
    (Subsingleton.elim _ 0)
  rw [Subsingleton.elim a 0, Ext.zero_comp] at ha
  exact ha.symm

theorem ext_zero_of_finite_exact_resolution
    (X : C) (K F : ℕ → C) (r : ℕ)
    (i : ∀ n, K (n + 1) ⟶ F n) (p : ∀ n, F n ⟶ K n)
    (hzero : ∀ n, i n ≫ p n = 0)
    (hexact : ∀ n < r, (ShortComplex.mk (i n) (p n) (hzero n)).ShortExact)
    (hmid : ∀ n < r, Subsingleton (Ext X (F n) n))
    (hend : Subsingleton (Ext X (K r) r)) :
    Subsingleton (Ext X (K 0) 0) := by
  exact Nat.decreasingInduction
    (motive := fun n _ => Subsingleton (Ext X (K n) n))
    (fun n hn ih => ext_subsingleton_of_shortExact X
      (ShortComplex.mk (i n) (p n) (hzero n)) (hexact n hn) n (hmid n hn) ih)
    hend (Nat.zero_le r)

theorem nonzero_ext_forces_resolution_obstruction
    (X : C) (K F : ℕ → C) (r : ℕ)
    (i : ∀ n, K (n + 1) ⟶ F n) (p : ∀ n, F n ⟶ K n)
    (hzero : ∀ n, i n ≫ p n = 0)
    (hexact : ∀ n < r, (ShortComplex.mk (i n) (p n) (hzero n)).ShortExact)
    (e : Ext X (K 0) 0) (he : e ≠ 0) :
    ¬ ((∀ n < r, Subsingleton (Ext X (F n) n)) ∧
      Subsingleton (Ext X (K r) r)) := by
  rintro ⟨hmid, hend⟩
  let := ext_zero_of_finite_exact_resolution X K F r i p hzero hexact hmid hend
  exact he (Subsingleton.elim _ _)

theorem lengthTwo_ext_zero
    (X : C) (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (hlink : T.X₃ = S.X₁)
    (hF₀ : Subsingleton (Ext X S.X₂ 0))
    (hF₁ : Subsingleton (Ext X T.X₂ 1))
    (hF₂ : Subsingleton (Ext X T.X₁ 2)) :
    Subsingleton (Ext X S.X₃ 0) := by
  have hK : Subsingleton (Ext X T.X₃ 1) :=
    ext_subsingleton_of_shortExact X T hT 1 hF₁ hF₂
  rw [hlink] at hK
  exact ext_subsingleton_of_shortExact X S hS 0 hF₀ hK

end ExactDimensionShifting

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

theorem associatedPrime_nonzero_quotient_hom (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ f : R ⧸ P →ₗ[R] M, f ≠ 0 := by
  obtain ⟨hprime, f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap P M).mp hP
  let := hprime
  refine ⟨f, ?_⟩
  intro hz
  have h10 : (1 : R ⧸ P) = 0 := hf (by simp [hz])
  exact one_ne_zero h10

theorem associatedPrime_nonzero_ext_zero (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0, e ≠ 0 := by
  obtain ⟨f, hf⟩ := associatedPrime_nonzero_quotient_hom P hP
  refine ⟨Ext.mk₀ (ModuleCat.ofHom f), ?_⟩
  intro he
  have hh := (Ext.mk₀_eq_zero_iff (ModuleCat.ofHom f)).mp he
  exact hf (congrArg (fun g : ModuleCat.of R (R ⧸ P) ⟶ ModuleCat.of R M => g.hom) hh)

theorem not_isAssociatedPrime_of_ext_zero (P : Ideal R)
    (h : Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0)) :
    ¬ IsAssociatedPrime P M := by
  intro hP
  obtain ⟨e, he⟩ := associatedPrime_nonzero_ext_zero P hP
  exact he (h.elim e 0)

theorem associatedPrime_local_nonzero_ext_zero (P : Ideal R) [P.IsPrime]
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext
      (ModuleCat.of (Localization.AtPrime P)
        (IsLocalRing.ResidueField (Localization.AtPrime P)))
      (ModuleCat.of (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) 0,
      e ≠ 0 := by
  have hlocal : IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (LocalizedModule.AtPrime P M) :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hP
  exact associatedPrime_nonzero_ext_zero
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) hlocal

end PiExponentJets.W18

end

end OAI
