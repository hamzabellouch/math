import OAI.Algebra.AuslanderReiten.Basic
import OAI.Algebra.AuslanderReiten.Complete.CompleteResolutionTail
import Mathlib.CategoryTheory.Abelian.Projective.Ext

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (R : Type u) [Ring R]
  (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem positiveExtVanish_iff_resolution
    (P : ProjectiveResolution (ModuleCat.of R M)) :
    PositiveExtVanish R M N ↔
      ∀ (n : ℕ) (f : P.complex.X (n + 1) ⟶ ModuleCat.of R N),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ ModuleCat.of R N,
          P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h n f hf
    have := h (n + 1) (Nat.zero_lt_succ n)
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (Subsingleton.elim _ _)
  · intro h n hn
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hz : ∀ a : CategoryTheory.Abelian.Ext
        (ModuleCat.of R M) (ModuleCat.of R N) (p + 1), a = 0 := by
      intro a
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (p + 2) rfl
      exact (P.extMk_eq_zero_iff f (p + 2) rfl hf p rfl).mpr (h p f hf)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem positiveExtVanish_iff_completeResolution
    (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom)
    (e : M ≃ₗ[R] CompleteCokernel P) :
    PositiveExtVanish R M N ↔
      ∀ (n : ℕ) (f : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] N),
        f.comp (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0 →
        ∃ g : P.X (n : ℤ) →ₗ[R] N,
          f = g.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom := by
  let Q := transportProjectiveResolution (completeCokernelResolution P hproj hex)
    e.symm.toModuleIso
  refine (positiveExtVanish_iff_resolution R M N Q).trans ⟨?_, ?_⟩
  · intro h n f hf
    have hfc : Q.complex.d (n + 2) (n + 1) ≫ ModuleCat.ofHom f = 0 := by
      change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ ModuleCat.ofHom f = 0
      rw [nonnegativeTail_d]
      exact ModuleCat.hom_ext hf
    obtain ⟨g, hg⟩ := h n (ModuleCat.ofHom f) hfc
    refine ⟨g.hom, ?_⟩
    change (nonnegativeTail P).d (n + 1) n ≫ g = ModuleCat.ofHom f at hg
    rw [nonnegativeTail_d] at hg
    exact (congrArg ModuleCat.Hom.hom hg).symm
  · intro h n f hf
    change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ f = 0 at hf
    rw [nonnegativeTail_d] at hf
    obtain ⟨g, hg⟩ := h n f.hom (congrArg ModuleCat.Hom.hom hf)
    refine ⟨ModuleCat.ofHom g, ?_⟩
    change (nonnegativeTail P).d (n + 1) n ≫ ModuleCat.ofHom g = f
    rw [nonnegativeTail_d]
    exact ModuleCat.hom_ext hg.symm

theorem positiveExtVanish_of_completeResolution
    (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom)
    (hdual : ∀ (n : ℤ) (f : P.X n →ₗ[R] N),
      f.comp (P.d (n + 1) n).hom = 0 →
      ∃ g : P.X (n - 1) →ₗ[R] N, f = g.comp (P.d n (n - 1)).hom)
    (e : M ≃ₗ[R] CompleteCokernel P) : PositiveExtVanish R M N := by
  let Q := transportProjectiveResolution (completeCokernelResolution P hproj hex)
    e.symm.toModuleIso
  apply (positiveExtVanish_iff_resolution R M N Q).2
  intro n f hf
  change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ f = 0 at hf
  rw [nonnegativeTail_d] at hf
  have aux (i j l : ℤ) (hi : i = j + 1) (hl : l = j - 1)
      (f : P.X j →ₗ[R] N) (hf : f.comp (P.d i j).hom = 0) :
      ∃ g : P.X l →ₗ[R] N, f = g.comp (P.d j l).hom := by
    subst i
    subst l
    exact hdual j f hf
  obtain ⟨g, hg⟩ := aux ((n + 1 + 1 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) (n : ℤ)
    (by omega) (by omega) f.hom (congrArg ModuleCat.Hom.hom hf)
  refine ⟨ModuleCat.ofHom g, ?_⟩
  change (nonnegativeTail P).d (n + 1) n ≫ ModuleCat.ofHom g = f
  rw [nonnegativeTail_d]
  exact ModuleCat.hom_ext hg.symm

theorem GorensteinProjective.positiveExt_regular
    (h : GorensteinProjective R M) : PositiveExtVanish R M R := by
  obtain ⟨P, hp, he, hd, ⟨e⟩⟩ := h
  exact positiveExtVanish_of_completeResolution R M R P (fun n => (hp n).2) he hd e

end ArExplicit

end OAI
