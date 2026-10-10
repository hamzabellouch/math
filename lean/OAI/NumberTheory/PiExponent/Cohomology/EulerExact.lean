import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Cohomology
open CategoryTheory CategoryTheory.Abelian

def alternatingTrunc (a : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), (-1 : ℤ)^i * a i

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma alternating_rank_identity (a b c f g h : ℕ → ℤ)
    (hB : ∀ n, b n = f n + g n) (hC : ∀ n, c n = g n + h n)
    (hA0 : a 0 = f 0) (hA : ∀ n, a (n+1) = h n + f (n+1)) (d : ℕ) :
    alternatingTrunc b d - alternatingTrunc a d - alternatingTrunc c d =
      (-1 : ℤ)^(d+1) * h d := by
  induction d with
  | zero => simp [alternatingTrunc, hB, hC, hA0]
  | succ d ih =>
    simp only [alternatingTrunc_succ]
    calc
      _ = (alternatingTrunc b d - alternatingTrunc a d - alternatingTrunc c d) +
          (-1 : ℤ)^(d+1) * (b (d+1) - a (d+1) - c (d+1)) := by ring
      _ = _ := by rw [ih, hB, hC, hA, pow_succ _ (d+1)]; ring

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

def extEuler (E M : C) (d : ℕ) : ℤ :=
  alternatingTrunc (fun n => Module.finrank K (Ext E M n)) d

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

def cohomologyMap₁ (n : ℕ) : Ext E S.X₁ n →ₗ[K] Ext E S.X₂ n :=
  (Ext.mk₀ S.f).postcompOfLinear K E (add_zero n)

def cohomologyMap₂ (n : ℕ) : Ext E S.X₂ n →ₗ[K] Ext E S.X₃ n :=
  (Ext.mk₀ S.g).postcompOfLinear K E (add_zero n)

def cohomologyBoundary (n : ℕ) : Ext E S.X₃ n →ₗ[K] Ext E S.X₁ (n+1) :=
  hS.extClass.postcompOfLinear K E rfl

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end Cohomology

namespace Geometry
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def sheafComplexLinear : Linear ℂ X.Modules where
  homModule M N := Module.compHom _ (baseScalars f)
  smul_comp M N P r g h := by
    change ((baseScalars f r) • g) ≫ h = (baseScalars f r) • (g ≫ h)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul M N P g r h := by
    change g ≫ ((baseScalars f r) • h) = (baseScalars f r) • (g ≫ h)
    exact Linear.comp_smul _ _ _ _ _ _

@[instance_reducible]
def complexExtModule (M : X.Modules) (n : ℕ) : Module ℂ (cohomology M n) :=
  letI := sheafComplexLinear f
  inferInstance

lemma complexExtModule_eq (M : X.Modules) (n : ℕ) :
    complexExtModule f M n = Module.compHom (cohomology M n) (baseScalars f) := by
  apply Module.ext'
  intro r x
  let := sheafComplexLinear f
  change r • x = (baseScalars f r) • x
  rw [Ext.smul_eq_comp_mk₀ (R := ℂ), Ext.smul_eq_comp_mk₀ (R := Γ(X, ⊤))]
  rfl

lemma eulerCharacteristic_eq_extEuler (M : X.Modules) (d : ℕ) :
    eulerCharacteristic f d M =
      letI := sheafComplexLinear f
      Cohomology.extEuler (K := ℂ) (structureSheaf X) M d := by
  unfold eulerCharacteristic Cohomology.extEuler Cohomology.alternatingTrunc
  apply Finset.sum_congr rfl
  intro n hn
  have hh := complexExtModule_eq f M n
  unfold cohomologyDimension
  rw [← hh]

theorem eulerCharacteristic_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₁ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₂ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₃ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₃ n))
    [Subsingleton (cohomology S.X₁ (d+1))] :
    eulerCharacteristic f d S.X₂ =
      eulerCharacteristic f d S.X₁ + eulerCharacteristic f d S.X₃ := by
  let := sheafComplexLinear f
  rw [eulerCharacteristic_eq_extEuler, eulerCharacteristic_eq_extEuler,
    eulerCharacteristic_eq_extEuler]
  apply Cohomology.extEuler_add (K := ℂ) (structureSheaf X) hS d
  · intro n hn
    have hh := complexExtModule_eq f S.X₁ n
    change @FiniteDimensional ℂ (cohomology S.X₁ n) _ _ (complexExtModule f S.X₁ n)
    rw [hh]
    exact hfinite₁ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₂ n
    change @FiniteDimensional ℂ (cohomology S.X₂ n) _ _ (complexExtModule f S.X₂ n)
    rw [hh]
    exact hfinite₂ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₃ n
    change @FiniteDimensional ℂ (cohomology S.X₃ n) _ _ (complexExtModule f S.X₃ n)
    rw [hh]
    exact hfinite₃ n hn

end Geometry

end PiExponentSeshadri

end

end OAI
