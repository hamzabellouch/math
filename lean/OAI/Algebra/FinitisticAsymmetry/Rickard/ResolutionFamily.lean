import Mathlib
import OAI.Algebra.Finitistic.Dimension.PDDimension
import OAI.Algebra.FinitisticAsymmetry.Nakayama.Minimality

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
private theorem mono_map_of_conjugate {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X₀ X₁ Y₀ Y₁ : C} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (h : f = e₀.hom ≫ g ≫ e₁.inv)
    (hf : Mono (F.map f)) : Mono (F.map g) := by
  let := hf
  have hg : F.map g = F.map e₀.inv ≫ F.map f ≫ F.map e₁.hom := by
    rw [h, F.map_comp, F.map_comp]
    simp
  rw [hg]
  infer_instance

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
open PDMinimal

def translatedResolution (M : FiniteModule k R) (d : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex M).extend (ComplexShape.embeddingUpIntLE d)

lemma translatedResolution_finite (M : FiniteModule k R) (d : ℕ) (j : ℤ) :
    Module.Finite R ((translatedResolution M d).X j) := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    let : Module.Finite R ((complex M).X n) := (inferInstance : Module.Finite R (term M n))
    exact Module.Finite.equiv ((complex M).extendXIso _ hn).symm.toLinearEquiv
  · have hz := (complex M).isZero_extend_X (ComplexShape.embeddingUpIntLE d) j (by simpa using h)
    let : Subsingleton ((translatedResolution M d).X j) := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

lemma translatedResolution_projective (M : FiniteModule k R) (d : ℕ) (j : ℤ) :
    Module.Projective R ((translatedResolution M d).X j) := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    let : Module.Projective R ((complex M).X n) :=
      (inferInstance : Module.Projective R (term M n))
    exact Module.Projective.of_equiv ((complex M).extendXIso _ hn).symm.toLinearEquiv
  · have hz := (complex M).isZero_extend_X (ComplexShape.embeddingUpIntLE d) j (by simpa using h)
    let : Subsingleton ((translatedResolution M d).X j) := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

lemma term_zero_above (M : FiniteModule k R) (d n : ℕ)
    (hd : HasProjectiveDimensionLE M.cat d) (hn : d < n) : Subsingleton (term M n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply term_zero_of_pdLE M m
  rw [← projectiveDimension_le_iff] at hd ⊢
  exact hd.trans (by exact_mod_cast (by omega : d ≤ m))

lemma translatedResolution_zero_negative (M : FiniteModule k R) (d : ℕ)
    (hd : HasProjectiveDimensionLE M.cat d) (j : ℤ) (hj : j < 0) :
    IsZero ((translatedResolution M d).X j) := by
  let n := (d - j).toNat
  have hn : (ComplexShape.embeddingUpIntLE d).f n = j := by
    rw [ComplexShape.embeddingUpIntLE_f]
    dsimp [n]
    omega
  have := term_zero_above M d n hd (by dsimp [n]; omega)
  exact ((complex M).extendXIso _ hn).isZero_iff.mpr
    (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (term M n) from inferInstance))

lemma translatedResolution_exact (M : FiniteModule k R) (d : ℕ) (j : ℤ) (hj : j ≠ d) :
    (translatedResolution M d).ExactAt j := by
  by_cases h : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE d).f n = j
  · obtain ⟨n, hn⟩ := h
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      simp only [ComplexShape.embeddingUpIntLE_f, Nat.cast_zero, sub_zero] at hn
      exact hj hn.symm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ((complex M).extend_exactAt_iff _ hn).mpr (complex_exactAt M m)
  · exact (complex M).extend_exactAt _ j (by simpa using h)

variable (k)
def nakayamaComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (Nakayama.functor k R).mapHomologicalComplex (.up ℤ) |>.obj P

lemma nakayamaComplex_hom_exact (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (P.X j)) (hproj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) (hex : P.ExactAt (j+1)) (f : Nakayama.DA k R ⟶ (nakayamaComplex k P).X (j+1))
    (hf : f ≫ (nakayamaComplex k P).d (j+1) (j+1+1) = 0) :
    ∃ g : Nakayama.DA k R ⟶ (nakayamaComplex k P).X j,
      g ≫ (nakayamaComplex k P).d j (j+1) = f := by
  let (i : ℤ) := hfin i
  let (i : ℤ) := hproj i
  obtain ⟨F⟩ := Nakayama.frame_nonempty R (P.X (j+1))
  obtain ⟨G⟩ := Nakayama.frame_nonempty R (P.X (j+1+1))
  obtain ⟨p, hp⟩ := Nakayama.eta_surjective k R _ F f.hom
  have hz : P.d (j+1) (j+1+1) p = 0 := by
    apply Nakayama.eta_injective k R _ G
    rw [← Nakayama.eta_natural, hp]
    have hf' := congrArg ModuleCat.Hom.hom hf
    change (Nakayama.map (P.d (j+1) (j+1+1))).comp f.hom = 0 at hf'
    rw [hf']
    ext h φ
    simp [Nakayama.etaMap]
    rfl
  have hx := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    ((HomologicalComplex.exactAt_iff' P j (j+1) (j+1+1) (by simp) (by simp)).mp hex)
  change LinearMap.range (P.d j (j+1)).hom = LinearMap.ker (P.d (j+1) (j+1+1)).hom at hx
  have hpker : p ∈ LinearMap.ker (P.d (j+1) (j+1+1)).hom := hz
  rw [← hx] at hpker
  obtain ⟨q, hq⟩ := hpker
  refine ⟨ModuleCat.ofHom (Nakayama.etaMap k R _ q), ?_⟩
  apply ModuleCat.hom_ext
  change (Nakayama.map (P.d j (j+1))).comp (Nakayama.etaMap k R _ q) = f.hom
  rw [Nakayama.eta_natural, hq, hp]

omit [FiniteDimensional k R] in
lemma nakayamaComplex_injective (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (P.X j)) (hproj : ∀ j, Module.Projective R (P.X j))
    (j : ℤ) : Injective ((nakayamaComplex k P).X j) := by
  let := hfin j
  let := hproj j
  exact Nakayama.object_injective k R (P.X j)

omit [FiniteDimensional k R] in
lemma nakayamaComplex_zero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (j : ℤ) (h : IsZero (P.X j)) : IsZero ((nakayamaComplex k P).X j) := by
  exact (Nakayama.functor k R).map_isZero h

lemma translated_nakayama_zero_cycle (M : FiniteModule k R) (d : ℕ)
    (hd : 0 < d) (hterm : ¬ Subsingleton (term M d)) :
    ∃ x : (nakayamaComplex k (translatedResolution M d)).X 0,
      x ≠ 0 ∧ (nakayamaComplex k (translatedResolution M d)).d 0 1 x = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let : Nontrivial (term M (n+1)) := not_subsingleton_iff_nontrivial.mp hterm
  let e := ComplexShape.embeddingUpIntLE ((n+1 : ℕ) : ℤ)
  have h₀ : e.f (n+1) = 0 := by simp [e]
  have h₁ : e.f n = 1 := by simp [e]
  let P := translatedResolution M (n+1)
  let F := Nakayama.functor k R
  have he : P.d 0 1 = ((complex M).extendXIso e h₀).hom ≫
      ModuleCat.ofHom (differential M n) ≫ ((complex M).extendXIso e h₁).inv := by
    simpa only [P, translatedResolution, e, complex_d] using! (complex M).extend_d_eq e h₀ h₁
  have hn : ¬ Function.Injective ((nakayamaComplex k P).d 0 1).hom := by
    intro hi
    have hmono : Mono (F.map (P.d 0 1)) := (ModuleCat.mono_iff_injective _).mpr hi
    have hh : Mono (F.map (ModuleCat.ofHom (differential M n))) :=
      mono_map_of_conjugate F ((complex M).extendXIso e h₀) ((complex M).extendXIso e h₁)
        (P.d 0 1) (ModuleCat.ofHom (differential M n)) he hmono
    exact Nakayama.minimal_nakayama_differential_noninjective M n
      ((ModuleCat.mono_iff_injective _).mp hh)
  rw [Function.Injective] at hn
  push Not at hn
  obtain ⟨x, y, hxy, hne⟩ := hn
  refine ⟨x-y, sub_ne_zero.mpr hne, ?_⟩
  change ((nakayamaComplex k P).d 0 1).hom (x-y) = 0
  rw [map_sub, hxy, sub_self]

end LittleFinitistic.Rickard

end

end OAI
