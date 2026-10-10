import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.DerivedSums
import OAI.Algebra.FinitisticAsymmetry.Derived.ModuleSums

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n+1)) (s : Cofan X) (hs : IsColimit s)

def telescopeMap : s.pt ⟶ s.pt :=
  hs.desc (Cofan.mk s.pt (fun n => s.inj n - f n ≫ s.inj (n+1)))

@[reassoc (attr := simp)]
lemma telescopeMap_inj (n : ℕ) :
    s.inj n ≫ telescopeMap f s hs = s.inj n - f n ≫ s.inj (n+1) :=
  hs.fac _ (Discrete.mk n)

def telescopeπ (c : Cocone (Functor.ofSequence f)) : s.pt ⟶ c.pt :=
  hs.desc (Cofan.mk c.pt c.ι.app)

omit [Preadditive C] in
@[reassoc (attr := simp)]
lemma telescopeπ_inj (c : Cocone (Functor.ofSequence f)) (n : ℕ) :
    s.inj n ≫ telescopeπ f s hs c = c.ι.app n := hs.fac _ (Discrete.mk n)

lemma telescope_zero (c : Cocone (Functor.ofSequence f)) :
    telescopeMap f s hs ≫ telescopeπ f s hs c = 0 := by
  apply hs.hom_ext
  intro n
  change s.inj n.as ≫ _ = _
  rw [telescopeMap_inj_assoc, Preadditive.sub_comp, telescopeπ_inj,
    Category.assoc, telescopeπ_inj, comp_zero]
  have h := c.w (homOfLE (Nat.le_add_right n.as 1))
  simpa using! sub_eq_zero.mpr h.symm

def telescopeCokernel (c : Cocone (Functor.ofSequence f)) (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (telescopeπ f s hs c) (telescope_zero f s hs c)) := by
  let d {Y : C} (g : s.pt ⟶ Y) (hg : telescopeMap f s hs ≫ g = 0) :
      Cocone (Functor.ofSequence f) :=
    { pt := Y
      ι := NatTrans.ofSequence (F := Functor.ofSequence f) (G := (Functor.const ℕ).obj Y) (fun n => s.inj n ≫ g) (fun n => by
        have h := congrArg (fun t => s.inj n ≫ t) hg
        rw [telescopeMap_inj_assoc, Preadditive.sub_comp, comp_zero] at h
        dsimp only [Functor.const_obj_map]
        rw [Functor.ofSequence_map_homOfLE_succ]
        change f n ≫ (s.inj (n+1) ≫ g) = (s.inj n ≫ g) ≫ 𝟙 Y
        simpa only [Category.comp_id, Category.assoc] using (sub_eq_zero.mp h).symm) }
  refine CokernelCofork.IsColimit.ofπ _ _ (fun g hg => hc.desc (d g hg)) ?_ ?_
  · intro Y g hg
    apply hs.hom_ext
    intro n
    change s.inj n.as ≫ _ = _
    erw [telescopeπ_inj_assoc, hc.fac]
    rfl
  · intro Y g hg m hm
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change c.ι.app n ≫ m = s.inj n ≫ g
    rw [← hm, telescopeπ_inj_assoc]
    rfl

end

section
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))

abbrev moduleTelescopeMap := telescopeMap f _ (moduleSumComplexIsColimit K)

def moduleTelescopeLinear (j : ℤ) : (Π₀ n, (K n).X j) →ₗ[R] (Π₀ n, (K n).X j) :=
  ((moduleTelescopeMap K f).f j).hom

lemma moduleTelescope_at_zero (j : ℤ) (x : Π₀ n, (K n).X j) :
    (moduleTelescopeLinear K f j x) 0 = x 0 := by
  classical
  let : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have h : (DFinsupp.lapply 0).comp (moduleTelescopeLinear K f j) =
      (DFinsupp.lapply 0 : (Π₀ n, (K n).X j) →ₗ[R] (K 0).X j) := by
    apply DFinsupp.lhom_ext
    intro n y
    have hlin := congrArg (fun t => (t.f j).hom) (telescopeMap_inj f _ (moduleSumComplexIsColimit K) n)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, ModuleCat.hom_sub, ModuleCat.hom_comp] at hlin
    have hfun := LinearMap.congr_fun hlin y
    simp only [moduleSumComplexCofan, cofan_mk_inj, moduleSumComplexInj] at hfun
    have hsing : moduleTelescopeLinear K f j (DFinsupp.single n y) =
        (DFinsupp.single n y : Π₀ n, (K n).X j) - DFinsupp.single (n+1) ((f n).f j y) := by
      simpa [moduleTelescopeLinear, moduleTelescopeMap, moduleSumComplexCofan, moduleSumComplexInj, moduleSumComplex] using! hfun
    change (moduleTelescopeLinear K f j (DFinsupp.single n y)) 0 = _
    rw [hsing, DFinsupp.sub_apply]
    simp [DFinsupp.lapply_apply]
  exact LinearMap.congr_fun h x

lemma moduleTelescope_at_succ (j : ℤ) (x : Π₀ n, (K n).X j) (n : ℕ) :
    (moduleTelescopeLinear K f j x) (n+1) = x (n+1) - (f n).f j (x n) := by
  classical
  let : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have h : (DFinsupp.lapply (n+1)).comp (moduleTelescopeLinear K f j) =
      (DFinsupp.lapply (n+1) : (Π₀ n, (K n).X j) →ₗ[R] (K (n+1)).X j) -
        ((f n).f j).hom.comp (DFinsupp.lapply n) := by
    apply DFinsupp.lhom_ext
    intro m y
    have hlin := congrArg (fun t => (t.f j).hom) (telescopeMap_inj f _ (moduleSumComplexIsColimit K) m)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, ModuleCat.hom_sub, ModuleCat.hom_comp] at hlin
    have hfun := LinearMap.congr_fun hlin y
    simp only [moduleSumComplexCofan, cofan_mk_inj, moduleSumComplexInj] at hfun
    have hsing : moduleTelescopeLinear K f j (DFinsupp.single m y) =
        (DFinsupp.single m y : Π₀ n, (K n).X j) - DFinsupp.single (m+1) ((f m).f j y) := by
      simpa [moduleTelescopeLinear, moduleTelescopeMap, moduleSumComplexCofan, moduleSumComplexInj, moduleSumComplex] using! hfun
    change (moduleTelescopeLinear K f j (DFinsupp.single m y)) (n+1) = _
    rw [hsing, DFinsupp.sub_apply]
    by_cases hmn : m = n
    · subst m
      simp
    · simp [hmn]
  exact LinearMap.congr_fun h x

instance moduleTelescopeMap_mono : Mono (moduleTelescopeMap K f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  rw [ModuleCat.mono_iff_injective]
  apply (injective_iff_map_eq_zero _).2
  change ∀ (x : Π₀ n, (K n).X j), moduleTelescopeLinear K f j x = 0 → x = 0
  intro x hx
  have he (n : ℕ) : x n = 0 := by
    induction n with
    | zero => simpa [hx] using (moduleTelescope_at_zero K f j x).symm
    | succ n ih =>
      have h := moduleTelescope_at_succ K f j x n
      rw [hx, ih, map_zero, sub_zero] at h
      exact h.symm
  exact DFinsupp.ext he

end

universe u w
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))
variable (c : Cocone (Functor.ofSequence f)) (hc : IsColimit c)

def moduleTelescopeShortComplex : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (moduleTelescopeMap K f)
    (telescopeπ f _ (moduleSumComplexIsColimit K) c)
    (telescope_zero f _ (moduleSumComplexIsColimit K) c)

lemma moduleTelescope_shortExact (hc : IsColimit c) : (moduleTelescopeShortComplex K f c).ShortExact where
  mono_f := by change Mono (moduleTelescopeMap K f); infer_instance
  epi_g := epi_of_isColimit_cofork (telescopeCokernel f _ (moduleSumComplexIsColimit K) c hc)
  exact := (moduleTelescopeShortComplex K f c).exact_of_g_is_cokernel
    (telescopeCokernel f _ (moduleSumComplexIsColimit K) c hc)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

lemma localizing_sequence_colimit (hc : IsColimit c) (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]
    (hK : ∀ n, P (DerivedCategory.Q.obj (K n))) : P (DerivedCategory.Q.obj c.pt) := by
  have hs : P (DerivedCategory.Q.obj (moduleSumComplex K)) :=
    P.prop_of_isColimit (derivedCofanIsColimit _ (moduleSumComplexIsColimit K))
      (fun n => hK n.as)
  exact P.ext_of_isTriangulatedClosed₃ _
    (DerivedCategory.triangleOfSES_distinguished (moduleTelescope_shortExact K f c hc)) hs hs

end LittleFinitistic.DerivedSupport

end

end OAI
