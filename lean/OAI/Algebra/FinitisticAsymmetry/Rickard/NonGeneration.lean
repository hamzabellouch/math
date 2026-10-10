import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.ModuleGeneration
import OAI.Algebra.FinitisticAsymmetry.Rickard.Orthogonal
import OAI.Algebra.FinitisticAsymmetry.Rickard.ResolutionFamily
import OAI.Algebra.FinitisticAsymmetry.Nakayama.Coinduction
import OAI.Algebra.FinitisticAsymmetry.Rickard.ReducedProducts
import OAI.Algebra.FinitisticAsymmetry.Rickard.OrthogonalStalks
import OAI.Algebra.FinitisticAsymmetry.Rickard.FiniteFamilies

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
local instance nonGenerationHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

lemma prop_injective_of_da
    (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hcop : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
    (hD : P ((DerivedCategory.singleFunctor _ 0).obj (Nakayama.DA k R)))
    (M : ModuleCat.{u} R) [Injective M] :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  let V := (ModuleCat.restrictScalars (algebraMap k R)).obj M
  let b := Module.Free.chooseBasis k V
  let S := ModuleCat.of R (Π₀ _ : Module.Free.ChooseBasisIndex k V, Nakayama.DA k R)
  let cs : Cofan (fun _ : Module.Free.ChooseBasisIndex k V => Nakayama.DA k R) :=
    Cofan.mk S (fun i => ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun _ : Module.Free.ChooseBasisIndex k V => Nakayama.DA k R) i))
  have hc : IsColimit cs := by
    refine Cofan.IsColimit.mk _
      (fun t => ModuleCat.ofHom (DFinsupp.lsum ℤ (fun i => (t.inj i).hom))) ?_ ?_
    · intro t i
      ext x
      change (DFinsupp.lsum ℤ (fun i => (t.inj i).hom)) (DFinsupp.single i x) = (t.inj i).hom x
      simp only [DFinsupp.lsum_single]
    · intro t f hf
      apply ModuleCat.hom_ext
      apply DFinsupp.lhom_ext'
      intro i
      apply LinearMap.ext
      intro x
      have hh := ConcreteCategory.congr_hom (hf i) x
      change f.hom (DFinsupp.single i x) =
        (DFinsupp.lsum ℤ (fun i => (t.inj i).hom)) (DFinsupp.single i x)
      rw [DFinsupp.lsum_single]
      exact hh
  let := hcop (ULift.{u} ℕ)
  let : P.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ))
  let := hcop (Module.Free.ChooseBasisIndex k V)
  have hS : P ((DerivedCategory.singleFunctor _ 0).obj S) :=
    DerivedSupport.prop_single_of_cofan P cs hc (fun _ => hD)
  let e : S ≅ Nakayama.coind k R V :=
    (LinearEquiv.ofBijective (Nakayama.coindBasisMap V b)
      (Nakayama.coindBasisMap_bijective k R V b)).toModuleIso
  have hC : P ((DerivedCategory.singleFunctor _ 0).obj (Nakayama.coind k R V)) :=
    P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e) hS
  let j := Nakayama.moduleCoindInclusion k R M
  let : Mono j := Nakayama.moduleCoindInclusion_mono k R M
  let p := Injective.factorThru (𝟙 M) j
  have hjp : j ≫ p = 𝟙 M := Injective.comp_factorThru (𝟙 M) j
  let F := DerivedCategory.singleFunctor (ModuleCat R) 0
  exact DerivedSupport.localizing_of_retract (F.map j) (F.map p)
    (by rw [← F.map_comp, hjp, F.map_id]) P hC

lemma not_generate_of_minimal_family (M : ℕ → PDMinimal.FiniteModule k R)
    (d : ℕ → ℕ) (hd : ∀ i, i < d i)
    (hpd : ∀ i, HasProjectiveDimensionLE (M i).cat (d i))
    (hlast : ∀ i, ¬ Subsingleton (PDMinimal.term (M i) (d i))) :
    ¬ InjectivesGenerate R := by
  classical
  let K := fun i => nakayamaComplex k (translatedResolution (M i) (d i))
  let L := reducedComplex K
  have hkzero : ∀ i j, j < 0 → IsZero ((K i).X j) := fun i j hj =>
    nakayamaComplex_zero k _ j (translatedResolution_zero_negative (M i) (d i) (hpd i) j hj)
  have hknon : ∀ i, ∃ x : (K i).X 0, x ≠ 0 ∧ (K i).d 0 1 x = 0 := fun i =>
    translated_nakayama_zero_cycle k (M i) (d i) (by have := hd i; omega) (hlast i)
  have hkinj : ∀ i j, Injective ((K i).X j) := fun i j =>
    nakayamaComplex_injective k _ (translatedResolution_finite (M i) (d i))
      (translatedResolution_projective (M i) (d i)) j
  let : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  let (j : ℤ) : Injective (L.X j) := reducedComplex_injective K hkinj j
  let : L.IsStrictlyGE (-1) := reduced_isStrictlyGE K hkzero
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-1)
  have hnon : ¬ IsZero (DerivedCategory.Q.obj L) :=
    not_isZero_Q_of_not_exact_zero L (reduced_not_exact_zero K hkzero hknon)
  let : Module.Finite R (Nakayama.DA k R) := Nakayama.da_finite k R
  have hex (j : ℤ) (f : Nakayama.DA k R ⟶ L.X j) (hf : f ≫ L.d j (j+1) = 0) :
      ∃ g : Nakayama.DA k R ⟶ L.X (j-1), g ≫ L.d (j-1) j = f := by
    have he : ∃ s : Finset ℕ, ∀ i ∉ s, ∀ f : Nakayama.DA k R ⟶ (K i).X (j-1+1),
        f ≫ (K i).d (j-1+1) (j-1+1+1) = 0 →
        ∃ g : Nakayama.DA k R ⟶ (K i).X (j-1), g ≫ (K i).d (j-1) (j-1+1) = f := by
      refine ⟨Finset.range (j.toNat+1), ?_⟩
      intro i hi f hf
      apply nakayamaComplex_hom_exact k _ (translatedResolution_finite (M i) (d i))
        (translatedResolution_projective (M i) (d i)) (j-1) _ f hf
      apply translatedResolution_exact
      have hdi := hd i
      simp only [Finset.mem_range, not_lt] at hi
      omega
    have hh := reduced_hom_exact K (Nakayama.DA k R) (j-1) he
    rw [sub_add_cancel] at hh
    exact hh f hf
  apply not_generate_of_orthogonal (DerivedCategory.Q.obj L) hnon
  intro N hN
  let := hN
  apply (perpendicular_iff (DerivedCategory.Q.obj L) _).mp
  apply prop_injective_of_da (k := k) (perpendicular (DerivedCategory.Q.obj L))
    (fun I => inferInstance) _ N
  apply (perpendicular_iff _ _).mpr
  exact orthogonal_single_of_hom_exact _ L hex

lemma not_injectivesGenerate_of_little_eq_top (k : Type u) [Field k] [Algebra k R]
    [FiniteDimensional k R]
    (h : littleFinitisticDimension R = ⊤) : ¬ InjectivesGenerate R := by
  obtain ⟨M, d, hd, hpd, hterm⟩ := exists_minimal_family (k := k) h
  exact not_generate_of_minimal_family M d hd hpd hterm

end LittleFinitistic.Rickard

end

end OAI
