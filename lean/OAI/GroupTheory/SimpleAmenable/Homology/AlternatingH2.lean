import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PolygonHomologyAction
import OAI.GroupTheory.SimpleAmenable.Configurations.AlternatingStability

namespace OAI

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2
namespace PolygonPlacement.Configuration
variable {a m : ℕ}

noncomputable def altEmptyIso (a m : ℕ) :
    altColumn a m 0 ≅ Rep.trivial ℤ (polygonAlternatingGroup a m) ℤ :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).mapIso (emptyIso a m)

@[simp] lemma altEmptyIso_single (a m : ℕ) (x : Configuration a m 0) (z : ℤ) :
    (altEmptyIso a m).hom.hom (single x z)=z := emptyIso_single a m x z
lemma altAugmentation_pointMap (f : Configuration a m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) q).map (altBoundary a m 0) ≫
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) q).map (altEmptyIso a m).hom =
    TrivialHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso a m).hom.hom ((boundary a m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma alternatingStabilizer_H2_epi (a m : ℕ) (hm : 34 ≤ m) (f : Configuration a m 1) :
    Epi (TrivialHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype 2) := by
  have := TransitiveInduction.isIso_map_pointMap f (fun g => alternating_transitive f g (by omega)) 2
  have first : Epi (groupHomology.map
      (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype
      (TransitiveInduction.pointMap f) 2) := inferInstance
  have second := altBoundary_zero_H2_epi a m hm
  have third : Epi ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 2).map
      (altEmptyIso a m).hom) := inferInstance
  rw [← altAugmentation_pointMap f 2]
  have composite := epi_comp' first (epi_comp' second third)
  exact composite

lemma stabilizeAlternating_H2_epi (a n : ℕ) (hn : 33 ≤ n) :
    Epi (TrivialHomology.map (PolygonTracks.stabilizeAlternating a 1 n) 2) := by
  rw [← alternatingStabilizerEquiv_subtype a 1 n (by omega), TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (alternatingStabilizerEquiv a 1 n (by omega)) 2
  have := alternatingStabilizer_H2_epi a (1+n) (by omega) (standard a 1 n)
  infer_instance
end PolygonPlacement.Configuration

namespace PolygonTracks
noncomputable def castAlternating (a : ℕ) {m n : ℕ} (h : m=n) :
    polygonAlternatingGroup a m ≃* polygonAlternatingGroup a n := h ▸ MulEquiv.refl _

@[simp] lemma castAlternating_val (a : ℕ) {m n : ℕ} (h : m=n) (g : polygonAlternatingGroup a m) :
    (castAlternating a h g).val=castFull a h g.val := by subst n; rfl

lemma stabilizeAlternating_add (a k l n : ℕ) : stabilizeAlternating a (k+l) n =
    (castAlternating a (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilizeAlternating a k (l+n)).comp (stabilizeAlternating a l n)) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  change stabilize a (k+l) n g.val=_
  rw [stabilize_add]
  simp only [MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom,
    castAlternating_val,stabilizeAlternating_val]

lemma stabilizeAlternating_zero_bijective (a n : ℕ) (hn : 32 ≤ n) :
    Function.Bijective (stabilizeAlternating a 0 n) := by
  refine ⟨stabilizeAlternating_injective,?_⟩
  intro g
  obtain ⟨f,hf⟩ := (stabilize_zero_bijective a n).surjective g.val
  have hg : f∈polygonAlternatingGroup a n := by
    rw [← stabilize_alternating_comap a 0 n hn]
    change stabilize a 0 n f∈polygonAlternatingGroup a (0+n)
    rw [hf]
    exact g.property
  exact ⟨⟨f,hg⟩,Subtype.ext hf⟩

lemma stabilizeAlternating_H2_epi (a k n : ℕ) (hn : 33 ≤ n) :
    Epi (TrivialHomology.map (stabilizeAlternating a k n) 2) := by
  induction k with
  | zero =>
      have : IsIso (TrivialHomology.map (stabilizeAlternating a 0 n) 2) :=
        TrivialHomology.isIso_equiv
        (MulEquiv.ofBijective (stabilizeAlternating a 0 n)
          (stabilizeAlternating_zero_bijective a n (by omega))) 2
      infer_instance
  | succ k ih =>
    have he : Epi (TrivialHomology.map (stabilizeAlternating a (1+k) n) 2) := by
      rw [stabilizeAlternating_add, TrivialHomology.map_comp, TrivialHomology.map_comp]
      have := TrivialHomology.isIso_equiv (castAlternating a (Nat.add_assoc 1 k n).symm) 2
      have := PolygonPlacement.Configuration.stabilizeAlternating_H2_epi a (k+n) (by omega)
      have := ih
      infer_instance
    rw [show k+1=1+k by omega]
    exact he

lemma stabilizeAlternating_mapH2_surjective (a k n : ℕ) (hn : 33 ≤ n) :
    Function.Surjective (IntegralHomology.mapH2 (stabilizeAlternating a k n)) := by
  have := stabilizeAlternating_H2_epi a k n hn
  exact (ModuleCat.epi_iff_surjective (TrivialHomology.map (stabilizeAlternating a k n) 2)).mp inferInstance

lemma fullAction_trivial (a m : ℕ) (hm : 205 < m) (f : polygonFullGroup a m) :
    IntegralHomology.mapH2 (fullConjugation a m f)=LinearMap.id := by
  obtain ⟨k,rfl⟩ : ∃k,m=k+33 := ⟨m-33,by omega⟩
  exact mapH2_fullConjugation_eq_id_of_surjective (by omega)
    (stabilizeAlternating_mapH2_surjective a k 33 (by omega)) f
end PolygonTracks
end SimpleAmenable

end

open CategoryTheory CategoryTheory.Limits

namespace FiniteHomologyReturn

section
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

lemma finite_of_exact {X : ShortComplex (ModuleCat.{u} R)} (hX : X.Exact)
    [Module.Finite R X.X₁] [Module.Finite R X.X₃] : Module.Finite R X.X₂ := by
  have : Module.Finite R (LinearMap.range X.g.hom) :=
    Module.Finite.of_injective (LinearMap.range X.g.hom).subtype Subtype.val_injective
  exact Module.Finite.of_exact (f:=X.f.hom) (g:=X.g.hom.rangeRestrict)
    (by
      rw [LinearMap.exact_iff]
      simpa using hX.moduleCat_range_eq_ker.symm)
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)

lemma finite_range_of_exact {A B C D : ModuleCat.{u} R}
    (p : A ⟶ B) (δ : B ⟶ C) (f : B ⟶ D) (w : p ≫ δ=0)
    (hex : (ShortComplex.mk p δ w).Exact) (hpf : p ≫ f=0)
    [Module.Finite R C] : Module.Finite R (LinearMap.range f.hom) := by
  have : Module.Finite R (LinearMap.range δ.hom) :=
    Module.Finite.of_injective (LinearMap.range δ.hom).subtype Subtype.val_injective
  have : Module.Finite R (B ⧸ LinearMap.ker δ.hom) :=
    Module.Finite.equiv δ.hom.quotKerEquivRange.symm
  have hk : LinearMap.ker δ.hom ≤ LinearMap.ker f.hom := by
    rw [← hex.moduleCat_range_eq_ker]
    exact LinearMap.range_le_ker_iff.mpr (ModuleCat.hom_ext_iff.mp hpf)
  let φ : (B ⧸ LinearMap.ker δ.hom) →ₗ[R] LinearMap.range f.hom :=
    (LinearMap.ker δ.hom).liftQ f.hom.rangeRestrict (by
      intro x hx
      exact Subtype.ext (hk hx))
  exact Module.Finite.of_surjective φ (by
    rintro ⟨y,x,rfl⟩
    exact ⟨(LinearMap.ker δ.hom).mkQ x,rfl⟩)

end

open BoundedHomologyEdge
variable {R G : Type} [CommRing R] [IsNoetherianRing R] [Group G]

variable {Z₁ Z₂ Z₃ C₀ C₁ C₂ C₃ C₄ : Rep R G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {i₃ : Z₃ ⟶ C₃} {p₃ : C₃ ⟶ Z₂}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0} {w₃ : i₃ ≫ p₃ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (h₃ : (ShortComplex.mk i₃ p₃ w₃).ShortExact)
  (e : C₄ ⟶ Z₃) [Epi e]

include h₁ h₂ h₃ e

lemma finite_H2 [Module.Finite R (groupHomology C₀ 2)]
    [Module.Finite R (groupHomology C₄ 0)]
    (hz₃ : IsZero (groupHomology C₃ 1))
    (hd : Hmap 2 (p₂ ≫ i₁)=0) : Module.Finite R (groupHomology C₁ 2) := by
  have : Module.Finite R ((groupHomology.functor R G 0).obj C₄) :=
    ‹Module.Finite R (groupHomology C₄ 0)›
  have : Module.Finite R ((groupHomology.functor R G 2).obj C₀) :=
    ‹Module.Finite R (groupHomology C₀ 2)›
  let : Epi (Hmap 0 e) := epi_Hmap_zero e
  have : Module.Finite R (groupHomology Z₃ 0) :=
    Module.Finite.of_surjective (Hmap 0 e).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  let : Mono (groupHomology.δ h₃ 1 0 rfl) :=
    (exact₃ h₃ 0).mono_g_iff.mpr (hz₃.eq_zero_of_src _)
  have : Module.Finite R (groupHomology Z₂ 1) :=
    Module.Finite.of_injective (groupHomology.δ h₃ 1 0 rfl).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite R (LinearMap.range (Hmap 2 i₁).hom) :=
    finite_range_of_exact (Hmap 2 p₂) (groupHomology.δ h₂ 2 1 rfl) (Hmap 2 i₁)
      (groupHomology.mapShortComplex₃ h₂ rfl).zero (exact₃ h₂ 1)
      (by rw [← Hmap_comp]; exact hd)
  exact finite_of_exact (X:=ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.range (Hmap 2 i₁).hom).subtype) (Hmap 2 p₁)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Hmap 2 p₁).hom x.val=0
      exact (show LinearMap.range (Hmap 2 i₁).hom ≤ LinearMap.ker (Hmap 2 p₁).hom by
        rw [(exact₂ h₁ 2).moduleCat_range_eq_ker]) x.property))
    (by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa using (exact₂ h₁ 2).moduleCat_range_eq_ker)

end FiniteHomologyReturn

end OAI
