import OAI.AlgebraicGeometry.SurfaceCones.CartierSupport

namespace OAI

/-!
# Global denominator clearing for coherent lattices

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
private local instance gluingSectionModule {Z : Scheme.{0}} (M : Z.Modules)
    (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance gluingCoherentSectionModule {Z : Scheme.{0}} (M : CoherentGlobal.Coh Z)
    (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

open ActualSheafTensor CoherentGlobal Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [CompactSpace Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

/-- Restrict a slice-site module morphism to a smaller open. -/
def restrictOverHom {M N : Y.Modules} {U V : Y.Opens} (h : V ≤ U)
    (a : M.over U ⟶ N.over U) : M.over V ⟶ N.over V :=
  ((SheafOfModules.overFunctorMap Y.ringCatSheaf (homOfLE h)).app M).inv ≫
    (SheafOfModules.overMap Y.ringCatSheaf (homOfLE h)).map a ≫
      ((SheafOfModules.overFunctorMap Y.ringCatSheaf (homOfLE h)).app N).hom

include d in
/-- Denominator-cleared local extensions of a fixed Cartier-puncture morphism
agree on overlaps and glue. -/
lemma exists_gluing_of_puncture {ι : Type*} (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤)
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ⟶
      N.over (ActualOpenSupport.complement g))
    (a : ∀ i, M.over (U i) ⟶ N.over (U i))
    (ha : ∀ i (V : Y.Opens) (hi : V ≤ U i)
      (hV : V ≤ ActualOpenSupport.complement g) (x : M.val.obj (op V)),
      (a i).val.app (op (Over.mk (homOfLE hi))) x =
        e.val.app (op (Over.mk (homOfLE hV))) x) :
    ∃ f : M ⟶ N, ∀ i, f.over (U i) = a i := by
  let : IsNoetherian Y := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Y := IsNoetherian.noetherianSpace
  apply SheafHomGluing.exists_gluing_hom M N U hU a
  intro i j V hi hj x
  have : CompactSpace V.toScheme := by
    exact @TopologicalSpace.NoetherianSpace.compactSpace (↥(V : Set Y)) _
      (TopologicalSpace.NoetherianSpace.set (V : Set Y))
  let A := restrictOverHom (M := M) (N := N) hi (a i)
  let B := restrictOverHom (M := M) (N := N) hj (a j)
  have hAB : A = B := by
    apply over_hom_ext_of_puncture g d V M N hN A B
    intro W hWV hW w
    exact (ha i W (hWV.trans hi) hW w).trans (ha j W (hWV.trans hj) hW w).symm
  exact congrArg (fun q : M.over V ⟶ N.over V =>
    q.val.app (op (Over.mk (𝟙 V))) x) hAB

include d in
/-- Injective local extensions glue to an injective global extension. -/
lemma exists_mono_gluing_of_puncture {ι : Type*} (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤)
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ⟶
      N.over (ActualOpenSupport.complement g))
    (a : ∀ i, M.over (U i) ⟶ N.over (U i)) [∀ i, Mono (a i)]
    (ha : ∀ i (V : Y.Opens) (hi : V ≤ U i)
      (hV : V ≤ ActualOpenSupport.complement g) (x : M.val.obj (op V)),
      (a i).val.app (op (Over.mk (homOfLE hi))) x =
        e.val.app (op (Over.mk (homOfLE hV))) x) :
    ∃ f : M ⟶ N, Mono f ∧ ∀ i, f.over (U i) = a i := by
  obtain ⟨f, hf⟩ := exists_gluing_of_puncture g d U hU M N hN e a ha
  refine ⟨f, ?_, hf⟩
  apply SheafLocality.module_mono_of_coversTop Y.ringCatSheaf
    ((Opens.coversTop_iff Y _).mpr hU) f
  intro j
  change Mono (f.over (U j))
  rw [hf j]
  infer_instance
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open ActualSheafTensor CoherentGlobal Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [CompactSpace Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

include d in
/-- Compatible injective local extensions of a puncture morphism
glue to an injective global extension of that morphism. -/
lemma exists_mono_extension_of_local {ι : Type*} (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤)
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ⟶
      N.over (ActualOpenSupport.complement g))
    (a : ∀ i, M.over (U i) ⟶ N.over (U i)) [∀ i, Mono (a i)]
    (ha : ∀ i (V : Y.Opens) (hi : V ≤ U i)
      (hV : V ≤ ActualOpenSupport.complement g) (x : M.val.obj (op V)),
      (a i).val.app (op (Over.mk (homOfLE hi))) x =
        e.val.app (op (Over.mk (homOfLE hV))) x) :
    ∃ f : M ⟶ N, Mono f ∧ f.over (ActualOpenSupport.complement g) = e := by
  obtain ⟨f, hfmono, hf⟩ := exists_mono_gluing_of_puncture g d U hU M N hN e a ha
  refine ⟨f, hfmono, ?_⟩
  apply SheafHomGluing.over_eq_of_local_values U hU M N _ e f
  intro i V hi hV x
  exact (congrArg (fun q : M.over (U i) ⟶ N.over (U i) =>
    q.val.app (op (Over.mk (homOfLE hi))) x) (hf i)).trans (ha i V hi hV x)

include d in
/-- A finite cover admits a single bound for all local extension
exponents. Every exponent beyond that bound gives a global
injective extension preserving its specified puncture map. -/
lemma exists_uniform_mono_extension {ι : Type*} [Fintype ι] (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (M : ℕ → Y.Modules) (N : Y.Modules)
    [∀ n, (M n).IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : ∀ n, (M n).over (ActualOpenSupport.complement g) ⟶
      N.over (ActualOpenSupport.complement g))
    (hloc : ∀ i, ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : (M n).over (U i) ⟶ N.over (U i), Mono a ∧
        ∀ (V : Y.Opens) (hi : V ≤ U i)
          (hV : V ≤ ActualOpenSupport.complement g) (x : (M n).val.obj (op V)),
          a.val.app (op (Over.mk (homOfLE hi))) x =
            (e n).val.app (op (Over.mk (homOfLE hV))) x) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ f : M n ⟶ N, Mono f ∧ f.over (ActualOpenSupport.complement g) = e n := by
  classical
  choose k hk using hloc
  refine ⟨Finset.univ.sup k, fun n hn => ?_⟩
  have hi (i : ι) : k i ≤ n :=
    (Finset.le_sup (f := k) (Finset.mem_univ i)).trans hn
  choose a ha hcomp using fun i => hk i n (hi i)
  let (i : ι) : Mono (a i) := ha i
  exact exists_mono_extension_of_local g d U hU (M n) N hN (e n) a hcomp
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules ActualSheafTensor CartierImageFiltration
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
lemma idealAction_isIso_of_isIso {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) [IsIso i] (M : SheafOfModules.{u} (ringSheaf R)) :
    IsIso ((idealAction R i).app M) := by
  change IsIso (((tensorLeftIso R (asIso i)) ≪≫ tensorUnitLeftIso R).app M).hom
  infer_instance
end ActualSheafTensor
namespace CartierImageFiltration
universe u v
variable {C : Type u} [Category.{v} C] (T : C ⥤ C) (a : T ⟶ 𝟭 C)
lemma powerAction_isIso (h : ∀ M, IsIso (a.app M)) (n : ℕ) (M : C) :
    IsIso ((powerAction T a n).app M) := by
  induction n generalizing M with
  | zero => exact inferInstanceAs (IsIso (𝟙 M))
  | succ n ih =>
    change IsIso ((powerAction T a n).app (T.obj M) ≫ a.app M)
    have := ih (T.obj M)
    have := h M
    infer_instance
end CartierImageFiltration
private lemma kernel_ι_isIso_of_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B : C} (q : A ⟶ B) [HasKernel q] (hq : q = 0) : IsIso (kernel.ι q) := by
  subst q
  infer_instance
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- The kernel ideal of a closed part becomes the unit ideal on
its open complement. This uses the pushforward sections. -/
lemma ideal_puncture_isIso (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊥) :
    IsIso ((restrictFunctor U.ι).map (idealι f)) := by
  let F := restrictFunctor U.ι
  have : PreservesFiniteLimits F := CoherentRestriction.preservesFiniteLimits U.ι
  have hz := pushforward_restrict_isZero f (SheafOfModules.unit X.ringCatSheaf) U hU
  have he : F.map (structureMap f) = 0 := hz.eq_of_tgt _ _
  have hh : F.map (idealι f) =
      (PreservesKernel.iso F (structureMap f)).hom ≫ kernel.ι (F.map (structureMap f)) := by
    exact (Iso.inv_comp_eq (PreservesKernel.iso F (structureMap f))).mp
      (PreservesKernel.iso_inv_ι F (structureMap f))
  have hk : IsIso (kernel.ι (F.map (structureMap f))) := kernel_ι_isIso_of_zero _ he
  rw [hh]
  exact IsIso.comp_isIso' (PreservesKernel.iso F (structureMap f)).isIso_hom hk

/-- Every Cartier tensor power is invertible on the geometric
puncture. In particular, a cleared lattice map retaining the original
puncture identification really is an isomorphism there. -/
lemma ideal_power_puncture_isIso (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊥)
    (n : ℕ) (M : Y.Modules) :
    IsIso ((restrictFunctor U.ι).map
      ((powerAction (tensorLeft Y.sheaf (idealSheaf f))
        (idealAction Y.sheaf (idealι f)) n).app M)) := by
  let F := restrictFunctor U.ι
  let T := tensorLeft Y.sheaf (idealSheaf f)
  let S := tensorLeft U.toScheme.sheaf (F.obj (idealSheaf f))
  have : IsIso (F.map (idealι f)) := ideal_puncture_isIso f U hU
  have hi : IsIso (restrictedIdeal U.ι (idealι f)) := by
    exact IsIso.comp_isIso' (ideal_puncture_isIso f U hU) (restrictUnitIso U.ι).isIso_hom
  have hp : ∀ N, IsIso ((idealAction U.toScheme.sheaf
      (restrictedIdeal U.ι (idealι f))).app N) := fun N =>
    @idealAction_isIso_of_isIso _ _ _ _ _ _ _ _ hi N
  have ha := powerAction_isIso S _ hp n (F.obj M)
  erw [← powerComparison_action T S F (tensorOpenRestrictNatIso U.ι _)
    (idealAction Y.sheaf (idealι f)) (idealAction U.toScheme.sheaf
      (restrictedIdeal U.ι (idealι f))) (tensorOpenRestrict_action U.ι (idealι f))]
  exact IsIso.comp_isIso'
    (powerComparison T S F (tensorOpenRestrictNatIso U.ι (idealSheaf f)) n M).isIso_hom ha
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open ActualSheafTensor CoherentGlobal Scheme.Modules CartierImageFiltration
variable {X Y : Scheme.{0}}

/-- Isomorphy on a open subscheme and on its slice site
are equivalent, using the restriction comparison equivalence. -/
lemma over_isIso_iff_restrict (U : Y.Opens) {M N : Y.Modules} (a : M ⟶ N) :
    IsIso (a.over U) ↔ IsIso ((restrictFunctor U.ι).map a) :=
  (isIso_iff_of_reflects_iso (a.over U) (overEquiv U).functor).symm.trans
    (NatIso.isIso_map_iff (overFunctorEquiv U) a)

/-- The geometric complement has empty inverse image. -/
lemma preimage_complement (g : X ⟶ Y) [IsClosedImmersion g] :
    g ⁻¹ᵁ ActualOpenSupport.complement g = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (hx ⟨x, rfl⟩).elim

/-- All powers of the Cartier ideal preserve coherence. -/
lemma coherent_power_tensor_line (L : Y.Modules)
    (d : LineTrivialization Y.sheaf L) (n : ℕ)
    (M : Y.Modules) [M.IsFinitePresentation] :
    ((power (tensorLeft Y.sheaf L) n).obj M).IsFinitePresentation := by
  induction n generalizing M with
  | zero => exact inferInstanceAs M.IsFinitePresentation
  | succ n ih =>
    have := coherent_tensor_line L M d
    exact ih ((tensorLeft Y.sheaf L).obj M)

/-- A global extension retaining a puncture identification is an isomorphism on the puncture. -/
lemma cleared_extension_puncture_isIso (g : X ⟶ Y) [IsClosedImmersion g]
    (M N : Y.Modules) (n : ℕ)
    (e : M.over (ActualOpenSupport.complement g) ≅ N.over (ActualOpenSupport.complement g))
    (a : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M ⟶ N)
    (ha : a.over (ActualOpenSupport.complement g) =
      ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
        (idealAction Y.sheaf (idealι g)) n).app M).over (ActualOpenSupport.complement g) ≫ e.hom) :
    IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a) := by
  let U := ActualOpenSupport.complement g
  have h := ideal_power_puncture_isIso g U (preimage_complement g) n M
  have : IsIso (((powerAction (tensorLeft Y.sheaf (idealSheaf g))
      (idealAction Y.sheaf (idealι g)) n).app M).over U) :=
    (over_isIso_iff_restrict U _).mpr h
  apply (over_isIso_iff_restrict U a).mp
  rw [ha]
  infer_instance
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open ActualSheafTensor CoherentGlobal Scheme.Modules CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [CompactSpace Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

include d in
/-- The local-to-global part of coherent denominator clearing, with the
ideal twist and the geometric puncture. Local bounds are
uniformized, overlap compatibility is proved by torsion freeness, maps
are glued, and the resulting cokernel is supported on the divisor.
The local extension property itself must still be supplied, for instance
by transporting the proved affine denominator-clearing theorem. -/
lemma exists_global_cleared_extension_of_local_bounds
    {ι : Type*} [Fintype ι] (U : ι → Y.Opens) (hU : (⨆ i, U i) = ⊤)
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g))
    (hloc : ∀ i, ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : ((power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M).over (U i) ⟶ N.over (U i),
        Mono a ∧ ∀ (V : Y.Opens) (hi : V ≤ U i)
          (hV : V ≤ ActualOpenSupport.complement g)
          (x : ((power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M).val.obj (op V)),
          a.val.app (op (Over.mk (homOfLE hi))) x =
            (((powerAction (tensorLeft Y.sheaf (idealSheaf g))
              (idealAction Y.sheaf (idealι g)) n).app M).over
                (ActualOpenSupport.complement g) ≫ e.hom).val.app
                  (op (Over.mk (homOfLE hV))) x) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M ⟶ N,
        Mono a ∧
        a.over (ActualOpenSupport.complement g) =
          ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
            (idealAction Y.sheaf (idealι g)) n).app M).over (ActualOpenSupport.complement g) ≫ e.hom ∧
        IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a) := by
  let P (n : ℕ) := (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M
  let (n : ℕ) : (P n).IsFinitePresentation :=
    coherent_power_tensor_line (idealSheaf g) d n M
  let ep (n : ℕ) : (P n).over (ActualOpenSupport.complement g) ⟶
      N.over (ActualOpenSupport.complement g) :=
    ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
       (idealAction Y.sheaf (idealι g)) n).app M).over (ActualOpenSupport.complement g) ≫ e.hom
  obtain ⟨k, hk⟩ := exists_uniform_mono_extension g d U hU P N hN ep hloc
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, ha, hae⟩ := hk n hn
  exact ⟨a, ha, hae, cleared_extension_puncture_isIso g M N n e a hae⟩
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualOpenModules
open Scheme.Modules
variable {X Y : Scheme.{0}}

/-- Restriction along a scheme isomorphism is an equivalence of
its module sheaf categories. -/
def isoRestrictEquiv (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId.symm ≪≫
      (restrictFunctorCongr e.inv_hom_id).symm) ≪≫ restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫
      restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId)

/-- The modules on any open-immersion chart are exactly the modules
on the target's slice site at its image open. -/
def chartEquiv (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules (Y.ringCatSheaf.over f.opensRange) ≌ X.Modules :=
  (overEquiv f.opensRange).trans (isoRestrictEquiv f.isoOpensRange)

/-- The chart equivalence intertwines global restriction with slice-site restriction. -/
def chartRestrictionIso (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.overFunctor Y.ringCatSheaf f.opensRange ⋙ (chartEquiv f).functor ≅
      restrictFunctor f :=
  Functor.isoWhiskerRight (overFunctorEquiv f.opensRange) (restrictFunctor f.isoOpensRange.hom) ≪≫
      (restrictFunctorComp f.isoOpensRange.hom f.opensRange.ι).symm ≪≫
        restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι f)

/-- Transfer a chart morphism to the target slice site by the fully faithful inverse. -/
def chartMap (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    M.over f.opensRange ⟶ N.over f.opensRange :=
  (chartEquiv f).functor.preimage
    (((chartRestrictionIso f).app M).hom ≫ a ≫ ((chartRestrictionIso f).app N).inv)

lemma chartMap_fac (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    (chartEquiv f).functor.map (chartMap f a) =
      ((chartRestrictionIso f).app M).hom ≫ a ≫ ((chartRestrictionIso f).app N).inv := by
  exact (chartEquiv f).functor.map_preimage _

lemma chartMap_mono (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) [Mono a] :
    Mono (chartMap f a) := by
  apply (chartEquiv f).functor.mono_of_mono_map
  rw [chartMap_fac]
  infer_instance
/-- Transferring a restricted global morphism recovers its slice-site restriction. -/
lemma chartMap_restrict (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (a : M ⟶ N) : chartMap f ((restrictFunctor f).map a) = a.over f.opensRange := by
  apply (chartEquiv f).functor.map_injective
  rw [chartMap_fac]
  have h := (chartRestrictionIso f).hom.naturality a
  change ((chartRestrictionIso f).hom.app M ≫ (restrictFunctor f).map a) ≫
    (chartRestrictionIso f).inv.app N = _
  erw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

end ActualOpenModules


namespace ActualOpenModules
open Scheme.Modules Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
lemma image_eq (U : X.Opens) :
    f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U) = f ''ᵁ U := by
  simp only [← Scheme.Hom.comp_image, Scheme.Hom.isoOpensRange_hom_ι]

private lemma over_hom_component (M : Y.Modules) (V : Y.Opens) (U : V.toScheme.Opens)
    (x : M.val.obj (op (V.ι ''ᵁ U))) :
    (((overFunctorEquiv V).hom.app M).app U).hom x = x := rfl
private lemma over_inv_component (M : Y.Modules) (V : Y.Opens) (U : V.toScheme.Opens)
    (x : M.val.obj (op (V.ι ''ᵁ U))) :
    (((overFunctorEquiv V).inv.app M).app U).hom x = x := rfl
private lemma restrict_map_component {Z : Scheme.{0}} (g : Z ⟶ Y) [IsOpenImmersion g]
    {M N : Y.Modules} (a : M ⟶ N) (U : Z.Opens) (x : M.val.obj (op (g ''ᵁ U))) :
    (((restrictFunctor g).map a).app U).hom x = (a.app (g ''ᵁ U)).hom x := rfl

private lemma over_hom_eq (M : Y.Modules) (V : Y.Opens) (U : V.toScheme.Opens) :
    (((overFunctorEquiv V).hom.app M).app U) = 𝟙 (M.presheaf.obj (op (V.ι ''ᵁ U))) := rfl
private lemma restrict_map_eq {Z : Scheme.{0}} (g : Z ⟶ Y) [IsOpenImmersion g]
    {M N : Y.Modules} (a : M ⟶ N) (U : Z.Opens) :
    (((restrictFunctor g).map a).app U) = a.app (g ''ᵁ U) := rfl

private lemma module_associator_component {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ X.Modules) (M : C) (U : X.Opens) :
    (((Functor.associator F G H).inv.app M).app U) = 𝟙 _ := rfl

private lemma chart_object (M : Y.Modules) (U : X.Opens) :
    (((SheafOfModules.overFunctor Y.ringCatSheaf f.opensRange ⋙
      (overEquiv f.opensRange).functor ⋙ restrictFunctor f.isoOpensRange.hom).obj M).presheaf.obj (op U)) =
        M.presheaf.obj (op (f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U))) := rfl


lemma chartRestriction_hom_apply (M : Y.Modules) (U : X.Opens)
    (x : M.val.obj (op (f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U)))) :
    ((((chartRestrictionIso f).hom.app M).app U).hom x) =
      M.val.map (eqToHom (image_eq f U).symm).op x := by
  let V := f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U)
  let W := (f.isoOpensRange.hom ≫ f.opensRange.ι) ''ᵁ U
  have h₁ : W = V := by dsimp [W, V]; rw [Scheme.Hom.comp_image]
  have h₂ : f ''ᵁ U = W := (image_eq f U).symm.trans h₁.symm
  change M.presheaf.map (eqToHom h₂).op (M.presheaf.map (eqToHom h₁).op x) =
    M.presheaf.map (eqToHom (image_eq f U).symm).op x
  have he : (eqToHom h₁).op ≫ (eqToHom h₂).op =
      (eqToHom (image_eq f U).symm).op := Subsingleton.elim _ _
  exact ConcreteCategory.congr_hom
    ((M.presheaf.map_comp _ _).symm.trans (congrArg M.presheaf.map he)) x

end ActualOpenModules

namespace ActualOpenModules
open Scheme.Modules Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
lemma chartMap_fac_hom {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) :
    (chartEquiv f).functor.map (chartMap f a) ≫ (chartRestrictionIso f).hom.app N =
      (chartRestrictionIso f).hom.app M ≫ a := by
  apply (Iso.eq_comp_inv ((chartRestrictionIso f).app N)).mp
  exact (chartMap_fac f a).trans (Category.assoc _ _ _).symm
end ActualOpenModules

namespace ActualOpenModules
open Scheme.Modules Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
lemma chartFunctor_apply {M N : Y.Modules} (b : M.over f.opensRange ⟶ N.over f.opensRange)
    (U : X.Opens)
    (x : M.val.obj (op (f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U)))) :
    ((chartEquiv f).functor.map b).val.app (op U) x =
      b.val.app (op (Over.mk (homOfLE (f.opensRange.ι_image_le _)))) x := rfl

private lemma raw_comp_apply {P Q R : X.Modules} (b : P ⟶ Q) (c : Q ⟶ R)
    (U : X.Opens) (x : P.val.obj (op U)) :
    (b ≫ c).val.app (op U) x = c.val.app (op U) (b.val.app (op U) x) := rfl

private lemma raw_chartRestriction_hom_apply (M : Y.Modules) (U : X.Opens)
    (x : M.val.obj (op (f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U)))) :
    ((chartRestrictionIso f).hom.app M).val.app (op U) x =
      M.val.map (eqToHom (image_eq f U).symm).op x :=
  chartRestriction_hom_apply f M U x

lemma chartMap_relation {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) (U : X.Opens)
    (x : M.val.obj (op (f.opensRange.ι ''ᵁ (f.isoOpensRange.hom ''ᵁ U)))) :
    N.val.map (eqToHom (image_eq f U).symm).op
      ((chartMap f a).val.app (op (Over.mk (homOfLE (f.opensRange.ι_image_le _)))) x) =
      (a.app U).hom (M.val.map (eqToHom (image_eq f U).symm).op x) := by
  have h := congrArg (fun b => b.val.app (op U) x) (chartMap_fac_hom f a)
  have h₁ := raw_chartRestriction_hom_apply f N U
    ((chartMap f a).val.app (op (Over.mk (homOfLE (f.opensRange.ι_image_le _)))) x)
  have h₂ := raw_chartRestriction_hom_apply f M U x
  exact h₁.symm.trans (h.trans (congrArg (fun z => a.val.app (op U) z) h₂))


end ActualOpenModules

namespace ActualOpenModules
open Scheme.Modules Opposite
variable {X Y : Scheme.{0}}
lemma over_eq_naturality {M N : Y.Modules} {W V V' : Y.Opens}
    (hV : V ≤ W) (hV' : V' ≤ W) (h : V = V') (b : M.over W ⟶ N.over W)
    (x : M.val.obj (op V)) :
    N.val.map (eqToHom h.symm).op (b.val.app (op (Over.mk (homOfLE hV))) x) =
      b.val.app (op (Over.mk (homOfLE hV')))
        (M.val.map (eqToHom h.symm).op x) := by
  let q : Over.mk (homOfLE hV') ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (eqToHom h.symm) (by subsingleton)
  exact (ConcreteCategory.congr_hom (b.val.naturality q.op) x).symm

lemma eq_map_cancel (M : Y.Modules) {V V' : Y.Opens} (h : V = V')
    (x : M.val.obj (op V')) :
    M.val.map (eqToHom h.symm).op (M.val.map (eqToHom h).op x) = x := by
  subst V'
  simp only [eqToHom_refl, op_id, PresheafOfModules.map_id]
  rfl

variable (f : X ⟶ Y) [IsOpenImmersion f]
lemma chartMap_apply {M N : Y.Modules}
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N) (U : X.Opens)
    (x : M.val.obj (op (f ''ᵁ U))) :
    (chartMap f a).val.app (op (Over.mk (homOfLE (f.image_le_opensRange U)))) x =
      (a.app U).hom x := by
  let y := M.val.map (eqToHom (image_eq f U)).op x
  have h := chartMap_relation f a U y
  erw [over_eq_naturality (f.opensRange.ι_image_le _) (f.image_le_opensRange U)
    (image_eq f U) (chartMap f a)] at h
  have hy : M.val.map (eqToHom (image_eq f U).symm).op y = x := by
    exact eq_map_cancel M (image_eq f U) x
  erw [hy] at h
  exact h
end ActualOpenModules

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualOpenModules
open Scheme.Modules Opposite
variable {X Y : Scheme.{0}}
lemma component_eq_transport {M N : Y.Modules} {V V' W W' : Y.Opens}
    (a : M.over W ⟶ N.over W) (b : M.over W' ⟶ N.over W')
    (h : V = V') (hV : V ≤ W) (hV' : V ≤ W')
    (h1 : V' ≤ W) (h2 : V' ≤ W')
    (hab : ∀ x : M.val.obj (op V),
      a.val.app (op (Over.mk (homOfLE hV))) x =
      b.val.app (op (Over.mk (homOfLE hV'))) x) :
    ∀ x : M.val.obj (op V'), a.val.app (op (Over.mk (homOfLE h1))) x =
      b.val.app (op (Over.mk (homOfLE h2))) x := by
  subst V'
  exact hab

variable (f : X ⟶ Y) [IsOpenImmersion f]
/-- Chart transport preserves the fixed morphism on every open in the geometric puncture. -/
lemma chartMap_puncture_compat {M N : Y.Modules} (W : Y.Opens)
    (a : (restrictFunctor f).obj M ⟶ (restrictFunctor f).obj N)
    (b : M.over W ⟶ N.over W)
    (hab : a.over (f ⁻¹ᵁ W) =
      ActualOpenComparison.pullOverHom f (f ⁻¹ᵁ W) W (f.image_preimage_le W) b)
    (V : Y.Opens) (hi : V ≤ f.opensRange) (hV : V ≤ W)
    (x : M.val.obj (op V)) :
    (chartMap f a).val.app (op (Over.mk (homOfLE hi))) x =
      b.val.app (op (Over.mk (homOfLE hV))) x := by
  have heq : f ''ᵁ (f ⁻¹ᵁ V) = V := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hi]
  apply component_eq_transport (chartMap f a) b heq
    (f.image_le_opensRange _) ((f.image_preimage_le V).trans hV) hi hV _ x
  intro y
  rw [chartMap_apply]
  let q := op (Over.mk (homOfLE (f.preimage_mono hV)))
  have hh := congrArg (fun k => k.val.app q y) hab
  exact hh
end ActualOpenModules

namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open ActualSheafTensor CoherentGlobal Scheme.Modules CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [CompactSpace Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))
include d

/-- Global coherent denominator clearing along the Cartier ideal
uses finite affine bounds and agreement on overlaps. -/
lemma exists_global_cleared_extension
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (M.val.obj V))
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M ⟶ N,
        Mono a ∧
        a.over (ActualOpenSupport.complement g) =
          ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
            (idealAction Y.sheaf (idealι g)) n).app M).over (ActualOpenSupport.complement g) ≫ e.hom ∧
        IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a) := by
  let c := d.finiteAffineCover
  apply exists_global_cleared_extension_of_local_bounds g d
    (fun i => (c.f i).opensRange) c.cover M N hN e
  intro i
  obtain ⟨k, hk⟩ := exists_chart_global_power_sandwich g (c.f i) (c.iso i) M N hM hN e
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, b, ha, hb, hae, hbe⟩ := hk n hn
  let := ha
  refine ⟨ActualOpenModules.chartMap (c.f i) a,
    ActualOpenModules.chartMap_mono (c.f i) a, ?_⟩
  intro V hi hV x
  apply ActualOpenModules.chartMap_puncture_compat (c.f i)
    (ActualOpenSupport.complement g) a _ ?_ V hi hV x
  erw [ActualOpenComparison.pullOverHom_comp, ActualOpenComparison.pullOverHom_global]
  exact hae

/-- The two-sided global Cartier lattice sandwich uses one bound
for every larger power and retains the fixed puncture identification. -/
lemma exists_global_power_sandwich
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (M.val.obj V))
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let T := tensorLeft Y.sheaf (idealSheaf g)
    let act := idealAction Y.sheaf (idealι g)
    let W := ActualOpenSupport.complement g
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ (a : (power T n).obj M ⟶ N) (b : (power T n).obj N ⟶ M),
        Mono a ∧ Mono b ∧
        a.over W = ((powerAction T act n).app M).over W ≫ e.hom ∧
        b.over W = ((powerAction T act n).app N).over W ≫ e.inv ∧
        IsIso ((restrictFunctor W.ι).map a) ∧
        IsIso ((restrictFunctor W.ι).map b) := by
  obtain ⟨k, hk⟩ := exists_global_cleared_extension g d M N hM hN e
  obtain ⟨l, hl⟩ := exists_global_cleared_extension g d N M hN hM e.symm
  refine ⟨max k l, fun n hn => ?_⟩
  obtain ⟨a, ha, hae, hai⟩ := hk n ((le_max_left _ _).trans hn)
  obtain ⟨b, hb, hbe, hbi⟩ := hl n ((le_max_right _ _).trans hn)
  exact ⟨a, b, ha, hb, hae, hbe, hai, hbi⟩
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open CoherentGlobal ActualSheafTensor CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
    (d : LineTrivialization Y.sheaf (idealSheaf g))

/-- A lattice embedding gives the divisor Grothendieck identity.
Torsion freeness descends from the target, and the cokernel supplies
the finite filtration by supported layers. -/
lemma embedding_puncture_identity {M N : Coh Y} (a : M ⟶ N) [Mono a]
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.obj.val.obj U))
    [IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map a))] :
    ∃ n : ℕ, cls ((restriction g d).obj M) = cls ((restriction g d).obj N) +
      ((idealLayers g d n (cokernel a)).map fun Q =>
        cls (conormalTensor g d Q) - cls Q).sum := by
  let S : ShortComplex (Coh Y) := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
  have hM := SheafTorsion.subobject ((cohInclusion Y).map a) hN
  exact lattice_puncture_identity g d hS hM hN

/-- The divisor identity for a denominator-cleared morphism of coherent module sheaves. -/
lemma module_embedding_puncture_identity (M N : Y.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] (a : M ⟶ N) [Mono a]
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.val.obj U))
    [IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a)] :
    let M' : Coh Y := ⟨M, inferInstance⟩
    let N' : Coh Y := ⟨N, inferInstance⟩
    let a' : M' ⟶ N' := ObjectProperty.homMk a
    ∃ n : ℕ, cls ((restriction g d).obj M') = cls ((restriction g d).obj N') +
      ((idealLayers g d n (cokernel a')).map fun Q =>
        cls (conormalTensor g d Q) - cls Q).sum := by
  dsimp only
  let M' : Coh Y := ⟨M, inferInstance⟩
  let N' : Coh Y := ⟨N, inferInstance⟩
  let a' : M' ⟶ N' := ObjectProperty.homMk a
  have : Mono a' := (cohInclusion Y).mono_of_mono_map (f := a') (by
    change Mono a
    infer_instance)
  have : IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map a')) := by
    change IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a)
    infer_instance
  exact embedding_puncture_identity g d a' hN
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
attribute [local instance] gluingSectionModule gluingCoherentSectionModule
open ActualSheafTensor CartierImageFiltration CoherentGlobal CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

/-- The coherent sheaf obtained by twisting a coherent lattice by
a nonnegative Cartier ideal power. -/
def clearedLattice (n : ℕ) (M : Y.Modules) [M.IsFinitePresentation] : Coh Y :=
  ⟨(power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M,
    coherent_power_tensor_line (idealSheaf g) d n M⟩

/-- Lattices identified off the divisor give a finite quotient filtration,
epimorphisms from conormal twists, and the divisor Grothendieck identity. -/
lemma exists_cleared_lattice_identity
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let L : Coh Y := ⟨N, inferInstance⟩
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : clearedLattice g d n M ⟶ L,
        Mono a ∧
        ((cohInclusion Y).map a).over (ActualOpenSupport.complement g) =
          ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
            (idealAction Y.sheaf (idealι g)) n).app M).over
              (ActualOpenSupport.complement g) ≫ e.hom ∧
        IsZero ((cokernel a).obj.over (ActualOpenSupport.complement g)) ∧
        ∃ l : ℕ, IsZero (idealMultiple g d l (cokernel a)) ∧
          cls ((restriction g d).obj (clearedLattice g d n M)) =
            cls ((restriction g d).obj L) +
              ((idealLayers g d l (cokernel a)).map fun Q =>
                cls (conormalTensor g d Q) - cls Q).sum ∧
          ∀ j : ℕ, Epi (twistedLayerQuotient g d (cokernel.π a) j) := by
  dsimp only
  let L : Coh Y := ⟨N, inferInstance⟩
  obtain ⟨k, hk⟩ := exists_global_cleared_extension g d M N hM hN e
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, ha, hae, hai⟩ := hk n hn
  let := ha
  let := hai
  let a' : clearedLattice g d n M ⟶ L := ObjectProperty.homMk a
  have ha' : Mono a' := (cohInclusion Y).mono_of_mono_map (f := a') (by
    change Mono a
    infer_instance)
  let S : ShortComplex (Coh Y) :=
    ShortComplex.mk a' (cokernel.π a') (cokernel.condition a')
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a' }
  have : IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map S.f)) := by
    change IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map a)
    infer_instance
  have hs : IsZero ((cokernel a').obj.over (ActualOpenSupport.complement g)) :=
    quotient_supported_of_puncture_iso g hS
  obtain ⟨l, hl⟩ := exists_idealMultiple_isZero g d (cokernel a') hs
  refine ⟨a', ha', hae, hs, l, hl, ?_, fun _ => inferInstance⟩
  apply lattice_nilpotent_identity g d hS _ hN l hl
  exact SheafTorsion.subobject ((cohInclusion Y).map a') hN
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v
variable {C : Type u} [Category.{v} C]
  (T : C ⥤ C) (a : T ⟶ 𝟭 C)
/-- Reassociate ideal powers without changing their order. -/
def powerAddIso (n : ℕ) : (m : ℕ) → (M : C) →
    (power T (n + m)).obj M ≅ (power T n).obj ((power T m).obj M)
  | 0, _ => Iso.refl _
  | m + 1, M => powerAddIso n m (T.obj M)

/-- The action of an added power is the composite of the two power actions, with the canonical reassociation included. -/
lemma powerAction_add (m n : ℕ) (M : C) :
    (powerAddIso T n m M).hom ≫
        (powerAction T a n).app ((power T m).obj M) ≫
          (powerAction T a m).app M = (powerAction T a (n + m)).app M := by
  induction m generalizing M with
  | zero => simp [powerAddIso, powerAction, power]
  | succ m ih =>
    change (powerAddIso T n m (T.obj M)).hom ≫
        (powerAction T a n).app ((power T m).obj (T.obj M)) ≫
        ((powerAction T a m).app (T.obj M) ≫ a.app M) =
      (powerAction T a (n + m)).app (T.obj M) ≫ a.app M
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ a.app M) (ih (T.obj M))

/-- A pair of maps that is inverse after restricting the puncture gives a
power-action factorization there, including the canonical power
reassociation. This is the functorial calculation for the Cartier sandwich. -/
lemma power_sandwich_map {D : Type*} [Category D] (F : C ⥤ D)
    (n : ℕ) {M N : C} (e : F.obj M ≅ F.obj N)
    (f : (power T n).obj M ⟶ N) (g : (power T n).obj N ⟶ M)
    (hf : F.map f = F.map ((powerAction T a n).app M) ≫ e.hom)
    (hg : F.map g = F.map ((powerAction T a n).app N) ≫ e.inv) :
    F.map ((powerAddIso T n n N).hom ≫ (power T n).map g ≫ f) =
      F.map ((powerAction T a (n + n)).app N) := by
  have hn := congrArg (fun k => F.map k) ((powerAction T a n).naturality g)
  simp only [Functor.map_comp, Functor.id_map] at hn
  simp only [Functor.map_comp, hf]
  rw [← Category.assoc (F.map ((power T n).map g)), hn]
  simp only [hg, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  simpa only [Functor.map_comp] using
    congrArg (fun k => F.map k) (powerAction_add T a n n N)

end CartierImageFiltration


end

end OAI
