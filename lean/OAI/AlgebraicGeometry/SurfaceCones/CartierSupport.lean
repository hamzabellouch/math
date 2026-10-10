import OAI.AlgebraicGeometry.SurfaceCones.CartierPullback

namespace OAI

private local instance coherentSectionModule (X : AlgebraicGeometry.Scheme.{0})
    (M : CoherentGlobal.Coh X) (U : X.Opensᵒᵖ) :
    Module (X.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

private local instance schemeSectionModule (X : AlgebraicGeometry.Scheme.{0})
    (M : X.Modules) (U : X.Opensᵒᵖ) :
    Module (X.sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance schemeGammaModule (X : AlgebraicGeometry.Scheme.{0})
    (M : X.Modules) (U : X.Opens) :
    Module (X.presheaf.obj (Opposite.op U)) (M.val.obj (Opposite.op U)) :=
  (M.val.obj (Opposite.op U)).isModule

private theorem kernelMono {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {A B : C} (g : A ⟶ B)
    [CategoryTheory.Limits.HasKernel g] : CategoryTheory.Mono (CategoryTheory.Limits.kernel.ι g) :=
  CategoryTheory.Limits.equalizer.ι_mono

/-!
# Cartier support and elementary transformations

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g]
    (d : LineTrivialization Y.sheaf (idealSheaf g))
    {ι : Type} [Fintype ι] (R : ι → CommRingCat.{0})
    (f : ∀ j, Spec (R j) ⟶ Y) [∀ j, IsOpenImmersion (f j)]
    (hcover : (⨆ j, (f j).opensRange) = ⊤)
    (e : ∀ j, (restrictFunctor (f j)).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec (R j)).ringCatSheaf)
include hcover e

omit [IsLocallyNoetherian X] in
/-- A coherent sheaf supported on the Cartier divisor is killed
by an ideal power. Its support is specified only by vanishing on the
geometric complement of the closed immersion. -/
lemma exists_idealMultiple_isZero_of_complement (M : Coh Y)
    (hM : IsZero (M.obj.over (ActualOpenSupport.complement g))) :
    ∃ n : ℕ, IsZero (idealMultiple g d n M) := by
  apply exists_idealMultiple_isZero_of_support g d R f hcover e M
  intro j
  exact ActualOpenSupport.isZero_restrict_of_disjoint g (f j) M.obj hM _
    (chart_equation_disjoint g (f j) (e j))

/-- Divisor support, a short exact sequence and the Cartier line
give the divisor-side Grothendieck identity. -/
lemma lattice_complement_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (hQ : IsZero (S.X₃.obj.over (ActualOpenSupport.complement g))) :
    ∃ n : ℕ, cls ((restriction g d).obj S.X₁) = cls ((restriction g d).obj S.X₂) +
      ((idealLayers g d n S.X₃).map fun Q => cls (conormalTensor g d Q) - cls Q).sum := by
  obtain ⟨n, hn⟩ := exists_idealMultiple_isZero_of_complement g d R f hcover e S.X₃ hQ
  exact ⟨n, lattice_nilpotent_identity g d hS h₁ h₂ n hn⟩
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TopologicalSpace
namespace ActualSheafTensor
open Scheme.Modules

/-- Finite affine trivializations, with their ordinary ring schemes,
covering maps and module-sheaf isomorphisms. -/
structure FiniteAffineLineCover {Y : Scheme.{0}} (L : Y.Modules) where
  I : Type
  finite : Fintype I
  R : I → CommRingCat.{0}
  f : ∀ j, Spec (R j) ⟶ Y
  isOpen : ∀ j, IsOpenImmersion (f j)
  cover : (⨆ j, (f j).opensRange (H := isOpen j)) = ⊤
  iso : ∀ j, (@restrictFunctor (Spec (R j)) Y (f j) (isOpen j)).obj L ≅
    SheafOfModules.unit (Spec (R j)).ringCatSheaf
attribute [instance] FiniteAffineLineCover.finite FiniteAffineLineCover.isOpen

variable {Y : Scheme.{0}} {L : Y.Modules} (d : LineTrivialization Y.sheaf L)

private abbrev ChartIndex := Σ i : d.I, (Scheme.Opens.toScheme (d.obj i)).affineOpenCover.I₀
private abbrev chartRing (j : ChartIndex d) : CommRingCat.{0} :=
  (Scheme.Opens.toScheme (d.obj j.1)).affineOpenCover.X j.2
private def chartMap (j : ChartIndex d) : Spec (chartRing d j) ⟶ Y :=
  (Scheme.Opens.toScheme (d.obj j.1)).affineOpenCover.f j.2 ≫ (Scheme.Opens.ι (d.obj j.1))
private instance (j : ChartIndex d) : IsOpenImmersion (chartMap d j) := by
  delta chartMap
  infer_instance

private def chartIso (j : ChartIndex d) :
    (restrictFunctor (chartMap d j)).obj L ≅
      SheafOfModules.unit (Spec (chartRing d j)).ringCatSheaf :=
  (restrictFunctorComp _ _).app L ≪≫
    (restrictFunctor ((Scheme.Opens.toScheme (d.obj j.1)).affineOpenCover.f j.2)).mapIso
      (d.schemeIso L j.1) ≪≫
    restrictUnitIso ((Scheme.Opens.toScheme (d.obj j.1)).affineOpenCover.f j.2)

private lemma chartCover : (⨆ j, (chartMap d j).opensRange) = ⊤ := by
  apply le_antisymm le_top
  intro y _
  have hy : y ∈ ⨆ i, d.obj i := by
    rw [(Opens.coversTop_iff Y _).mp d.cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  let z : (Scheme.Opens.toScheme (d.obj i)) := ⟨y, hi⟩
  obtain ⟨j, x, hx⟩ := (Scheme.Opens.toScheme (d.obj i)).affineOpenCover.openCover.exists_eq z
  apply Opens.mem_iSup.mpr
  refine ⟨⟨i, j⟩, x, ?_⟩
  exact congrArg (fun w : (Scheme.Opens.toScheme (d.obj i)) => w.1) hx

/-- Quasi-compactness gives a finite affine refinement of a line-bundle trivializing cover. -/
def LineTrivialization.finiteAffineCover [CompactSpace Y] : FiniteAffineLineCover L := Classical.choice <| by
  classical
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun j : ChartIndex d => ((chartMap d j).opensRange : Set Y))
    (fun j => (chartMap d j).opensRange.isOpen) (by
      intro y _
      have h : y ∈ ⨆ j, (chartMap d j).opensRange := by rw [chartCover d]; trivial
      exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp h))
  refine ⟨⟨s, inferInstance, (fun j => chartRing d j.1), (fun j => chartMap d j.1),
    (fun j => inferInstance), ?_, (fun j => chartIso d j.1)⟩⟩
  apply le_antisymm le_top
  intro y _
  obtain ⟨j, hjs⟩ := Set.mem_iUnion.mp (hs (show y ∈ Set.univ from trivial))
  obtain ⟨hj, hy⟩ := Set.mem_iUnion.mp hjs
  exact Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hy⟩
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierConnecting
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Connecting morphism and exactness on the Cartier divisor. -/
structure Boundary (K Q : ShortComplex D) where
  δ : K.X₃ ⟶ Q.X₁
  zero_left : K.g ≫ δ = 0
  zero_right : δ ≫ Q.f = 0
  exact_left : (ShortComplex.mk K.g δ zero_left).Exact
  exact_right : (ShortComplex.mk δ Q.f zero_right).Exact
  exact_cokernels : Q.Exact

/-- The snake connecting morphism descends through a fully faithful
exact closed pushforward to the divisor category. -/
def boundary
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (K Q : ShortComplex D) (S₁ S₂ : ShortComplex C)
    (i : K.map J ⟶ S₁) (m : S₁ ⟶ S₂) (p : S₂ ⟶ Q.map J)
    (wi : i ≫ m = 0) (wp : m ≫ p = 0)
    (hi : IsLimit (KernelFork.ofι i wi))
    (hp : IsColimit (CokernelCofork.ofπ p wp))
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) : Boundary K Q := by
  let S : ShortComplex.SnakeInput C :=
    { L₀ := K.map J, L₁ := S₁, L₂ := S₂, L₃ := Q.map J
      v₀₁ := i, v₁₂ := m, v₂₃ := p, w₀₂ := wi, w₁₃ := wp
      h₀ := hi, h₃ := hp, L₁_exact := h₁.exact, epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact, mono_L₂_f := h₂.mono_f }
  have : Mono S.L₁.f := h₁.mono_f
  have : Epi S.L₂.g := h₂.epi_g
  let δ : K.X₃ ⟶ Q.X₁ := J.preimage S.δ
  have mapδ : J.map δ = S.δ := J.map_preimage _
  have z₂ : K.g ≫ δ = 0 := by
    apply J.map_injective
    rw [J.map_comp, J.map_zero, mapδ]
    exact S.L₀_g_δ
  have z₃ : δ ≫ Q.f = 0 := by
    apply J.map_injective
    rw [J.map_comp, J.map_zero, mapδ]
    exact S.δ_L₃_f
  have e₄ : Q.Exact := (Q.exact_map_iff_of_faithful J).mp S.L₃_exact
  have e₂ : (ShortComplex.mk K.g δ z₂).Exact := by
    apply ((ShortComplex.mk K.g δ z₂).exact_map_iff_of_faithful J).mp
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := S.L₁') (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 (J.obj K.X₂) ≫ J.map K.g = J.map K.g ≫ 𝟙 (J.obj K.X₃)
            simp)
        (by change 𝟙 (J.obj K.X₃) ≫ J.map δ = S.δ ≫ 𝟙 (J.obj Q.X₁)
            exact (Category.id_comp _).trans (mapδ.trans (Category.comp_id _).symm))) S.L₁'_exact
  have e₃ : (ShortComplex.mk δ Q.f z₃).Exact := by
    apply ((ShortComplex.mk δ Q.f z₃).exact_map_iff_of_faithful J).mp
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := S.L₂') (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 (J.obj K.X₃) ≫ J.map δ = S.δ ≫ 𝟙 (J.obj Q.X₁)
            exact (Category.id_comp _).trans (mapδ.trans (Category.comp_id _).symm))
        (by change 𝟙 (J.obj Q.X₁) ≫ J.map Q.f = J.map Q.f ≫ 𝟙 (J.obj Q.X₂)
            simp)) S.L₂'_exact
  exact ⟨δ, z₂, z₃, e₂, e₃, e₄⟩

namespace Boundary
variable {K Q : ShortComplex D} (b : Boundary K Q)

lemma mono_of_middle_isZero (hz : IsZero K.X₂) : Mono b.δ :=
  b.exact_left.mono_g (hz.eq_of_src _ _)

/-- The right-hand morphism in the elementary modification sequence. -/
def toQuotientKernel (_b : Boundary K Q) : Q.X₁ ⟶ kernel Q.g := kernel.lift Q.g Q.f Q.zero

instance epi_toQuotientKernel : Epi b.toQuotientKernel :=
  b.exact_cokernels.epi_kernelLift

lemma δ_toQuotientKernel : b.δ ≫ b.toQuotientKernel = 0 := by
  apply (cancel_mono (kernel.ι Q.g)).mp
  simp only [Category.assoc, toQuotientKernel, kernel.lift_ι, b.zero_right, zero_comp]

/-- The sequence firstTor(layer) → restriction(modification) →
kernel(restriction(E) → layer), before suppressing the harmless zero terms. -/
def modificationComplex : ShortComplex D :=
  ShortComplex.mk b.δ b.toQuotientKernel b.δ_toQuotientKernel

/-- Once the middle lattice is Cartier-regular, this is a short
exact elementary-modification sequence on the divisor. -/
lemma modification_shortExact (hz : IsZero K.X₂) :
    b.modificationComplex.ShortExact := by
  have : Mono b.δ := b.mono_of_middle_isZero hz
  have : Mono b.modificationComplex.f := (inferInstance : Mono b.δ)
  refine { exact := ?_
           mono_f := (show Mono b.δ from inferInstance)
           epi_g := (show Epi b.toQuotientKernel from inferInstance) }
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro W w hw
  change w ≫ b.toQuotientKernel = 0 at hw
  change W ⟶ Q.X₁ at w
  have hzero : w ≫ Q.f = 0 := by
    have he : b.toQuotientKernel ≫ kernel.ι Q.g = Q.f := kernel.lift_ι _ _ _
    rw [← he, ← Category.assoc]
    exact (congrArg (fun z => z ≫ kernel.ι Q.g) hw).trans zero_comp
  exact ⟨b.exact_right.lift w hzero, b.exact_right.lift_f w hzero⟩

end Boundary
end CartierConnecting


end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierConnecting
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The divisor-valued boundary obtained from an invertible-ideal
resolution, retaining its morphisms and exactness rather than just Euler classes. -/
def from_resolution
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (T : C ⥤ C) [T.PreservesZeroMorphisms]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (K Q : C ⥤ D) [K.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms]
    (κ : K ⋙ J ⟶ T) (ε : T ⟶ 𝟭 C) (π : 𝟭 C ⟶ Q ⋙ J)
    (zK : κ ≫ ε = 0) (zQ : ε ≫ π = 0)
    (hK : ∀ X, IsLimit (KernelFork.ofι (κ.app X) (NatTrans.congr_app zK X)))
    (hQ : ∀ X, IsColimit (CokernelCofork.ofπ (π.app X) (NatTrans.congr_app zQ X)))
    {S : ShortComplex C} (hS : S.ShortExact) : Boundary (S.map K) (S.map Q) := by
  let i := S.mapNatTrans κ
  let m := S.mapNatTrans ε
  let p := S.mapNatTrans π
  have wi : i ≫ m = 0 := by
    ext <;> exact NatTrans.congr_app zK _
  have wp : m ≫ p = 0 := by
    ext <;> exact NatTrans.congr_app zQ _
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply ShortComplex.isLimitOfIsLimitπ
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₁ wi).symm ?_
      exact hK S.X₁
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₂ wi).symm ?_
      exact hK S.X₂
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₃ wi).symm ?_
      exact hK S.X₃
  have hp : IsColimit (CokernelCofork.ofπ p wp) := by
    apply ShortComplex.isColimitOfIsColimitπ
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ wp).symm ?_
      exact hQ S.X₁
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ wp).symm ?_
      exact hQ S.X₂
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ wp).symm ?_
      exact hQ S.X₃
  exact boundary J (S.map K) (S.map Q) (S.map T) S
    i m p wi wp hi hp (hS.map_of_exact T) hS

/-- The kernel and cokernel functors supply the universal properties
used in `from_resolution`. -/
def from_kernels
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (T : C ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : T ⟶ 𝟭 C) (K Q : C ⥤ D) [K.Additive] [Q.Additive]
    (eK : K ⋙ J ≅ kernel a) (eQ : Q ⋙ J ≅ cokernel a)
    {S : ShortComplex C} (hS : S.ShortExact) : Boundary (S.map K) (S.map Q) := by
  let k : K ⋙ J ⟶ T := eK.hom ≫ kernel.ι a
  let q : 𝟭 C ⟶ Q ⋙ J := cokernel.π a ≫ eQ.inv
  have zk : k ≫ a = 0 := by simp [k]
  have zq : a ≫ q = 0 := by simp [q, ← Category.assoc]
  have hk (X : C) : IsLimit (KernelFork.ofι (k.app X) (NatTrans.congr_app zk X)) := by
    let E := (evaluation C C).obj X
    have h := isLimitOfHasKernelOfPreservesLimit E a
    apply IsLimit.ofIsoLimit h
    refine Fork.ext (eK.app X).symm ?_
    dsimp [k]
    simp
    rfl
  have hq (X : C) : IsColimit (CokernelCofork.ofπ (q.app X) (NatTrans.congr_app zq X)) := by
    let E := (evaluation C C).obj X
    have h := isColimitOfHasCokernelOfPreservesColimit E a
    apply IsColimit.ofIsoColimit h
    refine Cofork.ext (eQ.app X).symm ?_
    rfl
  exact from_resolution J T K Q k a q zk zq hk hq hS
end CartierConnecting

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- The ideal action constructs the connecting morphism
and exact sequences of coherent sheaves on the Cartier divisor. -/
def connecting {S : ShortComplex (Coh Y)} (hS : S.ShortExact) :
    CartierConnecting.Boundary (S.map (firstTor f d)) (S.map (restriction f d)) := by
  let T := coherentTensorLine (idealSheaf f) d
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  exact CartierConnecting.from_kernels (cohPushforward f) T (action f d)
    (firstTor f d) (restriction f d) (firstTorPushforwardIso f d)
    (restrictionPushforwardIso f d) hS

/-- The elementary modification sequence underlying the elementary transformation formula,
with first Tor retained as the divisor sheaf. -/
lemma modification_shortExact {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U)) :
    (connecting f d hS).modificationComplex.ShortExact :=
  (connecting f d hS).modification_shortExact (firstTor_isZero f d S.X₂ hM)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

instance restrictionUnit_supported_isIso (N : Coh X) :
    IsIso ((restrictionUnit f d).app ((cohPushforward f).obj N)) := by
  have : IsIso (((restrictionUnit f d).app ((cohPushforward f).obj N)).hom) :=
    CokernelCofork.IsColimit.isIso_π _ (restrictionUnitIsColimit f d _)
      (congrArg (fun k => k.hom) (action_pushforward_zero f d N))
  change IsIso ((cohInclusion Y).map ((restrictionUnit f d).app ((cohPushforward f).obj N))) at this
  exact isIso_of_reflects_iso ((restrictionUnit f d).app ((cohPushforward f).obj N))
    (cohInclusion Y)

/-- The canonical coherent counit, inverse to ordinary restriction's unit
on a supported sheaf. -/
def supportedCounitIso (N : Coh X) : (restriction f d).obj ((cohPushforward f).obj N) ≅ N :=
  (cohPushforward f).preimageIso (asIso ((restrictionUnit f d).app ((cohPushforward f).obj N))).symm

omit [IsLocallyNoetherian X] in
lemma unit_supported_counit (N : Coh X) :
    (restrictionUnit f d).app ((cohPushforward f).obj N) ≫
      (cohPushforward f).map (supportedCounitIso f d N).hom = 𝟙 _ := by
  simp [supportedCounitIso]

/-- The ambient quotient map for an elementary transform. -/
def modificationMap {E : Coh Y} {G : Coh X} (q : (restriction f d).obj E ⟶ G) :
    E ⟶ (cohPushforward f).obj G :=
  (restrictionUnit f d).app E ≫ (cohPushforward f).map q

instance modificationMap_epi {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) [Epi q] : Epi (modificationMap f d q) := by
  dsimp only [modificationMap]
  infer_instance

/-- A coherent elementary modification is the kernel along the divisor. -/
def modificationSequence {E : Coh Y} {G : Coh X} (q : (restriction f d).obj E ⟶ G) :
    ShortComplex (Coh Y) :=
  ShortComplex.mk (kernel.ι (modificationMap f d q)) (modificationMap f d q)
    (kernel.condition _)

lemma modificationSequence_shortExact {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) [Epi q] :
    (modificationSequence f d q).ShortExact := by
  change (ShortComplex.mk (kernel.ι (modificationMap f d q)) (modificationMap f d q) _).ShortExact
  exact { exact := ShortComplex.exact_kernel _ }

omit [IsLocallyNoetherian X] in
lemma modificationMap_restrict {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) :
    (restriction f d).map (modificationMap f d q) ≫ (supportedCounitIso f d G).hom = q := by
  apply (cohPushforward f).map_injective
  apply (cancel_epi ((restrictionUnit f d).app E)).mp
  have hn : (restrictionUnit f d).app E ≫
      (cohPushforward f).map ((restriction f d).map (modificationMap f d q)) =
      modificationMap f d q ≫ (restrictionUnit f d).app ((cohPushforward f).obj G) :=
    ((restrictionUnit f d).naturality (modificationMap f d q)).symm
  rw [(cohPushforward f).map_comp, ← Category.assoc, hn, Category.assoc,
    unit_supported_counit]
  exact Category.comp_id _

/-- The right-hand kernel after restriction is the kernel of the last-factor quotient. -/
def modificationKernelIso {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) :
    kernel ((restriction f d).map (modificationMap f d q)) ≅ kernel q :=
  kernel.mapIso _ _ (Iso.refl _) (supportedCounitIso f d G)
    (by simpa only [Iso.refl_hom, Category.id_comp] using modificationMap_restrict f d q)

/-- Sequence G⊗J|X → E'|X → ker(P→G) of the elementary transformation formula. -/
def transformSequence {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) [Epi q] : ShortComplex (Coh X) := by
  let b := connecting f d (modificationSequence_shortExact f d q)
  exact ShortComplex.mk
    ((firstTor_supported_iso f d G).inv ≫ b.δ)
    (b.toQuotientKernel ≫ (modificationKernelIso f d q).hom)
    (by erw [Category.assoc, ← Category.assoc b.δ, b.δ_toQuotientKernel, zero_comp, comp_zero])

/-- The elementary transform has the exact divisor restriction
claimed by the manuscript, with the conormal tensor. -/
lemma transformSequence_shortExact {E : Coh Y} {G : Coh X}
    (q : (restriction f d).obj E ⟶ G) [Epi q]
    (hE : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (E.obj.val.obj U)) :
    (transformSequence f d q).ShortExact := by
  let b := connecting f d (modificationSequence_shortExact f d q)
  let e : b.modificationComplex ≅ transformSequence f d q :=
    ShortComplex.isoMk (firstTor_supported_iso f d G) (Iso.refl _)
      (modificationKernelIso f d q)
      (by
        change (firstTor_supported_iso f d G).hom ≫
          (firstTor_supported_iso f d G).inv ≫ b.δ = b.δ
        exact (firstTor_supported_iso f d G).hom_inv_id_assoc b.δ)
      (by simp [transformSequence, CartierConnecting.Boundary.modificationComplex, b])
  exact ShortComplex.shortExact_of_iso e
    (modification_shortExact f d (modificationSequence_shortExact f d q) hE)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal Scheme.Modules

/-- A sheaf supported on the closed divisor vanishes on every open
whose inverse image is empty. This uses its section modules. -/
lemma pushforward_restrict_isZero {X Y : Scheme.{0}} (f : X ⟶ Y)
    (G : X.Modules) (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊥) :
    IsZero ((restrictFunctor U.ι).obj ((pushforward f).obj G)) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hV : f ⁻¹ᵁ (U.ι ''ᵁ V.unop) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hU]
    apply (TopologicalSpace.Opens.map f.base).monotone
    exact U.ι_image_le V.unop
  have : Subsingleton Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
  have := Module.subsingleton Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V.unop))
    (G.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V.unop))))
  exact Subsingleton.elim (α := G.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V.unop)))) _ _

/-- An elementary modification is canonically unchanged off the divisor. -/
lemma modification_puncture_isIso {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (d : ActualSheafTensor.LineTrivialization Y.sheaf (idealSheaf f))
    {E : Coh Y} {G : Coh X} (q : (restriction f d).obj E ⟶ G) [Epi q]
    (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊥) :
    IsIso ((restrictFunctor U.ι).map
      ((cohInclusion Y).map (kernel.ι (modificationMap f d q)))) := by
  have : PreservesFiniteLimits (restrictFunctor U.ι) :=
    CoherentRestriction.preservesFiniteLimits U.ι
  have hs := ((modificationSequence_shortExact f d q).map_of_exact
    (cohInclusion Y)).map_of_exact (restrictFunctor U.ι)
  exact hs.isIso_f_iff.mpr (pushforward_restrict_isZero f G.obj U hU)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
    (d : LineTrivialization Y.sheaf (idealSheaf g))

omit [IsLocallyNoetherian X] in
/-- Quasi-compact coherent support on the Cartier divisor implies
a vanishing ideal multiple. The affine cover and exponent are constructed. -/
lemma exists_idealMultiple_isZero (M : Coh Y)
    (hM : IsZero (M.obj.over (ActualOpenSupport.complement g))) :
    ∃ n : ℕ, IsZero (idealMultiple g d n M) := by
  let c := d.finiteAffineCover
  exact exists_idealMultiple_isZero_of_complement g d c.R c.f c.cover c.iso M hM

omit [IsLocallyNoetherian X] [CompactSpace Y] in
/-- Cokernels of a lattice embedding are supported on the divisor
when that embedding is an isomorphism on its open complement. -/
lemma quotient_supported_of_puncture_iso {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    [IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map S.f))] :
    IsZero (S.X₃.obj.over (ActualOpenSupport.complement g)) := by
  let U := ActualOpenSupport.complement g
  have : PreservesFiniteLimits (restrictFunctor U.ι) :=
    CoherentRestriction.preservesFiniteLimits U.ι
  have hs := (hS.map_of_exact (cohInclusion Y)).map_of_exact (restrictFunctor U.ι)
  have hi : IsIso ((S.map (cohInclusion Y)).map (restrictFunctor U.ι)).f :=
    ‹IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map S.f))›
  exact ActualOpenSupport.isZero_over_of_restrict S.X₃.obj U (hs.isIso_f_iff.mp hi)

/-- The Cartier restriction identity follows from Cartier data and a puncture isomorphism. -/
lemma lattice_puncture_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    [IsIso ((restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map S.f))] :
    ∃ n : ℕ, cls ((restriction g d).obj S.X₁) = cls ((restriction g d).obj S.X₂) +
      ((idealLayers g d n S.X₃).map fun Q => cls (conormalTensor g d Q) - cls Q).sum := by
  obtain ⟨n, hn⟩ := exists_idealMultiple_isZero g d S.X₃
    (quotient_supported_of_puncture_iso g hS)
  exact ⟨n, lattice_nilpotent_identity g d hS h₁ h₂ n hn⟩
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- Tensor by a line bundle reflects the zero object by its local unit trivializations. -/
lemma isZero_of_tensor_line (L M : SheafOfModules.{u} (ringSheaf R))
    (d : LineTrivialization R L) (h : IsZero ((tensorLeft R L).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply SheafLocality.module_hom_ext_of_coversTop (ringSheaf R) d.cover
  intro i
  let F := SheafOfModules.overFunctor (ringSheaf R) (d.obj i)
  have : F.Additive := ⟨by intros; rfl⟩
  let e : ((tensorLeft R L).obj M).over (d.obj i) ≅ M.over (d.obj i) :=
    (tensorLeftCompOverIso R (d.obj i) L).app M ≪≫
      (tensorLeftIso (R.over (d.obj i)) (d.iso i)).app (M.over (d.obj i)) ≪≫
        (tensorUnitLeftIso (R.over (d.obj i))).app (M.over (d.obj i))
  have hz : IsZero (M.over (d.obj i)) := (F.map_isZero h).of_iso e.symm
  change F.map (𝟙 M) = F.map 0
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

lemma coherent_isZero_of_tensor_line {X : Scheme.{0}}
    (L : X.Modules) (d : LineTrivialization X.sheaf L) (M : CoherentGlobal.Coh X)
    (h : IsZero ((coherentTensorLine L d).obj M)) : IsZero M := by
  have hz : IsZero ((tensorLeft X.sheaf L).obj M.obj) :=
    (CoherentGlobal.cohInclusion X).map_isZero h
  have hm := isZero_of_tensor_line X.sheaf L M.obj d hz
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (CoherentGlobal.cohInclusion X).zero_of_map_zero
  rw [CategoryTheory.Functor.map_id]
  exact hm.eq_of_src _ _
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

omit [IsClosedImmersion g] in
/-- A torsion-free coherent sheaf annihilated by a Cartier ideal power is zero. -/
lemma isZero_of_idealMultiple_isZero (n : ℕ) (M : Coh Y)
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.obj.val.obj U))
    (hn : IsZero (idealMultiple g d n M)) : IsZero M := by
  induction n generalizing M with
  | zero => exact hn
  | succ n ih =>
    let Q := multiple (coherentTensorLine (idealSheaf g) d) (action g d) M
    have hι : Mono (Abelian.image.ι ((action g d).app M)) :=
      kernelMono (C := Coh Y) (cokernel.π ((action g d).app M))
    have hmap : Mono ((cohInclusion Y).map (Abelian.image.ι ((action g d).app M))) :=
      @Functor.map_mono _ _ _ _ (cohInclusion Y) _ _ _ _ hι
    have hQ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (Q.obj.val.obj U) :=
      @SheafTorsion.subobject Y _ _ ((cohInclusion Y).map (Abelian.image.ι ((action g d).app M))) hmap hM
    have hzQ : IsZero Q := ih Q hQ hn
    have hmono : Mono (idealι g) :=
      kernelMono (C := SheafOfModules Y.ringCatSheaf) (structureMap g)
    have : Mono ((idealAction Y.sheaf (idealι g)).app M.obj) :=
      @idealAction_mono_of_line _ _ _ Y.sheaf _ _ _ _ (idealSheaf g) d (idealι g) hmono M.obj hM
    have : Mono ((action g d).app M) :=
      (cohInclusion Y).mono_of_mono_map (f := (action g d).app M) (by assumption)
    have hi : IsIso (Abelian.factorThruImage ((action g d).app M)) :=
      @Abelian.isIso_factorThruImage (Coh Y) _ _ _ _ ((action g d).app M) inferInstance
    have hzT : IsZero ((coherentTensorLine (idealSheaf g) d).obj M) :=
      hzQ.of_iso (@asIso _ _ _ _ (Abelian.factorThruImage ((action g d).app M)) hi)
    exact coherent_isZero_of_tensor_line (idealSheaf g) d M hzT

include d in
/-- A coherent torsion-free sheaf supported on an effective Cartier divisor
vanishes. Support here means restriction to its geometric complement. -/
lemma isZero_of_supported_torsionFree [CompactSpace Y] (M : Coh Y)
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.obj.val.obj U))
    (hs : IsZero (M.obj.over (ActualOpenSupport.complement g))) : IsZero M := by
  obtain ⟨n, hn⟩ := exists_idealMultiple_isZero g d M hs
  exact isZero_of_idealMultiple_isZero g d n M hM hn
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

include d
/-- Restriction off an effective Cartier divisor is faithful
on morphisms into coherent torsion-free sheaves. -/
lemma hom_zero_of_puncture {M N : Coh Y} (a : M ⟶ N)
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.obj.val.obj U))
    (ha : (restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map a) = 0) : a = 0 := by
  let U := ActualOpenSupport.complement g
  let F := cohInclusion Y ⋙ restrictFunctor U.ι
  have : PreservesFiniteLimits (restrictFunctor U.ι) :=
    CoherentRestriction.preservesFiniteLimits U.ι
  have hi : F.map (Abelian.image.ι a) = 0 := by
    apply (cancel_epi (F.map (Abelian.factorThruImage a))).mp
    rw [← CategoryTheory.Functor.map_comp, Abelian.image.fac, comp_zero]
    exact ha
  have hz : IsZero (F.obj (Abelian.image a)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_mono (F.map (Abelian.image.ι a))).mp
    simpa only [Category.id_comp, zero_comp] using hi
  have hs : IsZero ((Abelian.image a).obj.over U) :=
    ActualOpenSupport.isZero_over_of_restrict (Abelian.image a).obj U hz
  have hI : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V)
      ((Abelian.image a).obj.val.obj V) :=
    SheafTorsion.subobject ((cohInclusion Y).map (Abelian.image.ι a)) hN
  have hzero := isZero_of_supported_torsionFree g d (Abelian.image a) hI hs
  rw [← Abelian.image.fac a, hzero.eq_of_src (Abelian.image.ι a) 0, comp_zero]

/-- The uniqueness assertion needed for gluing cleared lattice denominators. -/
lemma hom_ext_of_puncture {M N : Coh Y} (a b : M ⟶ N)
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.obj.val.obj U))
    (hab : (restrictFunctor (ActualOpenSupport.complement g).ι).map
      ((cohInclusion Y).map a) =
      (restrictFunctor (ActualOpenSupport.complement g).ι).map ((cohInclusion Y).map b)) :
    a = b := by
  apply sub_eq_zero.mp
  apply hom_zero_of_puncture g d (a - b) hN
  simpa only [CategoryTheory.Functor.map_sub, sub_eq_zero] using hab
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open ActualSheafTensor CoherentGlobal Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

include d in
/-- Faithfulness on a local chart, stated on the slice site's section maps. It is the uniqueness needed when denominator-cleared maps
from distinct charts are glued; agreement is required only off the divisor. -/
lemma over_hom_ext_of_puncture (U : Y.Opens) [CompactSpace U.toScheme]
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (a b : M.over U ⟶ N.over U)
    (hab : ∀ (V : Y.Opens) (hV : V ≤ U) (_hW : V ≤ ActualOpenSupport.complement g)
      (x : M.val.obj (op V)),
      a.val.app (op (Over.mk (homOfLE hV))) x =
        b.val.app (op (Over.mk (homOfLE hV))) x) : a = b := by
  let F := (overEquiv U).functor
  let P := (restrictFunctor U.ι).obj M
  let Q := (restrictFunctor U.ι).obj N
  have : P.IsFinitePresentation := coherent_restrict U.ι M
  have : Q.IsFinitePresentation := coherent_restrict U.ι N
  let PP : Coh U.toScheme := ⟨P, inferInstance⟩
  let QQ : Coh U.toScheme := ⟨Q, inferInstance⟩
  let aa : PP ⟶ QQ := ⟨((overFunctorEquiv U).app M).inv ≫ F.map a ≫
    ((overFunctorEquiv U).app N).hom⟩
  let bb : PP ⟶ QQ := ⟨((overFunctorEquiv U).app M).inv ≫ F.map b ≫
    ((overFunctorEquiv U).app N).hom⟩
  have he : aa = bb := by
    apply hom_ext_of_puncture (g ∣_ U) (restrictedLine g d U) aa bb
      (SheafTorsion.restrict U.ι N hN)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let W := U.ι ''ᵁ ((ActualOpenSupport.complement (g ∣_ U)).ι ''ᵁ V.unop)
    have hWU : W ≤ U := U.ι_image_le _
    have hWG : W ≤ ActualOpenSupport.complement g := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z ∈ ActualOpenSupport.complement (g ∣_ U) :=
        (ActualOpenSupport.complement (g ∣_ U)).ι_image_le _ hz
      rw [ActualOpenSupport.complement_restrict] at hz'
      exact hz'
    exact hab W hWU hWG x
  apply F.map_injective
  have e := congrArg (fun t : PP ⟶ QQ => (cohInclusion U.toScheme).map t) he
  change ((overFunctorEquiv U).app M).inv ≫ F.map a ≫ ((overFunctorEquiv U).app N).hom =
    ((overFunctorEquiv U).app M).inv ≫ F.map b ≫ ((overFunctorEquiv U).app N).hom at e
  simpa only [cancel_epi, cancel_mono] using e
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SheafHomGluing
variable {X : Scheme.{0}} (M N : X.Modules)

/-- Compatible restricted module morphisms glue by the sheaf of linear Hom. -/
lemma exists_gluing {ι : Type*} (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (a : ∀ i, M.over (U i) ⟶ N.over (U i))
    (ha : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (x : M.val.obj (op V)),
      (a i).val.app (op (Over.mk (homOfLE hi))) x =
        (a j).val.app (op (Over.mk (homOfLE hj))) x) :
    ∃ f : M ⟶ N, ∀ i (V : X.Opens) (hi : V ≤ U i) (x : M.val.obj (op V)),
      f.val.app (op V) x = (a i).val.app (op (Over.mk (homOfLE hi))) x := by
  let H := CoherentDual.homSheaf.{0,0,0,0} X.sheaf M N
  let Q : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf _).obj H
  let s (i : ι) : H.val.obj (op (U i)) := (CoherentDual.homSheafSectionsEquiv.{0,0,0,0} X.sheaf M N (U i)).symm (a i)
  have hs : TopCat.Presheaf.IsCompatible Q.obj U s := by
    intro i j
    apply Subtype.ext
    apply CoherentDual.local_ext
    intro V x
    exact ha i j V.unop.left
      (V.unop.hom.le.trans inf_le_left) (V.unop.hom.le.trans inf_le_right) x
  obtain ⟨t, ht, _⟩ := Q.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
    (by rw [hU]) s hs
  let f : M ⟶ N := CoherentDual.globalHomEquiv.{0} X.sheaf M N ⊤ isTerminalTop t
  refine ⟨f, fun i V hi x => ?_⟩
  have h := ht i
  exact congrArg (fun q => CoherentDual.localApp q.val (op (Over.mk (homOfLE hi))) x) h

/-- In categorical form, the glued morphism restricts to every given local
morphism. All compatibility is tested on the section maps. -/
lemma exists_gluing_hom {ι : Type*} (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
    (a : ∀ i, M.over (U i) ⟶ N.over (U i))
    (ha : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (x : M.val.obj (op V)),
      (a i).val.app (op (Over.mk (homOfLE hi))) x =
        (a j).val.app (op (Over.mk (homOfLE hj))) x) :
    ∃ f : M ⟶ N, ∀ i, f.over (U i) = a i := by
  obtain ⟨f, hf⟩ := exists_gluing M N U hU a ha
  refine ⟨f, fun i => ?_⟩
  ext V x
  exact hf i V.unop.left V.unop.hom.le x

end SheafHomGluing


end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SheafHomGluing
variable {Y : Scheme.{0}}

/-- The glued global morphism retains the prescribed morphism
on the open where its local extensions were constructed, by sheaf separatedness. -/
lemma over_eq_of_local_values {ι : Type*} (U : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (M N : Y.Modules) (W : Y.Opens)
    (e : M.over W ⟶ N.over W) (f : M ⟶ N)
    (hf : ∀ i (V : Y.Opens) (_hi : V ≤ U i) (hV : V ≤ W)
      (x : M.val.obj (op V)),
      f.val.app (op V) x = e.val.app (op (Over.mk (homOfLE hV))) x) :
    f.over W = e := by
  ext V x
  apply TopCat.Presheaf.IsSheaf.section_ext ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N).2
  intro y hy
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ ⨆ i, U i by rw [hU]; trivial)
  let Z := V.unop.left ⊓ U i
  have hZV : Z ≤ V.unop.left := inf_le_left
  have hZi : Z ≤ U i := inf_le_right
  have hZW : Z ≤ W := hZV.trans V.unop.hom.le
  refine ⟨Z, hZV, ⟨hy, hi⟩, ?_⟩
  let z := M.val.map (homOfLE hZV).op x
  have he := hf i Z hZi hZW z
  have hn := ConcreteCategory.congr_hom (f.val.naturality (homOfLE hZV).op) x
  let p : Over.mk (homOfLE hZW) ⟶ V.unop := Over.homMk (homOfLE hZV) (by subsingleton)
  have hm := ConcreteCategory.congr_hom (e.val.naturality p.op) x
  change f.val.app (op Z) z = N.val.map (homOfLE hZV).op (f.val.app (op V.unop.left) x) at hn
  change e.val.app (op (Over.mk (homOfLE hZW))) z =
    N.val.map (homOfLE hZV).op (e.val.app V x) at hm
  exact hn.symm.trans (he.trans hm)
end SheafHomGluing

end

end OAI
