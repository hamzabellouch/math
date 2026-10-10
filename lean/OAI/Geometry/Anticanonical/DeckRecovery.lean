import OAI.Geometry.Anticanonical.Product
import OAI.Geometry.Anticanonical.SectionFamilies

namespace OAI

/-! Recovery of invariant anticanonical sections across unramified deck coverings. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace DeckRecovery
open AnticanonicalTransport CanonicalProduct
attribute [local instance] CanonicalProduct.productCharts CanonicalProduct.productManifold

section Automorphisms
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ G]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ,E) (⊤ : WithTop ℕ∞) M]
  [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold 𝓘(ℂ,G) (⊤ : WithTop ℕ∞) N]

 
def productDiffeomorph
    (f : M ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E),𝓘(ℂ,E)⟯ M)
    (g : N ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,G),𝓘(ℂ,G)⟯ N) :
    (M × N) ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E × G),𝓘(ℂ,E × G)⟯ (M × N) where
  toEquiv := f.toEquiv.prodCongr g.toEquiv
  contMDiff_toFun := by
    rw [modelWithCornersSelf_prod]
    exact f.contMDiff.prodMap g.contMDiff
  contMDiff_invFun := by
    rw [modelWithCornersSelf_prod]
    exact f.symm.contMDiff.prodMap g.symm.contMDiff

 
def translationDiffeomorph (t : E) : E ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E),𝓘(ℂ,E)⟯ E where
  toEquiv := Equiv.addRight t
  contMDiff_toFun := by
    exact contMDiff_id.add contMDiff_const
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) (⊤ : WithTop ℕ∞) (fun x : E => x + -t)
    exact contMDiff_id.add contMDiff_const

 
def actionDiffeomorph {Γ : Type} [Group Γ] [MulAction Γ M]
    (hM : ∀ g : Γ, ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) (⊤ : WithTop ℕ∞) (fun x : M => g • x))
    (g : Γ) : M ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E),𝓘(ℂ,E)⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := hM g
  contMDiff_invFun := hM g⁻¹

end Automorphisms

section Families
variable {a : ℕ} {EW EF : Type} [NormedAddCommGroup EW] [NormedSpace ℂ EW]
  [NormedAddCommGroup EF] [NormedSpace ℂ EF] [FiniteDimensional ℂ EW] [FiniteDimensional ℂ EF]
  {W F : Type} [TopologicalSpace W] [ChartedSpace EW W]
  [IsManifold 𝓘(ℂ,EW) (⊤ : WithTop ℕ∞) W]
  [TopologicalSpace F] [ChartedSpace EF F]
  [IsManifold 𝓘(ℂ,EF) (⊤ : WithTop ℕ∞) F]
  (α : ContMDiffSection 𝓘(ℂ,Fin a → ℂ) (CanonicalBundle.Model (Fin a → ℂ))
    (⊤ : WithTop ℕ∞) (CanonicalBundle.Fiber (E := Fin a → ℂ) (M := Fin a → ℂ)))
  (hα : ∀ z, α z ≠ 0)
  (β : ContMDiffSection 𝓘(ℂ,EW) (CanonicalBundle.Model EW)
    (⊤ : WithTop ℕ∞) (CanonicalBundle.Fiber (E := EW) (M := W)))
  (hβ : ∀ w, β w ≠ 0)

 
def doubleSplit (d : ℕ) (p : (Fin a → ℂ) × W × F) :
    (anti (E := (Fin a → ℂ) × EW × EF) (M := (Fin a → ℂ) × W × F) d).Fiber p ≃L[ℂ]
      (anti (E := EF) (M := F) d).Fiber p.2.2 :=
  (antiSplit α hα d p).trans (antiSplit β hβ d p.2)

 
theorem contMDiff_doubleSplit (d : ℕ)
    (s : H0 (E := (Fin a → ℂ) × EW × EF) (M := (Fin a → ℂ) × W × F) d) :
    ContMDiff 𝓘(ℂ,(Fin a → ℂ) × EW × EF)
      ((𝓘(ℂ,EF)).prod 𝓘(ℂ,(anti (E := EF) (M := F) d).Model)) (⊤ : WithTop ℕ∞)
      (fun p => (⟨p.2.2, doubleSplit α hα β hβ d p (s p)⟩ :
        TotalSpace (anti (E := EF) (M := F) d).Model (anti (E := EF) (M := F) d).Fiber)) := by
  have h1 := contMDiff_antiSplit_apply α hα d
    (id : ((Fin a → ℂ) × W × F) → ((Fin a → ℂ) × W × F)) contMDiff_id
    (fun p => s p) s.contMDiff
  have hp : ContMDiff 𝓘(ℂ,(Fin a → ℂ) × EW × EF) 𝓘(ℂ,EW × EF)
      (⊤ : WithTop ℕ∞) (Prod.snd : ((Fin a → ℂ) × W × F) → W × F) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  exact contMDiff_antiSplit_apply β hβ d Prod.snd hp
    (fun p => antiSplit α hα d p (s p)) h1

 
def splitFamily (d : ℕ)
    (s : H0 (E := (Fin a → ℂ) × EW × EF) (M := (Fin a → ℂ) × W × F) d)
    (z : Fin a → ℂ) (w : W) : H0 (E := EF) (M := F) d where
  toFun x := doubleSplit α hα β hβ d (z,w,x) (s (z,w,x))
  contMDiff_toFun := by
    have hi : ContMDiff 𝓘(ℂ,EF) 𝓘(ℂ,(Fin a → ℂ) × EW × EF)
        (⊤ : WithTop ℕ∞) (fun x : F => (z,w,x)) := by
      simp only [modelWithCornersSelf_prod]
      exact contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id)
    exact (contMDiff_doubleSplit α hα β hβ d s).comp hi

 
theorem splitFamily_nonzero (d : ℕ)
    (s : H0 (E := (Fin a → ℂ) × EW × EF) (M := (Fin a → ℂ) × W × F) d) (hs : s ≠ 0) :
    ∃ z w, splitFamily α hα β hβ d s z w ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hs
  ext p
  apply (doubleSplit α hα β hβ d p).injective
  change (doubleSplit α hα β hβ d p) (s p) = (doubleSplit α hα β hβ d p) 0
  rw [map_zero]
  exact DFunLike.congr_fun (hn p.1 p.2.1) p.2.2

variable (f : (Fin a → ℂ) ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,Fin a → ℂ),𝓘(ℂ,Fin a → ℂ)⟯ (Fin a → ℂ))
  (g : W ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,EW),𝓘(ℂ,EW)⟯ W)
  (k : F ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,EF),𝓘(ℂ,EF)⟯ F)
  (hαf : ∀ z, canonicalPush f.isLocalDiffeomorph z (α z) = α (f z))
  (hβg : ∀ w, canonicalPush g.isLocalDiffeomorph w (β w) = β (g w))

include hαf hβg in
 
theorem doubleSplit_natural (d : ℕ) (p : (Fin a → ℂ) × W × F) :
    (antiPull (productDiffeomorph f (productDiffeomorph g k)).isLocalDiffeomorph d p).trans
        (doubleSplit α hα β hβ d p) =
      (doubleSplit α hα β hβ d ((productDiffeomorph f (productDiffeomorph g k)) p)).trans
        (antiPull k.isLocalDiffeomorph d p.2.2) := by
  have h1 := antiSplit_natural f.isLocalDiffeomorph
    (productDiffeomorph g k).isLocalDiffeomorph
    (productDiffeomorph f (productDiffeomorph g k)).isLocalDiffeomorph α hα hαf d p
  have h2 := antiSplit_natural g.isLocalDiffeomorph k.isLocalDiffeomorph
    (productDiffeomorph g k).isLocalDiffeomorph β hβ hβg d p.2
  ext v
  change antiSplit β hβ d p.2
    (antiSplit α hα d p
      (antiPull (productDiffeomorph f (productDiffeomorph g k)).isLocalDiffeomorph d p v)) = _
  rw [show antiSplit α hα d p
      (antiPull (productDiffeomorph f (productDiffeomorph g k)).isLocalDiffeomorph d p v) =
      antiPull (productDiffeomorph g k).isLocalDiffeomorph d p.2
        (antiSplit α hα d ((productDiffeomorph f (productDiffeomorph g k)) p) v) from
      DFunLike.congr_fun h1 v]
  exact DFunLike.congr_fun h2 _

include hαf hβg in
 
theorem splitFamily_equivariant (d : ℕ)
    (s : H0 (E := (Fin a → ℂ) × EW × EF) (M := (Fin a → ℂ) × W × F) d)
    (hs : pullSection (productDiffeomorph f (productDiffeomorph g k)).isLocalDiffeomorph d s = s)
    (z : Fin a → ℂ) (w : W) :
    splitFamily α hα β hβ d s (f z) (g w) =
      (pullSectionEquiv k d).symm (splitFamily α hα β hβ d s z w) := by
  apply (pullSectionEquiv k d).injective
  rw [LinearEquiv.apply_symm_apply]
  ext x
  have hn := DFunLike.congr_fun (doubleSplit_natural α hα β hβ f g k hαf hβg d (z,w,x))
    (s ((productDiffeomorph f (productDiffeomorph g k)) (z,w,x)))
  have hsx := DFunLike.congr_fun hs (z,w,x)
  exact hn.symm.trans (congrArg (doubleSplit α hα β hβ d (z,w,x)) hsx)

end Families

section Hermitian
 

theorem hermitian_norm_preserving_inner {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : InnerProductSpace.Core ℂ V) (ρ : V ≃ₗ[ℂ] V)
    (hρ : ∀ v, Real.sqrt (h.inner (ρ v) (ρ v)).re = Real.sqrt (h.inner v v).re) :
    ∀ v w, h.inner (ρ v) (ρ w) = h.inner v w := by
  let : InnerProductSpace.Core ℂ V := h
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := V)
  let : NormedSpace ℂ V := NormedSpace.ofCore (InnerProductSpace.Core.toNormedSpaceCore h)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  exact (LinearMap.norm_map_iff_inner_map_map ρ).mp hρ
end Hermitian

variable {a : ℕ} {EW EF : Type} [NormedAddCommGroup EW] [NormedSpace ℂ EW]
  [NormedAddCommGroup EF] [NormedSpace ℂ EF] [FiniteDimensional ℂ EW] [FiniteDimensional ℂ EF]
  {W F : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W] [ConnectedSpace W]
  [ChartedSpace EW W] [IsManifold 𝓘(ℂ,EW) (⊤ : WithTop ℕ∞) W]
  [TopologicalSpace F] [T2Space F] [CompactSpace F] [ConnectedSpace F]
  [ChartedSpace EF F] [IsManifold 𝓘(ℂ,EF) (⊤ : WithTop ℕ∞) F]
  {Γ : Type} [Group Γ] [MulAction Γ W] [MulAction Γ F]
  (hW : ∀ g : Γ, ContMDiff 𝓘(ℂ,EW) 𝓘(ℂ,EW) (⊤ : WithTop ℕ∞) (fun x : W => g • x))
  (hF : ∀ g : Γ, ContMDiff 𝓘(ℂ,EF) 𝓘(ℂ,EF) (⊤ : WithTop ℕ∞) (fun x : F => g • x))

 
def monodromy (d : ℕ) (g : Γ) : H0 (E := EF) (M := F) d ≃ₗ[ℂ] H0 (E := EF) (M := F) d :=
  (pullSectionEquiv (actionDiffeomorph hF g) d).symm

 

omit [T2Space W] [ConnectedSpace F] in
theorem native_deck_liouville_recovery
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ((Fin a → ℂ) × EW × EF) X]
    [IsManifold 𝓘(ℂ,(Fin a → ℂ) × EW × EF) (⊤ : WithTop ℕ∞) X]
    (d : ℕ) (_hd : 0 < d)
    (τ : Γ →* Multiplicative (Fin a → ℂ))
    (Λ : Submodule ℤ (Fin a → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hτ : Set.range (fun g => Multiplicative.toAdd (τ g)) = (Λ : Set (Fin a → ℂ)))
    (α : ContMDiffSection 𝓘(ℂ,Fin a → ℂ) (CanonicalBundle.Model (Fin a → ℂ))
      (⊤ : WithTop ℕ∞) (CanonicalBundle.Fiber (E := Fin a → ℂ) (M := Fin a → ℂ)))
    (hα : ∀ z, α z ≠ 0)
    (hαinv : ∀ g z, canonicalPush
      (translationDiffeomorph (Multiplicative.toAdd (τ g))).isLocalDiffeomorph z (α z) =
        α (z + Multiplicative.toAdd (τ g)))
    (β : ContMDiffSection 𝓘(ℂ,EW) (CanonicalBundle.Model EW)
      (⊤ : WithTop ℕ∞) (CanonicalBundle.Fiber (E := EW) (M := W)))
    (hβ : ∀ w, β w ≠ 0)
    (hβinv : ∀ g w, canonicalPush (actionDiffeomorph hW g).isLocalDiffeomorph w (β w) = β (g • w))
    (q : ((Fin a → ℂ) × W × F) → X)
    (hqsurj : Function.Surjective q)
    (hqquot : ∀ p p', q p = q p' ↔
      ∃ g : Γ, p' = (p.1 + Multiplicative.toAdd (τ g), g • p.2.1, g • p.2.2))
    (hq : IsLocalDiffeomorph 𝓘(ℂ,(Fin a → ℂ) × EW × EF)
      𝓘(ℂ,(Fin a → ℂ) × EW × EF) (⊤ : WithTop ℕ∞) q)
    (h : InnerProductSpace.Core ℂ (H0 (E := EF) (M := F) d))
    (hnorm : ∀ g v,
      Real.sqrt (h.inner (monodromy hF d g v) (monodromy hF d g v)).re =
        Real.sqrt (h.inner v v).re)
    (s : H0 (E := (Fin a → ℂ) × EW × EF) (M := X) d) (hs : s ≠ 0) :
    ∃ t : H0 (E := EF) (M := F) d, t ≠ 0 ∧
      (∀ z w, splitFamily α hα β hβ d (pullSection hq d s) z w = t) ∧
      ∀ g, monodromy hF d g t = t := by
  let lifted := pullSection hq d s
  have hlifted : lifted ≠ 0 := by
    intro hz
    apply hs
    apply pullSection_injective hq d hqsurj
    simpa only [map_zero] using hz
  let v := splitFamily α hα β hβ d lifted
  have hv : ContMDiff ((𝓘(ℂ,Fin a → ℂ)).prod ((𝓘(ℂ,EW)).prod 𝓘(ℂ,EF)))
      ((𝓘(ℂ,EF)).prod 𝓘(ℂ,(anti (E := EF) (M := F) d).Model)) (⊤ : WithTop ℕ∞)
      (fun p : (Fin a → ℂ) × W × F => (⟨p.2.2, v p.1 p.2.1 p.2.2⟩ :
        TotalSpace (anti (E := EF) (M := F) d).Model (anti (E := EF) (M := F) d).Fiber)) := by
    simpa only [modelWithCornersSelf_prod] using! contMDiff_doubleSplit α hα β hβ d lifted
  have heq (g : Γ) (z : Fin a → ℂ) (w : W) :
      v (z + Multiplicative.toAdd (τ g)) (g • w) = monodromy hF d g (v z w) := by
    let D := productDiffeomorph (translationDiffeomorph (Multiplicative.toAdd (τ g)))
      (productDiffeomorph (actionDiffeomorph hW g) (actionDiffeomorph hF g))
    have hdeck : q ∘ D = q := by
      funext p
      exact ((hqquot p (D p)).mpr ⟨g,rfl⟩).symm
    exact splitFamily_equivariant α hα β hβ
      (translationDiffeomorph (Multiplicative.toAdd (τ g)))
      (actionDiffeomorph hW g) (actionDiffeomorph hF g)
      (hαinv g) (hβinv g) d lifted (pullSection_deck hq d D.isLocalDiffeomorph hdeck s) z w
  have hinner : ∀ g u v, h.inner (monodromy hF d g u) (monodromy hF d g v) = h.inner u v :=
    fun g => hermitian_norm_preserving_inner h (monodromy hF d g) (hnorm g)
  obtain ⟨t, ht, hconst, hinv⟩ := NativeLiouville.native_family_recovery
    (E := EF) (F := (anti (E := EF) (M := F) d).Model) (anti (E := EF) (M := F) d).Fiber
    Λ (fun g => Multiplicative.toAdd (τ g)) hτ (fun g w => g • w)
    h (monodromy hF d) hinner v hv heq (splitFamily_nonzero α hα β hβ d lifted hlifted)
  exact ⟨t, ht, hconst, hinv⟩


end DeckRecovery

end

end OAI
