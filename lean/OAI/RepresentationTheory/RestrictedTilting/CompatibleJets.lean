import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

 
lemma IsRational.prod {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    {ρ : Representation k (SL2 k) M} {σ : Representation k (SL2 k) N}
    (hρ : IsRational k ρ) (hσ : IsRational k σ) :
    IsRational k (Representation.prod ρ σ) := by
  intro v l
  obtain ⟨P,hP⟩ := hρ v.1 (l.comp (LinearMap.inl k M N))
  obtain ⟨Q,hQ⟩ := hσ v.2 (l.comp (LinearMap.inr k M N))
  refine ⟨P+Q, fun g => ?_⟩
  rw [MvPolynomial.eval_add, ← hP, ← hQ]
  change l _ = l (ρ g v.1, 0) + l (0, σ g v.2)
  rw [← map_add]
  congr 1
  ext <;> simp [Representation.prod]

 
def representationPullback {G : Type u} [Group G] {B C T : FDRep k G}
    (g : B ⟶ C) (h : T ⟶ C) : Subrepresentation (Representation.prod B.ρ T.ρ) where
  toSubmodule := LinearMap.ker
    ((fdrepLinear k g).comp (LinearMap.fst k B T) -
      (fdrepLinear k h).comp (LinearMap.snd k B T))
  apply_mem_toSubmodule a v hv := by
    change fdrepLinear k g (B.ρ a v.1) - fdrepLinear k h (T.ρ a v.2) = 0
    rw [fdrepLinear_comm, fdrepLinear_comm, ← map_sub]
    change fdrepLinear k g v.1 - fdrepLinear k h v.2 = 0 at hv
    rw [hv, map_zero]

 

theorem good_weyl_lift [Infinite k] {A B C T : FDRep k (SL2 k)}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    (hB : IsRational k B.ρ) (hT : IsTilting k T)
    (hA : HasGoodFiltration k A) (h : T ⟶ C) :
    ∃ s : T ⟶ B, s ≫ g = h := by
  let PB := representationPullback k g h
  let E : FDRep k (SL2 k) := FDRep.of PB.toRepresentation
  have he (v : PB) : fdrepLinear k g v.val.1 = fdrepLinear k h v.val.2 :=
    sub_eq_zero.mp v.property
  let i : A ⟶ E := fdrepHom k
    { toFun := fun a => ⟨(fdrepLinear k f a, 0), by
        change fdrepLinear k g (fdrepLinear k f a) - fdrepLinear k h 0 = 0
        rw [map_zero, sub_zero]
        exact congrArg (fun z => fdrepLinear k z a) w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        change (fdrepLinear k f (a + b), (0 : T)) =
          (fdrepLinear k f a, (0 : T)) + (fdrepLinear k f b, (0 : T))
        simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        change (fdrepLinear k f (c • a), (0 : T)) = c • (fdrepLinear k f a, (0 : T))
        simp }
    (by
      intro a v
      apply Subtype.ext
      change (fdrepLinear k f (A.ρ a v), (0 : T)) = (B.ρ a (fdrepLinear k f v), T.ρ a 0)
      exact Prod.ext (fdrepLinear_comm k f a v) (map_zero (T.ρ a)).symm)
  let q : E ⟶ T := fdrepHom k ((LinearMap.snd k B T).comp PB.toSubmodule.subtype)
    (by intros; rfl)
  let r : E ⟶ B := fdrepHom k ((LinearMap.fst k B T).comp PB.toSubmodule.subtype)
    (by intros; rfl)
  have viq : i ≫ q = 0 := by apply fdrep_hom_ext k; intro a; rfl
  have hi : Function.Injective (fdrepLinear k i) := by
    have := hS.mono_f
    intro a b hab
    apply fdrep_injective k f
    exact congrArg (fun x : PB => x.val.1) hab
  have hq : Function.Surjective (fdrepLinear k q) := by
    have := hS.epi_g
    intro t
    obtain ⟨b,hb⟩ := fdrep_surjective k g (fdrepLinear k h t)
    exact ⟨⟨(b,t), sub_eq_zero.mpr hb⟩,rfl⟩
  have hex : LinearMap.range (fdrepLinear k i) = LinearMap.ker (fdrepLinear k q) := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      rfl
    · intro hv
      have hv2 : v.val.2 = 0 := hv
      have hv1 : v.val.1 ∈ LinearMap.ker (fdrepLinear k g) := by
        change fdrepLinear k g v.val.1 = 0
        rw [he v, hv2, map_zero]
      rw [← fdrep_exact k hS.exact] at hv1
      obtain ⟨a,ha⟩ := hv1
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact Prod.ext ha hv2.symm
  have hE : IsRational k E.ρ :=
    IsRational.of_injective k E.ρ (Representation.prod B.ρ T.ρ)
      PB.toSubmodule.subtype Subtype.val_injective (by intros; rfl) (hB.prod k hT.1)
  obtain ⟨s,hs⟩ := good_weyl_extension_split k hA hT.2.2 E hE i q viq
    (fdrep_shortExact k (ShortComplex.mk i q viq) hi hq hex)
  refine ⟨s ≫ r, ?_⟩
  apply fdrep_hom_ext k
  intro t
  change fdrepLinear k g (fdrepLinear k s t).val.1 = fdrepLinear k h t
  rw [he]
  exact congrArg (fdrepLinear k h) (congrArg (fun z => fdrepLinear k z t) hs)

variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]
  [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)]

 
noncomputable def planeJetFD (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) : FDRep k (SL2 k) := by
  let := planeJet_finite (M := M) k j
  exact FDRep.of (planeJetRep k σ hσ j)

noncomputable def planeJetLayerFD (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) : FDRep k (SL2 k) := by
  let := planeLayer_finite (M := M) k j
  exact FDRep.of (planeJetLayerRep k σ hσ j)

noncomputable def planeJetTransitionHom (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    planeJetFD k σ hσ (j+1) ⟶ planeJetFD k σ hσ j :=
  fdrepHom k (planeJetTransition k j) (planeJetTransition_intertwines k σ hσ j)

noncomputable def planeJetLayerInclusionHom (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    planeJetLayerFD k σ hσ j ⟶ planeJetFD k σ hσ (j+1) :=
  fdrepHom k (planeJetLayerInclusion k j) (planeJetLayerInclusion_intertwines k σ hσ j)

noncomputable def planeLayerMultiplyHom (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    costandard k j ⊗ planeJetFD k σ hσ 1 ⟶ planeJetLayerFD k σ hσ j :=
  fdrepHom k (planeLayerMultiply k j) (planeLayerMultiply_intertwines k σ hσ j)

 

theorem planeJetLayer_good (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w)
    (hT : HasGoodFiltration k (planeJetFD k σ hσ 1)) (j : ℕ) :
    HasGoodFiltration k (planeJetLayerFD k σ hσ j) := by
  let f := planeLayerMultiplyHom k σ hσ j
  let : IsIso f := fdrepHom_isIso_of_bijective k f
    ⟨planeLayerMultiply_injective k hx hy j, planeLayerMultiply_surjective k j⟩
  exact ((costandard_hasGoodFiltration k j).tensor k hT).of_iso k (asIso f)

 

theorem planeJet_lift [Infinite k] (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (hr : IsRational k σ)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w)
    (hT : IsTilting k (planeJetFD k σ hσ 1)) (j : ℕ)
    (h : planeJetFD k σ hσ 1 ⟶ planeJetFD k σ hσ j) :
    ∃ s : planeJetFD k σ hσ 1 ⟶ planeJetFD k σ hσ (j+1),
      s ≫ planeJetTransitionHom k σ hσ j = h := by
  let f := planeJetLayerInclusionHom k σ hσ j
  let g := planeJetTransitionHom k σ hσ j
  have w : f ≫ g = 0 := by
    apply fdrep_hom_ext k
    intro v
    change planeJetTransition (M := M) k j (planeJetLayerInclusion k j v) = 0
    exact (planeJet_shortExact (M := M) k j (planeJetLayerInclusion k j v)).2 ⟨v,rfl⟩
  have hS : (ShortComplex.mk f g w).ShortExact := by
    apply fdrep_shortExact k _ (planeJetLayerInclusion_injective k j)
      (planeJetTransition_surjective k j)
    change LinearMap.range (planeJetLayerInclusion (M := M) k j) =
      LinearMap.ker (planeJetTransition (M := M) k j)
    ext v
    exact (planeJet_shortExact (M := M) k j v).symm
  exact good_weyl_lift k f g w hS (planeJetRep_rational k σ hσ hr (j+1)) hT
    (planeJetLayer_good k σ hσ hx hy hT.2.1 j) h

 

theorem compatible_planeJet_sections [Infinite k] (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (hr : IsRational k σ)
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w)
    (hT : IsTilting k (planeJetFD k σ hσ 1)) :
    ∃ s : (j : ℕ) → planeJetFD k σ hσ 1 ⟶ planeJetFD k σ hσ (j+1),
      s 0 = 𝟙 _ ∧ ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j := by
  classical
  let s : (j : ℕ) → planeJetFD k σ hσ 1 ⟶ planeJetFD k σ hσ (j+1) :=
    Nat.rec (𝟙 _) (fun j t => Classical.choose (planeJet_lift k σ hσ hr hx hy hT (j+1) t))
  refine ⟨s,rfl,fun j => ?_⟩
  exact Classical.choose_spec (planeJet_lift k σ hσ hr hx hy hT (j+1) (s j))
end FiberFunctorProof

end OAI
