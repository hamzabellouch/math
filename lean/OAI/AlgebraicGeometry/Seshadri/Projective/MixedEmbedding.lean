import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.MixedDivisibleExtension

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.Projective

variable {X : Scheme.{0}} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.mixed_section_embedding [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L M : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i)))
    (hne : ∀ i, (sectionOpen X (s i) : Set X).Nonempty)
    (d : ∀ i, M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X ((L.pow n).tensor M).sheaf,
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U (i : ι) := sectionOpen X (s i)
  have hfinite (i : ι) : ∃ m : ℕ, ∃ b : Fin m → Γ((U i).toScheme,⊤),
      Function.Surjective (eval₂Hom ((U i).ι.appTop.hom.comp k) b) := by
    let : IsAffine (U i).toScheme := haff i
    obtain ⟨m,b,hb⟩ := affine_coordinate_generators ((U i).ι ≫ p)
    refine ⟨m,b,?_⟩
    simpa only [Scheme.Hom.comp_appTop,CommRingCat.hom_comp,RingHom.comp_assoc,k] using hb
  choose m b hb using hfinite
  choose N₀ hN₀ using fun i => L.mixed_frame_extension M (s i) (hne i) (d i)
  choose N hN using fun i j => L.divisible_mixed_extension M (s i) (hne i)
    (openSectionEquiv M.sheaf (U i) (scalarEnd (b i j) ≫ (d i).inv))
  let n := max (Finset.univ.sup N₀)
    (Finset.univ.sup (fun v : (i : ι) × Fin (m i) => N v.1 v.2))
  have hn₀ (i : ι) : N₀ i ≤ n :=
    (Finset.le_sup (f := N₀) (Finset.mem_univ i)).trans (le_max_left _ _)
  have hn (i : ι) (j : Fin (m i)) : N i j ≤ n :=
    (Finset.le_sup (f := fun v : (i : ι) × Fin (m i) => N v.1 v.2)
      (Finset.mem_univ ⟨i,j⟩)).trans (le_max_right _ _)
  choose r hr hrv using fun i => hN₀ i n (hn₀ i)
  choose t ht htv using fun i j => hN i j n (hn i j)
  let P := (L.pow (n+1)).tensor M
  let σ := ι ⊕ ((i : ι) × Fin (m i))
  let S : σ → GlobalSections X P.sheaf := Sum.elim r (fun v => t v.1 v.2)
  have hU (i : ι) : SectionOpens.isoOpen (S (Sum.inl i)) = U i := hr i
  have hSn (i : ι) : IsIso (restrictSection (U i).ι (S (Sum.inl i))) :=
    isIso_restricted_section _ _ (hU i)
  let e (i : ι) : P.sheaf.restrict (U i).ι ≅ O (U i).toScheme :=
    (asIso (restrictSection (U i).ι (S (Sum.inl i)))).symm
  have hnorm (i : ι) : coefficient (e i) (restrictSection (U i).ι (S (Sum.inl i))) = 1 :=
    coefficient_frame (e i)
  have hratio (i : ι) (j : Fin (m i)) :
      restrictSection (U i).ι (t i j) = scalarEnd (b i j) ≫ restrictSection (U i).ι (r i) := by
    apply (openSectionEquiv P.sheaf (U i)).injective
    rw [openSectionEquiv_restrict,openSectionEquiv_scalar,openSectionEquiv_restrict]
    refine (htv i j).trans ?_
    have hw := openSectionEquiv_scalar M.sheaf (U i) (b i j) (d i).inv
    have hh := congrArg (pure (L.pow (n+1)).sheaf M.sheaf (U i)
      ((powerSection (s i) (n+1)).app (U i) (1 : Γ(X,U i)))) hw
    exact hh.trans ((pure_smul_right _ _ _ _ _ _).trans
      (congrArg (fun z : Γ(P.sheaf,U i) => (U i).topIso.hom (b i j) • z) (hrv i).symm))
  have hS : (⨆ v, SectionOpens.isoOpen (S v)) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact (le_of_eq (hU i).symm).trans (le_iSup (fun v : σ => SectionOpens.isoOpen (S v)) (Sum.inl i))
  have hproper : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    rw [toSpec_scalarMap]
    infer_instance
  have hgen (i : ι) : Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun v => coefficient (e i) (restrictSection (U i).ι (S v)))) := by
    have heq : (fun v => coefficient (e i) (restrictSection (U i).ι (S v))) ∘
        (fun j : Fin (m i) => Sum.inr (⟨i,j⟩ : (i : ι) × Fin (m i))) = b i := by
      funext j
      exact coefficient_ratio (e i) (S (Sum.inl i)) (S (Sum.inr ⟨i,j⟩)) (b i j)
        (hnorm i) (hratio i j)
    intro z
    obtain ⟨q,hq⟩ := hb i z
    refine ⟨rename (fun j : Fin (m i) => Sum.inr (⟨i,j⟩ : (i : ι) × Fin (m i))) q,?_⟩
    rw [eval₂Hom_rename,heq]
    exact hq
  have hclosed := framedSectionsMorphism_closed k S U hc e Sum.inl hnorm hU (fun i => haff i) hgen
  rw [framedSectionsMorphism_eq_sectionsMorphism k S hS U hc e Sum.inl hnorm] at hclosed
  exact ⟨n+1,by omega,σ,inferInstance,S,hS,hclosed⟩

end
end MaximalSeshadri.Geometry

end



end OAI
