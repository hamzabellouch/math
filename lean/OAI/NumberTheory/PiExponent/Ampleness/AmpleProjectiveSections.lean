import OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree
import OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme}

lemma isIso_restricted_section {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) : IsIso (restrictSection U.ι s) := by
  subst U
  change IsIso (sectionFrame s).inv
  exact (sectionFrame s).isIso_inv

theorem LineBundle.power_extension_ratio [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ((sectionOpen X s).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.power_extension s hD ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

lemma coefficient_ratio {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ O U.toScheme) (s t : O X ⟶ M)
    (f : Γ(U.toScheme, ⊤)) (hs : coefficient e (restrictSection U.ι s) = 1)
    (ht : restrictSection U.ι t = scalarEnd f ≫ restrictSection U.ι s) :
    coefficient e (restrictSection U.ι t) = f := by
  rw [ht]
  change endValue (scalarEnd f ≫ restrictSection U.ι s ≫ e.hom) = f
  rw [endValue_comp, endValue_scalarEnd]
  change f * coefficient e (restrictSection U.ι s) = f
  rw [hs, mul_one]

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.power_section_embedding [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i)))
    (hne : ∀ i, (sectionOpen X (s i) : Set X).Nonempty) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U (i : ι) := sectionOpen X (s i)
  have hfinite (i : ι) : ∃ m : ℕ, ∃ b : Fin m → Γ((U i).toScheme, ⊤),
      Function.Surjective (eval₂Hom ((U i).ι.appTop.hom.comp k) b) := by
    let : IsAffine (U i).toScheme := haff i
    obtain ⟨m, b, hb⟩ := affine_coordinate_generators ((U i).ι ≫ p)
    refine ⟨m, b, ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc, k] using hb
  choose m b hb using hfinite
  choose N hN using fun i j => L.power_extension_ratio (s i) (hne i) (b i j)
  let n := max 1 (Finset.univ.sup (fun v : (i : ι) × Fin (m i) => N v.1 v.2))
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hn' (i : ι) (j : Fin (m i)) : N i j ≤ n :=
    (Finset.le_sup (f := fun v : (i : ι) × Fin (m i) => N v.1 v.2)
      (Finset.mem_univ ⟨i, j⟩)).trans (le_max_right _ _)
  choose t ht using fun i j => hN i j n (hn' i j)
  let σ := ι ⊕ ((i : ι) × Fin (m i))
  let S : σ → GlobalSections X (modulePow X L.sheaf n) :=
    Sum.elim (fun i => powerSection (s i) n) (fun v => t v.1 v.2)
  have hU (i : ι) : SectionOpens.isoOpen (S (Sum.inl i)) = U i :=
    L.sectionOpen_power (s i) hn
  have hSn (i : ι) : IsIso (restrictSection (U i).ι (S (Sum.inl i))) :=
    isIso_restricted_section _ _ (hU i)
  let e (i : ι) : (modulePow X L.sheaf n).restrict (U i).ι ≅ O (U i).toScheme :=
    (asIso (restrictSection (U i).ι (S (Sum.inl i)))).symm
  have hnorm (i : ι) : coefficient (e i) (restrictSection (U i).ι (S (Sum.inl i))) = 1 :=
    coefficient_frame (e i)
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
        (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) = b i := by
      funext j
      exact coefficient_ratio (e i) (S (Sum.inl i)) (S (Sum.inr ⟨i, j⟩)) (b i j)
        (hnorm i) (ht i j)
    intro r
    obtain ⟨q, hq⟩ := hb i r
    refine ⟨rename (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) q, ?_⟩
    rw [eval₂Hom_rename, heq]
    exact hq
  have hclosed := framedSectionsMorphism_closed k S U hc e Sum.inl hnorm hU
    (fun i => haff i) hgen
  rw [framedSectionsMorphism_eq_sectionsMorphism k S hS U hc e Sum.inl hnorm] at hclosed
  exact ⟨n, hn, σ, inferInstance, S, hS, hclosed⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

theorem LineBundle.ample_projective_sections [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  obtain ⟨d, hd, l, s, hc, ha, hn⟩ := L.ample_common_degree_cover hL
  obtain ⟨n, hn', σ, hσ, t, ht, he⟩ := (L.pow d).power_section_embedding p s hc ha hn
  let e : modulePow X (L.pow d).sheaf n ≅ modulePow X L.sheaf (d * n) :=
    linePowerMul L d n
  let T : σ → GlobalSections X (modulePow X L.sheaf (d*n)) := fun i => t i ≫ e.hom
  have hT : (⨆ i, SectionOpens.isoOpen (T i)) = ⊤ := by
    exact (iSup_congr (fun i => SectionOpens.isoOpen_postcomp (t i) e)).trans ht
  refine ⟨d*n, Nat.mul_pos hd hn', σ, hσ, T, hT, ?_⟩
  have htransport := sectionsMorphism_transport
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht e hT
  exact htransport.symm ▸ he

end PiExponentSeshadri.Geometry

end

end OAI
