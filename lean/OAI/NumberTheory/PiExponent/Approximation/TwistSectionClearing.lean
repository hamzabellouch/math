import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars

namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

lemma iso_section_restrict_zero {P Q : X.Modules} (e : P ≅ Q) (V : X.Opens)
    (x : Γ(P,⊤)) (hx : P.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op x = 0) :
    Q.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (e.hom.app ⊤ x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op) x
  change e.hom.app V (P.presheaf.map (homOfLE le_top).op x) =
    Q.presheaf.map (homOfLE le_top).op (e.hom.app ⊤ x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma frame_local_input_zero (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (x : Γ(P,⊤))
    (hx : P.presheaf.map (homOfLE (show PiExponentSeshadri.SectionOpens.isoOpen s ≤ ⊤ from le_top)).op x = 0) :
    (P.restrict U.ι).presheaf.map
      (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op
      (P.presheaf.map (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op x) = 0 := by
  have hD : U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤
      PiExponentSeshadri.SectionOpens.isoOpen s := by
    rw [← preimage_isoOpen s U.ι e]
    exact U.ι.image_preimage_le _
  change openRestriction P (U.ι.image_mono
    (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s))))
    (openRestriction P (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top) x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD le_top x]
  change openRestriction P hD (P.presheaf.map (homOfLE le_top).op x) = 0
  rw [hx]
  exact map_zero (openRestriction P hD)

lemma section_zero_of_imageTop (P : X.Modules) (U : X.Opens) (x : Γ(P,⊤))
    (hx : P.presheaf.map (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op x = 0) :
    P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x = 0 :=
  openRestriction_zero_congr P U.ι_image_top _ _ _ hx

lemma iso_section_restrict_zero_on {P Q : X.Modules} (e : P ≅ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE hVW).op x = 0) :
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE hVW).op) x
  change e.hom.app V (P.presheaf.map (homOfLE hVW).op x) =
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma frame_local_input_zero_on (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (W : X.Opens) (V : U.toScheme.Opens) (hVW : U.ι ''ᵁ V ≤ W)
    (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    (P.restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op
      (P.presheaf.map (homOfLE hVW).op x) = 0 := by
  have hD : U.ι ''ᵁ (V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))) ≤
      W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s := by
    apply le_inf
    · exact (U.ι.image_mono inf_le_left).trans hVW
    · apply (U.ι.image_mono inf_le_right).trans
      rw [← preimage_isoOpen s U.ι e]
      exact U.ι.image_preimage_le _
  change openRestriction P (U.ι.image_mono
    (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left))
    (openRestriction P hVW x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD inf_le_left x]
  change openRestriction P hD (P.presheaf.map (homOfLE inf_le_left).op x) = 0
  rw [hx]
  exact map_zero (openRestriction P hD)

theorem frame_twistForward_zero_on (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (V : U.toScheme.Opens) (hV : IsCompact (V : Set U.toScheme))
    (x : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι, V))
    (hx : (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V)) x = 0 := by
  let c := coefficient e (restrictSection U.ι s)
  let E := (moduleTwistRestrictFrame L U e n).app M
  have hz := iso_section_restrict_zero_on E
    (show V ⊓ U.toScheme.basicOpen c ≤ V from inf_le_left) x hx
  obtain ⟨K, hK⟩ := compact_open_section_zero (M.restrict U.ι) c V hV (E.hom.app V x) hz
  refine ⟨K, fun k hk => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V)).injective
  refine (moduleTwistForward_frame L s U e M V n k x).trans ?_
  have hh := hK k hk
  change (restrictScalar U.toScheme V (c ^ k)) • E.hom.app V x = 0 at hh
  rw [map_pow] at hh
  exact hh.trans (map_zero (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V).hom).symm

lemma hom_section_restriction {P Q : X.Modules} (f : P ⟶ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W)) :
    Q.presheaf.map (homOfLE hVW).op (f.app W x) =
      f.app V (P.presheaf.map (homOfLE hVW).op x) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE hVW).op) x
  exact h.symm

theorem frame_twistForward_ambient_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (W : X.Opens)
    (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      ((moduleTwistFunctor L (n+k)).obj M).presheaf.map
        (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op
        (((moduleTwistForward L s n k).app M).app W x) = 0 := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  let V := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V ≤ W := U.ι.image_preimage_le W
  have hlocal := frame_local_input_zero_on L s U e ((moduleTwistFunctor L n).obj M) W V hVW x hx
  obtain ⟨K, hK⟩ := frame_twistForward_zero_on L s U e M n V
    (NoetherianSpace.isCompact _) _ hlocal
  refine ⟨K, fun k hk => ?_⟩
  have hh : ((moduleTwistFunctor L (n+k)).obj M).presheaf.map (homOfLE hVW).op
      (((moduleTwistForward L s n k).app M).app W x) = 0 := by
    rw [hom_section_restriction]
    exact hK k hk
  have he : U.ι ''ᵁ V = U ⊓ W := by
    dsimp only [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact openRestriction_zero_congr ((moduleTwistFunctor L (n+k)).obj M) he _ _ _ hh

theorem twistForward_section_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (W : X.Opens) (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistForward L s n k).app M).app W x = 0 := by
  classical
  choose U hxU he using L.locallyRankOne
  let e (a : X) := Classical.choice (he a)
  have hcover : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro a ha
    exact Opens.mem_iSup.mpr ⟨a, hxU a⟩
  obtain ⟨I, hI⟩ := hcover.exists_finite_of_compactSpace
  have hI' : (⨆ i : I, U i.val) = ⊤ := hI
  choose K hK using fun i : I => frame_twistForward_ambient_zero L s (U i.val)
    (e i.val) M n W x hx
  refine ⟨Finset.univ.sup K, fun k hk => ?_⟩
  let P := (moduleTwistFunctor L (n+k)).obj M
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨P.presheaf, P.isSheaf⟩
    (fun i : I => U i.val ⊓ W) W (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hI', top_inf_eq])
  intro i
  have hi := hK i k ((Finset.le_sup (f := K) (Finset.mem_univ i)).trans hk)
  change P.presheaf.map _ (((moduleTwistForward L s n k).app M).app W x) = P.presheaf.map _ 0
  rw [map_zero]
  exact hi

theorem twistSection_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (x : Γ(M,W))
    (hx : M.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistSection L s k).app M).app W x = 0 := by
  obtain ⟨K, hK⟩ := twistForward_section_zero L s M 0 W x hx
  refine ⟨K, fun k hk => ?_⟩
  have he := moduleTwistSection_add L s 0 k
  simp only [moduleTwistSection] at he
  have he' : moduleTwistSection L s (0+k) = moduleTwistForward L s 0 k :=
    he.trans (Category.id_comp _)
  have hh := (congrArg (fun t => (t.app M).app W x) he').trans (hK k hk)
  let P (j : ℕ) : Prop := ((moduleTwistSection L s j).app M).app W x = 0
  exact Eq.mp (congrArg P (Nat.zero_add k)) hh

end
end PiExponent.TwistSectionClearing

end OAI
