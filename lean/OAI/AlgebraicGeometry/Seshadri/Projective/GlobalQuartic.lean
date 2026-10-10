import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SectionIdealExt
import OAI.AlgebraicGeometry.Seshadri.Divisors.CenteredSections
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticSubsystem

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def augmentedQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    Option (QuarticIndex σ) → (O X ⟶ modulePow X M 4)
  | none => powerSection (s none) 4
  | some j => doublePointQuartics s j

omit [Fintype σ] in
lemma augmentedQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (augmentedQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  cases i with
  | none =>
    exact (sectionOpen_le_powerSection (s none) 4).trans
      (le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) none)
  | some i =>
    calc
      SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) :=
        sectionOpen_le_powerSection _ _
      _ = SectionOpens.isoOpen (augmentedQuartics s (some (i,i,some i,some i))) := by
        exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
      _ ≤ _ := le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) _

omit [Fintype σ] in
lemma restrict_doublePointQuartic {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (U : X.Opens) (j : QuarticIndex σ) :
    restrictSection U.ι (doublePointQuartics s j) =
      (powerRestrictionUnit U 4).hom ≫
        doublePointQuartics (fun i => restrictSection U.ι (s i)) j ≫
          (modulePowRestrict U M 4).inv := by
  have restriction_factor : restrictSection U.ι (doublePointQuartics s j) ≫
      (modulePowRestrict U M 4).hom = (powerRestrictionUnit U 4).hom ≫
        doublePointQuartics (fun index => restrictSection U.ι (s index)) j := by
    change restrictSection U.ι (mixedPowerSection 4 _) ≫ _ = _
    exact restrictMixedPowerSection_factor U 4 _
  exact ((modulePowRestrict U M 4).eq_comp_inv.mpr restriction_factor).trans
    (Category.assoc _ _ _)

lemma sectionCombination_extend_zero {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (q : Option σ → (O X ⟶ M)) (v : σ → K) :
    sectionCombination k q (fun j => j.elim 0 v) = sectionCombination k (q ∘ some) v := by
  classical
  rw [sectionCombination, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, map_zero, scalarEnd_zero,
    Limits.zero_comp, zero_add, sectionCombination, Function.comp_apply]

def doublePointQuarticIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → K) : X.IdealSheafData :=
  sectionIdeal k (augmentedQuartics s) (augmentedQuartics_cover s hs) (fun j => j.elim 0 v)

lemma doublePointQuarticIdeal_restrict {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → K) :
    let V := centeredOpen s
    let t := fun i => restrictSection V.ι (s i)
    (doublePointQuarticIdeal k s hs v).comap V.ι =
      sectionIdeal (V.ι.appTop.hom.comp k) (doublePointQuartics t)
        (doublePointQuartics_cover t (restricted_centered_cover s)) v := by
  let V := centeredOpen s
  let t := fun i => restrictSection V.ι (s i)
  let q := doublePointQuartics t
  let hq := doublePointQuartics_cover t (restricted_centered_cover s)
  let a := powerRestrictionUnit V 4
  let e := (modulePowRestrict V M 4).symm
  let raw := fun j => a.hom ≫ q j ≫ e.hom
  have hr (j : QuarticIndex σ) : raw j = restrictSection V.ι (doublePointQuartics s j) :=
    (restrict_doublePointQuartic s V j).symm
  dsimp only
  rw [doublePointQuarticIdeal, sectionIdeal_restrict]
  calc
    _ = sectionIdeal (V.ι.appTop.hom.comp k) raw (twistedSections_cover a e q hq) v := by
      apply sectionIdeal_eq_of_combination
      rw [sectionCombination_extend_zero]
      congr 1
      exact funext (fun j => (hr j).symm)
    _ = _ := sectionIdeal_twist (V.ι.appTop.hom.comp k) a e q hq v

end
end MaximalSeshadri.Projective
end


end
end

end OAI
