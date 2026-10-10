import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.RestrictedGenerators
import OAI.AlgebraicGeometry.Seshadri.Geometry.SubsystemCoordinates

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

abbrev QuarticIndex (σ : Type) := σ × σ × Option σ × Option σ

def doublePointQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (j : QuarticIndex σ) : O X ⟶ modulePow X M 4 :=
  quarticSection (s (some j.1)) (s (some j.2.1)) (s j.2.2.1) (s j.2.2.2)

lemma doublePointQuartics_pure {M : X.Modules} (s : Option σ → (O X ⟶ M)) (i : σ) :
    doublePointQuartics s (i,i,some i,some i) = powerSection (s (some i)) 4 :=
  quarticSection_pure _

def centeredOpen {M : X.Modules} (s : Option σ → (O X ⟶ M)) : X.Opens :=
  ⨆ i : σ, SectionOpens.isoOpen (s (some i))

lemma restricted_centered_cover {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    (⨆ i : σ, SectionOpens.isoOpen (restrictSection (centeredOpen s).ι (s (some i)))) = ⊤ := by
  simp_rw [isoOpen_restrictSection]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

lemma doublePointQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i : σ, SectionOpens.isoOpen (s (some i))) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (doublePointQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  calc
    SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) := sectionOpen_le_powerSection _ _
    _ = SectionOpens.isoOpen (doublePointQuartics s (i,i,some i,some i)) := by
      exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
    _ ≤ (⨆ j : QuarticIndex σ, SectionOpens.isoOpen (doublePointQuartics s j)) :=
      le_iSup (fun j : QuarticIndex σ => SectionOpens.isoOpen (doublePointQuartics s j)) (i,i,some i,some i)

lemma sectionFrameOn_self_coefficient {M : X.Modules} (s t : O X ⟶ M) :
    coefficient (sectionFrameOn s (SectionOpens.isoOpen s) le_rfl)
      (restrictSection (SectionOpens.isoOpen s).ι t) =
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι t) := by
  simpa only [Scheme.homOfLE_rfl, Scheme.Hom.id_appTop, CommRingCat.id_apply] using
    sectionFrameOn_coefficient s t (SectionOpens.isoOpen s) le_rfl

theorem doublePointQuartics_local_coordinates {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] :
    let V := centeredOpen s
    let t (j : Option σ) := restrictSection V.ι (s j)
    let q := doublePointQuartics t
    let hq := doublePointQuartics_cover t (restricted_centered_cover s)
    ∀ x : V, ∃ j : QuarticIndex σ, ∃ U : V.toScheme.affineOpens, x ∈ U.1 ∧
      ∃ φ : PolyChart (R := K) j →+* Γ(V.toScheme, U.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K (QuarticIndex σ)) (MvPolynomial.X j) (poly_X_mem j) (by decide) =
            U.2.fromSpec ≫ sectionsMorphism (V.ι.appTop.hom.comp k) q hq := by
  let V := centeredOpen s
  let t (j : Option σ) := restrictSection V.ι (s j)
  let q := doublePointQuartics t
  let hq := doublePointQuartics_cover t (restricted_centered_cover s)
  dsimp only
  intro x
  have hx : x ∈ ⨆ i : σ, SectionOpens.isoOpen (t (some i)) := by
    rw [show (⨆ i : σ, SectionOpens.isoOpen (t (some i))) = ⊤ from restricted_centered_cover s]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (t (some i))
  obtain ⟨hU, hgen⟩ := restricted_chart_generators k s hs V (some i) (by
    exact le_iSup (fun j : σ => SectionOpens.isoOpen (s (some j))) i)
  have hU' : IsAffineOpen U := hU
  let A : V.toScheme.affineOpens := ⟨U, hU'⟩
  have hg : Function.Surjective (eval₂Hom (U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k))
      (fun j => coefficient (sectionFrameOn (t (some i)) U le_rfl) (restrictSection U.ι (t j)))) := by
    have hr : (fun j => coefficient (sectionFrameOn (t (some i)) U le_rfl)
        (restrictSection U.ι (t j))) = (fun j => coefficient (sectionFrame (t (some i)))
        (restrictSection U.ι (t j))) := funext (fun j => sectionFrameOn_self_coefficient _ _)
    rw [hr]
    exact hgen
  have hquart := quartic_generators (V.ι.appTop.hom.comp k) t i U le_rfl hg
  let j : QuarticIndex σ := (i,i,some i,some i)
  have hj : U ≤ SectionOpens.isoOpen (q j) := by
    rw [show q j = powerSection (t (some i)) 4 from doublePointQuartics_pure t i]
    exact sectionOpen_le_powerSection _ _
  have hquart' : Function.Surjective (eval₂Hom (U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k))
      (fun l => coefficient (sectionFrameOn (q j) U hj) (restrictSection U.ι (q l)))) := by
    simpa only [q, j, doublePointQuartics_pure, doublePointQuartics] using hquart
  obtain ⟨φ, hφ, heq⟩ := sections_local_coordinates (V.ι.appTop.hom.comp k) q hq j A hj hquart'
  exact ⟨j, A, hi, φ, hφ, heq⟩

end
end MaximalSeshadri.Projective

end


end
end

end OAI
