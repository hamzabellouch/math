import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticSubsystem

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ τ : Type} [CommRing K] {X : Scheme}

lemma sections_cover_reindex {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (e : τ ≃ σ) :
    (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤ := by
  apply le_antisymm le_top
  rw [← hs]
  refine iSup_le (fun i => ?_)
  obtain ⟨j, rfl⟩ := e.surjective i
  exact le_iSup (fun j : τ => SectionOpens.isoOpen (s (e j))) j

theorem doublePointQuartics_reindexed_local_coordinates {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (e : τ ≃ QuarticIndex σ) :
    let V := centeredOpen s
    let t (j : Option σ) := restrictSection V.ι (s j)
    let q := doublePointQuartics t
    let hq := sections_cover_reindex q (doublePointQuartics_cover t (restricted_centered_cover s)) e
    ∀ x : V, ∃ j : τ, ∃ U : V.toScheme.affineOpens, x ∈ U.1 ∧
      ∃ φ : PolyChart (R := K) j →+* Γ(V.toScheme, U.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K τ) (MvPolynomial.X j) (poly_X_mem j) (by decide) =
            U.2.fromSpec ≫ sectionsMorphism (V.ι.appTop.hom.comp k) (q ∘ e) hq := by
  intro V t q hq x
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
  let j := e.symm (i,i,some i,some i)
  have hjq : q (e j) = powerSection (t (some i)) 4 := by
    exact (congrArg q (e.apply_symm_apply (i, i, some i, some i))).trans
      (doublePointQuartics_pure t i)
  have hj : U ≤ SectionOpens.isoOpen (q (e j)) := by
    rw [hjq]
    exact sectionOpen_le_powerSection _ _
  have hquart' : Function.Surjective (eval₂Hom (U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k))
      (fun l => coefficient (sectionFrameOn (q (e j)) U hj) (restrictSection U.ι (q l)))) := by
    simpa only [hjq, q, doublePointQuartics] using hquart
  have hre := eval₂_surjective_reindex
    (U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k))
    (fun index => coefficient (sectionFrameOn (q (e j)) U hj)
      (restrictSection U.ι (q index))) e hquart'
  obtain ⟨φ, hφ, heq⟩ := sections_local_coordinates (V.ι.appTop.hom.comp k) (q ∘ e) hq j A hj hre
  exact ⟨j, A, hi, φ, hφ, heq⟩

end
end MaximalSeshadri.Projective

end


end
end

end OAI
