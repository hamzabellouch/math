import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionTransport
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionIdeal

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] [Fintype τ] {X : Scheme}

lemma idealSheaf_ext_local {I J : X.IdealSheafData}
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ I.ideal U = J.ideal U) : I = J := by
  choose U hx hU using h
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U _ hU
  exact top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)

lemma sectionIdeal_eq_of_combination {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (t : τ → (O X ⟶ M)) (ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤)
    (v : σ → K) (w : τ → K) (heq : sectionCombination k s v = sectionCombination k t w) :
    sectionIdeal k s hs v = sectionIdeal k t ht w := by
  apply idealSheaf_ext_local
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (ht.ge (Set.mem_univ x))
  let W := SectionOpens.isoOpen (s i) ⊓ SectionOpens.isoOpen (t j)
  obtain ⟨_, ⟨U, hUa, rfl⟩, hx, hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ W from ⟨hi, hj⟩) W.isOpen
  let A : X.affineOpens := ⟨U, hUa⟩
  have hUs : U ≤ SectionOpens.isoOpen (s i) := le_trans hU inf_le_left
  have hUt : U ≤ SectionOpens.isoOpen (t j) := le_trans hU inf_le_right
  let e := sectionFrameOn (s i) U hUs
  refine ⟨A, hx, ?_⟩
  rw [sectionIdeal_on_frame k s hs v A i hUs e,
    sectionIdeal_on_frame k t ht w A j hUt e, heq]

lemma sectionIdeal_twist {M N : X.Modules} (k : K →+* Γ(X, ⊤))
    (a : O X ≅ O X) (e : M ≅ N) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K) :
    sectionIdeal k (fun i => a.hom ≫ s i ≫ e.hom) (twistedSections_cover a e s hs) v =
      sectionIdeal k s hs v := by
  unfold sectionIdeal
  rw [sectionsMorphism_twist]

end
end MaximalSeshadri.Projective
end


end
end

end OAI
