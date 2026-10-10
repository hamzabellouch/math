import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Configurations.RationalPoint
import OAI.AlgebraicGeometry.Seshadri.Configurations.GlobalCenter
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticReindex
import OAI.AlgebraicGeometry.Seshadri.Configurations.SmoothRationalPoints

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

omit [Fintype σ] in
lemma embedding_reindex_nonempty [IsIntegral X] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] :
    ∃ t : Option σ → (O X ⟶ M), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsClosedImmersion (sectionsMorphism k t ht) ∧
      (SectionOpens.isoOpen (t none) : Set X).Nonempty := by
  classical
  let x : X := Classical.ofNonempty
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  let e : Option σ ≃ Option σ := Equiv.swap none i
  let ht := sections_cover_reindex s hs e
  refine ⟨s ∘ e, ht, sectionsMorphism_reindex_closed k s hs e ht, x, ?_⟩
  change x ∈ SectionOpens.isoOpen (s (e none))
  simpa only [e, Equiv.swap_apply_left] using hi

lemma exists_centered_embedding [IsIntegral X] [IsAlgClosed K] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] :
    ∃ t : Option σ → (O X ⟶ M), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsClosedImmersion (sectionsMorphism k t ht) ∧
      ∃ y : X, ∀ x : X, x ∉ centeredOpen t ↔ x = y := by
  obtain ⟨s, hs, hcl, h₀⟩ := embedding_reindex_nonempty k s hs
  have := hcl
  let U := SectionOpens.isoOpen (s none)
  let kU := U.ι.appTop.hom.comp k
  let a := fun i => coefficient (sectionFrame (s none)) (restrictSection U.ι (s i))
  obtain ⟨hUa, hgen⟩ := sectionsMorphism_chart_generators k s hs none
  have : IsAffine U.toScheme := hUa
  let : Nonempty U := ⟨⟨h₀.choose, h₀.choose_spec⟩⟩
  let : Algebra K Γ(U.toScheme, ⊤) := kU.toAlgebra
  have ha : Function.Surjective (MvPolynomial.aeval (R := K) a) := hgen
  have : Algebra.FiniteType K Γ(U.toScheme, ⊤) := Algebra.FiniteType.of_surjective
    (MvPolynomial.aeval (R := K) a) ha
  obtain ⟨p⟩ := exists_point_finite_type (K := K) (R := Γ(U.toScheme, ⊤))
  let t := shiftedSections k s (fun i => -p (a (some i)))
  let ht := shiftedSections_cover k s hs (fun i => -p (a (some i)))
  have hp : p.toRingHom.comp kU = RingHom.id K := p.comp_algebraMap
  obtain ⟨y, hy⟩ := centeredOpen_complement_singleton k s hs p.toRingHom hp
  exact ⟨t, ht, shiftedSections_closed k s hs h₀ _, y, hy⟩

omit [Fintype σ] in

lemma centeredOpen_nonempty_of_singleton [IsIntegral X] [IsAlgClosed K] [Uncountable K]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    {M : X.Modules} (s : Option σ → (O X ⟶ M)) (y : X)
    (hy : ∀ x : X, x ∉ centeredOpen s ↔ x = y) :
    (centeredOpen s : Set X).Nonempty := by
  by_contra h
  apply smooth_scheme_uncountable_rational_points g 2 (by decide)
  apply (Set.countable_singleton y).mono
  rintro x ⟨p, rfl⟩
  exact (hy _).mp (fun hx => h ⟨_, hx⟩)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
