import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.PrincipalSectionIdeal
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticBertini
import OAI.AlgebraicGeometry.Seshadri.Projective.GlobalQuartic

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionIdeal_eq_of_local_equations {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (J : X.IdealSheafData)
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : Γ(X, U.1), J.ideal U = Ideal.span {f} ∧
        ∃ b : M.restrict U.1.ι ≅ O U.1.toScheme,
          U.1.topIso.hom (coefficient b (restrictSection U.1.ι
            (sectionCombination k s v))) = f) :
    sectionIdeal k s hs v = J := by
  apply idealSheaf_ext_local
  intro x
  obtain ⟨U, hx, f, hf, b, hb⟩ := h x
  exact ⟨U, hx, (sectionIdeal_on_any_frame k s hs v U b).trans (by rw [hb, hf])⟩

lemma sectionCombination_reindex [Fintype τ] {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (v : τ → K) (e : τ ≃ σ) :
    sectionCombination k (s ∘ e) v = sectionCombination k s (v ∘ e.symm) := by
  classical
  unfold sectionCombination
  apply Fintype.sum_equiv e
  intro i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

lemma sectionIdeal_reindex [Fintype τ] {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : τ → K) (e : τ ≃ σ) :
    sectionIdeal k (s ∘ e) (sections_cover_reindex s hs e) v =
      sectionIdeal k s hs (v ∘ e.symm) :=
  sectionIdeal_eq_of_combination k _ _ _ _ _ _ (sectionCombination_reindex k s v e)

theorem exists_global_quartic_smooth_integral_away
    [CharZero K] [IsAlgClosed K] [Uncountable K] {M : X.Modules}
    (g : X ⟶ Spec (CommRingCat.of K))
    (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    {n : ℕ} (e : Option (Fin n) ≃ QuarticIndex σ)
    [IsIntegral (centeredOpen s).toScheme] [CompactSpace (centeredOpen s)]
    [SmoothOfRelativeDimension 2 ((centeredOpen s).ι ≫ g)]
    (P : MvPolynomial (Option (Fin n)) K) (hP : P ≠ 0) :
    let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    let V := centeredOpen s
    ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
      let J := (doublePointQuarticIdeal k s hs (v ∘ e.symm)).comap V.ι
      IsIntegral J.subscheme ∧ Smooth (J.subschemeι ≫ V.ι ≫ g) := by
  let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let V := centeredOpen s
  let t := fun i => restrictSection V.ι (s i)
  let q := doublePointQuartics t
  let hq := doublePointQuartics_cover t (restricted_centered_cover s)
  let h := sectionsMorphism (V.ι.appTop.hom.comp k) (q ∘ e)
    (sections_cover_reindex q hq e)
  obtain ⟨v, hv, hi, hsm, heq⟩ := doublePointQuartics_bertini g s hs e P hP
  have hid : sectionIdeal (V.ι.appTop.hom.comp k) (q ∘ e)
      (sections_cover_reindex q hq e) v = projectiveHyperplane h v := by
    apply sectionIdeal_eq_of_local_equations
    intro x
    obtain ⟨U, hx, f, _, hf, b, hb⟩ := heq x
    exact ⟨U, hx, f, hf, b, hb⟩
  have hext : (doublePointQuarticIdeal k s hs (v ∘ e.symm)).comap V.ι =
      projectiveHyperplane h v := by
    rw [doublePointQuarticIdeal_restrict, ← sectionIdeal_reindex _ q hq v e]
    exact hid
  refine ⟨v, hv, ?_⟩
  dsimp only
  rw [hext]
  exact ⟨hi, hsm⟩

end
end MaximalSeshadri.Projective
end


end
end

end OAI
