import OAI.Analysis.KadisonKastler.CommonPositionInitialAlignment
import OAI.Analysis.KadisonKastler.CommonReducingEquiv
import OAI.Analysis.KadisonKastler.ConjugateFactor

namespace OAI

/-! # A faithful neighboring factor on the first factor's standard cyclic space -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

theorem faithfulCyclic_projection_ne_zero (M : VonNeumannAlgebra H) :
    (faithfulCyclicSpace M).starProjection ≠ 0 := by
  intro hz
  have hv := (faithfulCyclicSpace M).starProjection_mem_subspace_eq_self
    (faithfulCyclicVector M)
  rw [hz, zero_apply] at hv
  have hn := norm_faithfulCyclicVector M
  have hv0 : faithfulCyclicVector M = 0 := Subtype.ext hv.symm
  rw [hv0, norm_zero] at hn
  exact zero_ne_one hn

theorem initial_cyclic_neighbor_of_alignment
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra) {γ : ℝ}
    (u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H))
    (huR : (u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) ∈
      (countableDiagonalAlgebra R).commutant)
    (hp : (faithfulCyclicSpace M).starProjection ∈
      (unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)).commutant)
    (hun : ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ ≤ 200000000 * γ) :
    ∃ (P : VonNeumannAlgebra (faithfulCyclicSpace M))
      (e : Algebra N ≃⋆ₐ[ℂ] Algebra P),
      IsII1Factor P.toStarSubalgebra ∧
      (∀ r : Algebra R,
        (e (coordinateInclusion hRN r)).val = faithfulCyclicHom M (coordinateInclusion hRM r)) ∧
      (∀ (a : Algebra M) (b : Algebra N), ‖b‖ ≤ 1 →
        ‖faithfulCyclicHom M a - (e b).val‖ ≤
          400000000 * γ + ‖a.val - b.val‖) ∧
      P = generatedVonNeumannAlgebra
        (commutantReducingHom (faithfulCyclicSpace M)
          (unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)) hp).range := by
  let E := faithfulCyclicSpace M
  let D := unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)
  let P := generatedVonNeumannAlgebra (commutantReducingHom E D hp).range
  have hD : IsII1Factor D.toStarSubalgebra :=
    unitaryConjugateAlgebra_isII1 (star u) (countableDiagonal_isII1 N hN)
  let f := reducingFactorEquiv E D hp (faithfulCyclic_projection_ne_zero M)
    (scalarCenter_of_isII1 D hD)
  let e : Algebra N ≃⋆ₐ[ℂ] Algebra P :=
    (countableDiagonalEquiv N).trans ((unitaryConjugateEquiv (star u)
      (countableDiagonalAlgebra N)).trans f)
  have he (b : Algebra N) :
      (e b).val = cornerCompression E (unitaryConj (star u) (l2Diagonal b.val)) := rfl
  have hstar : ‖((star u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H)) :
      CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ =
      ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using norm_star
      ((u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1)
  refine ⟨P, e, isII1Factor_of_starAlgEquiv e hN (traceHilbertVonNeumann_wotClosed P), ?_, ?_, rfl⟩
  · intro r
    rw [he]
    have hr : l2Diagonal r.val ∈ countableDiagonalAlgebra R :=
      subset_generatedVonNeumannAlgebra _ ⟨r, rfl⟩
    have hstarR : ((star u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H)) :
        CountableHilbertSum H →L[ℂ] CountableHilbertSum H) ∈
        (countableDiagonalAlgebra R).commutant := star_mem huR
    change cornerCompression E (unitaryConj (star u) (l2Diagonal r.val)) = _
    rw [unitaryConj_eq_self_of_mem_commutant hstarR hr]
    rfl
  · intro a b hb
    have hleft : faithfulCyclicHom M a = cornerCompression E (l2Diagonal a.val) := rfl
    have hdiff : faithfulCyclicHom M a - (e b).val =
        cornerCompression E (l2Diagonal a.val - unitaryConj (star u) (l2Diagonal b.val)) := by
      exact (congrArg₂ (fun S T => S - T) hleft (he b)).trans
        ((cornerCompression E).map_sub _ _).symm
    apply (congrArg norm hdiff).le.trans
    apply (norm_cornerCompression_le E _).trans
    have hdist := norm_sub_le_norm_sub_add_norm_sub (l2Diagonal a.val)
      (l2Diagonal b.val) (unitaryConj (star u) (l2Diagonal b.val))
    have hmove := norm_unitaryConj_sub_le (star u) (l2Diagonal b.val)
    rw [hstar, norm_l2Diagonal H] at hmove
    have hd : ‖l2Diagonal a.val - l2Diagonal b.val‖ = ‖a.val - b.val‖ := by
      change ‖(l2DiagonalHom (E := H)) a.val - (l2DiagonalHom (E := H)) b.val‖ = _
      rw [← map_sub]
      exact norm_l2Diagonal H _
    rw [hd, norm_sub_rev (l2Diagonal b.val)] at hdist
    have hmove' : ‖unitaryConj (star u) (l2Diagonal b.val) - l2Diagonal b.val‖ ≤
        400000000 * γ := hmove.trans (by
      change 2 * ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ * ‖b‖ ≤ _
      nlinarith [norm_nonneg ((u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1)])
    linarith

theorem exists_initial_cyclic_neighbor
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ < 1 / 256000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    ∃ (P : VonNeumannAlgebra (faithfulCyclicSpace M))
      (e : Algebra N ≃⋆ₐ[ℂ] Algebra P),
      IsII1Factor P.toStarSubalgebra ∧
      (∀ r : Algebra R,
        (e (coordinateInclusion hRN r)).val = faithfulCyclicHom M (coordinateInclusion hRM r)) ∧
      (∀ (a : Algebra M) (b : Algebra N), ‖b‖ ≤ 1 →
        ‖faithfulCyclicHom M a - (e b).val‖ ≤
          400000000 * γ + ‖a.val - b.val‖) := by
  exact (exists_common_cyclic_projection_alignment (H := H) M N R hRM hRN hN
    (γ := γ) hγ hsmall hMN hNM).elim (fun u hu =>
      (initial_cyclic_neighbor_of_alignment (H := H) M N R hRM hRN hN (γ := γ) u
        hu.1 hu.2.1 hu.2.2.2).elim (fun P hP => hP.elim (fun e he =>
          ⟨P, e, he.1, he.2.1, he.2.2.1⟩)))

end

end KadisonKastler

end OAI
