import OAI.Analysis.KadisonKastler.AmenableEmbedding

namespace OAI

/-! # The elementary gap bound for comparing two normalizing unitaries -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem comparison_unitary_gap (M N : VonNeumannAlgebra H)
    (u v : unitary (H →L[ℂ] H)) (hu : Conjugates u M M) (hv : Conjugates v N N) :
    kkDistance (unitaryConjugateAlgebra (v * star u) M) M ≤ 2 * kkDistance M N := by
  have hprod := hu.symm.trans (conjugates_unitaryConjugateAlgebra v M)
  have hsame : unitaryConjugateAlgebra (v * star u) M = unitaryConjugateAlgebra v M := by
    apply SetLike.coe_injective
    have hc := conjugates_unitaryConjugateAlgebra (v * star u) M
    change unitaryConj (v * star u) '' (M : Set (H →L[ℂ] H)) =
      (unitaryConjugateAlgebra (v * star u) M : Set (H →L[ℂ] H)) at hc
    change unitaryConj (v * star u) '' (M : Set (H →L[ℂ] H)) =
      (unitaryConjugateAlgebra v M : Set (H →L[ℂ] H)) at hprod
    exact hc.symm.trans hprod
  have hgap : kkDistance (unitaryConjugateAlgebra v M) N = kkDistance M N :=
    kkDistance_eq_of_conjugates (conjugates_unitaryConjugateAlgebra v M) hv
  rw [hsame]
  calc
    _ ≤ kkDistance (unitaryConjugateAlgebra v M) N + kkDistance N M :=
      kkDistance_triangle _ _ _
    _ = 2 * kkDistance M N := by rw [hgap, kkDistance_comm N M]; ring

end

end KadisonKastler

end OAI
