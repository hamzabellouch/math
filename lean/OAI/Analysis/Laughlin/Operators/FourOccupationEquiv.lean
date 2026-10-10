import OAI.Analysis.Laughlin.Fock.Quadruple

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationQuadruple_surjective (Q D : ℕ) (hQ : D+1 ≤ Q) :
    Function.Surjective (occupationQuadruple Q D) := by
  rintro ⟨⟨a,b,c,d⟩,h⟩
  let l := quadrupleEmbedding Q D a b c d hQ h
  let A := Set.powersetCard.ofFinEmbEquiv l
  have hl : occupationFourLabels Q A.val A.property = l :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply l
  have hw : (∑ i ∈ A.val, i.val)=D+1 := by
    rw [occupationFourLabels_sum Q A.val A.property,hl]
    exact (Certificate.mem_quadruples D a b c d).mp h |>.2.2.2
  refine ⟨⟨A.val,A.property,hw⟩,?_⟩
  apply Subtype.ext
  simp only [occupationQuadruple,hl]
  rfl

noncomputable def fourOccupationEquiv (Q D : ℕ) (hQ : D+1 ≤ Q) :
    FourOccupation Q D ≃ {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
  Equiv.ofBijective (occupationQuadruple Q D)
    ⟨occupationQuadruple_injective Q D,occupationQuadruple_surjective Q D hQ⟩

theorem sum_fourOccupations (Q D : ℕ) (hQ : D+1 ≤ Q) (f : (ℕ×ℕ×ℕ×ℕ) → ℝ) :
    ∑ A : FourOccupation Q D, f (occupationQuadruple Q D A).val =
      ((Certificate.quadruples D).map f).sum := by
  classical
  let : Fintype {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
    Fintype.ofFinset (Certificate.quadruples D).toFinset (by intro t; change t ∈ (Certificate.quadruples D).toFinset ↔ t ∈ Certificate.quadruples D; simp)
  rw [← List.sum_toFinset f (Certificate.quadruples_nodup D)]
  rw [Finset.sum_subtype (p := fun t => t ∈ Certificate.quadruples D) (Certificate.quadruples D).toFinset (by simp)]
  exact (fourOccupationEquiv Q D hQ).sum_comp (fun t => f t.val)

end Laughlin.Fock

end OAI
