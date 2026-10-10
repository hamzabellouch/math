import OAI.Analysis.Laughlin.Fock.FourLabels
import OAI.Analysis.Laughlin.FourBody.Quadruples

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

abbrev FourOccupation (Q D : ℕ) :=
  {A : Finset (Fin (Q+1)) // A.card=4 ∧ (∑ i ∈ A, i.val)=D+1}

noncomputable def occupationQuadruple (Q D : ℕ) (A : FourOccupation Q D) :
    {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
  let l := occupationFourLabels Q A.val A.property.1
  ⟨((l 0).val,(l 1).val,(l 2).val,(l 3).val),
    (Certificate.mem_quadruples D _ _ _ _).mpr
      ⟨l.strictMono (by decide),l.strictMono (by decide),l.strictMono (by decide),
        (occupationFourLabels_sum Q A.val A.property.1).symm.trans A.property.2⟩⟩

theorem occupationQuadruple_injective (Q D : ℕ) : Function.Injective (occupationQuadruple Q D) := by
  intro A B h
  have ht := congrArg Subtype.val h
  simp only [occupationQuadruple,Prod.mk.injEq] at ht
  have hl : occupationFourLabels Q A.val A.property.1 = occupationFourLabels Q B.val B.property.1 := by
    ext i
    fin_cases i
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2
  apply Subtype.ext
  rw [← occupationFourLabels_range Q A.val A.property.1,
    ← occupationFourLabels_range Q B.val B.property.1,hl]

noncomputable def quadrupleEmbedding (Q D a b c d : ℕ) (hQ : D+1 ≤ Q)
    (h : (a,b,c,d) ∈ Certificate.quadruples D) : Fin 4 ↪o Fin (Q+1) := by
  have hh := (Certificate.mem_quadruples D a b c d).mp h
  let f : Fin 4 → Fin (Q+1) := ![⟨a,by omega⟩,⟨b,by omega⟩,⟨c,by omega⟩,⟨d,by omega⟩]
  have hf : StrictMono f := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp [f,Fin.lt_def] <;> omega
  exact OrderEmbedding.ofStrictMono f hf

end Laughlin.Fock

end OAI
