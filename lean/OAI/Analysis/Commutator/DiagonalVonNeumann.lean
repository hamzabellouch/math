import Mathlib
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def matrixUnit (i j : ι) : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι :=
  (single ι i).comp (PiLp.proj 2 (fun _ : ι => H) j)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma matrixUnit_apply (i j : ι) (x : SumSpace (H:=H) ι) :
    matrixUnit ι i j x=single ι i (x j) := rfl

omit [CompleteSpace H] [Fintype ι] in
lemma matrixUnit_single (i j : ι) (x : H) :
    matrixUnit ι i j (single ι j x)=single ι i x := by
  simp

lemma matrixUnit_commutes (i j : ι) (T : H →L[ℂ] H) :
    matrixUnit ι (H:=H) i j*diagonal (H:=H) ι T=
      diagonal (H:=H) ι T*matrixUnit ι i j := by
  ext x k
  simp [mul_apply_eq_comp,diagonal_single]

lemma diagonal_of_matrixUnits (i₀ : ι) (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hT : ∀ i j, matrixUnit ι i j*T=T*matrixUnit ι i j) :
    T=diagonal (H:=H) ι (entry ι T i₀ i₀) := by
  have hs : ∀ j x, T (single ι j x)=single ι j (entry ι T i₀ i₀ x) := by
    intro j x
    have he := congrArg (fun R : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι => R (single ι i₀ x)) (hT j i₀)
    simpa [mul_apply_eq_comp,entry_apply] using he.symm
  ext x j
  conv_lhs => rw [←sum_single ι x]
  simp only [map_sum,hs]
  simp

def diagonalVonNeumann (i₀ : ι) (M : VonNeumannAlgebra H) : VonNeumannAlgebra (SumSpace (H:=H) ι) where
  toStarSubalgebra := M.toStarSubalgebra.map (diagonal (H:=H) ι)
  centralizer_centralizer' := by
    ext T
    constructor
    · intro hT
      have hU : ∀ i j, matrixUnit ι i j*T=T*matrixUnit ι i j := by
        intro i j
        apply hT
        rintro R ⟨a,ha,rfl⟩
        exact (matrixUnit_commutes ι i j a).symm
      let a := entry ι T i₀ i₀
      have he : T=diagonal (H:=H) ι a := diagonal_of_matrixUnits ι i₀ T hU
      have ha : a∈M := by
        rw [←SetLike.mem_coe,←M.centralizer_centralizer]
        intro b hb
        apply entry_commutes ι T b
        apply hT
        rintro R ⟨d,hd,rfl⟩
        have hh : d*b=b*d := hb d hd
        change diagonal (H:=H) ι d * diagonal (H:=H) ι b =
          diagonal (H:=H) ι b * diagonal (H:=H) ι d
        exact (map_mul (diagonal (H:=H) ι) d b).symm.trans
          ((congrArg (diagonal (H:=H) ι) hh).trans (map_mul (diagonal (H:=H) ι) b d))
      exact ⟨a,ha,he.symm⟩
    · rintro ⟨a,ha,rfl⟩
      apply diagonal_bicommutant ι M.toStarSubalgebra
      change a ∈ Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H)))
      rw [M.centralizer_centralizer]
      exact ha

@[simp] lemma mem_diagonalVonNeumann (i₀ : ι) (M : VonNeumannAlgebra H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    T∈diagonalVonNeumann ι i₀ M ↔ ∃ a∈M,diagonal (H:=H) ι a=T := Iff.rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
