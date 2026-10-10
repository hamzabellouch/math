import OAI.Analysis.CoulombTransport.ContactSelection
import OAI.Analysis.CoulombTransport.CommonBranches

namespace OAI

universe uE

/-! Extract the canonical four-branch selector from an original contact graph. -/

namespace Problem356.ContactSelection

variable {E : Type uE} [TopologicalSpace E]

/-- A permuted original contact graph with its first coordinate central selects
one of the four inverse-reparametrized branches, in the canonical ordering
`Y₁,W₁,Y₂,W₂`. Only the two displayed outer points need lie outside `B`. -/
theorem second_selects_common_four
    (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} {x y z s : E} {k : Fin 2}
    (hperm : List.Perm [x, y, z] [X k s, s, Z k s])
    (hx : x ∈ B) (hs : s ∈ (X k).source)
    (hsB : s ∉ B) (hzB : Z k s ∉ B) :
    ∃ i : Fin 4, y = CommonBranches.four X Z i x := by
  have hcentral := first_eq_of_perm hperm hx hsB hzB
  have hinv : (X k).symm x = s := by
    rw [hcentral]
    exact (X k).left_inv hs
  rcases second_eq_or_third_of_perm hperm hx hsB hzB with hy | hy
  · fin_cases k
    · exact ⟨0, hy.trans hinv.symm⟩
    · exact ⟨2, hy.trans hinv.symm⟩
  · have hz : y = Z k ((X k).symm x) :=
      hy.trans (congrArg (fun q => Z k q) hinv.symm)
    fin_cases k
    · exact ⟨1, hz⟩
    · exact ⟨3, hz⟩

end Problem356.ContactSelection

end OAI
