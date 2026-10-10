import OAI.Analysis.Pureness.Comparison.OrthogonalSupply
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_mul_eq_zero_symm {c d : A} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : c * d = 0) : d * c = 0 := by
  simpa only [star_mul, hc.star_eq, hd.star_eq, star_zero] using congrArg star h

theorem exists_finite_orthogonal_positive_family [IsSimpleCStarAlgebra A]
    (hinfinite : ¬ FiniteDimensional ℂ A) (n : ℕ) {b : A} (hb : 0 ≤ b) (hbn : b ≠ 0) :
    ∃ c : Fin n → A, (∀ i, 0 ≤ c i ∧ c i ≠ 0 ∧ c i ∈ hereditaryCorner b hb) ∧
      ∀ i j, i ≠ j → c i * c j = 0 := by
  induction n generalizing b with
  | zero => exact ⟨Fin.elim0, by intro i; exact i.elim0, by intro i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨c, d, hc, hd, hcn, hdn, hcd, hcm, hdm⟩ :=
      exists_orthogonal_positive_pair hinfinite hb hbn
    obtain ⟨f, hf, horth⟩ := ih hd hdn
    refine ⟨Fin.cons c f, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hc, hcn, hcm⟩
      · exact ⟨(hf j).1, (hf j).2.1,
          hereditaryCorner_le_of_mem hb hd hdm (hf j).2.2⟩
    · intro i j hij
      refine Fin.cases ?_ (fun i' => ?_) i j hij
      · intro j hne
        refine Fin.cases ?_ (fun j' => ?_) j hne
        · exact fun h => (h rfl).elim
        · intro _
          exact positive_mul_eq_zero_symm (hf j').1 hc
            (hereditaryCorner_mul_eq_zero hd (positive_mul_eq_zero_symm hc hd hcd) (hf j').2.2)
      · intro j hne
        refine Fin.cases ?_ (fun j' => ?_) j hne
        · intro _
          exact hereditaryCorner_mul_eq_zero hd (positive_mul_eq_zero_symm hc hd hcd) (hf i').2.2
        · intro h
          exact horth i' j' (fun heq => h (congrArg Fin.succ heq))
end CuntzComparison

end OAI
