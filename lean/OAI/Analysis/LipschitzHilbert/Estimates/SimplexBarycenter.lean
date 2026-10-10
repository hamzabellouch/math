import OAI.Analysis.LipschitzHilbert.Phase.SimplexTubeInterpolation

namespace OAI

/-! The shift-simplex vertices give the identical bound at the diagonal
parameter μ/K. The estimate has no factor depending on the number of shifts. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem phaseTubeBound_barycenter (F : (ι → ℂ) → ℂ) (D : Set (ι → ℝ))
    (hD : Convex ℝ D) (C mu : ℝ) (hC : 0 < C)
    (hentire : ∀ a ∈ D, ∀ b ∈ D, ∀ eta,
      Differentiable ℂ (fun z => F (phaseTubeLine a b eta z)))
    (hbounded : ∃ M : ℝ, ∀ a ∈ D, phaseTubeBound F M a)
    (hvertices : ∀ i : ι, Pi.single i mu ∈ D)
    (hvertex : ∀ i : ι, phaseTubeBound F C (Pi.single i mu)) :
    phaseTubeBound F C (fun _ => mu/(Fintype.card ι:ℝ)) := by
  have hcard : (Fintype.card ι:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := ι)
  have hsum : ∑ _i : ι, (1/(Fintype.card ι:ℝ)) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hmean : (∑ i : ι, (1/(Fintype.card ι:ℝ)) • Pi.single i mu) =
      fun _ => mu/(Fintype.card ι:ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,mul_ite,
      div_eq_mul_inv,mul_comm]
  rw [← hmean]
  exact phaseTubeBound_finite_convex_combination F D hD C hC hentire hbounded Finset.univ
    (fun _ => 1/(Fintype.card ι:ℝ)) (fun i => Pi.single i mu)
    (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)) hsum
    (fun i _ => hvertices i) (fun i _ => hvertex i)

end LipschitzHilbert

end

end OAI
