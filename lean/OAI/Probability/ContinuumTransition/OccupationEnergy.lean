import OAI.Probability.ContinuumTransition.PairMoments

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_le_cell_pairs {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (W : Space → Space → ℝ) (hWsym : ∀ x y, W x y = W y x)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i))
    (hW : ∀ i j, W (x i) (x j) ≤ J (c i) (c j)) :
    gibbsEnergy W x ≤ (1/2:ℝ)*∑ k, ∑ l,
      J k l*occupation (latticeCell (e k)) x*occupation (latticeCell (e l)) x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hf (k : κ) : occupation (latticeCell (e k)) x = (Fintype.card {i : ι // c i = k} : ℝ) := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change cellIndex (x i) = e k ↔ c i = k
    rw [hc i, he.eq_iff]
  simp_rw [hf]
  rw [gibbsEnergy_eq_pairSum _ hWsym]
  exact pairSum_le_cell_quadratic c J (fun i j => W (x i) (x j)) hJ (fun i j => hWsym _ _) hW

noncomputable def interactionFamily (F : ConfigFamily) (W : Space → Space → ℝ) : ConfigFamily :=
  fun ι _ x => F ι x*gibbsEnergy W x

theorem interactionFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (W : Space → Space → ℝ) (hW : ∀ x y, 0 ≤ W x y) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ interactionFamily F W ι x := mul_nonneg (hF ι x) (gibbsEnergy_nonneg W hW x)

end ContinuumTemperature
end

end OAI
