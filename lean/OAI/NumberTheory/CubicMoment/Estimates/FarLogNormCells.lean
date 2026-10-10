import OAI.NumberTheory.CubicMoment.Estimates.NearLogNormCells

namespace OAI

/-! Far cells are the exact complement of the actual near-cell graph.
Every product in such a cell has the lower frequency bound needed for IBP. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def allLogNormCells (P S : Finset Eisenstein) (J A B : ℝ) : Finset (ℤ × ℤ) :=
  (P.image (logNormCell J A)).product (S.image (logNormCell J B))

def farLogNormCells (P S : Finset Eisenstein) (J A B X₀ : ℝ) : Finset (ℤ × ℤ) :=
  allLogNormCells P S J A B \ nearLogNormCells P S J A B X₀

lemma nearLogNormCells_subset (P S : Finset Eisenstein) (J A B X₀ : ℝ) :
    nearLogNormCells P S J A B X₀ ⊆ allLogNormCells P S J A B :=
  Finset.filter_subset _ _

lemma farLogNormCells_subset (P S : Finset Eisenstein) (J A B X₀ : ℝ) :
    farLogNormCells P S J A B X₀ ⊆ allLogNormCells P S J A B :=
  Finset.sdiff_subset

lemma farLogNormCells_frequency (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (J A B : ℝ) {X₀ : ℝ} (hX : 0 < X₀)
    {e : ℤ × ℤ} (he : e ∈ farLogNormCells P S J A B X₀)
    {a b : Eisenstein} (ha : a ∈ logNormCellSupport P J A e.1)
    (hb : b ∈ logNormCellSupport S J B e.2) :
    1 < |J*(Real.log (norm (a*b))-Real.log X₀)| := by
  have heall := (Finset.mem_sdiff.mp he).1
  have henear := (Finset.mem_sdiff.mp he).2
  obtain ⟨ha,hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hbj⟩ := Finset.mem_filter.mp hb
  have hn : norm (a*b) ≠ 0 := norm_eq_zero_iff.not.mpr
    (mul_ne_zero (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb)))
  by_contra hh
  apply henear
  apply Finset.mem_filter.mpr
  refine ⟨heall,a,ha,b,hb,hai,hbj,?_⟩
  rw [Real.log_div hn hX.ne']
  exact le_of_not_gt hh

lemma sum_near_farLogNormCells {M : Type*} [AddCommMonoid M]
    (P S : Finset Eisenstein) (J A B X₀ : ℝ) (f : ℤ × ℤ → M) :
    (∑ e ∈ nearLogNormCells P S J A B X₀, f e)+
      (∑ e ∈ farLogNormCells P S J A B X₀, f e) =
      ∑ e ∈ allLogNormCells P S J A B, f e := by
  rw [add_comm]
  exact Finset.sum_sdiff (nearLogNormCells_subset P S J A B X₀)

end CubicFirstMoment

end

end OAI
