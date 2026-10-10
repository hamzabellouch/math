import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedGeometry

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma half_small {α : Type*} (T : Finset α) (w : α→ℝ) (τ : ℝ)
    (hτ : 0<τ) (hw : ∀ x∈T,0≤w x) (hm : (∑ x∈T,w x)≤τ*T.card) :
    (T.card:ℝ)/2≤((T.filter (fun x => w x≤2*τ)).card:ℝ) := by
  let A := T.filter (fun x => w x≤2*τ)
  let B := T\A
  have hb : ∀ x∈B,2*τ≤w x := by
    intro x hx
    have hh := mem_sdiff.mp hx
    exact (lt_of_not_ge (fun he => hh.2 (mem_filter.mpr ⟨hh.1,he⟩))).le
  have hsum : 2*τ*(B.card:ℝ)≤∑ x∈T,w x := by
    calc
      _ = ∑ x∈B,2*τ := by simp [mul_comm]
      _ ≤ ∑ x∈B,w x := sum_le_sum hb
      _ ≤ ∑ x∈T,w x := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x hx _ => hw x hx)
  have hc : B.card+A.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have hc' : (B.card:ℝ)+(A.card:ℝ)=T.card := by exact_mod_cast hc
  change (T.card:ℝ)/2≤(A.card:ℝ)
  nlinarith [hsum.trans hm]

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedSparse_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedSparse_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedSparse_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem sparse_training (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty)
    (τ : ℝ) (hτ : 0<τ) (hτsmall : 2*τ<9/10)
    (hSparse : (∑ H∈T,mass S c H)≤τ*T.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    E₀.Nonempty ∧ (T.card:ℝ)/2≤(E₀.card:ℝ) ∧
      E₀⊆badHyperplanes S U bs c ∧ ∀ H∈E₀,mass S c H≤2*τ := by
  dsimp only
  have hh := half_small T (mass S c) τ hτ (by intro H _; unfold mass; positivity) hSparse
  refine ⟨?_,hh,?_,?_⟩
  · apply card_pos.mp
    have hp : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
    have : (0:ℝ)<(T.filter (fun H => mass S c H≤2*τ)).card := lt_of_lt_of_le (by linarith) hh
    exact_mod_cast this
  · intro H hH
    have hb := (mem_filter.mp hH).2
    have habs : 1/10 < |mass S c H-1| := by
      rw [abs_of_neg (by linarith)]
      linarith
    simp only [badHyperplanes,RegularPencils.exceptional,mem_filter,mem_univ,true_and]
    exact Or.inl habs
  · intro H hH
    exact (mem_filter.mp hH).2

omit [Finite K] [FiniteDimensional K V] in

lemma sparse_training_exponent (S : Finset (Projectivization K V))
    (c L : ℝ≥0) (R : ℕ) (H : Projectivization K (Module.Dual K V))
    (τ : ℝ) (hH : mass S c H≤2*τ) :
    ((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤2*τ*((L:ℝ)*R) := by
  have hh := mul_le_mul_of_nonneg_left hH (show 0≤(L:ℝ)*R by positivity)
  unfold mass at hh
  simp only [inc,NNReal.coe_mul]
  nlinarith [hh]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
