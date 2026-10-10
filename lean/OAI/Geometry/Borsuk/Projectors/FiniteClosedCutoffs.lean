import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set Finset
lemma finite_closed_cutoffs {A X : Type*} [Fintype A] [DecidableEq A]
    [TopologicalSpace X] [NormalSpace X]
    (K S : A → Set X) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hdis : Pairwise (fun a b => Disjoint (K a) (K b))) :
    ∃ U : A → Set X, ∃ q : A → C(X,ℝ), (∀ a, IsOpen (U a)) ∧
      (∀ a, K a ⊆ U a) ∧ (∀ a x, q a x ∈ Icc (0:ℝ) 1) ∧
      (∀ a x, x ∈ U a → q a x = 1) ∧
      (∀ a x, q a x ≠ 0 → x ∈ S a) ∧
      Pairwise (fun a b => Disjoint (Function.support (q a)) (Function.support (q b))) := by
  classical
  let Z : A → Set X := fun a => (S a)ᶜ ∪ ⋃ b ∈ (Finset.univ.erase a : Finset A), K b
  have hZ (a) : IsClosed (Z a) := (hS a).isClosed_compl.union (isClosed_biUnion_finset fun b _ => hK b)
  have hd (a) : Disjoint (Z a) (K a) := by
    apply Set.disjoint_left.mpr
    intro x hx hxa
    rcases hx with hs | hb
    · exact hs (hKS a hxa)
    · obtain ⟨b,hb,hxb⟩ := Set.mem_iUnion₂.mp hb
      exact Set.disjoint_left.mp (hdis (Finset.ne_of_mem_erase hb)) hxb hxa
  have hs (a) := exists_continuous_zero_one_of_isClosed (hZ a) (hK a) (hd a)
  choose p hp0 hp1 hpb using hs
  let score : A → X → ℝ := fun a x => 2*p a x - ∑ b, p b x
  have hscore (a) : Continuous (score a) :=
    ((p a).continuous.const_mul 2).sub (continuous_finsetSum _ (fun b _ => (p b).continuous))
  have hscoreK (a x) (hx : x ∈ K a) : score a x = 1 := by
    have hpothers (b) (hb : b ≠ a) : p b x = 0 := hp0 b (Or.inr (Set.mem_iUnion₂.mpr ⟨a,Finset.mem_erase.mpr ⟨Ne.symm hb,Finset.mem_univ _⟩,hx⟩))
    dsimp [score]
    rw [Finset.sum_eq_single a]
    · rw [hp1 a hx]; norm_num
    · intro b _ hb; exact hpothers b hb
    · simp
  let U : A → Set X := fun a => {x | (3/4:ℝ) < score a x}
  let q : A → C(X,ℝ) := fun a => ⟨fun x => max 0 (min 1 (4*(score a x-1/2))),
    continuous_const.max (continuous_const.min (((hscore a).sub continuous_const).const_mul 4))⟩
  have hpos (a x) (hx : q a x ≠ 0) : (1/2:ℝ) < score a x := by
    change max 0 (min 1 (4*(score a x-1/2))) ≠ 0 at hx
    by_contra hn
    apply hx
    exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  refine ⟨U,q,fun a => isOpen_lt continuous_const (hscore a),?_,?_,?_,?_,?_⟩
  · intro a x hx
    change (3/4:ℝ) < score a x
    rw [hscoreK a x hx]; norm_num
  · intro a x
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · intro a x hx
    change max 0 (min 1 (4*(score a x-1/2))) = 1
    rw [min_eq_left (by change (3/4:ℝ) < score a x at hx; linarith)]
    norm_num
  · intro a x hx
    by_contra hn
    have hz : p a x = 0 := hp0 a (Or.inl hn)
    have hsum : 0 ≤ ∑ b, p b x := Finset.sum_nonneg (fun b _ => (hpb b x).1)
    have hh := hpos a x hx
    dsimp [score] at hh
    rw [hz] at hh
    linarith
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have ha := hpos a x hxa
    have hb := hpos b x hxb
    have hs : p a x + p b x ≤ ∑ c, p c x := by
      calc
        _ = ∑ c ∈ ({a,b} : Finset A), p c x := by simp [hab]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => (hpb c x).1)
    dsimp [score] at ha hb
    linarith
end BorsukNine

end OAI
