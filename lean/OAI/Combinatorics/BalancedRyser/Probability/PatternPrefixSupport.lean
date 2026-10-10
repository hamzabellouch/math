import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas
import OAI.Combinatorics.BalancedRyser.Probability.PatternOrderingAdapter

namespace OAI

namespace Balanced.PatternModel

attribute [local instance] Classical.propDecidable

variable (P : PatternModel)

def freshPrefixSupport (K₀ : Finset P.Color) (pre : List P.Label) : Finset P.Color :=
  pre.foldr (fun a U => U ∪ (P.support a \ K₀)) ∅

@[simp] lemma freshPrefixSupport_nil (K₀ : Finset P.Color) :
    P.freshPrefixSupport K₀ [] = ∅ := rfl

@[simp] lemma freshPrefixSupport_cons (K₀ : Finset P.Color) (a : P.Label)
    (pre : List P.Label) :
    P.freshPrefixSupport K₀ (a :: pre) =
      P.freshPrefixSupport K₀ pre ∪ (P.support a \ K₀) := rfl

lemma mem_freshPrefixSupport_iff (K₀ : Finset P.Color) (pre : List P.Label)
    (c : P.Color) :
    c ∈ P.freshPrefixSupport K₀ pre ↔
      ∃ a ∈ pre, c ∈ P.support a ∧ c ∉ K₀ := by
  induction pre with
  | nil => simp
  | cons a pre ih => simp [ih, or_comm]

lemma support_sdiff_subset_freshPrefixSupport (K₀ : Finset P.Color)
    (pre : List P.Label) {a : P.Label} (ha : a ∈ pre) :
    P.support a \ K₀ ⊆ P.freshPrefixSupport K₀ pre := by
  intro c hc
  exact (P.mem_freshPrefixSupport_iff K₀ pre c).mpr
    ⟨a, ha, (Finset.mem_sdiff.mp hc).1, (Finset.mem_sdiff.mp hc).2⟩

lemma disjoint_freshPrefixSupport_initial (K₀ : Finset P.Color) (pre : List P.Label) :
    Disjoint (P.freshPrefixSupport K₀ pre) K₀ := by
  apply Finset.disjoint_left.mpr
  intro c hc hc₀
  obtain ⟨a, ha, hca, hcnot⟩ := (P.mem_freshPrefixSupport_iff K₀ pre c).mp hc
  exact hcnot hc₀

lemma card_freshPrefixSupport_le (K₀ : Finset P.Color) (pre : List P.Label)
    (r : ℕ) (hr : ∀ a ∈ pre, (P.support a).card ≤ r) :
    (P.freshPrefixSupport K₀ pre).card ≤ pre.length * r := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      have hpre : ∀ b ∈ pre, (P.support b).card ≤ r :=
        fun b hb => hr b (List.mem_cons_of_mem a hb)
      have ha := hr a List.mem_cons_self
      have hsdiff : (P.support a \ K₀).card ≤ (P.support a).card :=
        Finset.card_le_card Finset.sdiff_subset
      calc
        (P.freshPrefixSupport K₀ (a :: pre)).card ≤
            (P.freshPrefixSupport K₀ pre).card + (P.support a \ K₀).card :=
          Finset.card_union_le _ _
        _ ≤ pre.length * r + r := Nat.add_le_add (ih hpre) (hsdiff.trans ha)
        _ = (a :: pre).length * r := by simp [Nat.add_mul]

lemma indicator_eq_of_agree_support (a : P.Label) (x y : P.Sample)
    (hxy : ∀ c ∈ P.support a, x c = y c) :
    P.indicator a x = P.indicator a y := by
  have he := P.dependsOn a x y hxy
  classical
  simp only [indicator, Set.indicator_apply]
  simp only [he]

lemma indicator_fixed_eq_of_agree_fresh (K₀ : Finset P.Color) (x₀ : P.Sample)
    (a : P.Label) (ω η : P.Sample)
    (hωη : ∀ c ∈ P.support a \ K₀, ω c = η c) :
    P.indicator a (P.fixCoordinates K₀ x₀ ω) =
      P.indicator a (P.fixCoordinates K₀ x₀ η) := by
  apply P.indicator_eq_of_agree_support
  intro c hc
  by_cases hc₀ : c ∈ K₀
  · simp [fixCoordinates, hc₀]
  · simpa [fixCoordinates, hc₀] using hωη c (Finset.mem_sdiff.mpr ⟨hc, hc₀⟩)

lemma prefix_product_fixed_eq_of_agree_fresh (K₀ : Finset P.Color)
    (x₀ : P.Sample) (pre : List P.Label) (shift : P.Label → ℝ) (ω η : P.Sample)
    (hωη : ∀ c ∈ P.freshPrefixSupport K₀ pre, ω c = η c) :
    (pre.map (fun a => P.indicator a (P.fixCoordinates K₀ x₀ ω) + shift a)).prod =
      (pre.map (fun a => P.indicator a (P.fixCoordinates K₀ x₀ η) + shift a)).prod := by
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [P.indicator_fixed_eq_of_agree_fresh K₀ x₀ a ω η]
  intro c hc
  exact hωη c (P.support_sdiff_subset_freshPrefixSupport K₀ pre ha hc)

lemma prefix_product_fixed_resample (K₀ K : Finset P.Color) (x₀ : P.Sample)
    (pre : List P.Label) (shift : P.Label → ℝ) (ω η : P.Sample)
    (hK : P.freshPrefixSupport K₀ pre ⊆ K) :
    (pre.map (fun a => P.indicator a
      (P.fixCoordinates K₀ x₀ (P.fixCoordinates K ω η)) + shift a)).prod =
      (pre.map (fun a => P.indicator a (P.fixCoordinates K₀ x₀ ω) + shift a)).prod := by
  apply P.prefix_product_fixed_eq_of_agree_fresh
  intro c hc
  simp [fixCoordinates, hK hc]

lemma overlapCount_freshPrefixSupport (K₀ : Finset P.Color) (pre : List P.Label)
    (ω : P.Sample) :
    P.overlapCount K₀ (P.freshPrefixSupport K₀ pre) ω =
      ∑ a, if PatternMoments.supportOverlap P.support K₀ pre a then
        P.indicator a ω else 0 := by
  classical
  unfold overlapCount PatternMoments.supportOverlap freshPrefixSupport
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

end Balanced.PatternModel

end OAI
