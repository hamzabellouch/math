import OAI.MeasureTheory.Falconer.Measures.DenseNeighborPruning

namespace OAI

/-! Four-edge paths and their sum labels. Injectivity of the labels is the
counting step converting dense neighborhoods into small difference sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

abbrev IntegerPath := Σ _v : ℤ, ℤ × ℤ

noncomputable def integerFourPaths (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) : Finset IntegerPath :=
  B.sigma fun v => integerCommonNeighbors A e b v ×ˢ integerCommonNeighbors A e c v

theorem integerFourPaths_card (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (b c : ℤ) :
    ((integerFourPaths A B e b c).card : ℝ) =
      ∑ v ∈ B, ((integerCommonNeighbors A e b v).card : ℝ)*
        ((integerCommonNeighbors A e c v).card : ℝ) := by
  simp only [integerFourPaths,Finset.card_sigma,Finset.card_product,Nat.cast_sum,Nat.cast_mul]

theorem integerFourPaths_lower (A B V : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) (hV : V ⊆ B) {L : ℝ} (hL : 0 ≤ L)
    (hcommon : ∀ v ∈ V, L ≤ ((integerCommonNeighbors A e b v).card : ℝ) ∧
      L ≤ ((integerCommonNeighbors A e c v).card : ℝ)) :
    (V.card : ℝ)*L^2 ≤ (integerFourPaths A B e b c).card := by
  rw [integerFourPaths_card]
  calc
    _ = ∑ _v ∈ V, L*L := by simp [pow_two]
    _ ≤ ∑ v ∈ V, ((integerCommonNeighbors A e b v).card : ℝ)*
        ((integerCommonNeighbors A e c v).card : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul (hcommon v hv).1 (hcommon v hv).2 hL (Nat.cast_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hV (fun _ _ _ => by positivity)

def integerPathSums (b c : ℤ) (p : IntegerPath) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((p.2.1+b,p.2.1+p.1),(p.2.2+p.1,p.2.2+c))

theorem integerPathSums_alternating (b c : ℤ) (p : IntegerPath) :
    (integerPathSums b c p).1.1-(integerPathSums b c p).1.2+
      (integerPathSums b c p).2.1-(integerPathSums b c p).2.2 = b-c := by
  dsimp [integerPathSums]
  ring

theorem integerPathSums_injective (b c : ℤ) : Function.Injective (integerPathSums b c) := by
  rintro ⟨v,a₁,a₂⟩ ⟨w,d₁,d₂⟩ he
  have h1 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1.1) he
  have h2 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1.2) he
  have h3 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1) he
  dsimp [integerPathSums] at h1 h2 h3
  have ha : a₁ = d₁ := by omega
  have hv : v = w := by omega
  have hd : a₂ = d₂ := by omega
  subst d₁
  subst w
  subst d₂
  rfl

theorem integerPathSums_mem (A B C : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → a+b ∈ C)
    {b c : ℤ} (hb : b ∈ B) (hc : c ∈ B) {p : IntegerPath}
    (hp : p ∈ integerFourPaths A B e b c) :
    integerPathSums b c p ∈ (C ×ˢ C) ×ˢ (C ×ˢ C) := by
  obtain ⟨hv,hp⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨ha₁,ha₁b,ha₁v⟩ := Finset.mem_filter.mp hp1
  obtain ⟨ha₂,ha₂c,ha₂v⟩ := Finset.mem_filter.mp hp2
  exact Finset.mem_product.mpr ⟨
    Finset.mem_product.mpr ⟨hlabels _ ha₁ _ hb ha₁b,hlabels _ ha₁ _ hv ha₁v⟩,
    Finset.mem_product.mpr ⟨hlabels _ ha₂ _ hv ha₂v,hlabels _ ha₂ _ hc ha₂c⟩⟩

end Falconer

end OAI
