import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedVertices
import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem occupied_parent_profile_count (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (N B : ℕ) (δ lam : ℝ) (mass : ℝ → ℝ)
    (hd : RegularizedProfileData Q ρ N B δ lam mass) (A : CellPath) (a n : ℕ)
    (hA : A.length = a) (hp : a+n ≤ N) :
    ((occupiedAnchorPaths (Q.descendant A) ρ n).card : ℝ) ≤
      64*((2:ℝ)^N)^(mass (a+n)-mass a+6*lam) := by
  classical
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hPpos := Q.descendant_side_pos hQpos A
  let C := occupiedAnchorPaths (Q.descendant A) ρ n
  have hsub : C.image (fun c => A++c) ⊆ occupiedCenterCells Q ρ (a+n) (Q.descendant A).center (3/(2:ℝ)^a) := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hlen,hmass⟩ := Finset.mem_filter.mp hb
    have hl := (mem_dyadicPaths _ _).mp hlen
    apply Finset.mem_filter.mpr
    refine ⟨by simp [mem_dyadicPaths,hA,hl],?_,?_⟩
    · simpa only [DyadicSquare.descendant_append] using hmass
    · rw [mem_ball,DyadicSquare.descendant_append]
      have hdist := (Q.descendant A).dist_le hPpos.le
        ((Q.descendant A).descendant_subset hPpos b
          (((Q.descendant A).descendant b).center_mem ((Q.descendant A).descendant_side_pos hPpos b)))
        ((Q.descendant A).center_mem hPpos)
      have hside : (Q.descendant A).side = 1/(2:ℝ)^a := by
        rw [DyadicSquare.descendant_side,hA,hQ]
      rw [hside] at hdist
      apply hdist.trans_lt
      rw [mul_one_div]
      exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hinj : Function.Injective (fun c : CellPath => A++c) := fun _ _ hh => List.append_cancel_left hh
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hh := hd.packing a (a+n) (Nat.le_add_right a n) hp (Q.descendant A).center 3 (by norm_num)
  simp only [hQ] at hh
  norm_num at hh
  exact (by exact_mod_cast hcard : (C.card:ℝ) ≤ _).trans hh

theorem sourceProductVertices_profile_count
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) (N B : ℕ) (δ lam : ℝ) (m₁ m₂ : ℝ → ℝ)
    (hd₁ : RegularizedProfileData Q₁ ρ N B δ lam m₁)
    (hd₂ : RegularizedProfileData Q₂ ν N B δ lam m₂)
    (A B' : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B'.length = a) (hp : a+n ≤ N) :
    ((sourceProductVertices Q₁ Q₂ ρ ν A B' n).card:ℝ) ≤
      4096*((2:ℝ)^N)^(m₁ (a+n)-m₁ a+(m₂ (a+n)-m₂ a)+12*lam) := by
  rw [sourceProductVertices_card,Nat.cast_mul]
  have h1 := occupied_parent_profile_count Q₁ hQ₁ ρ N B δ lam m₁ hd₁ A a n hA hp
  have h2 := occupied_parent_profile_count Q₂ hQ₂ ν N B δ lam m₂ hd₂ B' a n hB hp
  apply (mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)).trans_eq
  rw [mul_mul_mul_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  norm_num
  congr 1
  ring

end PlanarFalconer

end OAI
