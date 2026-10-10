import OAI.MeasureTheory.Falconer.Angular.AngularCountMean
import OAI.MeasureTheory.Falconer.Geometry.DyadicCenterSeparation
import OAI.MeasureTheory.Falconer.Geometry.DyadicInverseDistance

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem parallel_inverse_distance_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {g p : ℕ} (hgp : g ≤ p) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center ≤
      ((parallelTestCells Q ρ g p P).card:ℝ)*(2:ℝ)^g +
        ∑ j ∈ Finset.range (p-g),
          ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ)*
            (2:ℝ)^(g+j+1) := by
  classical
  let S := (parallelTestCells Q ρ g p P).erase P
  let d := fun c => dist (Q.descendant c).center (Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsep (c : CellPath) (hc : c ∈ S) : 1/(2:ℝ)^p ≤ d c := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_dyadicPaths p c).mp (Finset.mem_filter.mp hc').1
    simpa only [hQ] using dyadic_centers_separated Q hside hl hP (Finset.ne_of_mem_erase hc)
  have hd (c : CellPath) (hc : c ∈ S) : 0 < d c :=
    lt_of_lt_of_le (by positivity : 0 < 1/(2:ℝ)^p) (hsep c hc)
  have hh := sum_inverse_distance_dyadic S d g (p-g) hd (fun c hc => by
    simpa only [Nat.add_sub_of_le hgp] using hsep c hc)
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.erase_subset P (parallelTestCells Q ρ g p P))
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨hc,hdc⟩ := Finset.mem_filter.mp hc
    have hc' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    exact Finset.mem_filter.mpr ⟨hc'.1,hc'.2.1,hdc⟩

theorem parallel_inverse_distance_profile (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam : ℝ)
    (hpack : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : Plane, ∀ C₀ : ℝ, 0 ≤ C₀ →
      ((occupiedCenterCells Q ρ p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
        (4*(C₀+1)^2)*((2:ℝ)^N)^(m p-m g+6*lam))
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center ≤
      484*(((2:ℝ)^N)^(m p-m g+6*lam)*(2:ℝ)^g +
        ∑ j ∈ Finset.range (p-g),
          ((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1)) := by
  classical
  apply (parallel_inverse_distance_sum Q hQ ρ hgp hP).trans
  rw [mul_add,Finset.mul_sum]
  apply add_le_add
  · have hh := hpack g p hgp hpN (Q.descendant P).center 10 (by norm_num)
    change ((parallelTestCells Q ρ g p P).card:ℝ) ≤ _ at hh
    norm_num at hh
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (2:ℝ)^g)
  · apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hh := hpack (g+j) p (by omega) hpN (Q.descendant P).center 1 (by norm_num)
    norm_num at hh
    have hpos : 0 ≤ ((2:ℝ)^N)^(m p-m (g+j)+6*lam) := by positivity
    have hh' : ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ) ≤
        484*((2:ℝ)^N)^(m p-m (g+j)+6*lam) := by
      simp only [one_div]
      linarith
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2:ℝ)^(g+j+1))

end PlanarFalconer

end OAI
