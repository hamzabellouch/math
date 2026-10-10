import OAI.MeasureTheory.Falconer.Radial.PlateScales
import OAI.MeasureTheory.Falconer.Radial.HeavyPlateCover

namespace OAI

/-! # A common thicker-plate cover for the initial block of exclusion scales -/

namespace Falconer
open Set

private theorem plateScale_mul (j k : ℕ) :
    plateScale (k*j) = (plateScale j)^(k:ℝ) := by
  rw [plateScale,plateScale,Nat.cast_mul,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem initial_plate_block_cover {d : ℕ}
    (E : ℕ → Set (Space d × Space d)) (S : ℕ → Finset (Space d × ℝ))
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, E j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)})
    (j₀ : ℕ) :
    ∃ T : Finset (Space d × ℝ), (∀ p ∈ T, ‖p.1‖ = 1) ∧
      (T.card:ℝ) ≤ ((63*j₀:ℕ):ℝ)*A*(plateScale j₀)^(-64*b) ∧
      (⋃ i ∈ Finset.range (63*j₀), E (j₀+i)) ⊆
        ⋃ p ∈ T, {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j₀)^(1/4:ℝ)} ×ˢ
          {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j₀)^(1/4:ℝ)} := by
  classical
  let T := (Finset.range (63*j₀)).biUnion (fun i => S (j₀+i))
  refine ⟨T,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,hpi⟩ := Finset.mem_biUnion.mp hp
    exact hunit (j₀+i) p hpi
  · have hpower : (plateScale (64*j₀))^(-b) = (plateScale j₀)^(-64*b) := by
      rw [plateScale_mul,← Real.rpow_mul (plateScale_pos _).le]
      congr 1
      norm_num
    calc
      (T.card:ℝ) ≤ ∑ i ∈ Finset.range (63*j₀), ((S (j₀+i)).card:ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.range (63*j₀))
          (t := fun i => S (j₀+i)))
      _ ≤ ∑ _i ∈ Finset.range (63*j₀), A*(plateScale (64*j₀))^(-b) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (hcard (j₀+i)).trans
        apply mul_le_mul_of_nonneg_left _ hA
        apply Real.rpow_le_rpow_of_nonpos (plateScale_pos _)
          (plateScale_antitone (by have := Finset.mem_range.mp hi; omega)) (neg_nonpos.mpr hb)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,hpower]
        ring
  · intro xy hxy
    obtain ⟨i,hi,hxy⟩ := mem_iUnion₂.mp hxy
    obtain ⟨p,hp,hx,hy⟩ := mem_iUnion₂.mp (hcover (j₀+i) hxy)
    have hw : A*(plateScale (j₀+i))^(1/4:ℝ) ≤ A*(plateScale j₀)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (plateScale_pos _).le
        (plateScale_antitone (by omega)) (by norm_num)) hA
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_biUnion.mpr ⟨i,hi,hp⟩,hx.trans hw,hy.trans hw⟩

end Falconer

end OAI
