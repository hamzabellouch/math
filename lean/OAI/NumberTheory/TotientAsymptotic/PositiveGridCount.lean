import OAI.NumberTheory.TotientAsymptotic.PositiveCoordinateGrid
import OAI.NumberTheory.TotientAsymptotic.BandUnionCount

namespace OAI

/-! Finite-grid counting for all positive ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem positive_grid_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ X k K L : ℕ,4 ≤ X → 1 ≤ B X → 0 < k → 3 ≤ L → L ≤ K →
    (K:ℝ) ≤ B X+2 → Real.exp K ≤ Real.log X/(20*B X) → ∀ T : ℝ,
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
      (∀ j : Fin k,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
      T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*(K+1:ℕ)^k*Real.exp
      (-T+(B X+5-K)*(∑ j : Fin k,a (j.val+1))+
        (1-countBandWeight (k+1))*B (loglogCutoff L)+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B (loglogCutoff L)*K)) := by
  classical
  obtain ⟨C,D,hC,hD,hunion⟩ := normal_band_union_count
  refine ⟨C,D,hC,hD,?_⟩
  intro X k K L hX hBX hk hL hLK hK hbudget T Q hQ
  let S := loglogCutoff L
  let U := T-(B X+5-K)*(∑ j : Fin k,a (j.val+1))
  let V : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ => Finset.range (K+1))
  let P0 := V.image (coordinateGridCutoff L k)
  let P := P0.filter (fun Y => S ≤ Y 0 ∧ Y k=S ∧
    Real.log (Y 0) ≤ Real.log X/(20*B X) ∧
    (∀ j < k,Y (j+1) ≤ Y j) ∧ (∀ j < k,B (Y j) ≤ K) ∧
    U ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j))
  have hcut := loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))
  have hS : 2 ≤ S := hcut.1
  have hBS : 0 ≤ B S := by
    have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith [hcut.2.1]
  have hcover : ∀ v ∈ Q,∃ Y ∈ P,NormalBandWitness S X k Y v := by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hpos,hscore⟩ := hQ v hv
    let g := coordinateGridIndex K n k
    let Y := coordinateGridCutoff L k g
    obtain ⟨hg,hmono,hgrid⟩ := positive_coordinate_grid (by exact_mod_cast hX) hn
      (by exact_mod_cast (hφ ▸ hvX)) hL hLK hK hpos
    have hgm (j : Fin k) : L ≤ g j ∧ g j ≤ K ∧
        loglogCutoff (g j) < fordPrime n (j.val+1) ∧
        B (loglogCutoff (g j)) ≤ K ∧
        Real.log (loglogCutoff (g j)) ≤ Real.exp K ∧
        j.val+2 ≤ n.primeFactorsList.length := hg j
    have hYj (j : Fin k) : Y j.val=loglogCutoff (g j) := by simp [Y,coordinateGridCutoff]
    have hYscore : U ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j) := by
      have he : (∑ j ∈ Finset.range k,a (j+1)*B (Y j))=
          ∑ j : Fin k,a (j.val+1)*B (loglogCutoff (g j)) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        rw [hYj j]
      rw [he]
      dsimp [U]
      linarith
    have hYmem : Y ∈ P := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨g,Fintype.mem_piFinset.mpr
          (fun j => Finset.mem_range.mpr (by have := (hgm j).2.1; omega)),rfl⟩
      · have hY0 := hYj ⟨0,hk⟩
        refine ⟨?_,coordinate_grid_cutoff_terminal L k g,?_,?_,?_,hYscore⟩
        · rw [hY0]
          exact loglogCutoff_mono (by exact_mod_cast (hgm ⟨0,hk⟩).1)
        · rw [hY0]
          exact (hgm ⟨0,hk⟩).2.2.2.2.1.trans hbudget
        · exact coordinate_grid_cutoff_descending (fun j => (hgm j).1) hmono
        · intro j hj
          rw [hYj ⟨j,hj⟩]
          exact (hgm ⟨j,hj⟩).2.2.2.1
    refine ⟨Y,hYmem,n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,?_⟩
    intro j
    rw [hYj j]
    exact ⟨(hgm j).2.2.2.2.2,(hgm j).2.2.1⟩
  have hb := hunion S X k K U P hS hBS hBX (Nat.cast_nonneg K)
    (fun Y hY => (Finset.mem_filter.mp hY).2) Q hcover
  have hcard : (P.card:ℝ) ≤ (K+1:ℕ)^k := by
    have hc : P.card ≤ (K+1)^k := by
      calc
        _ ≤ P0.card := Finset.card_filter_le _ _
        _ ≤ V.card := Finset.card_image_le
        _ = _ := by simp [V,Fintype.card_piFinset]
    exact_mod_cast hc
  have hnon : 0 ≤ Real.exp (-U+(1-countBandWeight (k+1))*B S+
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*K)) := (Real.exp_pos _).le
  have hh := hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ C*X)) hnon)
  convert hh using 1
  congr 2
  dsimp [U,S]
  ring

end TotientAsymptotic

end

end OAI
