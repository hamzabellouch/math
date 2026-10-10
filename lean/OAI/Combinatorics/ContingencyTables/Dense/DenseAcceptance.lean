import OAI.Combinatorics.ContingencyTables.Dense.DenseGoodBins

namespace OAI

/-! # Constant stationary mass of wholly feasible dense bins -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- Every within-bin offset in these bins is feasible. Their stationary
mass is at least 1/32, and hence at least the paper's claimed 1/64. -/
theorem dense_good_bin_probability (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    (1 / 32 : ℝ) ≤
      (∑ a ∈ goodBins R P d e (K := 4 * d ^ 8), denseBinWeight R P d e a) /
        (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) := by
  let V := volume {x | denseGridFeasible R P d e x}
  let G := goodBins R P d e (K := 4 * d ^ 8)
  let Z := ∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a
  have hV : V ≠ ⊤ := by
    dsimp [V]
    rw [denseGridFeasible_volume]
    exact (DenseAffine.dense_feasible_compact R P d hd hR hP htotal).measure_ne_top
  have hG : V.toReal / 2 ≤ (G.card : ℝ) := by
    have h := ENNReal.toReal_mono (by simp)
      (goodBins_volume_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast, one_div_mul_eq_div] using h
  have hZ : Z ≤ 16 * V.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hV)
      (denseBin_normalizer_bound R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e)
    have hznonneg : 0 ≤ Z := Finset.sum_nonneg
      (fun a _ => (DenseWeights.binWeight_pos _ _ _).le)
    change (ENNReal.ofReal Z).toReal ≤ (16 * V).toReal at h
    simpa only [ENNReal.toReal_ofReal hznonneg, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have hK := denseGridSize_pos d hd
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  have hZpos : 0 < Z := Finset.sum_pos (fun a _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hsum : (∑ a ∈ G, denseBinWeight R P d e a) = G.card := by
    calc
      _ = ∑ _a ∈ G, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact goodBin_weight_one R P d hd hR hP hRmax hPmax hfree e a (Finset.mem_filter.mp ha).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  change (1 / 32 : ℝ) ≤ (∑ a ∈ G, denseBinWeight R P d e a) / Z
  rw [hsum]
  apply (le_div_iff₀ hZpos).mpr
  linarith

end

end ContingencyTables.GridBoundary

end OAI
