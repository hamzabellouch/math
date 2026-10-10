import OAI.NumberTheory.TotientAsymptotic.CenterComparison

namespace OAI

/-! Concentration at the full-scale bands after truncating the simplex. -/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

def fullSimplexCenter (m : ℕ) (B : ℝ) (k : ℕ) : ℝ :=
  B*rho^k*((m-k : ℕ) : ℝ)/m

def coarseCoordinateBad (m : ℕ) (B : ℝ) {N : ℕ} (i : Fin N) : Set (Fin N → ℝ) :=
  {u | u i < (95/100 : ℝ)*fullSimplexCenter m B (i.val+1) ∨
    (105/100 : ℝ)*fullSimplexCenter m B (i.val+1) < u i}

theorem truncated_simplex_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ (m q : ℕ) (B : ℝ), 0 < B → m-q=N+2 →
      ∀ i : Fin (N+2), i.val < N → 100*q ≤ m-(i.val+1) →
      (volume (prefixRegion (N+2) B 0 0 ∩ coarseCoordinateBad m B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := simplex_coordinate_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro N hN m q B hB hdim i hi hsmall
  have hqm : q < m := by omega
  have hik : i.val+1 ≤ m-q := by omega
  have him : i.val+1 < m := by omega
  have hmn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hS : 0 < B*rho^(i.val+1) := mul_pos hB (pow_pos rho_pos _)
  have hb : 0 < fullSimplexCenter m B (i.val+1) := by
    unfold fullSimplexCenter
    exact div_pos (mul_pos hS (Nat.cast_pos.mpr (Nat.sub_pos_of_lt him)))
      (Nat.cast_pos.mpr (by omega))
  have hcenter : fordSimplexCenter N B i =
      (B*rho^(i.val+1))*((N+2-(i.val+1) : ℕ) : ℝ)/(N+2) := by
    unfold fordSimplexCenter
    rw [Nat.cast_sub (by omega : i.val+1 ≤ N+2)]
    push_cast
    field_simp
  have hcompare := truncated_center_close hS.le hqm hik hsmall
  rw [hdim] at hcompare
  simp only [Nat.cast_add, Nat.cast_ofNat] at hcompare
  rw [← hcenter] at hcompare
  change (99/100 : ℝ)*fullSimplexCenter m B (i.val+1) ≤ fordSimplexCenter N B i ∧
    fordSimplexCenter N B i ≤ fullSimplexCenter m B (i.val+1) at hcompare
  have hbad : coarseCoordinateBad m B i ⊆ fordCoordinateBad N B i := by
    intro u hu
    apply outside_band_implies_deviation hb
      (by nlinarith [hcompare.1]) (by nlinarith [hcompare.2]) hu
  have hfin : volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono Set.inter_subset_left)
  exact (ENNReal.toReal_mono hfin (measure_mono (Set.inter_subset_inter_right _ hbad))).trans
    (hconc N hN B hB i hi)

end TotientAsymptotic

end

end OAI
