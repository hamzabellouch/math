import OAI.MeasureTheory.Falconer.Geometry.DyadicClasses
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

noncomputable def massBinCandidates (N : ℕ) (w : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (4*N+1)).filter fun k => (2:ℝ)^k ≤ (2:ℝ)^(4*N)*w

noncomputable def leafMassBin (N : ℕ) (w : ℝ) : ℕ :=
  if h : (massBinCandidates N w).Nonempty then (massBinCandidates N w).max' h else 0

theorem massBinCandidates_nonempty {N : ℕ} {w : ℝ}
    (hw : 1 ≤ (2:ℝ)^(4*N)*w) : (massBinCandidates N w).Nonempty := by
  classical
  exact ⟨0,by simp [massBinCandidates,hw]⟩

theorem leafMassBin_le (N : ℕ) (w : ℝ) : leafMassBin N w ≤ 4*N := by
  classical
  unfold leafMassBin
  split_ifs with h
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp ((massBinCandidates N w).max'_mem h)).1)
  · omega

theorem leafMassBin_lower {N : ℕ} {w : ℝ} (hw : 1 ≤ (2:ℝ)^(4*N)*w) :
    (2:ℝ)^(leafMassBin N w) ≤ (2:ℝ)^(4*N)*w := by
  classical
  unfold leafMassBin
  rw [dite_eq_left (massBinCandidates_nonempty hw)]
  exact (Finset.mem_filter.mp ((massBinCandidates N w).max'_mem (massBinCandidates_nonempty hw))).2

theorem leafMassBin_upper {N : ℕ} {w : ℝ} (hw : w ≤ 1) :
    (2:ℝ)^(4*N)*w < (2:ℝ)^(leafMassBin N w+1) := by
  classical
  by_cases hk : leafMassBin N w < 4*N
  · by_contra h
    have hm : leafMassBin N w+1 ∈ massBinCandidates N w := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),not_lt.mp h⟩
    have hh : leafMassBin N w+1 ≤ leafMassBin N w := by
      conv_rhs => rw [leafMassBin, dite_eq_left ⟨_,hm⟩]
      exact Finset.le_max' _ _ hm
    omega
  · have he : leafMassBin N w = 4*N := by have := leafMassBin_le N w; omega
    rw [he, pow_succ]
    have hp : 0 < (2:ℝ)^(4*N) := by positivity
    nlinarith

noncomputable def leafBinEndpoint (N k : ℕ) : ℝ := (2:ℝ)^k / (2:ℝ)^(4*N)

theorem leafBinEndpoint_pos (N k : ℕ) : 0 < leafBinEndpoint N k := by
  unfold leafBinEndpoint; positivity

theorem leaf_mass_bin_bounds {N : ℕ} {w : ℝ}
    (hlo : 1 ≤ (2:ℝ)^(4*N)*w) (hhi : w ≤ 1) :
    leafBinEndpoint N (leafMassBin N w) ≤ w ∧
      w < 2 * leafBinEndpoint N (leafMassBin N w) := by
  have hp : 0 < (2:ℝ)^(4*N) := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using leafMassBin_lower hlo)
  · have hu := leafMassBin_upper (N := N) hhi
    rw [pow_succ] at hu
    unfold leafBinEndpoint
    rw [← mul_div_assoc]
    exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hu)

noncomputable def sourceLeafLabel (Q : DyadicSquare) (μ : Measure Plane) (N : ℕ)
    (p : List (Bool × Bool)) : List ℕ := [leafMassBin N (μ (Q.descendant p).carrier).toReal]

theorem sourceLeafLabel_card_le (Q : DyadicSquare) (μ : Measure Plane) (N : ℕ)
    (L : Finset (List (Bool × Bool))) : (L.image (sourceLeafLabel Q μ N)).card ≤ 4*N+1 := by
  classical
  have hs : L.image (sourceLeafLabel Q μ N) ⊆
      (Finset.range (4*N+1)).image (fun k => [k]) := by
    intro T hT
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨leafMassBin N (μ (Q.descendant p).carrier).toReal,
      Finset.mem_range.mpr (by have := leafMassBin_le N (μ (Q.descendant p).carrier).toReal; omega),rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem retained_leaf_mass_bin_bounds (Q : DyadicSquare) (μ : Measure Plane)
    [IsProbabilityMeasure μ] (N : ℕ) {p : List (Bool × Bool)}
    (hp : p ∈ retainedLeaves Q μ N ((2:ℝ≥0∞)^(4*N))⁻¹) :
    let w := (μ (Q.descendant p).carrier).toReal
    leafBinEndpoint N (leafMassBin N w) ≤ w ∧ w < 2*leafBinEndpoint N (leafMassBin N w) := by
  have hm := (Finset.mem_filter.mp hp).2
  have ht := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at ht
  have hp : 0 < (2:ℝ)^(4*N) := by positivity
  apply leaf_mass_bin_bounds
  · exact (inv_le_iff_one_le_mul₀' hp).mp ht
  · have hh : μ (Q.descendant p).carrier ≤ 1 := prob_le_one
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).mpr hh

end PlanarFalconer

end OAI
