import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPrincipalMassBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds
open PrimeProgression PrimeCellReplacement LogCellPartition MixedCellIntegralFreezing
open scoped BigOperators

theorem giant_principalMass_raw_bounds (M : ℕ) (hM : 0 < M)
    {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z) :
    0 ≤ principalMass M (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z) ∧
      principalMass M (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z) ≤ 4*(Z⁻¹)^2 := by
  have hh := giant_normalized_harmonic_bounds M hM hG hZ
  simp only [principalMass,Finset.prod_const,Finset.card_univ,Fintype.card_bool]
  refine ⟨sq_nonneg _,?_⟩
  exact (pow_le_pow_left₀ hh.1 hh.2 2).trans_eq (by ring)

theorem giant_mixedPrincipalMass_raw_bounds (M : ℕ) (hM : 0 < M)
    {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z) :
    0 ≤ mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z) ∧
    mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z) ≤ 4*Real.exp 1*Z⁻¹ := by
  have hh := giant_normalized_harmonic_bounds M hM hG hZ
  have hi := giant_integerDensityMass_bounds M hM G
  rw [mixedPrincipalMass,residue_mixedLogMass_eq M (G-1) (G+1) G smoothPartition
    (fun _ : Unit=>Z) (fun _=>G-1) (fun _=>G+1) (by linarith) (fun _=>by linarith)]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one]
  refine ⟨mul_nonneg hi.1 hh.1,?_⟩
  exact (mul_le_mul hi.2 hh.2 hh.1 (by positivity)).trans_eq (by ring)

private theorem common_mass_envelope (m : ℕ) :
    4*Real.exp (4*((m:ℝ)+1)) ≤ Real.exp (10*((m:ℝ)+1)) := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h4 : (4:ℝ) ≤ Real.exp 2 := by
    calc
      _ = 2*2 := by norm_num
      _ ≤ Real.exp 1*Real.exp 1 := mul_le_mul h2 h2 (by norm_num) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; norm_num
  calc
    _ ≤ Real.exp 2*Real.exp (4*((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = Real.exp (2+4*((m:ℝ)+1)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) m])

theorem giant_principalMass_bounds (M : ℕ) (hM : 0 < M) (m : ℕ)
    {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hinv : Z⁻¹ ≤ Real.exp (2*((m:ℝ)+1))) :
    0 ≤ principalMass M (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z) ∧
      principalMass M (fun _ : Bool=>G-1) (fun _=>G+1) (fun _=>Z) ≤
        Real.exp (10*((m:ℝ)+1)) := by
  have hh := giant_principalMass_raw_bounds M hM hG hZ
  refine ⟨hh.1,hh.2.trans ((mul_le_mul_of_nonneg_left ?_ (by norm_num)).trans (common_mass_envelope m))⟩
  have hi := pow_le_pow_left₀ (inv_nonneg.mpr hZ.le) hinv 2
  convert hi using 1
  rw [←Real.exp_nat_mul]
  congr 1
  ring

theorem giant_mixedPrincipalMass_bounds (M : ℕ) (hM : 0 < M) (m : ℕ)
    {G Z : ℝ} (hG : 2 ≤ G) (hZ : 0 < Z)
    (hinv : Z⁻¹ ≤ Real.exp (2*((m:ℝ)+1))) :
    0 ≤ mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z) ∧
    mixedPrincipalMass M (G-1) (G+1) G smoothPartition
      (fun _ : Unit=>G-1) (fun _=>G+1) (fun _=>Z) ≤ Real.exp (10*((m:ℝ)+1)) := by
  have hh := giant_mixedPrincipalMass_raw_bounds M hM hG hZ
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ 4*Real.exp 1*Real.exp (2*((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 4*Real.exp (1+2*((m:ℝ)+1)) := by rw [Real.exp_add]; ring
    _ ≤ 4*Real.exp (4*((m:ℝ)+1)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) m])) (by norm_num)
    _ ≤ _ := common_mass_envelope m

end Ostmann.Arithmetic.HistoryGiantPrincipalMassBounds

end

end OAI
