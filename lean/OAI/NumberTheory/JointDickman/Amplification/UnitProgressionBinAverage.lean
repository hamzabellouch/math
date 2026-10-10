import OAI.NumberTheory.JointDickman.Analysis.CharacterBinShort
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! # Character decomposition of unit-class bin averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem complex_progression_sum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (g : ℕ → ℂ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ)*(∑ n ∈ S, if (n : ZMod q) = r then g n else 0) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*∑ n ∈ S, g n*χ (n : ZMod q) := by
  rw [mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = g n*(if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = g n*∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit,ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

noncomputable def unitProgressionBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0)/(H : ℂ)

theorem unitProgressionBinAverage_characters {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ w r H z =
      (∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*
        twistedWeightedBinAverage E ζ μ w χ H z)/(q.totient : ℂ) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (eq_div_iff hφ).mpr
  rw [mul_comm]
  have he := congrArg (fun x : ℂ => x/(H : ℂ))
    (complex_progression_sum_characters (Ioc ⌊z⌋₊ ⌊z+H⌋₊)
      (fun n => (binLabel E ζ n-μ)*(w n : ℂ)) r)
  simpa only [unitProgressionBinAverage,twistedWeightedBinAverage,mul_div_assoc,sum_div] using he

theorem unitProgressionBinAverage_square_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (H z : ℝ) :
    ‖unitProgressionBinAverage E ζ μ w r H z‖^2 ≤
      (∑ χ : DirichletCharacter ℂ q, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2)/(q.totient : ℝ) := by
  let F := fun χ : DirichletCharacter ℂ q => twistedWeightedBinAverage E ζ μ w χ H z
  have hc : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hn : ‖∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*F χ‖ ≤ ∑ χ, ‖F χ‖ := by
    simpa only [norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul] using
      norm_sum_le univ (fun χ : DirichletCharacter ℂ q => χ (r⁻¹ : (ZMod q)ˣ)*F χ)
  have hs := sum_mul_sq_le_sq_mul_sq univ (fun _ : DirichletCharacter ℂ q => (1 : ℝ)) (fun χ => ‖F χ‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,hc] at hs
  have he := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [unitProgressionBinAverage_characters,norm_div,Complex.norm_natCast,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hφ)).mpr
  change _ ≤ ((∑ χ, ‖F χ‖^2)/(q.totient : ℝ))*(q.totient : ℝ)^2
  convert he using 1
  field_simp

end JointDickman

end OAI
