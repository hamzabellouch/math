import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletion
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryProductCoefficients

namespace OAI

/-! The expanded ideal kernel is exactly a primary cube-divisor sum.
This reindexing retains the finite norm cutoff and arbitrary complex
coefficients; no analytic summability assumption enters the inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def weightedCubeSeries (B : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ) :
    ComplexIdealSeries := MvPowerSeries.expand 3 (by norm_num) (MvPowerSeries.rescale x B)

lemma weightedCubeSeries_coeff (B : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff (3 • ν) (weightedCubeSeries B x) =
      ν.prod (fun p k => x p^k)*MvPowerSeries.coeff ν B := by
  rw [weightedCubeSeries,MvPowerSeries.coeff_expand_smul,MvPowerSeries.coeff_rescale]

lemma primary_cube {c : Eisenstein} (hc : primary c) : primary (c^3) := by
  simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hc hc) hc

lemma primary_cube_injective {c d : Eisenstein} (hc : primary c) (hd : primary d)
    (h : c^3 = d^3) : c = d := by
  apply primary_eq_of_idealExponentOf_eq hc hd
  have he := congrArg idealExponentOf h
  rw [idealExponentOf_pow (primary_ne_zero hc),idealExponentOf_pow (primary_ne_zero hd)] at he
  ext p
  have hp := congrArg (fun ν : EisensteinIdealExponent => ν p) he
  simp only [Finsupp.smul_apply,smul_eq_mul] at hp
  omega

lemma weightedCubeSeries_nonzero_primary {B : ComplexIdealSeries}
    {x : EisensteinIdealPrime → ℂ} {b : Eisenstein} (hb : primary b)
    (h : MvPowerSeries.coeff (idealExponentOf b) (weightedCubeSeries B x) ≠ 0) :
    ∃ c : Eisenstein, primary c ∧ c^3 = b := by
  have hs : idealExponentOf b ∈ Function.support (weightedCubeSeries B x) := h
  obtain ⟨ν,_,he⟩ := MvPowerSeries.support_expand_subset 3 (by norm_num)
    (MvPowerSeries.rescale x B) hs
  have hν : ν ≤ idealExponentOf b := by
    rw [← he]
    intro p
    simp only [Finsupp.smul_apply,smul_eq_mul]
    omega
  refine ⟨idealPrimaryGenerator ν,idealPrimaryGenerator_primary hb hν,?_⟩
  apply primary_eq_of_idealExponentOf_eq (primary_cube (idealPrimaryGenerator_primary hb hν)) hb
  rw [idealExponentOf_pow (primary_ne_zero (idealPrimaryGenerator_primary hb hν)),
    idealExponentOf_primaryGenerator]
  exact he

def primaryCubeFiber (F : ℝ) (b : Eisenstein) : Finset (Fin 2 → Eisenstein) :=
  (Fintype.piFinset (fun _ : Fin 2 => primaryElementBall F)).filter
    (fun n => n 0^3*n 1 = b)

/-- Multiplying by the expanded series is a literal sum over primary
cube divisors, with every argument bounded by the original norm cutoff. -/
theorem weightedCubeSeries_product_primary
    (B A : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (weightedCubeSeries B x*A) =
      ∑ n ∈ primaryCubeFiber F b,
        ((idealExponentOf (n 0)).prod (fun p k => x p^k)*
          MvPowerSeries.coeff (idealExponentOf (n 0)) B)*
          MvPowerSeries.coeff (idealExponentOf (n 1)) A := by
  have he := coeff_product_primary_fiber (ι := Fin 2) ![weightedCubeSeries B x,A] hb hbF
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at he
  rw [he]
  symm
  apply Finset.sum_bij_ne_zero (fun n _ _ => ![n 0^3,n 1])
  · intro n hn _
    obtain ⟨hn,hprod⟩ := Finset.mem_filter.mp hn
    have hnp (i : Fin 2) := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hn i)).1
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
    · fin_cases i
      · apply mem_primaryElementBall.mpr
        refine ⟨primary_cube (hnp 0),?_⟩
        exact (norm_le_of_dvd (primary_ne_zero hb) ⟨n 1,hprod.symm⟩).trans hbF
      · simpa using Fintype.mem_piFinset.mp hn 1
    · simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hprod
  · intro n hn _ m hm _ h
    apply funext
    intro i
    have hn0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
    have hm0 := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm).1 0)).1
    fin_cases i
    · exact primary_cube_injective hn0 hm0 (congrFun h 0)
    · exact congrFun h 1
  · intro m hm hnon
    obtain ⟨hm,hprod⟩ := Finset.mem_filter.mp hm
    have hmp (i : Fin 2) := (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hm i)).1
    have hzero : MvPowerSeries.coeff (idealExponentOf (m 0)) (weightedCubeSeries B x) ≠ 0 :=
      (mul_ne_zero_iff.mp hnon).1
    obtain ⟨c,hc,hc3⟩ := weightedCubeSeries_nonzero_primary (hmp 0) hzero
    have hcb : c^3*m 1 = b := by simpa only [Fin.prod_univ_two,← hc3] using hprod
    have hcF : norm c ≤ F := (norm_le_of_dvd (primary_ne_zero hb)
      ((dvd_pow_self c (by norm_num : (3:ℕ) ≠ 0)).trans ⟨m 1,hcb.symm⟩)).trans hbF
    refine ⟨![c,m 1],Finset.mem_filter.mpr ⟨?_,?_⟩,?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      fin_cases i
      · exact mem_primaryElementBall.mpr ⟨hc,hcF⟩
      · simpa using Fintype.mem_piFinset.mp hm 1
    · simpa using hcb
    · rw [← hc3] at hnon
      simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
        idealExponentOf_pow (primary_ne_zero hc),weightedCubeSeries_coeff] using hnon
    · funext i
      fin_cases i
      · simpa using hc3
      · simp
  · intro n hn _
    have hnc := (mem_primaryElementBall.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      idealExponentOf_pow (primary_ne_zero hnc),weightedCubeSeries_coeff]

end CubicFirstMoment

end

end OAI
