import OAI.MeasureTheory.Falconer.Estimates.FarEnvelope
import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphBudget

namespace OAI

/-! # The uniform original-law remainder in the far reduction -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

 theorem originalMeasure_mass_le_one (D : JetStateFarData m B) : D.originalMeasure univ ≤ 1 := by
  let := D.regular.probability
  have hprod (Z : List (Fin (m+3) → Bool)) :
      ((D.ρ.restrict (D.Q.descendant Z).carrier).prod
        (D.ρ.restrict (D.Q.descendant Z).carrier)) univ =
      D.ρ (D.Q.descendant Z).carrier*D.ρ (D.Q.descendant Z).carrier := by
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ]
  unfold originalMeasure originalFourPointMeasure
  rw [← univ_prod_univ,Measure.prod_prod,hprod,hprod]
  have hx : D.ρ (D.Q.descendant D.X).carrier ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq (measure_univ : D.ρ univ = 1)
  have hy : D.ρ (D.Q.descendant D.Y).carrier ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq (measure_univ : D.ρ univ = 1)
  calc
    _ ≤ (1*1)*(1*1) := mul_le_mul' (mul_le_mul' hx hx) (mul_le_mul' hy hy)
    _ = 1 := by norm_num

 theorem prefactor_bound (D : JetStateFarData m B) :
    D.prefactor ≤ ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)) := by
  have ha : D.a ≤ D.N := by have := D.ah; have := D.ht; have := D.tN; omega
  have hprofile : D.profile ((D.a:ℝ)/D.N) ≤ (m+3:ℕ) :=
    (D.regular.range _ ⟨by positivity,(div_le_one (Nat.cast_pos.mpr D.N_pos)).mpr (Nat.cast_le.mpr ha)⟩).2
  have hp := profile_graph_error_weight_bound (m+3) (a := D.a) (p := D.a) D.N_pos
    D.profile D.profile (Nat.cast_le.mpr D.tN) hprofile hprofile
  have hm : profileModelMass D.profile D.N D.a ≠ 0 := by unfold profileModelMass; positivity
  have habs : |(profileModelMass D.profile D.N D.a)⁻¹*(profileModelMass D.profile D.N D.a)⁻¹*
      ((profileModelMass D.profile D.N D.a)⁻¹*(profileModelMass D.profile D.N D.a)⁻¹)| =
      (profileModelMass D.profile D.N D.a)⁻¹^4 := by
    rw [abs_of_nonneg (by unfold profileModelMass; positivity)]
    ring
  simpa only [prefactor,div_self hm,mul_one,one_mul,one_pow,habs] using hp

 theorem band_count_le (D : JetStateFarData m B) :
    2+(Finset.Icc (D.a+9) (D.h+6)).card ≤ D.N+3 := by
  rw [Nat.card_Icc]
  have := D.ht
  have := D.tN
  omega

 theorem farError_bound (D : JetStateFarData m B) (K : ℕ) {Cerr : ℝ} (hC : 0 ≤ Cerr) :
    D.farError K Cerr ≤ ENNReal.ofReal
      ((D.N+3:ℕ)*Cerr*(B^K*D.Z⁻¹)^4*
        ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss)) := by
  have hcount : (2+(Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞) ≤ (D.N+3:ℕ) := by
    exact_mod_cast D.band_count_le
  have hpf := ENNReal.ofReal_le_ofReal D.prefactor_bound
  have hc : 0 ≤ Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss) := by positivity
  calc
    D.farError K Cerr ≤ ENNReal.ofReal (((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ))) *
        (D.N+3:ℕ)*ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*1 :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' hpf hcount) le_rfl) D.originalMeasure_mass_le_one
    _ = _ := by
      rw [mul_one,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_sub (by positivity : 0 < (2:ℝ)^D.N),Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^D.N)]
      ring

end JetStateFarData
end Falconer

end OAI
