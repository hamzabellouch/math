import OAI.Analysis.PlanarPacking.RationalEnvelopes
import OAI.Analysis.PlanarPacking.BernsteinBoxes

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
noncomputable def sharpTaylor (ell n : ℕ) : ℝ :=
  (425:ℝ)/1000*piUpper^ell+(23:ℝ)/10*(directRational ell+transformRational ell n)+
    (17:ℝ)/1000*atomicRational ell n
lemma table_jet_sharp (a : Bool) (ell n : ℕ) : |tableHJet a ell n| ≤ sharpTaylor ell n := by
  have hd:=direct_spectral_bound (tableData a) ell (n:ℝ)
  have hk:=sharp_moment_bound (tableData (!a)) ell (Nat.cast_nonneg n)
  have hc:=table_constant_bound a
  have hm:=table_coeff_mass a
  have hcm:=table_constant_bound (!a)
  have hmm:=table_coeff_mass (!a)
  have hp:=pow_le_pow_left₀ Real.pi_pos.le pi_le_upper ell
  have hdn:=directEnvelope_nonneg ell
  have htn:=transformEnvelope_nonneg ell (Nat.cast_nonneg n)
  have han:=atomicEnvelope_nonneg ell (n:ℝ)
  have hd1:=mul_le_mul hc (show 25*Real.pi^ell ≤ 25*piUpper^ell by nlinarith) (by positivity : 0≤25*Real.pi^ell) (by norm_num : (0:ℝ)≤17/1000)
  have hd2:=mul_le_mul (show |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ ≤ (23:ℝ)/10 by linarith)
    (directEnvelope_le_rat ell) hdn (by norm_num : (0:ℝ)≤23/10)
  have hk1:=mul_le_mul (show |(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖ ≤ (23:ℝ)/10 by linarith)
    (transformEnvelope_le_rat ell n) htn (by norm_num : (0:ℝ)≤23/10)
  have hk2:=mul_le_mul hcm (atomicEnvelope_le_rat ell n) han (by norm_num : (0:ℝ)≤17/1000)
  have ha:=abs_add_le (cardinalSeries (tableData a) ell n) (K (tableData (!a)) ell n)
  change |K (tableData (!a)) ell n| ≤ (|(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖)*transformEnvelope ell n+|(tableData (!a)).C| * atomicEnvelope ell n at hk
  change |cardinalSeries (tableData a) ell n+K (tableData (!a)) ell n| ≤ _
  unfold sharpTaylor
  nlinarith
lemma normalizedH_table (a : Bool) (m : ℝ) (ell : ℕ) :
    normalizedH a m ell=tableHJet a ell m/(ell.factorial:ℝ) := by
  simp only [normalizedH,fullMoment_direct,fullMoment_transformed,tableHJet,add_div]
lemma sourcePower_sharp (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) :
    |sourcePower a n y nu r| ≤ |y|^r*sharpTaylor (r+nu) n/((r+nu).factorial:ℝ) := by
  rw [sourcePower,normalizedH_table,abs_mul,abs_mul,abs_pow,abs_div,abs_of_nonneg (Nat.cast_nonneg ((r+nu).factorial) : (0:ℝ)≤((r+nu).factorial:ℝ))]
  have ha : |(if a then (1:ℝ) else -1)|=1 := by cases a <;> norm_num
  rw [ha,one_mul,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (table_jet_sharp a (r+nu) n) (Nat.cast_nonneg _)) (pow_nonneg (abs_nonneg _) _)
lemma sourcePower_of_cap (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) {B : ℝ}
    (hB : sharpTaylor (r+nu) n/((r+nu).factorial:ℝ)≤B) :
    |sourcePower a n y nu r| ≤ |y|^r*B := by
  exact (sourcePower_sharp a n y nu r).trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hB (pow_nonneg (abs_nonneg y) r))
lemma RBox.contains_of_abs {box : RBox} {x B : ℝ} (hx : |x|≤B)
    (hl : (box.lo:ℝ)≤ -B*precision) (hu : B*precision≤(box.hi:ℝ)) : box.Contains x := by
  have hp : (0:ℝ)≤precision := (by exact_mod_cast (le_of_lt precision_pos))
  have hh:=abs_le.mp hx
  simpa only [RBox.Contains,mul_comm (precision:ℝ)] using (And.intro (hl.trans (mul_le_mul_of_nonneg_right hh.1 hp)) ((mul_le_mul_of_nonneg_right hh.2 hp).trans hu))
end SharpPlanar

end OAI
