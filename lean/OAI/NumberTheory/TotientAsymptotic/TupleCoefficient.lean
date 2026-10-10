import OAI.NumberTheory.TotientAsymptotic.TupleMassApproximation
import OAI.NumberTheory.TotientAsymptotic.MassVolumeApproximation

namespace OAI

/-! The actual tuple count approximates the finite arithmetic coefficient. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def tupleNormalization (x : ℝ) : ℝ := x/Real.log x*G x (m x)

lemma tupleNormalization_pos {x : ℝ} (hx : 1 < x) (hB : 0 < B x) :
    0 < tupleNormalization x :=
  mul_pos (div_pos (zero_lt_one.trans hx) (Real.log_pos hx)) (G_pos hB _)

/-- The largest-prime summation error tends to zero for each fixed cutoff,
uniformly over all bounded weights and all comparable endpoints. -/
theorem tuple_mass_normalized_approximation (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ t : ℝ, a*x ≤ t → t ≤ x → ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |weightedTupleCount x H t f/tupleNormalization x-(t/x)*(M x H f/G x (m x))| ≤ ε := by
  obtain ⟨C,hC,hupper⟩ := mass_upper hbox hren hmertens
  filter_upwards [hupper, eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hH hH2 hP
  let C₀ := C*Real.exp ((4*(lam/rho))*cofactorScale H)
  have hC₀ : 0 < C₀ := mul_pos hC (Real.exp_pos _)
  intro ε hε
  filter_upwards [weighted_tuple_mass_relative hpnt ha (P_lt_self hH2) hP (div_pos hε hC₀),
    hH, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x herr hmass hx hB
  intro t ht htx f hf
  have hnorm := tupleNormalization_pos hx hB
  have hG := G_pos hB (m x)
  have ht0 : 0 < t := (mul_pos ha (zero_lt_one.trans hx)).trans_le ht
  have hlog := Real.log_pos hx
  have heq : weightedTupleCount x H t f/tupleNormalization x-(t/x)*(M x H f/G x (m x)) =
      (weightedTupleCount x H t f-(t/Real.log x)*M x H f)/tupleNormalization x := by
    unfold tupleNormalization
    field_simp
  rw [heq, abs_div, abs_of_pos hnorm]
  apply (div_le_iff₀ hnorm).mpr
  apply (herr t ht htx f hf).trans
  have hm : M x H (fun _ => 1) ≤ C₀*G x (m x) := hmass _ (fun _ => le_rfl)
  calc
    (ε/C₀)*(t/Real.log x)*M x H (fun _ => 1) ≤
        (ε/C₀)*(t/Real.log x)*(C₀*G x (m x)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = ε*(t/Real.log x)*G x (m x) := by field_simp
    _ ≤ ε*tupleNormalization x := by
      unfold tupleNormalization
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htx hlog.le) hε.le) hG.le

/-- Combining the proved prime summation with the proved mass/volume bridge
leaves only the distinct-value/collision argument. This is a theorem about
actual tuples, not a published hypothesis. -/
theorem tuple_finite_coefficient_approximation (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hmertens : MertensProductInput)
    (hren : FordRenewalInput) (hford : FordCoordinateConcentrationInput)
    {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, a*x ≤ t → t ≤ x →
        |weightedTupleCount x H t f/tupleNormalization x-(t/x)*AH H f (theta x)| ≤ δ H+ε := by
  obtain ⟨δ,hδ,hmass⟩ := mass_finite_coefficient_approximation hbox hmertens hren hford
  refine ⟨fun H => |δ H|, by simpa using hδ.abs, ?_⟩
  filter_upwards [hmass, tuple_mass_normalized_approximation hpnt hbox hren hmertens ha] with H hH htuple
  intro f hf ε hε
  filter_upwards [hH f hf (ε/2) (by positivity), htuple (ε/2) (by positivity),
    eventually_gt_atTop (1 : ℝ)] with x hx htup hx1
  intro t ht htx
  have ht0 : 0 ≤ t/x := div_nonneg ((mul_pos ha (zero_lt_one.trans hx1)).trans_le ht).le
    (zero_lt_one.trans hx1).le
  have ht1 : t/x ≤ 1 := (div_le_one (zero_lt_one.trans hx1)).mpr htx
  calc
    _ ≤ |weightedTupleCount x H t f/tupleNormalization x-(t/x)*(M x H f/G x (m x))|+
        |(t/x)*(M x H f/G x (m x))-(t/x)*AH H f (theta x)| := abs_sub_le _ _ _
    _ ≤ ε/2+(δ H+ε/2) := by
      apply add_le_add (htup t ht htx f hf)
      rw [← mul_sub, abs_mul, abs_of_nonneg ht0]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht1).trans hx
    _ ≤ |δ H|+ε := by linarith [le_abs_self (δ H)]

end TotientAsymptotic

end

end OAI
