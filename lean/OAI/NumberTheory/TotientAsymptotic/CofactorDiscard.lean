import OAI.NumberTheory.TotientAsymptotic.UntruncatedMass
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

/-- Any finite family of preimages with oversized smooth cofactors has
vanishing normalized size. The family may be chosen from actual bad values. -/
theorem oversized_cofactor_count (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ S : Finset (RemainderDatum (L x H) × ℕ),
      (∀ q ∈ S, IsUntruncatedRemainder x H q.1 ∧ q.2.Prime ∧
        x^(9/10 : ℝ) ≤ q.2 ∧ ((wholePreimage q.2 q.1).totient : ℝ) ≤ x ∧
        Real.exp (2*bandScale x (L x H)) < Real.log q.1.cofactor) →
      (S.card : ℝ) ≤ ε H*tupleNormalization x := by
  obtain ⟨C,hC,htail⟩ := smooth_cutoff_tail hmertens
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp htail
  let ε := fun H => 10*C*Real.exp (-lam*cofactorScale H)
  have ht : Tendsto ε atTop (nhds 0) := by
    have hh := Real.tendsto_exp_atBot.comp (cofactorScale_tendsto.const_mul_atTop_of_neg (neg_neg_of_pos lam_pos))
    simpa only [ε,mul_zero,Function.comp_def] using hh.const_mul (10*C)
  refine ⟨ε,ht,?_⟩
  filter_upwards [full_prime_mass_le_G hbox hren,eventually_ge_atTop 2,
    (cofactorScale_tendsto.const_mul_atTop lam_pos).eventually (eventually_ge_atTop b₀)]
    with H hmass hH hlarge
  filter_upwards [hmass,untruncated_witness_count,theta_eventually_mem,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hmass hcount hs hm hx hB
  intro S hS
  have hPH := P_lt_self hH
  have hL : 0<L x H := by unfold L; omega
  let T := S.image Prod.fst
  let Q := T.image RemainderDatum.cofactor
  have hT (η : RemainderDatum (L x H)) (hη : η ∈ T) : IsUntruncatedRemainder x H η := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hη
    exact (hS q hq).1
  have hQ (a : ℕ) (ha : a ∈ Q) : 0<a ∧ largestPrimeFactor a ≤ remainderPrimeBound x (L x H) ∧
      Real.exp (2*bandScale x (L x H))<Real.log a := by
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hη
    exact ⟨(hS q hq).1.1,untruncated_cofactor_smooth hL (hS q hq).1,(hS q hq).2.2.2.2⟩
  have hb := terminal_band_lower hs.1 (hPH.le.trans hm)
  have hsmall := hb₀ (bandScale x (L x H)) (hlarge.trans hb) x (L x H) rfl Q hQ
  have hwt : (∑ η ∈ T, (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight η.primes) ≤
      (C*Real.exp (-bandScale x (L x H)))*G x (m x) := by
    apply (untruncated_weight_product T hT).trans
    exact mul_le_mul hsmall hmass
      (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p)) (by positivity)
  have hsmall' : C*Real.exp (-bandScale x (L x H)) ≤ C*Real.exp (-lam*cofactorScale H) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    nlinarith [hb]
  have hx0 := zero_lt_one.trans hx
  have hlog := Real.log_pos hx
  have hscale : 0 ≤ 10*x/Real.log x := by positivity
  calc
    _ ≤ (10*x/Real.log x)*∑ η ∈ T, (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight η.primes :=
      hcount H S (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1,(hS q hq).2.2.1,(hS q hq).2.2.2.1⟩)
    _ ≤ (10*x/Real.log x)*((C*Real.exp (-bandScale x (L x H)))*G x (m x)) :=
      mul_le_mul_of_nonneg_left hwt hscale
    _ ≤ (10*x/Real.log x)*((C*Real.exp (-lam*cofactorScale H))*G x (m x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall' (G_pos hB _).le) hscale
    _ = _ := by unfold ε tupleNormalization; ring

end TotientAsymptotic

end

end OAI
