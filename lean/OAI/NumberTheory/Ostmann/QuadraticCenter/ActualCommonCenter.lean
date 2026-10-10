import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayMeanScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterProducts
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericProductLift
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessLiftCount

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_common_center_of_witness_probability (c C : ℝ)
    (hc : 0<c) (hC : 0<C) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ, ∀ [NeZero L],
      T/2≤Real.log Z → Real.log Z≤2*T →
      1≤z → T^auxiliaryExponent/2≤Real.log z → Real.log z≤2*T^auxiliaryExponent →
      Squarefree L → (L:ℝ)≤(Z:ℝ)^(1/50:ℝ) →
      ∀ (A : ∀ p : ℕ,Finset (ZMod p)) (P : Finset ℕ),
      (∀p∈P,Nat.Prime p) → (∀p∈P,Z≤p ∧ p≤2*Z) → c*(Z:ℝ)/Real.log Z≤P.card →
      ∀ t : ℕ → ℤ,
      Real.exp (-C*(auxiliaryK Z z:ℝ))≤
        ((quadraticWitnessProducts P (evenMomentParameter (parameterX T) Z) L A
          (parameterX T) (auxiliaryK Z z) t).card:ℝ)/
          (P.card.choose (evenMomentParameter (parameterX T) Z):ℝ) →
      ∃ h : ℤ,∃ m : ℕ,∃ P₀ : Finset ℕ,
        0 < m ∧ m≤quadraticLiftMultiplierBound Z ∧ IsCoprime h (m:ℤ) ∧
        h.natAbs≤quadraticLiftHeight (parameterX T) Z ∧ P₀⊆P ∧
        commonCenterCutoff Z≤P₀.card ∧
        commonCenterMomentScale P.card Z (evenMomentParameter (parameterX T) Z)/4 ≤
          2*(P.card:ℝ)*(P₀.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) ∧
        ∀p∈P₀,(p:ℤ)∣h-(m:ℤ)*t p := by
  classical
  filter_upwards [eventually_commonCenter_numeric_inputs c C hc hC,
    eventually_divisor_quadratic_bounded_lift,eventually_primeProduct_radius_bounds,
    parameterX_tendsto.eventually_gt_atTop 0,eventually_ge_atTop (1:ℝ)]
    with T hnum hlift hradius hX hT
  intro Z z L _ hZl hZu hz hzl hzu hL hLZ A P hP hband hJ t hprob
  have hlogZ : 0<Real.log Z := by linarith
  have hZ : 2≤Z := by
    have hh := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ
    exact_mod_cast (show (2:ℕ)≤Z from by exact_mod_cast (show (1:ℝ)<Z from hh))
  have hJupper : P.card≤2*Z := by
    have hsub : P⊆Finset.Icc 1 (2*Z) := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,(hband p hp).2⟩
    simpa using Finset.card_le_card hsub
  let k := evenMomentParameter (parameterX T) Z
  let E := quadraticWitnessProducts P k L A (parameterX T) (auxiliaryK Z z) t
  have hn := hnum Z z hZl hZu hz hzl hzu P.card E.card hJ hJupper hprob
  have he : E⊆primeProductSamples P k := Finset.filter_subset _ _
  have hw : ∀q∈E,∃a:ℕ,1≤a ∧ a≤quadraticLiftMultiplierBound Z ∧
      (boundedSubsetLifts q.primeFactors a t (quadraticLiftHeight (parameterX T) Z)).Nonempty := by
    intro q hq
    obtain ⟨hqs,hevent⟩ := Finset.mem_filter.mp hq
    obtain ⟨s,hs,d,hd,v,hv,hlarge⟩ := hevent
    have hsI := Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1
    have hqp : 0<q := (primeProductSamples_primeFactors hP hqs).1.ne_zero.bot_lt
    have hR := hradius Z hZl P hband q hqs
    exact hlift Z z L hZ hZl hZu hz hzl hzu hL (Nat.pos_of_neZero L) hLZ A
      (adaptiveInverse q) s v d q hsI.1 hsI.2.le hv hd hqp (parameterX T)
      (by exact_mod_cast hX) hR.1 hR.2 (centerCorrection q L (primeProductCenter q t)) t hlarge
  obtain ⟨h,m,P₀,hm,hmA,hcop,hh,hsub,hcut,hsize,hcenter⟩ :=
    reduced_common_center_from_product_witnesses hP he t (quadraticLiftMultiplierBound Z)
      (quadraticLiftHeight (parameterX T) Z) Z (k-10) (commonCenterCutoff Z)
      (commonCenterMass P.card Z k) hn.multiplier_pos hn.multiplier_lt
      (fun p hp => (hband p hp).1) (by have := hn.k_ten_le; omega)
      (Nat.sub_le _ _) hn.mass_pos hw hn.budget hn.spacing hn.gap
  exact ⟨h,m,P₀,hm,hmA,hcop,hh,hsub,hcut,hn.mass_lower.trans hsize,hcenter⟩

end Ostmann.QuadraticCenter

end

end OAI
