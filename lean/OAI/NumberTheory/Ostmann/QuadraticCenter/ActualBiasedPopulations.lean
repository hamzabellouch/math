import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualBiasedPopulationsBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasedCommonCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_biased_populations (d : Decomposition)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ cA : ℝ,0 < cA ∧ ∀ᶠ T : ℝ in atTop,∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      ∀ P : Finset ℕ,(∀p∈P,p.Prime) → (∀p∈P,Odd p) →
      (∀p∈P,Z≤p ∧ p≤2*Z) → c*(Z:ℝ)/Real.log Z ≤ P.card →
      ∀ ε t : ℕ→ℤ,
      (∀p∈P,(ε p=1 ∨ ε p=-1) ∧
        δ/4≤(∑x∈positiveIntegerWindow d.A (parameterX T),
          ((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/(positiveIntegerWindow d.A (parameterX T)).card ∧
        (∑x∈negativeIntegerWindow d.B (parameterX T),
          ((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/(negativeIntegerWindow d.B (parameterX T)).card≤-δ/4) →
      ∃ h : ℤ, ∃ m : ℕ, ∃ P₀ : Finset ℕ, ∃ e : ℕ→ℤ, ∃ A₀ D₀ : Finset ℤ,
        0 < m ∧ m ≤ quadraticLiftMultiplierBound Z ∧ m < Z ∧ IsCoprime h (m:ℤ) ∧
        h.natAbs ≤ quadraticLiftHeight (parameterX T) Z ∧ P₀⊆P ∧
        commonCenterCutoff Z ≤ P₀.card ∧
        commonCenterMomentScale P.card Z (evenMomentParameter (parameterX T) Z)/4 ≤
          2*(P.card:ℝ)*(P₀.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) ∧
        (∀p∈P₀,e p=1 ∨ e p=-1) ∧
        A₀⊆positiveIntegerWindow d.A (parameterX T) ∧
        D₀⊆negativeIntegerWindow d.B (parameterX T) ∧
        cA*Real.sqrt (parameterX T)/(Real.log (parameterX T:ℝ))^3 ≤ A₀.card ∧
        cA*Real.sqrt (parameterX T)/(Real.log (parameterX T:ℝ))^3 ≤ D₀.card ∧
        (∀x∈A₀∪D₀,δ/8 ≤ |affineKernelAverage P₀ e m h x| ∧ (m:ℤ)*x-h≠0) ∧
        (∀x∈A₀,∀y∈A₀,|(x:ℝ)-(y:ℝ)|≤parameterX T) ∧
        (∀x∈D₀,∀y∈D₀,|(x:ℝ)-(y:ℝ)|≤parameterX T) ∧
        (∀x∈A₀,∀y∈D₀,Nat.Prime (x-y).natAbs ∧
          (parameterX T:ℝ)^(9/10:ℝ)≤((x-y).natAbs:ℝ)) := by
  obtain ⟨c₀,hc₀,hcard⟩ := actual_integerWindows_card_lower d
  refine ⟨(δ/8)*c₀,by positivity,?_⟩
  filter_upwards [eventually_biased_common_center d c δ hc hδ,
    parameterX_tendsto.eventually hcard,
    parameterX_tendsto.eventually (eventually_actual_integerWindows_cross d),
    eventually_nat_condition_of_logBand (eventually_ge_atTop (2:ℕ))]
      with T hcenter hcard hcross hZtwo
  intro Z hZl hZu P hP ho hband hJ ε t hbias
  obtain ⟨h,m,P₀,hm,hmB,hmZ,hcop,hh,hsub,hcut,hcount,hres⟩ :=
    hcenter Z hZl hZu P hP ho hband hJ ε t
      (fun p hp => (hbias p hp).1.symm) (fun p hp => (hbias p hp).2.1)
  have hZ : 2≤Z := hZtwo Z hZl
  have hcutpos : 1≤commonCenterCutoff Z := by
    change 1≤⌊(Z:ℝ)^(3/5:ℝ)⌋₊
    have hh : (1:ℝ)≤(Z:ℝ)^(3/5:ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1≤Z by omega)) (by norm_num)
    exact Nat.le_floor (by simpa only [Nat.cast_one] using hh)
  have hP₀ : 0 < P₀.card := lt_of_lt_of_le (by omega : 0 < commonCenterCutoff Z) hcut
  have hprime : ∀p∈P₀,p.Prime ∧ m < p := fun p hp =>
    ⟨hP p (hsub hp),hmZ.trans_le (hband p (hsub hp)).1⟩
  obtain ⟨A₀,D₀,hA,hD,hAc,hDc,_hApos,_hDpos,hbias₀⟩ :=
    actual_commonCenter_large_bias_subsets d (parameterX T) P₀ hP₀ ε t m h hm hprime hres hδ
      (fun p hp => hbias p (hsub hp))
  have hsign := (actual_commonCenter_bias_transport d (parameterX T) P₀ hP₀ ε t m h hm
    hprime hres δ (fun p hp => hbias p (hsub hp))).1
  refine ⟨h,m,P₀,commonCenterOrientation ε m,A₀,D₀,hm,hmB,hmZ,hcop,hh,hsub,hcut,hcount,
    hsign,hA,hD,?_,?_,hbias₀,?_,?_,?_⟩
  · have hs := mul_le_mul_of_nonneg_left hcard.1 (by positivity : (0:ℝ)≤δ/8)
    calc
      _ = (δ/8)*(c₀*Real.sqrt (parameterX T)/(Real.log (parameterX T:ℝ))^3) := by ring
      _ ≤ _ := hs.trans hAc
  · have hs := mul_le_mul_of_nonneg_left hcard.2 (by positivity : (0:ℝ)≤δ/8)
    calc
      _ = (δ/8)*(c₀*Real.sqrt (parameterX T)/(Real.log (parameterX T:ℝ))^3) := by ring
      _ ≤ _ := hs.trans hDc
  · exact fun x hx y hy => positiveIntegerWindow_diameter (hA hx) (hA hy)
  · exact fun x hx y hy => negativeIntegerWindow_diameter (hD hx) (hD hy)
  · exact fun x hx y hy => hcross x (hA hx) y (hD hy)

end Ostmann.QuadraticCenter

end

end OAI
