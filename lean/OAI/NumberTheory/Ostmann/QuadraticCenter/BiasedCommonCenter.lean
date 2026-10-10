import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterAuxiliaryChoice
import OAI.NumberTheory.Ostmann.QuadraticCenter.SelectedCommonCenter

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_biased_common_center (d : Decomposition)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      ∀ P : Finset ℕ,(∀r∈P,r.Prime) → (∀r∈P,Odd r) →
      (∀r∈P,Z≤r ∧ r≤2*Z) → c*(Z:ℝ)/Real.log Z ≤ P.card →
      ∀ ε t : ℕ→ℤ,(∀r∈P,ε r = -1 ∨ ε r = 1) →
      (∀r∈P,δ/4 ≤ (∑a∈positiveIntegerWindow d.A (parameterX T),
        ((ε r*jacobiSym (a-t r) r:ℤ):ℝ))/(positiveIntegerWindow d.A (parameterX T)).card) →
      ∃ h : ℤ, ∃ m : ℕ, ∃ P₀ : Finset ℕ,
        0 < m ∧ m ≤ quadraticLiftMultiplierBound Z ∧ m < Z ∧ IsCoprime h (m:ℤ) ∧
        h.natAbs ≤ quadraticLiftHeight (parameterX T) Z ∧ P₀ ⊆ P ∧
        commonCenterCutoff Z ≤ P₀.card ∧
        commonCenterMomentScale P.card Z (evenMomentParameter (parameterX T) Z)/4 ≤
          2*(P.card:ℝ)*(P₀.card:ℝ)^(evenMomentParameter (parameterX T) Z-1) ∧
        ∀p∈P₀,(p:ℤ) ∣ h-(m:ℤ)*t p := by
  classical
  filter_upwards [eventually_actual_selected_common_center d c δ hc hδ,
    eventually_actual_auxiliary_product d,eventually_commonCenterElementaryBounds c hc]
    with T hcenter haux helem
  intro Z hZl hZu P hP ho hband hJ ε t hε hbias
  have hJupper : P.card ≤ 2*Z := by
    have hsub : P ⊆ Finset.Icc 1 (2*Z) := fun p hp =>
      Finset.mem_Icc.mpr ⟨(hP p hp).pos,(hband p hp).2⟩
    simpa using Finset.card_le_card hsub
  have he := helem Z hZl P.card hJ hJupper
  obtain ⟨z,F,hz,hzl,hzu,hzZ,hFK,_hsf,_hprod,hsize,hF,_hdisj⟩ := haux Z hZl hZu
  obtain ⟨h,m,P₀,hm,hmA,hcop,hh,hsub,hcut,hcount,hres⟩ :=
    hcenter Z z hZl hZu hz hzl hzu F hFK (fun p hp => (hF p hp).1)
      (fun p hp => (hF p hp).2.1) (fun p hp => (hF p hp).2.2.trans hzZ)
      (by simpa only [Nat.cast_prod] using hsize) P hP ho hband hJ ε t hε hbias
  exact ⟨h,m,P₀,hm,hmA,hmA.trans_lt he.multiplier_lt,hcop,hh,hsub,hcut,hcount,hres⟩

end Ostmann.QuadraticCenter

end

end OAI
