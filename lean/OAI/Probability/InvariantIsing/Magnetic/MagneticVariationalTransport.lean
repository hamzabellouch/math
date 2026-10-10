import OAI.Probability.InvariantIsing.Magnetic.MagneticCouplingField
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupInterior

namespace OAI

/-! Transportation stability of the finite magnetic variational formula.
The bound is independent of the covariance path and optimizing bias. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

theorem finiteMagneticFunctional_transport_le {A B ι : Type*}
    [Fintype A] [Fintype B] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ)
    (hw : ∀ a j, 0 ≤ w a j) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ j, 0 < δ j)
    (hγsum : ∑ a, γ a=1) (hδsum : ∑ j, δ j=1)
    (hrow : ∀ a, ∑ j, w a j=γ a) (hcol : ∀ j, ∑ a, w a j=δ j) :
    (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ c).toReal+
        ∑ a, ∑ j, w a j* |b a-c j| := by
  classical
  let R := finiteR ρ eig hρ hsum
  let T := (finiteMagneticFunctional R δ c).toReal
  let cost := ∑ a, ∑ j, w a j* |b a-c j|
  have hR := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hF := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hR.1 hR.2
  have hbound : finiteMagneticFunctional R γ b ≤ ((T+cost : ℝ) : EReal) := by
    apply iSup_le
    intro mag
    let u := transportedMagnetization w δ (fun a => (mag.val a : ℝ))
    obtain ⟨s,hs,hms,_⟩ := exists_uniform_magnetization_radius
      (fun _ : ℕ => fun a => (mag.val a : ℝ)) (fun a => (mag.val a : ℝ))
      tendsto_const_nhds mag.property
    have hu j : |u j|<1 :=
      (transportedMagnetization_radius w δ _ hw hδ hcol hms j).trans_lt hs
    have hv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
      (fun a => (mag.val a : ℝ)) hγ hγsum (fun a => (mag.property a).le)
    have hvu := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum δ u
      (fun j => (hδ j).le) hδsum (fun j => (hu j).le)
    have he := transportedMagnetization_variational R w γ δ
      (fun a => (mag.val a : ℝ)) hw hδ hrow hcol (fun a => (mag.property a).le)
    rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_toReal hvu.1 hvu.2] at he
    have he' := EReal.coe_le_coe_iff.mp he
    have htrial := finiteMagneticFunctional_real_profile ρ eig hρ hsum δ c u
      (fun j => (hδ j).le) hδsum hu
    have hcost := transportedMagnetization_field_cost w γ b δ c
      (fun a => (mag.val a : ℝ)) hw hδ hrow (fun a => (mag.property a).le)
    rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_add]
    apply EReal.coe_le_coe
    change _ ≤ cost at hcost
    change _ ≤ T at htrial
    change _ ≤ (magneticVariationalFunctional R δ u).toReal at he'
    linarith
  rw [← EReal.coe_toReal hF.1 hF.2] at hbound
  exact EReal.coe_le_coe_iff.mp hbound

end InvariantIsing

end

end OAI
