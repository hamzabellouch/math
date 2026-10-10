import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem condExp_spin_eq_of_restricted_density
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hdensity : Measure.map X (mu.restrict {x | S x = IsingSpin.pos}) =
      (Measure.map X mu).withDensity (fun y => ENNReal.ofReal ((1 + q y) / 2))) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  let E : Set Ω := {x | S x = IsingSpin.pos}
  have hE : MeasurableSet E :=
    (show MeasurableSet ({IsingSpin.pos} : Set IsingSpin) from trivial).preimage hS
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hI : Integrable I mu := (integrable_const (1 : ℝ)).indicator hE
  have hsrc : (fun x => ((mu.restrict E).rnDeriv mu x).toReal) =ᵐ[mu] I := by
    filter_upwards [Measure.rnDeriv_restrict_self mu hE] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [I, hxE]
  have hRN := toReal_rnDeriv_map (Measure.absolutelyContinuous_restrict (μ := mu) (s := E)) hX
  have hpost :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] mu[I | mY.comap X] :=
    hRN.trans (condExp_congr_ae hsrc)
  have htarg :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] fun x => (1 + q (X x)) / 2 := by
    have hderiv := Measure.rnDeriv_withDensity (Measure.map X mu)
      (show Measurable (fun y => ENNReal.ofReal ((1 + q y) / 2)) by fun_prop)
    rw [← hdensity] at hderiv
    filter_upwards [ae_of_ae_map hX.aemeasurable hderiv,
      ae_of_ae_map hX.aemeasurable hqb] with x hx hxb
    rw [hx, ENNReal.toReal_ofReal]
    have := (abs_le.mp hxb).1
    linarith
  have hIp : mu[I | mY.comap X] =ᵐ[mu] fun x => (1 + q (X x)) / 2 :=
    hpost.symm.trans htarg
  have hsrepr : (fun x => spinSign (S x)) = (2 : ℝ) • I - (fun _ => 1) := by
    funext x
    cases hs : S x <;> norm_num [I, E, hs, spinSign]
  rw [hsrepr]
  have hsub := condExp_sub (hI.smul (2 : ℝ)) (integrable_const (1 : ℝ)) (mY.comap X)
  have hmul := condExp_smul (μ := mu) (2 : ℝ) I (mY.comap X)
  filter_upwards [hsub, hmul, hIp] with x hxsub hxmul hxI
  rw [hxsub, Pi.sub_apply, hxmul, Pi.smul_apply, smul_eq_mul,
    condExp_const hX.comap_le, hxI]
  ring

theorem condExp_spin_eq_of_conditional_linearTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hfair : mu {x | S x = IsingSpin.pos} = (1 / 2 : ENNReal))
    (hcond : Measure.map X (ProbabilityTheory.cond mu {x | S x = IsingSpin.pos}) =
      linearSignalTilt (Measure.map X mu) q 1) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  apply condExp_spin_eq_of_restricted_density hS hX hq hqb
  have hscaled := congrArg (fun nu : Measure Y => (1 / 2 : ENNReal) • nu) hcond
  rw [ProbabilityTheory.cond, Measure.map_smul _ hX.aemeasurable, hfair, smul_smul] at hscaled
  norm_num at hscaled
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤), one_smul] at hscaled
  rw [hscaled, linearSignalTilt, ← withDensity_smul (2⁻¹) (by fun_prop)]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp [div_eq_mul_inv, mul_comm]

end Problem367

end

end OAI
