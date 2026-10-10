import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRaw

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem no_slot_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C : ℝ),
      0≤r → r≤R → 0≤C →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawMoment data W c κ C → RawMoment data (scaleProfile W) c κ C →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) 0 0‖^2)≤
        C*K*U^(sourceExponent r+ε) := by
  obtain ⟨c,κ,hc,hc1,hκ,hbudget⟩ := exists_amplification_budget R ε hR hε
  obtain ⟨d,hd,havg⟩ := eventually_fixed_ray_amplification M H hH S φ hφ hφc hφp
    hφ0 hφne a b B ha hab hB hφs hφB
  obtain ⟨x0,hx0⟩ := eventually_atTop.mp havg
  let A := max 1 (max x0 (1/b))
  have hb : 0<b := ha.trans_le hab
  have hA : 1≤A := le_max_left _ _
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hAx0 : x0≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hbA : 1≤b*A := by
    have hh : 1/b≤A := (le_max_right _ _).trans (le_max_right _ _)
    have hh' := (div_le_iff₀ hb).mp hh
    nlinarith
  obtain ⟨Klog,hKlog,hlog⟩ := logarithmic_cost_eventually A b (R/3) (ε/2)
    hA hbA (by positivity) (by positivity)
  let F := (b*A)^6*((b*A)^6)^κ/A
  let K := (4/d)*F*Klog
  have hF : 0≤F := by dsimp [F]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with U hlog hU
  intro r data rows W wa wb C hr hrR hC hwa hwb hWs hW hrows hraw0 hraw1
  let p := amplificationPower c r
  let x := A*U^p
  let D := U^r
  let V := b*x
  let N := U*V^6
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hp : 0≤p := amplificationPower_nonneg c r
  have hpR : p≤R/3 := amplificationPower_upper c r R hc1 hr hrR
  have hxA : A≤x := fixed_multiplier_lower U A p hU hAp.le hp
  have hV : 1≤V := by
    change 1≤b*(A*U^p)
    rw [←mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hbA (Real.one_le_rpow hU hp)
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hN : 1≤N := one_le_mul_of_one_le_of_one_le hU (one_le_pow₀ hV)
  have hDN : D^(1+c)≤N := amplified_norm_dominates U A b c r hU hbA
  have hxb : x*b=V := mul_comm x b
  have hav := hx0 x (hAx0.trans hxA) data rows W wa wb D U
    (C*N*(N*D)^κ) hwa hwb hWs hW hDp hrows
    (by rw [hxb]; exact hraw0.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
    (by rw [hxb]; exact hraw1.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
  have hlog' := hlog p hp hpR
  have hnorm : N*(N*D)^κ/x=F*U^(1+5*p+κ*(1+6*p+r)) :=
    amplified_energy_power U A b p r κ hUp
  have hexp := hbudget r hr hrR
  have hpow : U^(1+5*p+κ*(1+6*p+r)+ε/2)≤U^(sourceExponent r+ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by dsimp [p]; linarith)
  calc
    _ ≤ 4*(1+2*Real.log (x*b))*(C*N*(N*D)^κ)*Real.log x/(d*x) := hav
    _ = C*(4/d)*(N*(N*D)^κ/x)*((1+2*Real.log (b*x))*Real.log x) := by
      rw [mul_comm x b]
      ring
    _ = (C*(4/d)*F)*((1+2*Real.log (b*x))*Real.log x)*
        U^(1+5*p+κ*(1+6*p+r)) := by rw [hnorm]; ring
    _ ≤ (C*(4/d)*F)*(Klog*U^(ε/2))*U^(1+5*p+κ*(1+6*p+r)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
      exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C*K*U^(1+5*p+κ*(1+6*p+r)+ε/2) := by
      rw [Real.rpow_add hUp (1+5*p+κ*(1+6*p+r)) (ε/2)]
      dsimp [K]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)

end SevenEighths.HeckeInverseAmplification

end

end OAI
