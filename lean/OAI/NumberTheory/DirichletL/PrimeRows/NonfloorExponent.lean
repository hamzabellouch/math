import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily

lemma adaptive_mixed_saving (N : ℕ) (a q Δ ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2<a) (ha' : a≤1) (hq : 0≤q) (hq' : q≤(2*a-1)/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hε : 0≤ε) (hεm : 0≤εm)
    (hslot : 0≤slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤3/16) (hv : v≤13/16+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤e) (heps : 0≤eps)
    (hbudget : (13/16)*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+overhead+saving≤49/440640) :
    mixedSourceExponent a v d (adaptiveRowExponent (2*a-1) q Δ ε εm slotMesh ν) q+
      ProbeCentralExponent.realLoss N v e eps loss mesh+overhead≤3/16+Δ-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_saving (2*a-1) (q/(2*a-1)) Δ (159*ε+εm+slotMesh+7*ν)
      ζ μ v d (ProbeCentralExponent.realLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' hΔ hΔ' hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    simpa only [adaptiveRowExponent,ite_eq_left hd,add_assoc] using hb
  · have hhl : 0≤78*ε+εm := by positivity
    have hh := high_mixed_margin (2*a-1) q Δ (78*ε+εm) ζ μ v d
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl (by linarith)
      hζ hv hμ hdv
    rw [haeq] at hh
    simp only [adaptiveRowExponent,ite_eq_right hd]
    simp only [add_assoc] at hh ⊢
    linarith

lemma central_class_exponent_identity (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) :
    ((25/48)*a-181/300+(105/8)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6)=
    mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh+overhead := by
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
