import Mathlib
import OAI.Analysis.Commutator.PolarSupport

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_of_nonneg {T : H →L[ℂ] H} (hT : 0≤T) :
    partialIsometry T=rightSupport T := by
  have h : ∀ x : initial T, initialMap T x=(x : H) := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (initialMap T).continuous continuous_subtype_val) ?_
    intro y
    rw [initialMap_abs]
    change T y=CFC.abs T y
    rw [CFC.abs_of_nonneg T hT]
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma mul_rightSupport_eq_zero_of_nonneg {T B : H →L[ℂ] H} (hT : 0≤T)
    (hBT : B*T=0) : B*rightSupport T=0 := by
  have h : ∀ x : initial T, B x=0 := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (B.continuous.comp continuous_subtype_val) continuous_const) ?_
    intro y
    change B (CFC.abs T y)=0
    rw [CFC.abs_of_nonneg T hT]
    exact congrArg (fun R : H →L[ℂ] H => R y) hBT
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma rightSupport_mul_eq_zero_of_nonneg {T B : H →L[ℂ] H} (hT : 0≤T)
    (hTB : T*B=0) : rightSupport T*B=0 := by
  have hs : star B*T=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hT).star_eq,star_zero] using congrArg star hTB
  simpa only [star_mul,star_star,(isProjection_rightSupport T).isSelfAdjoint.star_eq,star_zero] using
    congrArg star (mul_rightSupport_eq_zero_of_nonneg hT hs)

lemma posPart_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : T⁺∈M := by
  change T⁺∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  exact ((show Commute T B from hB T hT).cfcₙ_real (·⁺)).eq.symm

def halfCut (T : H →L[ℂ] H) : H →L[ℂ] H :=
  rightSupport (T+T-(1 : H →L[ℂ] H))⁺

lemma isProjection_halfCut (T : H →L[ℂ] H) : IsStarProjection (halfCut T) :=
  isProjection_rightSupport _

lemma halfCut_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : halfCut T∈M := by
  apply rightSupport_mem M
  apply posPart_mem M
  exact M.toStarSubalgebra.sub_mem (M.add_mem hT hT) M.one_mem

lemma halfCut_mul_shift {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    halfCut T*(T+T-(1 : H →L[ℂ] H))=(T+T-(1 : H →L[ℂ] H))⁺ := by
  let b := T+T-(1 : H →L[ℂ] H)
  have hb : IsSelfAdjoint b := (hT.add hT).sub (IsSelfAdjoint.one _)
  change rightSupport b⁺*b=b⁺
  have hp : rightSupport b⁺*b⁺=b⁺ := by
    simpa only [CFC.abs_of_nonneg _ (CFC.posPart_nonneg b)] using initial_mul_abs b⁺
  have hn : rightSupport b⁺*b⁻=0 :=
    rightSupport_mul_eq_zero_of_nonneg (CFC.posPart_nonneg b) (CFC.posPart_mul_negPart b)
  nth_rw 2 [←CFC.posPart_sub_negPart b hb]
  rw [mul_sub,hp,hn,sub_zero]

lemma halfCut_commute {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) : Commute (halfCut T) T := by
  let b := T+T-(1 : H →L[ℂ] H)
  have hb : Commute b T := ((Commute.refl T).add_left (Commute.refl T)).sub_left (Commute.one_left T)
  have hbp : Commute b⁺ T := hb.cfcₙ_real (·⁺)
  have hs : Commute b⁺ (star T) := by rwa [hT.star_eq]
  change Commute (rightSupport b⁺) T
  simpa only [partialIsometry_of_nonneg (CFC.posPart_nonneg b)] using partialIsometry_commutes b⁺ T hbp hs

lemma halfCut_rounding {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) :
    star (halfCut T-T)*(halfCut T-T)≤T-T*T := by
  let b := T+T-(1 : H →L[ℂ] H)
  let q := halfCut T
  have hb : IsSelfAdjoint b := ((IsSelfAdjoint.of_nonneg hT).add (IsSelfAdjoint.of_nonneg hT)).sub (IsSelfAdjoint.one _)
  have hc : Commute b T := ((Commute.refl T).add_left (Commute.refl T)).sub_left (Commute.one_left T)
  have hp : Commute b⁺ T := hc.cfcₙ_real (·⁺)
  have hn : Commute b⁻ T := hc.cfcₙ_real (·⁻)
  have hpos : 0≤(1-T)*b⁺+T*b⁻ := add_nonneg
    (Commute.mul_nonneg (sub_nonneg.mpr hT1) (CFC.posPart_nonneg b)
      ((Commute.one_left b⁺).sub_left hp.symm))
    (Commute.mul_nonneg hT (CFC.negPart_nonneg b) hn.symm)
  have hqb : q*b=b⁺ := halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)
  have hq : q*q=q := (isProjection_halfCut T).isIdempotentElem.eq
  have hcq : q*T=T*q := (halfCut_commute (IsSelfAdjoint.of_nonneg hT)).eq
  have hnb : b⁻=q*b-b := by
    rw [hqb]
    calc
      b⁻=b⁺-(b⁺-b⁻) := by abel
      _=b⁺-b := by rw [CFC.posPart_sub_negPart b hb]
  have he : T-T*T-(q-T)*(q-T)=(1-T)*b⁺+T*b⁻ := by
    rw [hnb,←hqb]
    dsimp only [b]
    noncomm_ring [hq,hcq]
  rw [star_sub,(isProjection_halfCut T).isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hT).star_eq]
  exact sub_nonneg.mp (he.symm ▸ hpos)

end Kadison.Polar

end

end
end

end OAI
