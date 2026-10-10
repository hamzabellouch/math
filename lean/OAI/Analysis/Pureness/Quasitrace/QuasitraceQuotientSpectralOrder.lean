import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSpectralCuts
import Mathlib.Tactic.Module

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_projection_nonneg {p : T.CauchyQuotient hadd} (hsa : IsSelfAdjoint p) (hid : p*p=p) : 0 ≤ p := by
  have h := star_mul_self_nonneg p
  rwa [hsa.star_eq,hid] at h

lemma quotient_projection_separated_corners {x p q : T.CauchyQuotient hadd} {s t : ℝ}
    (hp : IsSelfAdjoint p) (hp2 : p*p=p) (hq : IsSelfAdjoint q) (hq2 : q*q=q)
    (hpq : Commute p q) (hpx : Commute p x) (hqx : Commute q x)
    (hst : s<t) (hlow : t • p ≤ p*x) (hupp : (1-q)*x ≤ s • (1-q)) : p*(1-q)=0 := by
  let e := 1-q
  have he2 : e*e=e := by
    dsimp [e]
    calc
      (1-q)*(1-q)=1-q-q+q*q := by noncomm_ring
      _ = 1-q := by rw [hq2]; abel
  have he : IsSelfAdjoint e := by
    change star (1-q)=1-q
    rw [star_sub,star_one,hq.star_eq]
  have hp0 := T.quotient_projection_nonneg hadd hp hp2
  have he0 := T.quotient_projection_nonneg hadd he he2
  have hpe : Commute p e := (Commute.one_right _).sub_right hpq
  have hxe : Commute x e := (Commute.one_right _).sub_right hqx.symm
  let r := p*e
  have hr0 : 0 ≤ r := Commute.mul_nonneg hp0 he0 hpe
  have hl : 0 ≤ r*x-t • r := by
    have hc : Commute (p*x-t • p) e := (hpe.mul_left hxe).sub_left (hpe.smul_left t)
    have h := Commute.mul_nonneg (sub_nonneg.mpr hlow) he0 hc
    have heq : (p*x-t • p)*e=r*x-t • r := by
      dsimp [r]
      rw [sub_mul,smul_mul_assoc,mul_assoc p x e,hxe.eq,←mul_assoc]
    rwa [heq] at h
  have hu : 0 ≤ s • r-r*x := by
    have hc : Commute p (s • e-e*x) :=
      (hpe.smul_right s).sub_right (hpe.mul_right hpx)
    have h := Commute.mul_nonneg hp0 (sub_nonneg.mpr hupp) hc
    change 0 ≤ p*(s • e-e*x) at h
    simpa only [r,mul_sub,mul_smul_comm,←mul_assoc] using h
  have hsr : 0 ≤ (s-t) • r := by
    have h := add_nonneg hl hu
    convert h using 1
    module
  have hn : 0 ≤ -r := by
    have h : 0 ≤ (t-s)⁻¹ • ((s-t) • r) :=
      (Positive.smul ⟨(t-s)⁻¹, inv_nonneg.mpr (sub_pos.mpr hst).le⟩
        ⟨(s-t) • r, hsr⟩).2
    have heq : (t-s)⁻¹ • ((s-t) • r)= -r := by
      rw [smul_smul]
      have he : (t-s)⁻¹*(s-t)= -1 := by
        field_simp [(sub_pos.mpr hst).ne']
        ring
      rw [he]
      exact neg_one_smul ℝ r
    rwa [heq] at h
  exact le_antisymm (neg_nonneg.mp hn) hr0

lemma quotientSpectralCut_antitone (x : selfAdjoint (T.CauchyQuotient hadd)) :
    Antitone (T.quotientSpectralCut hadd hsqrt x) := by
  intro s t hst
  rcases hst.eq_or_lt with he | hlt
  · subst t; exact le_rfl
  · let p := T.quotientSpectralCut hadd hsqrt x t
    let q := T.quotientSpectralCut hadd hsqrt x s
    have hp := T.quotientSpectralCut_spec hadd hsqrt x t
    have hq := T.quotientSpectralCut_spec hadd hsqrt x s
    have hc : Commute p q := T.quotientSpectralCuts_commute hadd hsqrt x x (Commute.refl _) t s
    have hz := T.quotient_projection_separated_corners hadd hp.1 hp.2.1 hq.1 hq.2.1 hc
      (hp.2.2.1 x.1 (Commute.refl _)) (hq.2.2.1 x.1 (Commute.refl _)) hlt hp.2.2.2.1 hq.2.2.2.2
    have hqp : q*p=p := by
      rw [mul_sub,mul_one] at hz
      exact hc.eq.symm.trans (sub_eq_zero.mp hz).symm
    have hpc : IsSelfAdjoint (1-p) := by
      change star (1-p)=1-p
      rw [star_sub,star_one,hp.1.star_eq]
    have hpc2 : (1-p)*(1-p)=1-p := by
      calc
        (1-p)*(1-p)=1-p-p+p*p := by noncomm_ring
        _ = 1-p := by rw [hp.2.1]; abel
    have hnon := Commute.mul_nonneg (T.quotient_projection_nonneg hadd hq.1 hq.2.1)
      (T.quotient_projection_nonneg hadd hpc hpc2) ((Commute.one_right q).sub_right hc.symm)
    rw [mul_sub,mul_one,hqp] at hnon
    exact sub_nonneg.mp hnon
end CuntzPureness.PositiveQuasitrace

end

end OAI
