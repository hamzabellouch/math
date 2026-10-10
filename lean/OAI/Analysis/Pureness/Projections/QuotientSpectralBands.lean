import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSpectralProducts

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def quotientSpectralBand (x : selfAdjoint (T.CauchyQuotient hadd)) (s t : ℝ) :=
  T.quotientSpectralCut hadd hsqrt x s - T.quotientSpectralCut hadd hsqrt x t

lemma quotientSpectralBand_spec (x : selfAdjoint (T.CauchyQuotient hadd)) {s t : ℝ} (hst : s ≤ t) :
    IsSelfAdjoint (T.quotientSpectralBand hadd hsqrt x s t) ∧
    T.quotientSpectralBand hadd hsqrt x s t*T.quotientSpectralBand hadd hsqrt x s t =
      T.quotientSpectralBand hadd hsqrt x s t ∧
    0 ≤ T.quotientSpectralBand hadd hsqrt x s t ∧
    (∀ y, Commute x.1 y → Commute (T.quotientSpectralBand hadd hsqrt x s t) y) := by
  have hp := T.quotientSpectralCut_spec hadd hsqrt x s
  have hq := T.quotientSpectralCut_spec hadd hsqrt x t
  refine ⟨hp.1.sub hq.1, ?_, sub_nonneg.mpr (T.quotientSpectralCut_antitone hadd hsqrt x hst), ?_⟩
  · dsimp [quotientSpectralBand]
    rw [sub_mul,mul_sub,mul_sub,hp.2.1,hq.2.1,
      T.quotientSpectralCut_mul,T.quotientSpectralCut_mul,max_eq_right hst,max_eq_left hst]
    abel
  · intro y hy
    exact (hp.2.2.1 y hy).sub_left (hq.2.2.1 y hy)

lemma quotientSpectralBand_orthogonal (x : selfAdjoint (T.CauchyQuotient hadd))
    {s t u v : ℝ} (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    T.quotientSpectralBand hadd hsqrt x s t*T.quotientSpectralBand hadd hsqrt x u v=0 := by
  dsimp [quotientSpectralBand]
  rw [sub_mul,mul_sub,mul_sub]
  simp only [T.quotientSpectralCut_mul,max_eq_right (hst.trans htu),
    max_eq_right (hst.trans (htu.trans huv)),max_eq_right htu,max_eq_right (htu.trans huv)]
  abel

lemma quotientSpectralBands_commute (x y : selfAdjoint (T.CauchyQuotient hadd))
    (hxy : Commute x.1 y.1) (s t u v : ℝ) :
    Commute (T.quotientSpectralBand hadd hsqrt x s t) (T.quotientSpectralBand hadd hsqrt y u v) := by
  apply Commute.sub_left <;> apply Commute.sub_right <;>
    exact T.quotientSpectralCuts_commute hadd hsqrt x y hxy _ _

lemma quotientSpectralBand_bounds (x : selfAdjoint (T.CauchyQuotient hadd)) {s t : ℝ} (hst : s ≤ t) :
    s • T.quotientSpectralBand hadd hsqrt x s t ≤ T.quotientSpectralBand hadd hsqrt x s t*x.1 ∧
    T.quotientSpectralBand hadd hsqrt x s t*x.1 ≤ t • T.quotientSpectralBand hadd hsqrt x s t := by
  let p := T.quotientSpectralCut hadd hsqrt x s
  let q := T.quotientSpectralCut hadd hsqrt x t
  let e := T.quotientSpectralBand hadd hsqrt x s t
  have hp := T.quotientSpectralCut_spec hadd hsqrt x s
  have hq := T.quotientSpectralCut_spec hadd hsqrt x t
  have he := T.quotientSpectralBand_spec hadd hsqrt x hst
  have hep : e*p=e := by
    dsimp [e,quotientSpectralBand,p]
    rw [sub_mul,hp.2.1,T.quotientSpectralCut_mul,max_eq_left hst]
  have heq : e*(1-q)=e := by
    dsimp [e,quotientSpectralBand,q]
    rw [mul_sub,mul_one,sub_mul,T.quotientSpectralCut_mul,max_eq_right hst,hq.2.1,sub_self,sub_zero]
  have hcp : Commute e p := he.2.2.2 p (hp.2.2.1 x.1 (Commute.refl _)).symm
  have hcq : Commute e (1-q) := (Commute.one_right _).sub_right (he.2.2.2 q (hq.2.2.1 x.1 (Commute.refl _)).symm)
  have hcx : Commute e x.1 := he.2.2.2 x.1 (Commute.refl _)
  constructor
  · have h := Commute.mul_nonneg he.2.2.1 (sub_nonneg.mpr hp.2.2.2.1)
      ((hcp.mul_right hcx).sub_right (hcp.smul_right s))
    change 0 ≤ e*(p*x.1-s • p) at h
    rw [mul_sub,←mul_assoc,mul_smul_comm,hep] at h
    exact sub_nonneg.mp h
  · have h := Commute.mul_nonneg he.2.2.1 (sub_nonneg.mpr hq.2.2.2.2)
      ((hcq.smul_right t).sub_right (hcq.mul_right hcx))
    change 0 ≤ e*(t • (1-q)-(1-q)*x.1) at h
    rw [mul_sub,mul_smul_comm,←mul_assoc,heq] at h
    exact sub_nonneg.mp h
end CuntzPureness.PositiveQuasitrace

end

end OAI
