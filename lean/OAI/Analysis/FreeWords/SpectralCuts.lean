import Mathlib
import OAI.Analysis.FreeWords.PositiveSupport

namespace OAI

noncomputable section

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H}

end

end KKSpectralSupport

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H}

end

end KKSpectralSupport

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H}

theorem supportProjection_of_isUnit {a : ConcreteAlgebra M} (ha : IsUnit a) :
    supportProjection a=1 := by
  obtain ⟨u,rfl⟩ := ha
  have h := congrArg (fun x : ConcreteAlgebra M => x*↑u⁻¹) (supportProjection_mul (u : ConcreteAlgebra M))
  simpa only [mul_assoc,Units.mul_inv, mul_one] using h

theorem spectralCut_eq_one (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) {t : ℝ}
    (ht : t < -‖a‖) : spectralCut a t=1 := by
  rcases subsingleton_or_nontrivial (ConcreteAlgebra M) with h | h
  · exact Subsingleton.elim _ _
  apply supportProjection_of_isUnit
  apply (isUnit_cfc_iff (fun x : ℝ => max (x-t) 0) a (by fun_prop) ha).mpr
  intro x hx
  have hb : -‖a‖ ≤ x := by
    have hh := spectrum.norm_le_norm_of_mem hx
    exact (neg_le_neg hh).trans (neg_abs_le x)
  exact ne_of_gt ((sub_pos.mpr (ht.trans_le hb)).trans_le (le_max_left _ _))

theorem spectralCut_eq_zero (a : ConcreteAlgebra M) {t : ℝ} (ht : ‖a‖ ≤ t) :
    spectralCut a t=0 := by
  rcases subsingleton_or_nontrivial (ConcreteAlgebra M) with h | h
  · exact Subsingleton.elim _ _
  have he : positiveCut a t=0 := by
    change cfc (fun x : ℝ => max (x-t) 0) a=0
    calc
      _ = cfc (fun _ : ℝ => 0) a := by
        apply cfc_congr
        intro x hx
        exact max_eq_right (sub_nonpos.mpr ((Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans ht)))
      _ = 0 := cfc_const_zero ℝ a
  rw [spectralCut,he,supportProjection_zero]

theorem spectralCut_commute_of_commute {a b : ConcreteAlgebra M}
    (_ : IsSelfAdjoint a) (hba : Commute b a) (t : ℝ) : Commute b (spectralCut a t) := by
  apply supportProjection_commute (IsSelfAdjoint.of_nonneg (positiveCut_nonneg a t))
  exact (hba.symm.cfc_real _).symm

theorem projection_restrict_nonneg {b p d : ConcreteAlgebra M}
    (hp : IsStarProjection p) (hd : IsStarProjection d) (hdp : d ≤ p)
    (hbd : Commute b d) (hpos : 0 ≤ b*p) : 0 ≤ b*d := by
  have h := hd.isSelfAdjoint.conjugate_nonneg hpos
  have he : d*(b*p)*d=b*d := by
    calc
      d*(b*p)*d=(d*b)*(p*d) := by simp only [mul_assoc]
      _ = (b*d)*d := by rw [← hbd.eq,(hd.le_iff_mul_eq_right hp).mp hdp]
      _ = b*d := by rw [mul_assoc,hd.isIdempotentElem.eq]
  rwa [he] at h

def spectralBand (a : ConcreteAlgebra M) (s t : ℝ) : ConcreteAlgebra M :=
  spectralCut a s-spectralCut a t

theorem spectralBand_isProjection (a : ConcreteAlgebra M) {s t : ℝ} (hst : s ≤ t) :
    IsStarProjection (spectralBand a s t) :=
  ((spectralCut_isProjection a t).le_iff_sub (spectralCut_isProjection a s)).mp (spectralCut_antitone a hst)

theorem spectralBand_commute (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (s t : ℝ) :
    Commute a (spectralBand a s t) := (spectralCut_commute a ha s).sub_right (spectralCut_commute a ha t)

theorem spectralBand_lower (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ (a-algebraMap ℝ (ConcreteAlgebra M) s)*spectralBand a s t := by
  apply projection_restrict_nonneg (spectralCut_isProjection a s) (spectralBand_isProjection a hst)
  · exact sub_le_self _ (spectralCut_isProjection a t).nonneg
  · exact (spectralBand_commute a ha s t).sub_left (Algebra.commutes _ _)
  · rw [spectralCut_compression a ha s]
    exact positiveCut_nonneg a s

theorem spectralBand_upper (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ (algebraMap ℝ (ConcreteAlgebra M) t-a)*spectralBand a s t := by
  have hd := spectralBand_isProjection a hst
  have htd : spectralCut a t*spectralBand a s t=0 := by
    rw [spectralBand,mul_sub,((spectralCut_isProjection a t).le_iff_mul_eq_left
      (spectralCut_isProjection a s)).mp (spectralCut_antitone a hst),
      (spectralCut_isProjection a t).isIdempotentElem.eq,sub_self]
  have hdle : spectralBand a s t ≤ 1-spectralCut a t :=
    (hd.le_iff_mul_eq_right (spectralCut_isProjection a t).one_sub).mpr (by rw [sub_mul,one_mul,htd,sub_zero])
  apply projection_restrict_nonneg (spectralCut_isProjection a t).one_sub hd hdle
  · exact (show Commute (algebraMap ℝ (ConcreteAlgebra M) t) (spectralBand a s t) from Algebra.commutes _ _).sub_left (spectralBand_commute a ha s t)
  · rw [← neg_sub a,neg_mul,spectralCut_complement a ha t,neg_neg]
    exact negativeCut_nonneg a t

end

end KKSpectralSupport
end

end OAI
