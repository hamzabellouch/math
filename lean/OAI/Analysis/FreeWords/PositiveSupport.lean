import Mathlib
import OAI.Analysis.FreeWords.SupportProjections

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

theorem positive_sqrt_square {a : ConcreteAlgebra M} (ha : 0 ≤ a) :
    cfc Real.sqrt a * cfc Real.sqrt a = a := by
  rw [← sq,← cfc_pow Real.sqrt 2 a Real.continuous_sqrt.continuousOn (IsSelfAdjoint.of_nonneg ha)]
  calc
    cfc (fun t : ℝ => Real.sqrt t^2) a = cfc (fun t : ℝ => t) a := by
      apply cfc_congr
      intro t ht
      exact Real.sq_sqrt (spectrum_nonneg_of_nonneg ha ht)
    _ = a := cfc_id' ℝ _ (IsSelfAdjoint.of_nonneg ha)

theorem positive_annihilate {a p : ConcreteAlgebra M} (ha : 0 ≤ a)
    (hp : IsSelfAdjoint p) (h : p*a*p=0) : a*p=0 := by
  let s := cfc Real.sqrt a
  have hs : IsSelfAdjoint s := IsSelfAdjoint.cfc
  have hss : s*s=a := positive_sqrt_square ha
  have he : star (s*p)*(s*p)=0 := by
    rw [star_mul,hp.star_eq,hs.star_eq]
    calc p*s*(s*p)=p*(s*s)*p := by simp only [mul_assoc]
         _ = 0 := by rw [hss,h]
  have hn : ‖s*p‖^2=0 := by rw [pow_two,← CStarRing.norm_star_mul_self,he,norm_zero]
  have hsp : s*p=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  rw [← hss,mul_assoc,hsp,mul_zero]

theorem supportProjection_mono {a b : ConcreteAlgebra M} (ha : 0 ≤ a) (hab : a ≤ b) :
    supportProjection a ≤ supportProjection b := by
  have hb : 0 ≤ b := ha.trans hab
  let q := 1-supportProjection b
  have hq : IsStarProjection q := (supportProjection_isProjection b).one_sub
  have hbq : b*q=0 := by
    dsimp [q]
    rw [mul_sub,mul_one,mul_supportProjection (IsSelfAdjoint.of_nonneg hb),sub_self]
  have hle : q*a*q ≤ 0 := by
    have hh := star_left_conjugate_le_conjugate hab q
    rw [hq.isSelfAdjoint.star_eq,mul_assoc q b,hbq,mul_zero] at hh
    exact hh
  have heq : q*a*q=0 := le_antisymm hle (hq.isSelfAdjoint.conjugate_nonneg ha)
  have haq := positive_annihilate ha hq.isSelfAdjoint heq
  have hap : a*supportProjection b=a := by
    dsimp [q] at haq
    rw [mul_sub,mul_one] at haq
    exact (sub_eq_zero.mp haq).symm
  have hpa : supportProjection b*a=a := by
    simpa only [star_mul,(supportProjection_isProjection b).isSelfAdjoint.star_eq,
      (IsSelfAdjoint.of_nonneg ha).star_eq] using congrArg star hap
  exact supportProjection_le (supportProjection_isProjection b) hpa

def positiveCut (a : ConcreteAlgebra M) (t : ℝ) : ConcreteAlgebra M := cfc (fun x : ℝ => max (x-t) 0) a

def negativeCut (a : ConcreteAlgebra M) (t : ℝ) : ConcreteAlgebra M := cfc (fun x : ℝ => max (t-x) 0) a

def spectralCut (a : ConcreteAlgebra M) (t : ℝ) : ConcreteAlgebra M := supportProjection (positiveCut a t)

theorem positiveCut_nonneg (a : ConcreteAlgebra M) (t : ℝ) : 0 ≤ positiveCut a t :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

theorem negativeCut_nonneg (a : ConcreteAlgebra M) (t : ℝ) : 0 ≤ negativeCut a t :=
  cfc_nonneg (fun _ _ => le_max_right _ _)

theorem spectralCut_isProjection (a : ConcreteAlgebra M) (t : ℝ) : IsStarProjection (spectralCut a t) :=
  supportProjection_isProjection _

theorem cuts_difference (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (t : ℝ) :
    positiveCut a t-negativeCut a t=a-algebraMap ℝ (ConcreteAlgebra M) t := by
  calc
    _ = cfc (fun x : ℝ => max (x-t) 0 - max (t-x) 0) a := by
      exact (cfc_sub (fun x : ℝ => max (x-t) 0) (fun x : ℝ => max (t-x) 0) a).symm
    _ = cfc (fun x : ℝ => x-t) a := by
      apply cfc_congr
      intro x hx
      change max (x-t) 0-max (t-x) 0=x-t
      by_cases h : t ≤ x
      · simp only [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h),sub_zero]
      · have h' := le_of_not_ge h
        simp only [max_eq_right (sub_nonpos.mpr h'),max_eq_left (sub_nonneg.mpr h'),zero_sub]
        ring
    _ = _ := by rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => t) a,cfc_id' ℝ a ha,cfc_const t a ha]

theorem cuts_product (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (t : ℝ) :
    negativeCut a t*positiveCut a t=0 := by
  rw [negativeCut,positiveCut,← cfc_mul (fun x : ℝ => max (t-x) 0) (fun x : ℝ => max (x-t) 0) a]
  calc
    cfc (fun x : ℝ => max (t-x) 0*max (x-t) 0) a=cfc (fun _ : ℝ => 0) a := by
      apply cfc_congr
      intro x hx
      change max (t-x) 0*max (x-t) 0=0
      by_cases ht : t ≤ x
      · rw [max_eq_right (sub_nonpos.mpr ht),zero_mul]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge ht)),mul_zero]
    _ = 0 := by rw [cfc_const 0 a ha,map_zero]

theorem spectralCut_commute (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (t : ℝ) :
    Commute a (spectralCut a t) := by
  apply supportProjection_commute (IsSelfAdjoint.of_nonneg (positiveCut_nonneg a t))
  change Commute a (cfc (fun x : ℝ => max (x-t) 0) a)
  exact ((Commute.refl a).cfc (by simpa only [ha.star_eq] using Commute.refl a) _).symm

theorem spectralCut_compression (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (t : ℝ) :
    (a-algebraMap ℝ (ConcreteAlgebra M) t)*spectralCut a t=positiveCut a t := by
  rw [← cuts_difference a ha t,sub_mul,spectralCut,mul_supportProjection (IsSelfAdjoint.of_nonneg (positiveCut_nonneg a t)),
    annihilate_supportProjection (cuts_product a ha t),sub_zero]

theorem spectralCut_complement (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (t : ℝ) :
    (a-algebraMap ℝ (ConcreteAlgebra M) t)*(1-spectralCut a t)=-negativeCut a t := by
  rw [mul_sub,mul_one,spectralCut_compression a ha t,← cuts_difference a ha t]
  abel

theorem spectralCut_antitone (a : ConcreteAlgebra M) : Antitone (spectralCut a) := by
  intro s t hst
  apply supportProjection_mono (positiveCut_nonneg a t)
  exact cfc_mono (fun x hx => max_le_max (sub_le_sub_left hst x) le_rfl)

end

end KKSpectralSupport
end

end OAI
