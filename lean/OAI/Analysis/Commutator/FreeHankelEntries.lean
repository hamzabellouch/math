import Mathlib
import OAI.Analysis.Commutator.DihedralFejer
import OAI.Analysis.Commutator.FreeDihedralEntries
import OAI.Analysis.Commutator.FreeSymmetry14

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

lemma two_scaled_sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    (u a b c : ℂ) (x y : M) (hc : 2*b=c) :
    (2*u) • (a • x+b • y)=u • ((2*a) • x+c • y) := by
  rw [←hc]
  module

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {p : A} (hp : IsStarProjection p)

lemma projection_factor_trace (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    t.functional (e:A)=((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  have hn := (factorTrace t f hf).preGNS_norm_sq ((factorTrace t f hf).toPreGNS e0)
  have he := corner_projection_coe hp (e:=e) heproj
  symm
  simpa only [TracialGNS.algebraVector_apply,Completion.norm_coe,
    Complex.ofReal_pow,PositiveLinearMap.ofPreGNS_toPreGNS,pullbackState_apply,
    map_mul,map_star,heq,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq] using hn

lemma halfCornerTrace_normalization (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    halfCornerTrace hp t.functional.toLinearMap e=
      ((2*‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  rw [halfCornerTrace_apply,PositiveLinearMap.coe_toLinearMap,
    projection_factor_trace t f hf hp e0 e heq heproj]
  push_cast
  rfl

lemma halfCornerTrace_normalization_re (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    (halfCornerTrace hp t.functional.toLinearMap e).re=
      2*‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2 := by
  rw [halfCornerTrace_normalization t f hf hp e0 e heq heproj,Complex.ofReal_re]

lemma normalized_dihedral_scalar (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖) :
    (((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹:ℝ):ℂ)^2 *
      (halfCornerTrace hp t.functional.toLinearMap e)^2)=
      2*((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) := by
  rw [halfCornerTrace_normalization t f hf hp e0 e heq heproj,Complex.ofReal_re]
  have hn : (‖TracialGNS.algebraVector (factorTrace t f hf) e0‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast
  field_simp

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include hfree htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp in
theorem finite_fejer_entry (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    ((ContinuousLinearMap.adjoint (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (dihedralColumn t S hfree (e:A) (d*s)
      ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ i.val)).comp
      (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
      (dihedralColumn t S hfree (e:A) (d*s)
        ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ j.val)=
    ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
      ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
        ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
          ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+
       (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A)) := by
  have hm : 0 < 2*N := by omega
  have hb := fejerCorner_mem hp (d*s) d hrot hpform hdp (2*N)
  have hb0 := fejerCorner_centered hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hrot hd2 hpform (2*N) hm
  have hentry := dihedral_entry_operator t S hfree htr d s hd hs hd0 hs0 hrot hd2 hs2
    hp hpform hpd hdp hpD e (fejerCorner hp (d*s) (2*N)) he hb hb0 heproj
    ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ i.val j.val
  rw [normalized_dihedral_scalar t f hf hp e0 e heq heproj hr] at hentry
  have hcoef := fejerCorner_positive_coefficient hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hrot hd2 hpform (2*N) (i.val+j.val+1) hm (by omega) (by omega)
  have hcoef' : 2*t.functional (wave (d*s) ((i.val:ℤ)+j.val+1)*
      ((fejerCorner hp (d*s) (2*N):Corner hp):A))=
      Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_ofNat,Complex.ofReal_natCast,Complex.ofReal_one,
      sub_add_eq_sub_sub] using hcoef
  rw [ContinuousLinearMap.comp_assoc,hentry]
  exact two_scaled_sum
    (M:=Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))
    _ _ _ _ _ _ hcoef'

end Kadison.FreeBlocks

end

end
end

end OAI
