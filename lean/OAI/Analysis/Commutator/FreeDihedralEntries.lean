import Mathlib
import OAI.Analysis.Commutator.DihedralExpectationEntries
import OAI.Analysis.Commutator.FreeHilbertEntries

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

lemma inner_scaled_operator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (α β γ : ℂ) (T : E →L[ℂ] E) (v z : E) :
    inner ℂ z ((α • (β • ContinuousLinearMap.id ℂ E+γ • T)) v)=
      α*(β*inner ℂ z v+γ*inner ℂ z (T v)) := by
  change inner ℂ z (α • (β • v+γ • T v))=_
  rw [inner_smul_right,inner_add_right,inner_smul_right,inner_smul_right]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma base_compression_of_entries
    (U V : multiplicityLevel t S true 0 →L[ℂ] t.functional.GNS)
    (L : t.functional.GNS →L[ℂ] t.functional.GNS)
    (α β γ : ℂ) (R : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0)
    (hh : ∀ v z : factorSpace t S true,
      inner ℂ (U (z : multiplicityLevel t S true 0))
        (L (V (v : multiplicityLevel t S true 0)))=
      α*(β*inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
        γ*inner ℂ (z : multiplicityLevel t S true 0) (R (v : multiplicityLevel t S true 0)))) :
    (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS) U).comp
      (L.comp V)=α • (β • ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+γ • R) := by
  apply base_operator_ext t S
  intro v z
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right
    (E := multiplicityLevel t S true 0) (F := t.functional.GNS)]
  change inner ℂ (U (z : multiplicityLevel t S true 0))
    (L (V (v : multiplicityLevel t S true 0)))=
    inner ℂ (z : Completion (factorSpace t S true))
      (α • (β • (v : Completion (factorSpace t S true))+
        γ • R (v : multiplicityLevel t S true 0)))
  rw [inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),inner_add_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),
    inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true))]
  exact hh v z

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

variable (e b : Corner hp) (he : e∈cornerFactor hp (S false) hpD)
  (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
  (hb0 : halfCornerTrace hp t.functional.toLinearMap b=0)

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_projection_coe (heproj : IsStarProjection e) : IsStarProjection (e:A) where
  isSelfAdjoint := by
    show star (e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isSelfAdjoint.star_eq
  isIdempotentElem := by
    show (e:A)*(e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isIdempotentElem.eq

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_supported (heproj : IsStarProjection e) :
    (e:A)*((e:A)*(b:A)*(e:A))*(e:A)=(e:A)*(b:A)*(e:A) := by
  have h := (corner_projection_coe hp (e := e) heproj).isIdempotentElem.eq
  calc
    _ = ((e:A)*(e:A))*(b:A)*((e:A)*(e:A)) := by simp only [mul_assoc]
    _ = _ := by rw [h]

include htr hd hs hd0 hs0 hd2 hs2 hpd he hb hb0 in
theorem dihedral_entry_pairing (heproj : IsStarProjection e)
    (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
    inner ℂ (dihedralColumn t S hfree (e:A) (d*s) c n (z : multiplicityLevel t S true 0))
      (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))
        (dihedralColumn t S hfree (e:A) (d*s) c m (v : multiplicityLevel t S true 0)))=
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)*
      (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
       t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0)
          (baseAction t S hfree (s:A) (v : multiplicityLevel t S true 0))) := by
  rw [dihedralColumn_inner t S hfree (e:A) _ (corner_projection_coe hp (e := e) heproj)
    (sandwich_supported hp (e := e) (b := b) heproj),base_inner,baseAction_inner]
  have hv : factorValue t S true v∈S true := by exact v.property
  have hz : factorValue t S true z∈S true := by exact z.property
  have hh := compression_expectation_pairing S t.functional.toLinearMap t.normalized htr
    (fun a => map_star t.functional a) hfree d s hd hs hd0 hs0 hr hd2 hs2
    hp hpform hpd hdp hpD e b he hb hb0 ((S true).mul_mem hv ((S true).star_mem' hz))
    (n:ℤ) (m:ℤ)
  have hrot : t.functional (star (factorValue t S true z)*
      (wave (d*s) (n:ℤ)*((e:A)*(b:A)*(e:A))*wave (d*s) (-(m:ℤ)))*
      factorValue t S true v)=
    t.functional ((factorValue t S true v*star (factorValue t S true z))*
      (wave (d*s) (n:ℤ)*((e:A)*(b:A)*(e:A))*wave (d*s) (-(m:ℤ)))) := by
    rw [htr]
    congr 1
    exact mul_assoc _ _ _ |>.symm
  rw [hrot]
  change (c:ℂ)^2*t.functional.toLinearMap _=_
  rw [hh]
  have hrot0 := htr (factorValue t S true v) (star (factorValue t S true z))
  have hrot1 : t.functional (factorValue t S true v*star (factorValue t S true z)*(s:A))=
      t.functional (star (factorValue t S true z)*(s:A)*factorValue t S true v) := by
    rw [mul_assoc,htr]
  change (c:ℂ)^2*(t.functional _*_ * t.functional _ +t.functional _*_ * t.functional _)=_
  rw [hrot0,hrot1]
  ring

include htr hd hs hd0 hs0 hd2 hs2 hpd he hb hb0 in
theorem dihedral_entry_operator (heproj : IsStarProjection e)
    (c : ℝ) (n m : ℕ) :
    (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
      (dihedralColumn t S hfree (e:A) (d*s) c n)).comp
      ((t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))).comp
        (dihedralColumn t S hfree (e:A) (d*s) c m))=
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2) •
      (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A)) •
          ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+
       t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A)) • baseAction t S hfree (s:A)) := by
  exact base_compression_of_entries t S
    (dihedralColumn t S hfree (e:A) (d*s) c n)
    (dihedralColumn t S hfree (e:A) (d*s) c m)
    (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A)))
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)
    (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A)))
    (t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A)))
    (baseAction t S hfree (s:A))
    (dihedral_entry_pairing t S hfree htr d s hd hs hd0 hs0 hr hd2 hs2
      hp hpform hpd hdp hpD e b he hb hb0 heproj c n m)

end Kadison.FreeBlocks

end

end
end

end OAI
