import Mathlib
import OAI.Analysis.Commutator.AlgebraFreeExpectation
import OAI.Analysis.Commutator.HankelAlgebra

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include htr in
lemma corner_wave_pairing (u : unitary A) (n : ℤ) (b : Corner hp) :
    halfCornerTrace hp τ (cosine u hp n*b)=2*τ (wave u n*(b:A)) := by
  rw [halfCornerTrace_apply,corner_mul,cosine_coe]
  congr 1
  calc
    τ ((p*wave u n*p)*(b:A)) = τ (p*(wave u n*(b:A))) := by
      simp only [mul_assoc,b.property.1]
    _ = τ ((wave u n*(b:A))*p) := htr _ _
    _ = τ (wave u n*(b:A)) := by rw [mul_assoc,b.property.2]

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
theorem free_compression_wave_pairing (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (n : ℤ) :
    τ (wave (d*s) n*((e:A)*(b:A)*(e:A)))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) n*(b:A)) := by
  let R := cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD
  have hR := corner_cosine_free τ h1 htr hstar hfree d s i j hij hd hs hd0 hs0
    hr hd2 hp hpform hpd hdp hpD
  have hn : cosine (d*s) hp n∈R true := cosine_mem (d*s) hp n
  have hz := AlgebraFreeExpectation.free_compression_pairing (halfCornerTrace hp τ)
    (halfCornerTrace_one τ h1 d hd0 hp hpform) R hR Bool.false_ne_true he hb hn hb0
  rw [corner_wave_pairing τ htr hp,corner_wave_pairing τ htr hp] at hz
  change 2*τ (wave (d*s) n*((e:A)*(b:A)*(e:A)))=
    (halfCornerTrace hp τ e)^2*(2*τ (wave (d*s) n*(b:A))) at hz
  linear_combination (1/2:ℂ)*hz

include hdp in
lemma reflection_corner (x : Corner hp) : (d:A)*(x:A)=(x:A) := by
  calc
    (d:A)*(x:A) = (d:A)*(p*(x:A)) := by rw [x.property.1]
    _ = (d:A)*p*(x:A) := (mul_assoc _ _ _).symm
    _ = (x:A) := by rw [hdp,x.property.1]

include htr in
lemma rotation_sandwich_trace (u : unitary A) (x : A) (a b : ℤ) :
    τ (wave u a*x*wave u (-b))=τ (wave u (a-b)*x) := by
  rw [htr,←mul_assoc,←wave_add]
  congr 2
  congr 1
  omega

include hd2 in
lemma symmetry_wave_product (a : ℤ) : (s:A)*wave (d*s) a=
    (d:A)*wave (d*s) (a+1) := by
  have hw : wave (d*s) (a+1)=((d:A)*(s:A))*wave (d*s) a := by
    rw [add_comm a 1,wave_add]
    simp only [wave,zpow_one,Submonoid.coe_mul]
  rw [hw,←mul_assoc,←mul_assoc,hd2,one_mul]

include htr hr hd2 hdp in
lemma symmetry_sandwich_trace (x : Corner hp) (a b : ℤ) :
    τ ((s:A)*(wave (d*s) a*(x:A)*wave (d*s) (-b)))=
      τ (wave (d*s) (-(a+b+1))*(x:A)) := by
  calc
    _ = τ (wave (d*s) (-b)*((s:A)*wave (d*s) a)*(x:A)) := by
      rw [←mul_assoc (s:A),htr]
      simp only [mul_assoc]
    _ = τ (wave (d*s) (-b)*((d:A)*wave (d*s) (a+1))*(x:A)) := by
      rw [symmetry_wave_product d s hd2]
    _ = τ (wave (d*s) (-b)*(wave (d*s) (-(a+1))*(d:A))*(x:A)) := by
      rw [reflection_wave (d*s) d hr]
    _ = τ ((wave (d*s) (-b)*wave (d*s) (-(a+1)))*((d:A)*(x:A))) := by
      simp only [mul_assoc]
    _ = τ (wave (d*s) (-b+-(a+1))*(x:A)) := by
      rw [reflection_corner d hp hdp,←wave_add]
    _ = _ := by congr 2; congr 1; omega

include htr hr hpd hdp in
lemma wave_corner_even (x : Corner hp) (n : ℤ) :
    τ (wave (d*s) (-n)*(x:A))=τ (wave (d*s) n*(x:A)) := by
  have h := congrArg (fun z : Corner hp => halfCornerTrace hp τ (z*x))
    (cosine_neg (d*s) d hr hp hpd hdp n)
  rw [corner_wave_pairing τ htr hp,corner_wave_pairing τ htr hp] at h
  linear_combination (1/2:ℂ)*h

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
lemma compression_rotation_sandwich (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (a c : ℤ) :
    τ (wave (d*s) a*((e:A)*(b:A)*(e:A))*wave (d*s) (-c))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) (a-c)*(b:A)) := by
  rw [rotation_sandwich_trace τ htr]
  exact free_compression_wave_pairing τ h1 htr hstar hfree d s i j hij hd hs hd0 hs0
    hr hd2 hp hpform hpd hdp hpD e b he hb hb0 (a-c)

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
lemma compression_symmetry_sandwich (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (a c : ℤ) :
    τ ((s:A)*(wave (d*s) a*((e:A)*(b:A)*(e:A))*wave (d*s) (-c)))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) (a+c+1)*(b:A)) := by
  change τ ((s:A)*(wave (d*s) a*((e*b*e:Corner hp):A)*wave (d*s) (-c)))=_
  rw [symmetry_sandwich_trace τ htr d s hr hd2 hp hdp]
  simp only [corner_mul]
  rw [free_compression_wave_pairing τ h1 htr hstar hfree d s i j hij hd hs hd0 hs0
    hr hd2 hp hpform hpd hdp hpD e b he hb hb0]
  rw [wave_corner_even τ htr d s hr hp hpd hdp]

end Kadison.DihedralCorner

end

end
end

end OAI
