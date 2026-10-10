import Mathlib
import OAI.Analysis.Commutator.FreeCompressionNorm
import OAI.Analysis.Commutator.HankelAlgebra
import OAI.Analysis.Commutator.DihedralFejer

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include hd0 hpform in
lemma half_projection_trace : t.functional p=((1/2:ℝ):ℂ) := by
  rw [hpform,map_smul,map_add,t.normalized,hd0,add_zero,smul_eq_mul,mul_one]
  norm_num

def halfCornerState (hpt : t.functional p=((1/2:ℝ):ℂ)) : FaithfulState (Corner hp) where
  functional := cornerFunctional hp t.functional (1/2) (by norm_num)
  normalized := cornerFunctional_normalized hp t.functional (by norm_num) hpt
  faithful := cornerFunctional_faithful hp t.functional (by norm_num) t.faithful

lemma halfCornerState_linear (hpt : t.functional p=((1/2:ℝ):ℂ)) :
    (halfCornerState t hp hpt).functional.toLinearMap=halfCornerTrace hp t.functional.toLinearMap := by
  ext a
  change (1/2:ℝ)⁻¹ • t.functional (a:A)=2*t.functional (a:A)
  norm_num [Complex.real_smul]

include hfree htr hd hs hd0 hs0 hr hd2 hpform hpd hdp in
theorem free_fejer_norm (e : Corner hp) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m) :
    ‖(e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A)‖≤
      4*Real.sqrt 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        Real.sqrt ((m:ℝ)⁻¹)+2*(halfCornerTrace hp t.functional.toLinearMap e).re := by
  let tc := halfCornerState t hp (half_projection_trace t d hd0 hpform)
  let R := cornerPairFactors (S:=S) d s false hr hp hpform hdp hpD
  have hR : Free R tc.functional.toLinearMap := by
    rw [halfCornerState_linear]
    exact corner_cosine_free t.functional.toLinearMap t.normalized htr
      (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD
  have heR : e∈R false := he
  have hbR : fejerCorner hp (d*s) m∈R true := fejerCorner_mem hp (d*s) d hr hpform hdp m
  have hb0 : tc.functional (fejerCorner hp (d*s) m)=0 := by
    change tc.functional.toLinearMap (fejerCorner hp (d*s) m)=0
    rw [halfCornerState_linear]
    exact fejerCorner_centered hp t.functional S t.normalized htr
      (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hpform m hm
  have hn := FreeCreation.free_compression_norm_intrinsic tc R hR Bool.false_ne_true
    heproj heR (fejerCorner_selfAdjoint hp (d*s) m) hbR hb0
  have htce : tc.functional e = halfCornerTrace hp t.functional.toLinearMap e :=
    congrArg (fun f : Corner hp →ₗ[ℂ] ℂ => f e) (halfCornerState_linear t hp _)
  rw [htce] at hn
  have hu : 0≤(halfCornerTrace hp t.functional.toLinearMap e).re := by
    rw [←htce,←FreeCreation.norm_preGNS_projection_sq tc heproj]
    positivity
  have hb2 := fejerCorner_preGNS_norm hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hr hpform m hm
  have hbnorm := fejerCorner_norm_le hp (d*s) m hm
  change ‖e*fejerCorner hp (d*s) m*e‖≤_
  calc
    _ ≤ 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        ‖tc.functional.toPreGNS (fejerCorner hp (d*s) m)‖+
        (halfCornerTrace hp t.functional.toLinearMap e).re*‖fejerCorner hp (d*s) m‖ := hn
    _ ≤ 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        (2*Real.sqrt 2*Real.sqrt ((m:ℝ)⁻¹))+
        (halfCornerTrace hp t.functional.toLinearMap e).re*2 :=
      add_le_add (mul_le_mul_of_nonneg_left hb2 (by positivity))
        (mul_le_mul_of_nonneg_left hbnorm hu)
    _ = _ := by ring

lemma fejer_numeric_bound (u : ℝ) (m : ℕ) (hm : 0 < m) (hsize : 8≤(m:ℝ)*u) :
    4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹)+2*u≤4*u := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hu : 0<u := (mul_pos_iff_of_pos_left hm').mp (lt_of_lt_of_le (by norm_num) hsize)
  have hi : 0≤(m:ℝ)⁻¹ := inv_nonneg.mpr hm'.le
  have hiu : 8*(m:ℝ)⁻¹ ≤ u := by
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ hm').2 (by simpa only [mul_comm] using hsize)
  have sq2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have squ := Real.sq_sqrt hu.le
  have sqi := Real.sq_sqrt hi
  have hs0 : 0≤4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹) := by positivity
  have hsq : (4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹))^2≤(2*u)^2 := by
    calc
      _ = 32*u*(m:ℝ)⁻¹ := by rw [mul_pow,mul_pow,mul_pow,sq2,squ,sqi]; ring
      _ ≤ (2*u)^2 := by nlinarith [mul_le_mul_of_nonneg_left hiu hu.le]
  have hs : 4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹)≤2*u :=
    (sq_le_sq₀ hs0 (by positivity)).mp hsq
  linarith

include hfree htr hd hs hd0 hs0 hr hd2 hpform hpd hdp in
theorem free_fejer_gns_norm (e : Corner hp) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m)
    (hsize : 8≤(m:ℝ)*(halfCornerTrace hp t.functional.toLinearMap e).re) :
    ‖t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A))‖≤
      4*(halfCornerTrace hp t.functional.toLinearMap e).re := by
  rw [FreeCreation.norm_gns]
  exact (free_fejer_norm t S hfree htr d s hd hs hd0 hs0 hr hd2
    hp hpform hpd hdp hpD e heproj he m hm).trans (fejer_numeric_bound _ m hm hsize)

end Kadison.FreeBlocks

end

end
end

end OAI
