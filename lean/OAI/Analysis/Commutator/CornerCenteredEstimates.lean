import Mathlib
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

open TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

def cornerScalar (p b : A) : ℂ := τ (p*b)/τ p

def cornerCenter (p b : A) : A := p*b*p-cornerScalar τ p b • p

lemma projection_trace_real {p : A} (hp : IsStarProjection p) : τ p=((τ p).re:ℂ) := by
  apply Complex.ext
  · rfl
  have h := (τ.map_nonneg hp.nonneg).2
  simpa only [Complex.zero_im,Complex.ofReal_im] using h.symm

lemma projection_trace_norm {p : A} (hp : IsStarProjection p) : ‖τ p‖=(τ p).re := by
  calc
    _=‖((τ p).re:ℂ)‖ := congrArg (fun z : ℂ => ‖z‖) (projection_trace_real τ hp)
    _=(τ p).re := by
      rw [Complex.norm_real,Real.norm_of_nonneg (τ.map_nonneg hp.nonneg).1]

omit [StarOrderedRing A] in
lemma cornerCenter_left {p : A} (hp : IsStarProjection p) (b : A) :
    p*cornerCenter τ p b=cornerCenter τ p b := by
  simp only [cornerCenter,mul_sub,mul_smul_comm,←mul_assoc,hp.isIdempotentElem.eq]

omit [StarOrderedRing A] in
lemma cornerCenter_right {p : A} (hp : IsStarProjection p) (b : A) :
    cornerCenter τ p b*p=cornerCenter τ p b := by
  simp only [cornerCenter,sub_mul,smul_mul_assoc,mul_assoc,hp.isIdempotentElem.eq]

include hτ in
omit [StarOrderedRing A] in
lemma cornerCenter_trace {p : A} (hp : IsStarProjection p) (ht : 0<(τ p).re) (b : A) :
    τ (cornerCenter τ p b)=0 := by
  have ht0 : τ p≠0 := fun h => by rw [h,Complex.zero_re] at ht; exact lt_irrefl _ ht
  have he : τ (p*b*p)=τ (p*b) := by rw [hτ (p*b),←mul_assoc,hp.isIdempotentElem.eq]
  simp only [cornerCenter,map_sub,map_smul,smul_eq_mul,cornerScalar,he]
  rw [div_mul_cancel₀ _ ht0,sub_self]

lemma compress_center {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) :
    q*b*q=q*cornerCenter τ p b*q+cornerScalar τ p b • q := by
  have h1 := (hq.le_iff_mul_eq_left hp).mp hqp
  have h2 := (hq.le_iff_mul_eq_right hp).mp hqp
  simp only [cornerCenter,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  have h3 : q*(p*b*p)*q=q*b*q := by
    calc
      _=(q*p)*b*(p*q) := by noncomm_ring
      _=_ := by rw [h1,h2]
  rw [h3,h1,hq.isIdempotentElem.eq,sub_add_cancel]

lemma compressed_bound {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) (b : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    norm τ (q*b*q)*norm τ q ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  have hsmall' : norm τ (q*cornerCenter τ p b*q) ≤ δ*norm τ q := by
    apply (sq_le_sq₀ (norm_nonneg τ _) (mul_nonneg hδ (norm_nonneg τ _))).mp
    rw [mul_pow,norm_projection_sq τ hq]
    exact hsmall
  have hh : norm τ (q*b*q) ≤ (δ+‖cornerScalar τ p b‖)*norm τ q := by
    rw [compress_center τ hp hq hqp b]
    calc
      _ ≤ norm τ (q*cornerCenter τ p b*q)+norm τ (cornerScalar τ p b • q) :=
        norm_add τ _ _
      _ ≤ δ*norm τ q+‖cornerScalar τ p b‖*norm τ q := by
        rw [TracialL2.norm_smul]
        exact add_le_add hsmall' le_rfl
      _=_ := by ring
  calc
    _ ≤ ((δ+‖cornerScalar τ p b‖)*norm τ q)*norm τ q :=
      mul_le_mul_of_nonneg_right hh (norm_nonneg τ _)
    _ = (δ+‖cornerScalar τ p b‖)*(norm τ q)^2 := by ring
    _ = _ := by rw [norm_projection_sq τ hq]

include hτ in
lemma trace_centered_compression_bound {p q b a c w z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p)
    (hw : w*q=w) (hz : q*z=z)
    (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hwn : ‖w‖ ≤ 1) (hzn : ‖z‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    ‖τ (a*w*b*z*c)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re :=
  (trace_two_corner_letters τ hτ hq hw hz ha hc hwn hzn).trans
    (compressed_bound τ hp hq hqp b hδ hsmall)

include hτ in
lemma trace_single_support_bound {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) (b : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    ‖τ (q*b)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  have he : τ (q*b)=τ ((q*b*q)*q) := by
    rw [mul_assoc (q*b),hq.isIdempotentElem.eq,hτ (q*b),←mul_assoc,hq.isIdempotentElem.eq]
  rw [he]
  exact (norm_trace_mul τ hτ _ _).trans (compressed_bound τ hp hq hqp b hδ hsmall)

lemma cornerScalar_complement_bound {f : A} (hf : IsStarProjection f) (b : A)
    {t B : ℝ} (ht : 0<t) (htr : t ≤ (τ (1-f)).re)
    (hb : ‖τ b‖ ≤ B) (hfb : ‖τ (f*b)‖ ≤ B) :
    ‖cornerScalar τ (1-f) b‖ ≤ 2*B/t := by
  have hnum : ‖τ ((1-f)*b)‖ ≤ 2*B := by
    rw [sub_mul,one_mul,map_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hden : 0<(τ (1-f)).re := ht.trans_le htr
  rw [cornerScalar,norm_div,projection_trace_norm τ hf.one_sub]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans
    (div_le_div_of_nonneg_left (by linarith [_root_.norm_nonneg (τ b)]) ht htr)

end Kadison.FinitePatching

end

end
end

end OAI
