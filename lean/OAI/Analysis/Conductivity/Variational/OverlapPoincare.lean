import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def localVariance (Q : Set X) (f : X → ℝ) (m : ℝ) : ℝ := ∫ x in Q, (f x-m)^2 ∂μ

lemma localVariance_nonneg (Q : Set X) (f : X → ℝ) (m : ℝ) :
    0 ≤ localVariance μ Q f m := integral_nonneg (fun x => sq_nonneg (f x - m))

lemma localVariance_mono {Q R : Set X} {f : X → ℝ} {m : ℝ}
    (h : IntegrableOn (fun x => (f x-m)^2) R μ) (hQR : Q⊆R) :
    localVariance μ Q f m ≤ localVariance μ R f m :=
  setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ hx => hQR hx))

lemma overlap_means_bound {Q R : Set X} {f : X → ℝ} {a b : ℝ}
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-b)^2) R μ)
    (hfin : μ (Q∩R) ≠ ⊤) :
    (μ.real (Q∩R))*(a-b)^2 ≤
      2*localVariance μ Q f a+2*localVariance μ R f b := by
  let : IsFiniteMeasure (μ.restrict (Q∩R)) := ⟨by simpa using hfin.lt_top⟩
  have hQ := hfQ.mono_set (inter_subset_left : Q∩R⊆Q)
  have hR := hfR.mono_set (inter_subset_right : Q∩R⊆R)
  have hi := integral_mono (μ := μ.restrict (Q∩R)) (integrable_const ((a-b)^2))
    ((hQ.const_mul 2).add (hR.const_mul 2))
    (fun x => show (a-b)^2 ≤ 2*(f x-a)^2+2*(f x-b)^2 by
      nlinarith [sq_nonneg (2*f x-a-b)])
  change (∫ x in Q∩R, (a-b)^2 ∂μ) ≤ ∫ x in Q∩R, 2*(f x-a)^2+2*(f x-b)^2 ∂μ at hi
  rw [integral_add (hQ.const_mul 2) (hR.const_mul 2),integral_const_mul,integral_const_mul,
    integral_const] at hi
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hi
  apply hi.trans
  exact add_le_add (mul_le_mul_of_nonneg_left (localVariance_mono μ hfQ inter_subset_left) (by norm_num))
    (mul_le_mul_of_nonneg_left (localVariance_mono μ hfR inter_subset_right) (by norm_num))

lemma localVariance_change_mean {Q : Set X} {f : X → ℝ} {a b : ℝ}
    (hf : IntegrableOn (fun x => (f x-b)^2) Q μ)
    (hfa : IntegrableOn (fun x => (f x-a)^2) Q μ) (hfin : μ Q≠⊤) :
    localVariance μ Q f a ≤ 2*localVariance μ Q f b+2*(μ.real Q)*(b-a)^2 := by
  let : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hfin.lt_top⟩
  have hi := integral_mono (μ := μ.restrict Q) hfa
    ((hf.const_mul 2).add (integrable_const (2*(b-a)^2)))
    (fun x => show (f x-a)^2 ≤ 2*(f x-b)^2+2*(b-a)^2 by
      nlinarith [sq_nonneg (f x-2*b+a)])
  change (∫ x in Q, (f x-a)^2 ∂μ) ≤ ∫ x in Q, 2*(f x-b)^2+2*(b-a)^2 ∂μ at hi
  rw [integral_add (hf.const_mul 2) (integrable_const _),integral_const_mul,integral_const] at hi
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hi
  change localVariance μ Q f a ≤ 2*localVariance μ Q f b+μ.real Q*(2*(b-a)^2) at hi
  nlinarith

lemma localVariance_union_le {Q R : Set X} {f : X → ℝ} {a : ℝ}
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-a)^2) R μ) :
    localVariance μ (Q∪R) f a ≤ localVariance μ Q f a+localVariance μ R f a := by
  change (∫ x, (f x-a)^2 ∂μ.restrict (Q∪R)) ≤ _
  apply le_trans (integral_mono_measure (Measure.restrict_union_le (μ := μ) Q R)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Integrable.add_measure hfQ hfR))
  rw [integral_add_measure hfQ hfR]
  exact le_rfl

theorem overlap_poincare_glue {Q R : Set X} {f : X → ℝ} {a b E A B : ℝ}
    (_ : 0≤E) (_ : 0≤A) (_ : 0≤B)
    (hfinQ : μ Q≠⊤) (hfinR : μ R≠⊤) (hpos : 0<μ.real (Q∩R))
    (hfQ : IntegrableOn (fun x => (f x-a)^2) Q μ)
    (hfR : IntegrableOn (fun x => (f x-b)^2) R μ)
    (hfRa : IntegrableOn (fun x => (f x-a)^2) R μ)
    (hQa : localVariance μ Q f a≤A*E) (hRb : localVariance μ R f b≤B*E) :
    localVariance μ (Q∪R) f a ≤
      (A+2*B+4*(μ.real R)/(μ.real (Q∩R))*(A+B))*E := by
  have hfinQR : μ (Q∩R)≠⊤ := ne_top_of_le_ne_top hfinQ (measure_mono inter_subset_left)
  have hi := overlap_means_bound μ hfQ hfR hfinQR
  have hid : (a-b)^2 ≤ 2*(A+B)*E/(μ.real (Q∩R)) := by
    apply (le_div_iff₀ hpos).2
    nlinarith
  have hc := localVariance_change_mean μ hfR hfRa hfinR
  have hμ : 0≤μ.real R := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hid (show 0≤2*μ.real R by positivity)
  have hu := localVariance_union_le μ hfQ hfRa
  have hs : (b-a)^2=(a-b)^2 := by ring
  rw [hs] at hc
  calc localVariance μ (Q∪R) f a
      ≤ A*E+2*B*E+2*μ.real R*(2*(A+B)*E/μ.real (Q∩R)) := by linarith
    _ = (A+2*B+4*(μ.real R)/(μ.real (Q∩R))*(A+B))*E := by ring

end ScalarConductivity

end

end OAI
