import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedQuadrature
import OAI.Probability.SKRatio.Certificates.CertifiedGaussian

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

def sumBoxes (B : ℕ → Box) : ℕ → Box
  | 0 => Box.rat 0
  | n+1 => Box.add (sumBoxes B n) (B n)

lemma integral_batches (e : Expr) (a h : ℚ) (k m : ℕ) (B : ℕ → Box)
    (hc : ∀ i < m, e.check (a+i*(k*h)) h k (B i) = true) :
    IntervalIntegrable e.val volume a (a+m*(k*h):ℚ) ∧
    (∫ x in (a:ℝ)..(a+m*(k*h):ℚ), e.val x) ∈ sumBoxes B m := by
  induction m with
  | zero =>
    simp only [sumBoxes,Nat.cast_zero,zero_mul,add_zero,IntervalIntegrable.refl,intervalIntegral.integral_same]
    exact ⟨trivial,by simpa only [Rat.cast_zero] using Box.mem_rat 0⟩
  | succ m hm =>
    have ht := hm (fun i hi => hc i (lt_trans hi (Nat.lt_succ_self m)))
    have hn := e.check_sound (hc m (Nat.lt_succ_self m))
    have he : a+(m:ℚ)*(k*h)+k*h = a+(m+1:ℕ)*(k*h) := by push_cast; ring
    rw [he] at hn
    refine ⟨ht.1.trans hn.1,?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals ht.1 hn.1]
    exact Box.mem_add ht.2 hn.2

def normalizerBox : Box := ⟨39894227/100000000,39894229/100000000⟩
lemma normalizer_mem : gaussianNormalizer ∈ normalizerBox := by
  change ((39894227/100000000:ℚ):ℝ) ≤ gaussianNormalizer ∧ gaussianNormalizer ≤ ((39894229/100000000:ℚ):ℝ)
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  exact normalizer_bounds

def normalizedBox (B : Box) : Box := Box.mul normalizerBox (B.widen (1/1000000))

def batchCheck (B : ℕ → Box) (m : ℕ) (A : Box) : Bool :=
  A.contains (normalizedBox (sumBoxes B m))

lemma gaussian_certificate {e : Expr} {β : ℝ} {f : ℝ → ℝ} {B : ℕ → Box} {A : Box}
    {h : ℚ} {k : ℕ} (hh : (k:ℚ)*h=1/2)
    (hfun : ∀ x, e.val x = f (β^2+β*x)*gaussianWeight x)
    (hf : Measurable f) (hb : ∀ x, |f (β^2+β*x)| ≤ 32*(1+x^2))
    (hc : ∀ i : ℕ, i < 40 → e.check (-10+(i:ℚ)*(k*h)) h k (B i) = true)
    (hsum : batchCheck B 40 A = true) : (∫ h, f h ∂Scalar.fieldLaw β) ∈ A := by
  have ht := integral_batches e (-10) h k 40 B hc
  rw [hh] at ht
  norm_num only [show (-10:ℚ)+40*(1/2) = 10 by norm_num] at ht
  have htail := gaussian_truncation (f := fun x => f (β^2+β*x))
    (hf.comp (by fun_prop)).aestronglyMeasurable hb
  have hI : (∫ x in (-10:ℝ)..10, f (β^2+β*x)*gaussianWeight x) ∈ sumBoxes B 40 := by
    simpa only [hfun,Rat.cast_neg,Rat.cast_ofNat] using ht.2
  have hfull := Box.mem_widen (y := ∫ x, f (β^2+β*x)*gaussianWeight x) (r := 1/1000000) hI (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,abs_sub_comm] using htail)
  rw [affine_gaussian_integral β hf]
  exact Box.mem_of_contains hsum (Box.mem_mul normalizer_mem hfull)
end SKRatio.Certificate

end

end OAI
