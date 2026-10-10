import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSlice
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! A nontrivial common prime divisor of a rough prime convolution is
itself large. In the retained small-divisor range only the empty subset
survives; its coefficient remains the original convolution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_prime_divisor_coordinate (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {b p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ b)
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    ∃ i, p ∈ fullPrimeSupport R W X i := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨i,_,hi⟩ := (hp.2.dvd_finsetProd_iff f).mp hpd
  have hfi := Fintype.mem_piFinset.mp hf i
  have hfp := fullPrimeSupport_prime R W X i (f i) hfi
  have he : p = f i := primary_associated_eq hp.1 hfp.1
    ((hp.2.dvd_prime_iff_associated hfp.2).mp hi)
  exact ⟨i,he.symm ▸ hfi⟩

lemma fullPrime_nonempty_divisor_large {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    {b : Eisenstein} (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X))
    (hsd : (∏ p ∈ s, p) ∣ b) : D < norm (∏ p ∈ s, p) := by
  obtain ⟨p,hps⟩ := hsne
  have hp := hs p hps
  have hpf : p ∣ ∏ p ∈ s, p := Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hps
  obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hp (hpf.trans hsd) hb
  have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
  have hn : X i ≤ norm p := by
    have hratio : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hratio
  have hf : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hs p hp).2.ne_zero)
  exact (hrough i).trans_le (hn.trans (norm_le_of_dvd hf hpf))

lemma fullPrime_small_divisor_slice_empty {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    (hsmall : norm (∏ p ∈ s, p) ≤ D) (e : Eisenstein) :
    fullPrimeSliceSupport R W X (∏ p ∈ s, p) e = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hb := (Finset.mem_filter.mp hn).2
  have hh := fullPrime_nonempty_divisor_large W X hX hlo hhi hrough s hs hsne
    (Finset.mem_filter.mp hb).1 (dvd_mul_right _ n)
  exact (not_lt_of_ge hsmall) hh

end CubicFirstMoment

end

end OAI
