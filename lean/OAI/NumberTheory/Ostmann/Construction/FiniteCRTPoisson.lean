import OAI.NumberTheory.Ostmann.Construction.NormalizedCRTPoisson
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction

theorem cutoff_fourier_zero_outside {Q V : ℕ} (hQ : 0<Q) {X : ℝ} (hX : 0<X)
    (hV : (Q:ℝ)/(4*X)≤V) {s : ℤ}
    (hs : s∉Finset.Icc (-(V:ℤ)) (V:ℤ)) :
    𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/Q)=0 := by
  have hs' : (V:ℤ) < |s| := by
    simp only [Finset.mem_Icc] at hs
    by_contra hn
    exact hs (abs_le.mp (le_of_not_gt hn))
  have ha : (V:ℝ) < |(s:ℝ)| := by exact_mod_cast hs'
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  apply SchwartzCutoff.fourier_psi_zero_of_abs_ge
  rw [abs_div,abs_mul,abs_neg,abs_of_pos hX,abs_of_pos hQ']
  apply (le_div_iff₀ hQ').mpr
  have hb := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hX)).mp hV
  nlinarith

theorem cutoff_tsum_eq_finite {Q V : ℕ} (hQ : 0<Q) {X : ℝ} (hX : 0<X)
    (hV : (Q:ℝ)/(4*X)≤V) (A : ℤ → ℂ) :
    (∑' s : ℤ,A s*𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/Q)) =
      ∑ s∈Finset.Icc (-(V:ℤ)) (V:ℤ),A s*𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/Q) := by
  apply tsum_eq_sum
  intro s hs
  rw [cutoff_fourier_zero_outside hQ hX hV hs,mul_zero]

theorem crt_normalized_poisson_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i,NeZero (p i)] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i,ZMod (p i) → ℂ) {X : ℝ} (hX : 0<X) (V : ℕ)
    (hV : ((∏ i,p i : ℕ):ℝ)/(4*X)≤V) :
    (∑' n : ℤ,(∏ i,F i (n:ZMod (p i)))*SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
      (Real.sqrt (X/(∏ i,p i : ℕ)):ℂ)*
        (∑ s∈Finset.Icc (-(V:ℤ)) (V:ℤ),
          (∏ i,Supply.unitaryDFT (F i) (crtFrequency p s i))*
          𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(∏ i,p i : ℕ))) := by
  rw [crt_normalized_poisson p hcop F SchwartzCutoff.psi hX,
    cutoff_tsum_eq_finite (NeZero.pos _) hX hV]

theorem crt_product_transform_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i,NeZero (p i)] (F : ∀ i,ZMod (p i) → ℂ)
    (j : ι) (hj : ∑ x,F j x=0) :
    (∏ i,Supply.unitaryDFT (F i) (crtFrequency p 0 i))=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp only [crtFrequency,Int.cast_zero,zero_mul,Supply.unitaryDFT,ZMod.dft_apply_zero,hj,zero_div]

end Ostmann.Construction

end

end OAI
