import OAI.NumberTheory.Ostmann.Construction.CRTDFT
import OAI.NumberTheory.Ostmann.Construction.ZModPoisson
import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem product_dft_eq_unitary (p : ι → ℕ) [∀ i, NeZero (p i)]
    (F : ∀ i,ZMod (p i) → ℂ) (v : ∀ i,ZMod (p i)) :
    (∏ i,ZMod.dft (F i) (v i)) =
      (Real.sqrt (∏ i,p i : ℕ):ℂ)*(∏ i,Supply.unitaryDFT (F i) (v i)) := by
  have hsqrt : (Real.sqrt (∏ i,p i : ℕ):ℂ)=∏ i,(Real.sqrt (p i):ℂ) := by
    rw [Nat.cast_prod,Real.sqrt_prod Finset.univ (fun i _ => Nat.cast_nonneg (p i)),
      Complex.ofReal_prod]
  rw [hsqrt,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hs : (Real.sqrt (p i):ℂ)≠0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos (p i))).ne'
  rw [Supply.unitaryDFT,mul_div_cancel₀ _ hs]

theorem crt_scaled_poisson (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i,ZMod (p i) → ℂ) (ψ : SchwartzMap ℝ ℂ) {X : ℝ} (hX : 0<X) :
    (∑' n : ℤ,(∏ i,F i (n:ZMod (p i)))*ψ ((n:ℝ)/X)) =
      (X/(∏ i,p i : ℕ):ℂ)*(Real.sqrt (∏ i,p i : ℕ):ℂ)*
        (∑' s : ℤ,(∏ i,Supply.unitaryDFT (F i) (crtFrequency p s i))*
          𝓕 ψ (-(s:ℝ)*X/(∏ i,p i : ℕ))) := by
  let f : ZMod (∏ i,p i) → ℂ := fun z => ∏ i,F i (ZMod.prodEquivPi p hcop z i)
  have hf (n : ℤ) : f (n:ZMod (∏ i,p i))=∏ i,F i (n:ZMod (p i)) := by
    unfold f
    congr 1
    funext i
    exact congrArg (fun x => F i (x i)) (map_intCast (ZMod.prodEquivPi p hcop) n)
  have h := zmod_scaled_poisson (∏ i,p i) ψ f hX
  simp_rw [hf] at h
  rw [h]
  change (X/(∏ i,p i : ℕ):ℂ)*(∑' s : ℤ,
    ZMod.dft (fun z => ∏ i,F i (ZMod.prodEquivPi p hcop z i)) (s:ZMod (∏ i,p i))*
      𝓕 ψ (-(s:ℝ)*X/(∏ i,p i : ℕ))) = _
  simp_rw [dft_crt_product p hcop F,product_dft_eq_unitary p F,mul_assoc]
  rw [tsum_mul_left]

theorem crt_normalized_poisson (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i,ZMod (p i) → ℂ) (ψ : SchwartzMap ℝ ℂ) {X : ℝ} (hX : 0<X) :
    (∑' n : ℤ,(∏ i,F i (n:ZMod (p i)))*ψ ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
      (Real.sqrt (X/(∏ i,p i : ℕ)):ℂ)*
        (∑' s : ℤ,(∏ i,Supply.unitaryDFT (F i) (crtFrequency p s i))*
          𝓕 ψ (-(s:ℝ)*X/(∏ i,p i : ℕ))) := by
  let Q := ∏ i,p i
  have hQ : (0:ℝ)<Q := by exact_mod_cast NeZero.pos Q
  have hscalar : (X/Q)*Real.sqrt Q/Real.sqrt X=Real.sqrt (X/Q) := by
    rw [Real.sqrt_div hX.le]
    have hx := Real.sq_sqrt hX.le
    have hq := Real.sq_sqrt hQ.le
    have hx0 := (Real.sqrt_pos.mpr hX).ne'
    have hq0 := (Real.sqrt_pos.mpr hQ).ne'
    field_simp
    nlinarith
  have hc : (X/Q:ℂ)*(Real.sqrt Q:ℂ)/(Real.sqrt X:ℂ)=(Real.sqrt (X/Q):ℂ) := by
    exact_mod_cast hscalar
  rw [crt_scaled_poisson p hcop F ψ hX]
  rw [mul_div_right_comm,hc]

end Ostmann.Construction

end

end OAI
