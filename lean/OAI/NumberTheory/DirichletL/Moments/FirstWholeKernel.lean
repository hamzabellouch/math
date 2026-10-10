import OAI.NumberTheory.DirichletL.Moments.FirstFrequency
import OAI.NumberTheory.DirichletL.Moments.Scale

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentFirstAssembly
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

def windows (V : Fin 4 → ℝ → ℂ) (K H A B K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  V 0 (Real.log (K/K₀))*V 1 (Real.log (H/H₀))*
    V 2 (Real.log (A/A₀))*V 3 (Real.log (B/B₀))

theorem dilated_frequency_whole_kernel {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    dilatedFrequency P hcop hg j e a b ha hb k h *
      windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀ *
      paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)=
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        star (ρ h)*originalPhase e r ρ a b *
        (gaussRow a ha h*star (gaussRow b hb (-h)))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log (‖eisEmbedding a‖^2/A₀)) (Real.log (‖eisEmbedding b‖^2/B₀)) := by
  dsimp only
  have haN : 0<‖eisEmbedding a‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha))
  have hbN : 0<‖eisEmbedding b‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb))
  have hrN : 0<‖eisEmbedding (finitePrimeModulus P)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  have hhN : 0<‖eisEmbedding h‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
  have hk' : 0<k/‖eisEmbedding (finitePrimeModulus P)‖^2 := div_pos hk (sq_pos_of_pos hrN)
  rw [show dilatedFrequency P hcop hg j e a b ha hb k h=_ from
    normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e a b ha hb har hbr k h]
  rw [wholeKernel_actual W V _ _ _ _ K₀ H₀ A₀ B₀ hk' (sq_pos_of_pos hhN)
    (sq_pos_of_pos haN) (sq_pos_of_pos hbN) hK₀ hH₀ hA₀ hB₀]
  have harg : k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2=
      (k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2) := by
    simp only [map_mul,norm_mul]
    ring
  rw [harg]
  simp only [windows,Real.sqrt_sq haN.le,Real.sqrt_sq hbN.le,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  have hA : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hB : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  have hr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrN.ne'
  have ha' : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr haN.ne'
  have hb' : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hbN.ne'
  have alg (c r a b A B x y u v : ℂ) (hr : r≠0) (ha : a≠0) (hb : b≠0)
      (hA : A≠0) (hB : B≠0) :
      (c/r*x*(u/a*(v/b)))*y=c/(r*A*B)*x*(u*v)*((A*B/(a*b))*y) := by
    field_simp
  convert alg ((k:ℂ)*canonicalNormalizedGauss P hcop hg j)
    (‖eisEmbedding (finitePrimeModulus P)‖:ℂ) (‖eisEmbedding a‖:ℂ) (‖eisEmbedding b‖:ℂ)
    (Real.sqrt A₀:ℂ) (Real.sqrt B₀:ℂ)
    (star (finiteSexticRow P hg j h)*originalPhase e (finitePrimeModulus P) (finiteSexticRow P hg j) a b)
    (windows V (k/‖eisEmbedding (finitePrimeModulus P)‖^2) (‖eisEmbedding h‖^2)
      (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀*
      paperRadialFourier W ((k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2)))
    (gaussRow a ha h) (star (gaussRow b hb (-h))) hr ha' hb' hA hB using 1 <;>
    simp only [windows,Complex.star_def] <;> ring

end SevenEighths.CenteredMomentFirstWholeKernel

end

end OAI
