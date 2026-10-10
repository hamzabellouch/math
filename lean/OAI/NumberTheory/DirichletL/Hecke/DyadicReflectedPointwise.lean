import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds

theorem reflected_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ Cg Cr : ℝ, 0<Cg ∧ 0<Cr ∧
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let H := (3*i+2 : ℕ)*T
      let Q := ((χ j).modulus.absNorm : ℝ)
      let R := ((radical (χ j).modulus).absNorm : ℝ)
      let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
      let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
        (presentationComplexity (χ j) H)^ε
      ‖polynomial (χ j) false W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(1/2-a-6*e)*Kr*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*Kg/(1+V)^n)*|1+a+6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨Cg,hCg,hglobal⟩ := original_upper_strip ε hε
  obtain ⟨Cr,hCr,hreflect⟩ := buffered_reflected_line_control e ε he he' hε
  refine ⟨Cg,Cr,hCg,hCr,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let H : ℝ := (3*i+2 : ℕ)*T
  let Q : ℝ := (χ j).modulus.absNorm
  let R : ℝ := (radical (χ j).modulus).absNorm
  let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
  let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
    (presentationComplexity (χ j) H)^ε
  have hKg : 0≤Kg := by dsimp [Kg,Q,R]; positivity
  have hKr : 0≤Kr := by dsimp [Kr,Q,R,presentationComplexity,HeckeLogarithmic.complexity]; positivity
  have hlr : 1-a-6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      1-a-6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧ |(s+shift σ freq).im|≤H := by
    have h := translated_rectangle_mem (a:=1-a-12*e) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : 1-a-12*e+6*e≤1-a-6*e-σ+σ)
      (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
    constructor
    · linarith [h.1]
    · exact h.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) false (s+shift σ freq)‖≤Kg := by
    have h := hglobal (χ j) (hχ j) (s+shift σ freq) (by linarith [(hmem hs).1])
    apply h.trans
    dsimp [Kg,Q,R]
    gcongr
    exact (hmem hs).2.2
  have hcentral (t : ℝ) (ht : t∈Icc (-V) V) :
      ‖series (χ j) false (((1-a-6*e-σ : ℝ) : ℂ)+t*I+shift σ freq)‖≤Kr := by
    have him : |t-freq|≤H := (abs_sub _ _).trans (by
      have ht' := abs_le.mpr ht
      change |t|+|freq|≤H
      linarith)
    apply hreflect χ hχ T a i hT ha ha' hmax j
    · simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero,shift_re]
      ring
    · simpa [shift,sub_eq_add_neg,H] using him
  have hb := polynomial_bound_of_rectangle_split (χ j) (hχ j) false W A B hA hWs hW
    D σ freq (1-a-6*e-σ) (2-σ) V C₂ Cn Kg Kr n hD hlr (by linarith)
    hV hC₂ hCn hKg hKr hm₂ hmn hcentral (fun _ _ h => Bool.false_ne_true h |>.elim) hseries
  dsimp only [Kg,Kr,Q,R,H] at hb
  convert hb using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI
