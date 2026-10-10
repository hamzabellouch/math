import OAI.NumberTheory.DirichletL.Hecke.DyadicPointwise

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem buffered_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
      ‖polynomial (χ j) inverse W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(a+6*e-1/2)*K*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*K/(1+V)^n)*|2-a-6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨C,hC,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
  have hK : 0≤K := mul_nonneg hC.le (Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _)
  have hlr : a+6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    translated_rectangle_mem (a:=a) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : a+6*e≤a+6*e-σ+σ) (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
  have hz {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    hrect χ hχ T a i hT ha ha' hmax j (s+shift σ freq) (hmem hs).1 (hmem hs).2.1 (hmem hs).2.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) inverse (s+shift σ freq)‖≤K := by
    have hb := (hz hs).2
    cases inverse
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb
  have hbound := polynomial_bound_of_rectangle (χ j) (hχ j) inverse W A B hA hWs hW
    D σ freq (a+6*e-σ) (2-σ) V C₂ Cn K n hD hlr (by linarith) hV hC₂ hCn hK hm₂ hmn
    (fun _ hs _ => (hz hs).1) hseries
  dsimp only [K] at hbound
  convert hbound using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI
