import OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
import OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentGaussNormalization
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentDivisorRawEnergy CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem gaussPolynomial_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => d*c i) z=d*gaussPolynomial S a ha c z := by
  simp only [gaussPolynomial,Finset.mul_sum,mul_assoc]

theorem gaussEnergy_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy S a ha (fun i => d*c i) W K=((‖d‖^2:ℝ):ℂ)*gaussEnergy S a ha c W K := by
  simp only [gaussEnergy,gaussPolynomial_const_mul,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,tsum_mul_left]

theorem gaussEnergy_central {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (gaussEnergy S a ha (fun i => (Real.sqrt T:ℂ)⁻¹*c i) W K).re=
      (gaussEnergy S a ha c W K).re/T := by
  rw [gaussEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,div_eq_mul_inv,mul_comm]

theorem sourceGaussEnergy_central (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy Q (fun I => (Real.sqrt T:ℂ)⁻¹*c I) f W K).re=
      (sourceGaussEnergy Q c f W K).re/T := by
  unfold sourceGaussEnergy
  simp only [mul_assoc]
  exact gaussEnergy_central Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) T hT W K

theorem sourceGaussEnergy_nonneg (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤(sourceGaussEnergy Q c f W K).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) (fun I : supportedColumns Q => c I*f I) W K hK
  change 0≤(gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

end SevenEighths.CenteredMomentGaussNormalization

end

end OAI
