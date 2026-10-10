import OAI.NumberTheory.DirichletL.Moments.AmplificationSourceError
import OAI.NumberTheory.DirichletL.Moments.AmplificationErrorPool

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceError CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

def localErrorCost (p : O) (n : ℕ) : ℝ :=
  if n=5 then (1-(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹)^2
  else (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity

theorem localErrorCost_exact (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (h : O) (hh : ¬p∣h) : ‖errorScalar p hp.ne_zero n h‖^2=localErrorCost p n := by
  have he := errorScalar_norms p hp hs hg hc h hh
  rcases hn with rfl|rfl|rfl
  · simpa only [localErrorCost,show ¬(0:ℕ)=5 by decide,ite_false] using he.1
  · simpa only [localErrorCost,ite_true] using he.2.1
  · simpa only [localErrorCost,show ¬(6:ℕ)=5 by decide,ite_false] using he.2.2

theorem finite_original_error_energy (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2 ∣ p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) (T : ℝ) (hT : 0<T)
    (rows : Finset O) (hrows : ∀ h∈rows,¬p∣h)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)≤
      localErrorCost p n *
        ((sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => c ((Ideal.span {p})^(n+1)*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re /
          (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  let Q := residualColumns S p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  let d : supportedColumns Q → ℂ := fun I =>
    c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I)
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he : (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)=
      localErrorCost p n *∑ h∈rows,
        ‖gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I => (Real.sqrt T':ℂ)⁻¹*d I) h‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [normalized_source_error_sq S c p hp hs hpp n h T hT,
      localErrorCost_exact p hp hs hg hc n hn h (hrows h hh)]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (localErrorCost_nonneg p n)
  have hh := finite_energy_le_gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I => (Real.sqrt T':ℂ)⁻¹*d I) W K hK rows hW hmajor
  rw [gaussEnergy_central _ _ _ d T' ht] at hh
  exact hh

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI
