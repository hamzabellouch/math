import OAI.Probability.InvariantIsing.Arrays.TensorGrowingDepthGG
import OAI.Probability.InvariantIsing.Arrays.TensorGrowingDepthDiagonal
import OAI.Probability.InvariantIsing.Cavity.CavityDepthRatePair
import OAI.Probability.InvariantIsing.Arrays.TensorObjectiveContinuity

namespace OAI

/-! Actual zero-field perturbation minima admit a GG subsequence for any
prescribed finite cascade depths. System sizes are selected from the
original sequence; the diagonal rate conditions are proved in the selection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem tensor_growing_depth_minimizers_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ r, CascadeExponents (depth r) (b r))
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ) (K : ℝ) (hK : 0<K)
    (heig : ∀ k i, |eig k i|≤K) (I : (k : ℕ) → Fin m → Finset (Fin (N k))) :
    ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧
    ∃ u : (r : ℕ) → Fin (N (φ r)) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2) ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => tensorPerturbedArrayLaw (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r))
        (u r) (v r) 1 (depth (ψ r)) (b (ψ r)) (fun _ => 0)) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) := by
  obtain ⟨CG,hCG,hGG⟩ := tensor_growing_depth_minimizers_spectralGG hhaar hgauss
  obtain ⟨CD,hCD,hDiagonal⟩ := tensor_growing_depth_minimizers_constantDiagonal hhaar hgauss
  let LG := fun r => 4*(∫ T, (Real.log (rawTreeTotal (depth r) T).toReal)^2
      ∂(rawCascadeLaw (depth r) (b r) : Measure (RawTree (depth r))))+
      (0:ℝ)+4+CG*(K+4*m+8)^2
  let LD := fun r => 4*(∫ T, (Real.log (rawTreeTotal (depth r) T).toReal)^2
      ∂(rawCascadeLaw (depth r) (b r) : Measure (RawTree (depth r))))+
      (0:ℝ)+4+CD*(K+4*m+8)^2
  obtain ⟨φ,hφ,hD,hG⟩ := cavity_choose_pair_depth_rates N hNlim m LG LD
  have hmin r := tensorPerturbationObjective_exists_minimum hhaar hgauss (hN (φ r))
    (μ (φ r)) (hμinv (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r)) 1 (depth r) (b r) (hb r)
    (fun _ => 0) monotone_const le_rfl
  choose u v hu hv hm using hmin
  let laws := fun r => tensorPerturbedArrayLaw (μ (φ r)) (eig (φ r)) (fun _ => 0) (I (φ r))
    (u r) (v r) 1 (depth r) (b r) (fun _ => 0)
  let center := fun r => tensorMinimumArrayDiagonal (N (φ r)) (depth r) (v r)
  obtain ⟨Q,q,ψ,hψ,hL,hc⟩ := spectralArray_center_subsequence (m+1) laws center
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  refine ⟨τ,ψ,hτ,hψ,fun r => u (ψ r),fun r => v (ψ r),fun r => hu (ψ r),
    fun r => hv (ψ r),Q,q,hL,?_,?_⟩
  · exact hGG (fun r => N (τ r)) (fun r => hN (τ r)) (hNlim.comp hτ.tendsto_atTop)
      m (fun r => depth (ψ r)) (fun r => b (ψ r)) (fun r => hb (ψ r))
      (fun r => μ (τ r)) (fun r => hμinv (τ r)) (fun r => eig (τ r)) (fun _ _ => 0)
      K hK (fun r => heig (τ r)) (fun r => I (τ r))
      (fun r => u (ψ r)) (fun r => hu (ψ r)) (fun r => v (ψ r)) (fun r => hv (ψ r))
      (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
      (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hm (ψ r))
      (fun j B => (hG j B).comp hψ.tendsto_atTop) Q hL
  · have hco : Continuous (fun z : Fin (m+1) → Set.Icc (0 : ℝ) 1 => fun a => (z a : ℝ)) :=
      continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
    have hc' := (hco.tendsto q).comp hc
    exact hDiagonal (fun r => N (τ r)) (fun r => hN (τ r)) (hNlim.comp hτ.tendsto_atTop)
      m (fun r => depth (ψ r)) (fun r => b (ψ r)) (fun r => hb (ψ r))
      (fun r => μ (τ r)) (fun r => hμinv (τ r)) (fun r => eig (τ r)) (fun _ _ => 0)
      K hK (fun r => heig (τ r)) (fun r => I (τ r))
      (fun r => u (ψ r)) (fun r => hu (ψ r)) (fun r => v (ψ r)) (fun r => hv (ψ r))
      (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 0) (fun _ => monotone_const)
      (fun _ => le_rfl) 0 (fun _ => le_rfl) (fun r => hm (ψ r))
      (hD.comp hψ.tendsto_atTop) Q hL (fun a => (q a : ℝ)) hc'

end InvariantIsing

end

end OAI
