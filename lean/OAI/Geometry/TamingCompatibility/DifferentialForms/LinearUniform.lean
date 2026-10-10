import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalH1Linear

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem linearly_normalized_uniform_regular {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(E,F)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n
        (-directionalPrincipal d g u + matrixLowerOrder b L v c K u) →
      MemSobolevLoc V ((n:ℝ)+2) u := by
  let G := principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
    (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
  let B := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i)
  let C := fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)
  obtain ⟨V,hV,hpV,hVU,hall⟩ := normalized_scalar_uniform_regular
    (hU.preimage A.symm.continuous) (A p) (by simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hp)
    G hgp B L (fun i => A (v i)) C K
  refine ⟨A ⁻¹' V,hV.preimage A.continuous,hpV,?_,?_⟩
  · intro x hx
    have h := hVU hx
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h
  · intro n u hu hf
    have hf' : MemSobolevLoc (A.symm ⁻¹' U) n
        (-directionalPrincipal (stdOrthonormalBasis ℝ E) G (linearDistribution A u) +
          matrixLowerOrder B L (fun i => A (v i)) C K (linearDistribution A u)) := by
      have h := memSobolevLoc_linear n A hf
      rw [map_add,map_neg,directionalPrincipal_linear,matrixLowerOrder_linear,
        directionalPrincipal_basis (stdOrthonormalBasis ℝ E)] at h
      exact h
    have hr := hall n (linearDistribution A u) (memSobolevLoc_linear_one A hu) hf'
    have hr' : MemSobolevLoc V ((n+2 : ℕ) : ℝ) (linearDistribution A u) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hr
    have h := memSobolevLoc_linear (n+2) A.symm hr'
    rw [linearDistribution_inverse] at h
    simpa only [Nat.cast_add,Nat.cast_ofNat,ContinuousLinearEquiv.symm_symm] using h

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma metric_square_uniform_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j)
    : ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(V,C 2)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n (square e a b ρ u) →
      MemSobolevLoc W ((n:ℝ)+2) u := by
  let G := principalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [principalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  obtain ⟨W,hW,hpW,hWU,hall⟩ := linearly_normalized_uniform_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 2 × Fin 2 => B q.1 q.2.1 q.2.2)
    (fun q => unit 2 2 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 2 × Fin 2 => Cc q.1 q.2) (fun q => unit 2 2 q.1 q.2)
  refine ⟨W,hW,hpW,hWU,?_⟩
  intro n u hu hf
  apply hall n u hu
  have h := hf
  rw [square_scalar_expansion e a b ρ g ha] at h
  rw [add_assoc,entries_lowerOrder] at h
  exact h

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma localSolutionSpace.source_regular (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : localSolutionSpace U n P) :
    MemSobolevLoc U n (P (toDistribution E F 1 u.val.1)) := by
  intro ψ hψ hψU
  rw [(mem_localSolutionSpace_iff U n P u.val).mp u.property ψ hψ hψU]
  exact memSobolev_nat_product n ψ (toDistribution_memSobolev n u.val.2)

lemma localSolutionSpace.solution_regular (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : localSolutionSpace U n P) :
    MemSobolevLoc U 1 (toDistribution E F 1 u.val.1) := by
  exact memSobolevLoc_one_of_global (toDistribution_memSobolev 1 u.val.1) U

theorem local_regular_estimate (U W : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hreg : ∀ u, MemSobolevLoc U 1 u → MemSobolevLoc U n (P u) →
      MemSobolevLoc W ((n:ℝ)+2) u)
    (g : 𝓢(E,ℂ)) (hg : HasCompactSupport (g : E → ℂ)) (hgW : tsupport g ⊆ W) :
    ∃ T : localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2),
      ∀ u, toDistribution E F ((n:ℝ)+2) (T u) =
        smulLeftCLM F g (toDistribution E F 1 u.val.1) := by
  have hr (u : localSolutionSpace U n P) :
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1)) :=
    hreg _ (localSolutionSpace.solution_regular U n P u)
      (localSolutionSpace.source_regular U n P u) g hg hgW
  exact ⟨interiorLift U n P g hr,interiorLift_spec U n P g hr⟩
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
