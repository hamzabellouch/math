import OAI.GroupTheory.Kervaire.SpectralApproximation

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator := H →L[ℂ] H

/-- The strongly closed algebra in which the phase comparison is performed. -/
def algebra (S : Set (Operator (H := H))) : StarSubalgebra ℂ (Operator (H := H)) :=
  StarSubalgebra.centralizer ℂ S

instance (S : Set (Operator (H := H))) : IsClosed (algebra S : Set (Operator (H := H))) :=
  Set.isClosed_centralizer _

/-- The inclusion is continuous for the inherited operator norm. -/
def inclusion (S : Set (Operator (H := H))) : algebra S →L[ℂ] Operator (H := H) :=
  (algebra S).toSubalgebra.toSubmodule.subtypeL

local instance : ContinuousFunctionalCalculus ℝ (Operator (H := H)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The right-translation commutants are closed under continuous square roots. -/
theorem sqrt_mem (S : Set (Operator (H := H))) {X : Operator (H := H)}
    (hX : X ∈ algebra S) : CFC.sqrt X ∈ algebra S := by
  rw [algebra, StarSubalgebra.mem_centralizer_iff] at hX ⊢
  intro R hR
  obtain ⟨h₁, h₂⟩ := hX R hR
  exact ⟨((show Commute X R from h₁.symm).cfcₙ_nnreal NNReal.sqrt).eq.symm,
    ((show Commute X (star R) from h₂.symm).cfcₙ_nnreal NNReal.sqrt).eq.symm⟩

/-- The inherited positive-operator order, not a replacement order. -/
instance orderedRing (S : Set (Operator (H := H))) : StarOrderedRing (algebra S) := by
  apply StarOrderedRing.of_le_iff
  intro X Y
  constructor
  · intro h
    change (X : Operator (H := H)) ≤ (Y : Operator (H := H)) at h
    have hD : 0 ≤ ((Y : Operator (H := H)) - (X : Operator (H := H))) := sub_nonneg.mpr h
    let Q : algebra S := ⟨CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H))),
      sqrt_mem S ((algebra S).sub_mem Y.property X.property)⟩
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    change (Y : Operator (H := H)) = (X : Operator (H := H)) +
      star (CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H)))) * CFC.sqrt ((Y : Operator (H := H)) - (X : Operator (H := H)))
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
      CFC.sqrt_mul_sqrt_self _ hD]
    abel
  · rintro ⟨Q, rfl⟩
    change (X : Operator (H := H)) ≤ (X : Operator (H := H)) + star (Q : Operator (H := H)) * (Q : Operator (H := H))
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

@[simp] theorem inclusion_apply (S : Set (Operator (H := H))) (X : algebra S) :
    inclusion S X = (X : Operator (H := H)) := rfl

/-- Unitarity is unchanged when an operator is viewed in its centralizer. -/
theorem unitary_iff (S : Set (Operator (H := H))) (X : algebra S) :
    X ∈ unitary (algebra S) ↔ (X : Operator (H := H)) ∈ unitary (Operator (H := H)) := by
  simp only [Unitary.mem_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩

end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The unnormalized finite sum of vector functionals used for matrix traces. -/
def vectorSum (ξ : ι → H) : Operator H →L[ℂ] ℂ := ∑ j, vectorCLM (ξ j)

omit [CompleteSpace H] in
@[simp] theorem vectorSum_apply (ξ : ι → H) (T : Operator H) :
    vectorSum ξ T = ∑ j, vectorCLM (ξ j) T := by simp [vectorSum]

/-- The phase measured by a finite family of vectors. -/
def sumPhase (U : Operator H) [IsStarNormal U] (ξ : ι → H) : ℝ :=
  ∑ j, vectorPhase U (ξ j)

/-- Regularized tracial phases distribute over a finite vector family. -/
theorem smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) {a : ℂ} (ha : ‖a‖ < 1) :
    smoothTrace (vectorSum ξ) a U = ∑ j, smoothTrace (vectorCLM (ξ j)) a U := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace, traceLog_eq_calculus U hU _ ha, vectorSum_apply]
  simp only [Complex.re_sum, Complex.im_sum, Finset.sum_div, Finset.sum_sub_distrib]

/-- Bounded convergence for the precise matrix-trace phase. -/
theorem tendsto_smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorSum ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (sumPhase U ξ)) := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace_vectorSum U hU ξ (norm_cutApproach_cutTime_lt_one _)]
  exact tendsto_finsetSum _ (fun j _ => tendsto_smoothTrace_vectorCLM U hU (ξ j))

/-- Finite vector functionals are positive on squares. -/
theorem vectorSum_star_mul_nonneg (ξ : ι → H) (T : Operator H) :
    0 ≤ (vectorSum ξ (star T * T)).re := by
  rw [vectorSum_apply, Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ (inner ℂ (ξ j) (star T (T (ξ j)))).re
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change 0 ≤ RCLike.re (inner ℂ (T (ξ j)) (T (ξ j)))
  rw [inner_self_eq_norm_sq]
  positivity

/-- Finite vector functionals respect adjoints. -/
theorem vectorSum_star (ξ : ι → H) (T : Operator H) :
    vectorSum ξ (star T) = star (vectorSum ξ T) := by
  simp only [vectorSum_apply, star_sum]
  exact Finset.sum_congr rfl (fun j _ => vectorCLM_star (ξ j) T)

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The vector sum restricted to the correct finite-trace algebra. -/
def trace (S : Set (Operator (H := H))) (ξ : ι → H) : algebra S →L[ℂ] ℂ :=
  (vectorSum ξ).comp (inclusion S)

@[simp] theorem trace_apply (S : Set (Operator (H := H))) (ξ : ι → H) (X : algebra S) :
    trace S ξ X = vectorSum ξ (X : Operator (H := H)) := rfl

/-- The logarithm trace commutes with the centralizer inclusion. -/
theorem traceLog_inclusion (S : Set (Operator (H := H))) (ξ : ι → H)
    (a : ℂ) (X : algebra S) :
    traceLog (trace S ξ) a X = traceLog (vectorSum ξ) a (X : Operator (H := H)) := by
  unfold traceLog
  apply tsum_congr
  intro n
  simp

/-- The smooth trace computed internally is the same operator trace. -/
theorem smoothTrace_inclusion (S : Set (Operator (H := H))) (ξ : ι → H)
    (a : ℂ) (X : algebra S) :
    smoothTrace (trace S ξ) a X = smoothTrace (vectorSum ξ) a (X : Operator (H := H)) := by
  simp [smoothTrace, traceLog_inclusion]

/-- The bounded phase logarithm stays in every operator centralizer. -/
theorem exists_phaseOperator_mem (S : Set (Operator (H := H))) (U : algebra S)
    (hU : U ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    ∃ B : algebra S, 0 ≤ B ∧ NormedSpace.exp (phaseVelocity B) = U ∧
      ∀ ξ : H, (vectorCLM ξ (B : Operator (H := H))).re = vectorPhase (U : Operator (H := H)) ξ := by
  have hU' := (unitary_iff S U).mp hU
  obtain ⟨B, hB, _, _, hexp, hvec, hcomm⟩ := exists_phaseOperator (U : Operator (H := H)) hU'
  have hBm : B ∈ algebra S := by
    rw [algebra, StarSubalgebra.mem_centralizer_iff]
    intro R hR
    have hu := (StarSubalgebra.mem_centralizer_iff ℂ).mp U.property R hR
    have hv := (StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem U.property) R hR
    exact ⟨(hcomm R hu.1.symm hv.1.symm).eq.symm,
      (hcomm (star R) hu.2.symm hv.2.symm).eq.symm⟩
  let Bs : algebra S := ⟨B, hBm⟩
  refine ⟨Bs, hB, ?_, hvec⟩
  apply Subtype.ext
  let : NormedAlgebra ℚ (Operator (H := H)) := NormedAlgebra.restrictScalars ℚ ℂ (Operator (H := H))
  let : NormedAlgebra ℚ (algebra S) := NormedAlgebra.restrictScalars ℚ ℂ (algebra S)
  rw [show ((NormedSpace.exp (phaseVelocity Bs) : algebra S) : Operator (H := H)) =
      NormedSpace.exp (phaseVelocity (Bs : Operator (H := H))) by
    exact NormedSpace.map_exp (algebra S).subtype continuous_subtype_val (phaseVelocity Bs)]
  convert hexp using 1
  simp [phaseVelocity, Bs]

/-- Spectral phase subadditivity in a finite-vector tracial centralizer.
 The trace property will be proved for the arbitrary-group matrix representation. -/
theorem phase_subadditive [Nontrivial H] (S : Set (Operator (H := H))) (ξ : ι → H)
    (ht : ∀ X Y : algebra S, trace S ξ (X * Y) = trace S ξ (Y * X))
    (U V : algebra S) (hU : U ∈ unitary (algebra S)) (hV : V ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S V).mp hV)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S (U*V)).mp ((unitary _).mul_mem hU hV))
    sumPhase ((U*V : algebra S) : Operator (H := H)) ξ ≤
      sumPhase (U : Operator (H := H)) ξ + sumPhase (V : Operator (H := H)) ξ := by
  have hU' := (unitary_iff S U).mp hU
  have hV' := (unitary_iff S V).mp hV
  have hUV' := (unitary_iff S (U*V)).mp ((unitary _).mul_mem hU hV)
  let hVN := isStarNormal_of_mem_unitary hV'
  obtain ⟨B,hB,hBV,hvec⟩ := exists_phaseOperator_mem S V hV
  have htrace : (trace S ξ B).re = sumPhase (V : Operator (H := H)) ξ := by
    simp only [trace_apply, vectorSum_apply, Complex.re_sum, hvec, sumPhase]
  have hp (X : algebra S) : 0 ≤ (trace S ξ (star X * X)).re :=
    vectorSum_star_mul_nonneg ξ (X : Operator (H := H))
  have hs (X : algebra S) : trace S ξ (star X) = star (trace S ξ X) :=
    vectorSum_star ξ (X : Operator (H := H))
  have hbound (n : ℕ) := smoothTrace_mul_exp_le (trace S ξ) ht hp hs hU hB
    (norm_cutApproach_cutTime_lt_one n)
  simp only [hBV, htrace, smoothTrace_inclusion] at hbound
  exact le_of_tendsto_of_tendsto
    (tendsto_smoothTrace_vectorSum _ hUV' ξ)
    ((tendsto_smoothTrace_vectorSum _ hU' ξ).add tendsto_const_nhds)
    (Filter.Eventually.of_forall hbound)

end KervaireCentralizer

end

end OAI
