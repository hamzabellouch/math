import OAI.Analysis.IrrationalRotation.Operators.BicommutantAmplification
import OAI.Analysis.IrrationalRotation.Operators.BicommutantCyclic
import OAI.Analysis.IrrationalRotation.Operators.BicommutantStrongTopology
import OAI.Analysis.IrrationalRotation.Model.Hyperfinite

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.BicommutantDensity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_amplified_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    {ι : Type*} [Fintype ι] (v : Amplification (H := H) ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ A ∧ ‖amplify ι a v - amplify ι T v‖ < ε := by
  classical
  have hdiag := amplify_mem_bicommutant ι A hT
  obtain ⟨B, hB, hclose⟩ := Bicommutant.exists_single_vector_approximation
    (StarSubalgebra.map (amplifyHom (H := H) ι) A) hdiag v hε
  obtain ⟨a, ha, hBa⟩ := StarSubalgebra.mem_map.mp hB
  refine ⟨a, ha, ?_⟩
  rw [← hBa] at hclose
  exact hclose

theorem exists_finite_vector_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    {ι : Type*} [Fintype ι] (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ A ∧ ∀ i, ‖a (x i) - T (x i)‖ < ε := by
  let v : Amplification (H := H) ι := WithLp.toLp 2 x
  obtain ⟨a, ha, hclose⟩ := exists_amplified_approximation A hT v hε
  refine ⟨a, ha, fun i => ?_⟩
  have hi := PiLp.norm_apply_le (amplify ι a v - amplify ι T v) i
  change ‖a (x i) - T (x i)‖ ≤ ‖amplify ι a v - amplify ι T v‖ at hi
  exact hi.trans_lt hclose

theorem strongClosure_eq_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ A} =
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈
        Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))} := by
  classical
  apply Set.Subset.antisymm (strongClosure_subset_bicommutant _)
  intro T hT
  have h := (mem_strongClosure_iff (A : Set (H →L[ℂ] H))
    (strongOperatorUnderlying T)).2 ?_
  · simpa only [strongView_underlying] using h
  intro s hs ε hε
  let := hs.fintype
  obtain ⟨a, ha, hclose⟩ := exists_finite_vector_approximation A hT
    (fun x : s => (x : H)) hε
  exact ⟨a, ha, fun x hx => hclose ⟨x, hx⟩⟩

theorem isStronglyClosed_iff_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsStronglyClosed A.toSubalgebra ↔
      Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) = A := by
  constructor
  · intro hA
    have hclosure := hA.closure_eq
    change closure {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ A} =
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ A} at hclosure
    rw [strongClosure_eq_bicommutant A] at hclosure
    apply Set.ext
    intro T
    simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, underlying_strongView] using
      (Set.ext_iff.mp hclosure (strongView T))
  · intro hA
    change IsClosed {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ (A : Set (H →L[ℂ] H))}
    rw [← hA]
    exact isClosed_strongCentralizer _

theorem isHyperfinite_of_bicommutant_chain (M : VonNeumannAlgebra H)
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hmono : Monotone A)
    (hinside : ∀ n, A n ≤ M.toStarSubalgebra)
    (hfinite : ∀ n, FiniteDimensional ℂ (A n))
    (hgenerate : Set.centralizer (Set.centralizer
      {T : H →L[ℂ] H | ∃ n, T ∈ A n}) = (M : Set (H →L[ℂ] H))) :
    IsHyperfinite M := by
  refine ⟨A, hmono, hinside, hfinite, ?_⟩
  have hcoe : ((⨆ n, A n : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      {T | ∃ n, T ∈ A n} := by
    rw [StarSubalgebra.coe_iSup_of_directed hmono.directed_le]
    ext T
    simp
  have h := strongClosure_eq_bicommutant (⨆ n, A n)
  change closure {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈
      ((⨆ n, A n : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H))} = _ at h
  rw [hcoe, hgenerate] at h
  exact h

end Invariant233.BicommutantDensity

end

end OAI
