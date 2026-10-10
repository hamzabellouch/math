import OAI.Analysis.IrrationalRotation.Model.Hyperfinite
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Analysis.VonNeumannStrongClosure

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.HyperfiniteCriterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def asStrong (T : H →L[ℂ] H) : H →Lₚₜ[ℂ] H :=
  UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite} T

omit [CompleteSpace H] in
@[simp] theorem underlying_asStrong (T : H →L[ℂ] H) :
    strongOperatorUnderlying (asStrong T) = T := rfl

omit [CompleteSpace H] in
@[simp] theorem asStrong_apply (T : H →L[ℂ] H) (x : H) :
    asStrong T x = T x := rfl

theorem mem_iSup_iff (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Monotone A) (T : H →L[ℂ] H) :
    T ∈ iSup A ↔ ∃ n, T ∈ A n := by
  change T ∈ (↑(iSup A) : Set (H →L[ℂ] H)) ↔ _
  rw [StarSubalgebra.coe_iSup_of_directed hA.directed_le]
  exact Set.mem_iUnion

theorem strong_union_eq (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : Monotone A) :
    {B : H →Lₚₜ[ℂ] H | ∃ n, strongOperatorUnderlying B ∈ A n} =
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ iSup A} := by
  ext B
  exact (mem_iSup_iff A hA (strongOperatorUnderlying B)).symm

theorem mem_strong_union_closure_of_tendsto
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hT : ∀ n, T n ∈ A n)
    (hlim : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (S x))) :
    asStrong S ∈ closure {B : H →Lₚₜ[ℂ] H |
      ∃ n, strongOperatorUnderlying B ∈ A n} := by
  have hstrong : Tendsto (fun n => asStrong (T n)) atTop (𝓝 (asStrong S)) :=
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr hlim
  exact mem_closure_of_tendsto hstrong (Eventually.of_forall fun n => ⟨n, hT n⟩)

theorem strong_union_closure_subset
    (M : VonNeumannAlgebra H) (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hAM : ∀ n, A n ≤ M.toStarSubalgebra) :
    closure {B : H →Lₚₜ[ℂ] H | ∃ n, strongOperatorUnderlying B ∈ A n} ⊆
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ M} := by
  apply closure_minimal
  · rintro B ⟨n, hn⟩
    exact hAM n hn
  · exact vonNeumannAlgebra_stronglyClosed M

theorem generated_iSup_eq_of_generator_approximation
    (s : Set (H →L[ℂ] H)) (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hAM : ∀ n, A n ≤ (vonNeumannGenerated s).toStarSubalgebra)
    (hs : ∀ T ∈ s, asStrong T ∈ closure {B : H →Lₚₜ[ℂ] H |
      ∃ n, strongOperatorUnderlying B ∈ A n}) :
    vonNeumannGenerated (↑(iSup A) : Set (H →L[ℂ] H)) = vonNeumannGenerated s := by
  apply le_antisymm
  · apply vonNeumannGenerated_le
    exact iSup_le hAM
  · apply vonNeumannGenerated_le
    intro T hT
    have hinclude : ∀ n, A n ≤
        (vonNeumannGenerated (↑(iSup A) : Set (H →L[ℂ] H))).toStarSubalgebra := by
      intro n S hS
      exact subset_vonNeumannGenerated _ ((le_iSup A n) hS)
    exact strong_union_closure_subset _ A hinclude (hs T hT)

end Invariant233.HyperfiniteCriterion

end

end OAI
