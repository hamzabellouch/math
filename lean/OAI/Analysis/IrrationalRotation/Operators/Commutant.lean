import OAI.Analysis.IrrationalRotation.Model.Commutant

namespace OAI

namespace Invariant233.Commutant

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem mem_iff (T A : H →L[ℂ] H) :
    A ∈ Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) ↔
      T * A = A * T := by
  simp [Subalgebra.mem_centralizer_iff]

theorem one_mem (T : H →L[ℂ] H) :
    (1 : H →L[ℂ] H) ∈ Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) :=
  (Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))).one_mem

theorem isClosed_strong_commutant (T : H →L[ℂ] H) :
    IsClosed {A : H →Lₚₜ[ℂ] H | ∀ x : H, T (A x) = A (T x)} := by
  have h : ∀ x : H,
      IsClosed {A : H →Lₚₜ[ℂ] H | T (A x) = A (T x)} := by
    intro x
    exact isClosed_eq (T.continuous.comp (continuous_eval_const x))
      (continuous_eval_const (T x))
  simpa only [Set.iInter_ofPred] using isClosed_iInter h

theorem commute_of_strong_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (T A : H →L[ℂ] H) (B : ι → H →L[ℂ] H)
    (hB : ∀ᶠ i in l, T * B i = B i * T)
    (hlim : ∀ x : H, Filter.Tendsto (fun i => B i x) l (nhds (A x))) :
    T * A = A * T := by
  ext x
  have h₁ := T.continuous.continuousAt.tendsto.comp (hlim x)
  have h₂ := hlim (T x)
  apply tendsto_nhds_unique_of_eventuallyEq h₁ h₂
  filter_upwards [hB] with i hi
  exact congrArg (fun S : H →L[ℂ] H => S x) hi

end Invariant233.Commutant

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem operatorCommutant_mem_iff (T A : H →L[ℂ] H) :
    A ∈ operatorCommutant T ↔ T * A = A * T :=
  Commutant.mem_iff T A

theorem operatorCommutant_stronglyClosed (T : H →L[ℂ] H) :
    IsStronglyClosed (operatorCommutant T) := by
  unfold IsStronglyClosed
  have heq : {A : H →Lₚₜ[ℂ] H | strongOperatorUnderlying A ∈ operatorCommutant T} =
      {A : H →Lₚₜ[ℂ] H | ∀ x : H, T (A x) = A (T x)} := by
    ext A
    change strongOperatorUnderlying A ∈ operatorCommutant T ↔ _
    exact (operatorCommutant_mem_iff T (strongOperatorUnderlying A)).trans
      ContinuousLinearMap.ext_iff
  rw [heq]
  exact Commutant.isClosed_strong_commutant T

theorem operatorCommutant_transitive_iff (T : H →L[ℂ] H) :
    IsTransitive (operatorCommutant T) ↔ HasNoNontrivialHyperinvariantSubspace T := by
  constructor
  · intro h L hL
    exact h L hL.1 hL.2
  · intro h L hclosed hinvariant
    exact h L ⟨hclosed, hinvariant⟩

theorem IsHyperinvariant.isInvariant {T : H →L[ℂ] H} {L : Submodule ℂ H}
    (h : IsHyperinvariant T L) : IsInvariant T L := by
  apply h.2 T
  rw [operatorCommutant_mem_iff]

end Invariant233

end OAI
