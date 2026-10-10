import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! A countable measurable partition on which a C1 curve has nearly
its pointwise derivative norm as a Lipschitz bound. -/
open Set Function Filter Topology
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_derivative_lipschitz_bound
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {x : ℝ} (hx : x ∈ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Set ℝ) (K : ℝ≥0), IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      LipschitzOnWith K γ U ∧ ∀ y ∈ U, (K : ℝ) ≤ ‖d y‖ + ε := by
  let K : ℝ≥0 := ⟨‖d x‖ + ε / 2, by positivity⟩
  have hK : ‖d x‖₊ < K := by
    change ‖d x‖ < ‖d x‖ + ε / 2
    linarith
  obtain ⟨V, hV, hLip⟩ := (hd x hx).exists_lipschitzOnWith_of_nnnorm_lt K hK
  have hn : {y : ℝ | (K : ℝ) < ‖d y‖ + ε} ∈ 𝓝 x := by
    apply ((hc.continuousAt (hD.mem_nhds hx)).norm.add_const ε).preimage_mem_nhds
    exact Ioi_mem_nhds (by change ‖d x‖ + ε / 2 < ‖d x‖ + ε; linarith)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (inter_mem hV (inter_mem (hD.mem_nhds hx) hn))
  exact ⟨U, K, hU, hxU, fun y hy => (hUsub hy).2.1,
    hLip.mono (fun y hy => (hUsub hy).1), fun y hy => (hUsub hy).2.2.le⟩

lemma derivative_lipschitz_partition
    {D : Set ℝ} (hD : IsOpen D) (hne : D.Nonempty)
    {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set ℝ) (K : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧ (⋃ n, A n) = D ∧
      (∀ n, LipschitzOnWith (K n) γ (A n)) ∧
      ∀ n y, y ∈ A n → (K n : ℝ) ≤ ‖d y‖ + ε := by
  classical
  let : Nonempty D := hne.to_subtype
  choose U K hUo hxU hUD hLip hnorm using fun x : D =>
    local_derivative_lipschitz_bound hD hd hc x.property hε
  have hcov : D ⊆ ⋃ x : D, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof D := (isLindelof_iff_lindelofSpace).mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hUo hcov
  let A : ℕ → Set ℝ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  refine ⟨A, fun n => K (v n), (fun n => MeasurableSet.disjointed (fun j => (hUo (v j)).measurableSet) n),
    disjoint_disjointed _, ?_, (fun n => (hLip (v n)).mono (hAU n)), ?_⟩
  · change (⋃ n, disjointed (fun j => U (v j)) n) = D
    rw [iUnion_disjointed]
    exact (iUnion_subset (fun n => hUD (v n))).antisymm hv
  · exact fun n y hy => hnorm (v n) y (hAU n hy)

end CircleDomainRigidity

end

end OAI
