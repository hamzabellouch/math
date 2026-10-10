import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.TrueProbabilityMap
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderLaw

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section ClockOrders
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem iid_table_relabel (ν : PMF V) (σ : Equiv.Perm K) :
    (productPMF (fun _ : K => ν)).map (fun ω => ω ∘ σ.symm) =
      productPMF (fun _ : K => ν) := by
  ext ω
  rw [PMF.map_apply, tsum_fintype]
  have he : ∀ θ : K → V, ω = θ ∘ σ.symm ↔ θ = ω ∘ σ := by
    intro θ
    constructor
    · intro h
      funext k
      simpa only [Function.comp_apply, σ.symm_apply_apply] using (congrFun h (σ k)).symm
    · rintro rfl
      funext k
      simp
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    productPMF_apply, Function.comp_apply]
  exact Equiv.prod_comp σ (fun k => ν (ω k))

noncomputable def clockOrder (ω : K → ℕ) : List K :=
  Finset.univ.toList.mergeSort (fun a b => ω a ≤ ω b)

theorem clockOrder_enumerates (ω : K → ℕ) :
    Enumerates Finset.univ (clockOrder ω) := by
  have hp := List.mergeSort_perm Finset.univ.toList (fun a b => ω a ≤ ω b)
  refine ⟨hp.nodup_iff.mpr (Finset.nodup_toList _), ?_⟩
  apply Finset.eq_univ_of_forall
  intro k
  simp only [List.mem_toFinset]
  exact hp.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))

omit [DecidableEq K] in
theorem clockOrder_pairwise (ω : K → ℕ) :
    (clockOrder ω).Pairwise (fun a b => ω a ≤ ω b) := by
  let : Std.Total (fun a b : K => ω a ≤ ω b) := ⟨fun a b => le_total _ _⟩
  let : IsTrans K (fun a b : K => ω a ≤ ω b) := ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_mergeSort' _ _

theorem clockOrder_relabel (ω : K → ℕ) (hω : Function.Injective ω)
    (σ : Equiv.Perm K) : clockOrder (ω ∘ σ.symm) = (clockOrder ω).map σ := by
  let ρ := ω ∘ σ.symm
  let : Std.Antisymm (fun a b : K => ρ a ≤ ρ b) :=
    ⟨fun a b hab hba => σ.symm.injective (hω (le_antisymm hab hba))⟩
  have ha := clockOrder_enumerates ρ
  have hb := enumerates_map_perm (clockOrder_enumerates ω) σ
  have hp : (clockOrder ρ).Perm ((clockOrder ω).map σ) :=
    List.perm_of_nodup_nodup_toFinset_eq ha.1 hb.1 (ha.2.trans hb.2.symm)
  apply hp.eq_of_pairwise' (clockOrder_pairwise ρ)
  rw [List.pairwise_map]
  simpa only [ρ, Function.comp_apply, σ.symm_apply_apply] using clockOrder_pairwise ω

theorem iid_random_relabel (ν : PMF V) :
    (productPMF (fun _ : K => ν)).bind (fun ω =>
      (PMF.uniformOfFintype (Equiv.Perm K)).map (fun σ : Equiv.Perm K => ω ∘ σ.symm)) =
      productPMF (fun _ : K => ν) := by
  change (productPMF (fun _ : K => ν)).bind (fun ω =>
    (PMF.uniformOfFintype (Equiv.Perm K)).bind
      (fun σ => PMF.pure (ω ∘ σ.symm))) = _
  rw [PMF.bind_comm]
  change (PMF.uniformOfFintype (Equiv.Perm K)).bind (fun σ =>
    (productPMF (fun _ : K => ν)).map (fun ω => ω ∘ σ.symm)) = _
  simp only [iid_table_relabel, PMF.bind_const]

theorem clock_order_error (N : ℕ) [NeZero N] (F : List K → Bool) :
    |trueProbability ((productPMF (gridPriorities (τ := K) N)).map
        (fun ω => F (clockOrder (fun k => (ω k).val)))) -
      trueProbability ((orderLaw (Fintype.card K) Finset.univ).map F)| ≤
        (Fintype.card K : ℝ) ^ 2 / N := by
  classical
  let p := productPMF (gridPriorities (τ := K) N)
  let u := PMF.uniformOfFintype (Equiv.Perm K)
  let q := p.bind (fun ω => u.map (fun σ => (ω, σ)))
  let b₁ : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => F (clockOrder (fun k => (z.1 (z.2.symm k)).val))
  let b₂ : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => F ((clockOrder (fun k => (z.1 k).val)).map z.2)
  let bad : (K → Fin N) × Equiv.Perm K → Bool :=
    fun z => decide (¬Function.Injective z.1)
  have hagrees : ∀ z ∈ q.support, bad z = false → b₁ z = b₂ z := by
    intro z _ hz
    have hinj : Function.Injective z.1 := by simpa [bad] using hz
    have hinj' : Function.Injective (fun k => (z.1 k).val) :=
      Fin.val_injective.comp hinj
    exact congrArg F (clockOrder_relabel _ hinj' z.2)
  have h₁ : q.map b₁ = p.map (fun ω => F (clockOrder (fun k => (ω k).val))) := by
    have hh := congrArg (fun r : PMF (K → Fin N) =>
      r.map (fun ω => F (clockOrder (fun k => (ω k).val))))
      (iid_random_relabel (K := K) (PMF.uniformOfFintype (Fin N)))
    simp only [q, PMF.map_bind, PMF.map_comp, b₁, Function.comp_def]
    change (p.bind (fun ω => u.map (fun σ : Equiv.Perm K =>
      F (clockOrder (fun k => (ω (σ.symm k)).val))))) =
      p.map (fun ω => F (clockOrder (fun k => (ω k).val)))
    rw [show p = productPMF (fun _ : K => PMF.uniformOfFintype (Fin N)) from rfl]
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, u] using hh
  have h₂ : q.map b₂ = (orderLaw (Fintype.card K) Finset.univ).map F := by
    have hh : ∀ ω : K → Fin N,
        u.map (fun σ : Equiv.Perm K => (clockOrder (fun k => (ω k).val)).map σ) =
        orderLaw (Fintype.card K) Finset.univ := by
      intro ω
      exact uniform_relabel_eq_orderLaw _ le_rfl _ (clockOrder_enumerates _)
    simp only [q, PMF.map_bind, PMF.map_comp, b₂, Function.comp_def]
    have hr : ∀ ω : K → Fin N,
        u.map (fun σ : Equiv.Perm K => F ((clockOrder (fun k => (ω k).val)).map σ)) =
        (orderLaw (Fintype.card K) Finset.univ).map F := by
      intro ω
      simpa only [PMF.map_comp, Function.comp_def] using congrArg (fun r => r.map F) (hh ω)
    simp only [hr, PMF.bind_const]
  have hb : q.map bad = p.map (fun ω => decide (¬Function.Injective ω)) := by
    simp only [q, PMF.map_bind, PMF.map_comp, bad, Function.comp_def]
    change p.bind (fun ω => u.bind (fun _ => PMF.pure (decide (¬Function.Injective ω)))) = _
    simp only [PMF.bind_const]
    rfl
  have hle := boolean_coupling_bound q b₁ b₂ bad hagrees
  rw [h₁, h₂, hb] at hle
  exact hle.trans (grid_table_ties_bound N)

end ClockOrders
end SharpTerminalLeave

end

end OAI
