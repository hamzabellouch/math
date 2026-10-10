import OAI.Probability.UnimodularPercolation.Escape.CollisionTails
import OAI.Probability.UnimodularPercolation.Clusters.KernelMoments

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem mem_reachBall_symm (G : BondGraph V E) (x y : V) (M : ℕ)
    (hy : y ∈ reachBall G x M) : x ∈ reachBall G y M := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G x M hy
  obtain ⟨l,hl,he,_⟩ := walk_lift_bonds G Set.univ q.reverse
  have hlen : l.length ≤ M := by
    have hh := congrArg List.length he
    have hh' : l.length = q.length := by
      simpa only [List.length_map,SimpleGraph.Walk.length_edges,
        SimpleGraph.Walk.length_reverse] using hh
    exact hh'.le.trans hq
  exact reachBall_mono G y hlen hl.mem_reachBall

theorem ball_multiplicity_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (M : ℕ) (W : Finset V)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ a ∈ W, ∑ c ∈ W, if c ∈ reachBall G a M then f c else 0) ≤
      ((d+1)^M : ℕ) * ∑ c ∈ W, f c := by
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hs : W.filter (fun a => c ∈ reachBall G a M) ⊆
      (finite_reachBall hloc c M).toFinset := by
    intro a ha
    exact (finite_reachBall hloc c M).mem_toFinset.mpr
      (mem_reachBall_symm G a c M (Finset.mem_filter.mp ha).2)
  have hn : (W.filter (fun a => c ∈ reachBall G a M)).card ≤ (d+1)^M := by
    apply (Finset.card_le_card hs).trans
    simpa only [←Set.ncard_eq_toFinset_card] using
      reachBall_ncard_le_pow G hloc d hd c M
  calc
    _ = ((W.filter (fun a => c ∈ reachBall G a M)).card : ℝ) * f c := by
      rw [←Finset.sum_filter]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (hf c)

theorem deletedBoundaryPotential_sum_bound (G : BondGraph V E)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (M : ℕ) (W : Finset V) (p : unitInterval) :
    (∑ a ∈ W, deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M) ≤
      ((d+1)^M : ℕ) *
        ∑ c ∈ W, ∑ b ∈ neighbors G hloc c,
          inducedSusceptibility G (W : Set V)ᶜ p b := by
  let f (c : V) := ∑ b ∈ neighbors G hloc c,
    inducedSusceptibility G (W : Set V)ᶜ p b
  have he (a : V) :
      deletedBoundaryPotential G hloc (W : Set V)ᶜ p a M =
        ∑ c ∈ W, if c ∈ reachBall G a M then f c else 0 := by
    unfold deletedBoundaryPotential
    simp only [Set.mem_compl_iff,Finset.mem_coe,not_not]
    have hs : (finite_reachBall hloc a M).toFinset.filter (· ∈ W) =
        W.filter (fun c => c ∈ reachBall G a M) := by
      ext c
      simp only [Finset.mem_filter,Set.Finite.mem_toFinset]
      exact and_comm
    rw [hs,Finset.sum_filter]
  simp_rw [he]
  exact ball_multiplicity_bound G hloc d hd M W f
    (fun c => Finset.sum_nonneg (fun b _ => inducedSusceptibility_nonneg G _ p b))

theorem inducedSusceptibility_ball_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : Set V)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (a b : V) (M : ℕ)
    (ha : a ∉ D) (hb : b ∈ reachBall G a M)
    (hfin : ∀ c, Summable (fun z => (law p).real
      {η | Conn G (η ∩ internalEdges G D) c z})) :
    inducedSusceptibility G D p b ≤
      (p : ℝ)^(-(M : ℤ)) * deletedBoundaryPotential G hloc D p a M := by
  obtain ⟨q,hq⟩ := reachBall_exists_short_walk G a M hb
  obtain ⟨l,hl,he,ho⟩ := walk_lift_bonds G Set.univ q
  have hlen : l.length ≤ M := by
    have hh : l.length = q.length := by
      simpa only [List.length_map,SimpleGraph.Walk.length_edges] using congrArg List.length he
    exact hh.le.trans hq
  have hh := short_path_deleted_potential_bound G hloc D p hp Set.univ a b M
    l hl hlen ho hfin
  simpa only [deletedLocalPotential,ite_eq_right ha,zero_add] using hh

end Percolation.BenjaminiSchramm

end OAI
