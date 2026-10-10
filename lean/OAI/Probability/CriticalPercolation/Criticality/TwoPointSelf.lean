import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEventUpperSet
import OAI.Probability.CriticalPercolation.Criticality.GrowthAlternatives
import OAI.Probability.CriticalPercolation.Criticality.TwoPoint

namespace OAI

section
section CurrentModule11
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma twoPoint_self (p : unitInterval) (o : V) : twoPoint G p o o = 1 := by
  rw [twoPoint,hit_singleton_eq]
  have he : {ω | (G.openGraph ω).Reachable o o} = Set.univ := by
    ext ω; exact iff_of_true (.refl _) (Set.mem_univ ω)
  rw [he]
  simp

lemma twoPoint_image [Countable V] [Countable E] (φ : G.Aut) (p : unitInterval) (o v : V) :
    twoPoint G p (φ.vertex o) (φ.vertex v) = twoPoint G p o v := by
  unfold twoPoint
  rw [measureReal_def,measureReal_def]
  congr 1
  calc
    _ = (G.law p).map (fun ω : Set E => φ.edge '' ω) (G.hitEvent (φ.vertex o) {φ.vertex v}) := by
      rw [G.law_map_aut]
    _ = _ := by
      rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
        (G.measurableSet_hitEvent _ _)]
      congr 1
      ext ω
      simp only [Set.mem_preimage,hit_singleton_eq,Set.mem_ofPred_eq]
      exact SimpleGraph.Iso.reachable_iff (φ := BondGraph.Aut.openGraphIso G φ ω)

lemma twoPoint_mul_le [Countable V] [Countable E] (p : unitInterval) (x y z : V) :
    twoPoint G p x y * twoPoint G p y z ≤ twoPoint G p x z := by
  apply (G.joint_gluing p x {y} {z} (twoPoint G p y z) ?_).trans
    (measureReal_mono Set.inter_subset_right (measure_ne_top _ _))
  intro w hw
  have he : w = y := hw
  subst w
  exact le_refl _

lemma local_bound_propagation [Countable V] [Countable E] (p : unitInterval)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
    ∀ (k : ℕ) (x y : V), y ∈ G.vertexBall x (k*n) → a^k ≤ twoPoint G p x y := by
  intro k
  induction k with
  | zero =>
    intro x y hy
    have he : y = x := by simpa only [Nat.zero_mul,BondGraph.vertexBall,Set.mem_singleton_iff] using hy
    subst y
    rw [pow_zero,twoPoint_self]
  | succ k ih =>
    intro x y hy
    rw [Nat.succ_mul] at hy
    obtain ⟨z,hz,hy⟩ := Set.mem_iUnion₂.mp (G.vertexBall_add_cover x (k*n) n hy)
    rw [pow_succ]
    exact (mul_le_mul (ih x z hz) (hlocal z y hy) ha (twoPoint_nonneg G p x z)).trans
      (twoPoint_mul_le G p x z y)

lemma exists_lower_local_parameter [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval) (hp : 0 < p)
    (n : ℕ) (a : ℝ)
    (ha : ∀ x y : V, y ∈ G.vertexBall x n → a < twoPoint G p x y) :
    ∃ q : unitInterval, q < p ∧ ∀ x y : V, y ∈ G.vertexBall x n → a < twoPoint G q x y := by
  obtain ⟨R,hR,horbit⟩ := hq
  let := hR.fintype
  let (r : R) := (G.vertexBall_finite hl r.val n).fintype
  let I := (r : R) × G.vertexBall r.val n
  obtain ⟨q,_hhalf,hqp,hqI⟩ := BernoulliProduct.exists_lower_parameter
    (I := I) (fun i => G.hitEvent i.1.val {i.2.val})
    (fun i => G.hitEvent_isUpperSet _ _) (fun i => G.hitEvent_hasFiniteOpenWitness _ _)
    p hp (fun _ => a) (fun i => by
      simpa only [twoPoint,BondGraph.law,BernoulliProduct.law_const] using ha i.1.val i.2.val i.2.property)
  refine ⟨q,hqp,?_⟩
  intro x y hy
  obtain ⟨r,hr,φ,rfl⟩ := horbit x
  let y' := φ.vertex.symm y
  have hy' : y' ∈ G.vertexBall r n := by
    apply (BondGraph.Aut.vertexBall_mem G φ r y' n).mp
    simpa only [y',Equiv.apply_symm_apply] using hy
  have hh := hqI ⟨⟨r,hr⟩,⟨y',hy'⟩⟩
  have he : twoPoint G q (φ.vertex r) y = twoPoint G q r y' := by
    simpa only [y',Equiv.apply_symm_apply] using twoPoint_image G φ q r y'
  rw [he]
  simpa only [twoPoint,BondGraph.law,BernoulliProduct.law_const] using hh

end CriticalPercolation.Sharpness
end
end CurrentModule11

end

end OAI
