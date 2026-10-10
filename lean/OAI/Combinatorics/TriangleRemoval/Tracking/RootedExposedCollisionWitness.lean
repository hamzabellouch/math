import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (label : Fin N → V)

theorem rooted_exposed_collision_witness (hrules : B.SpawnRules G label)
    (R : ℕ) (hroots : Set.InjOn label {v : Fin N | v.val < R})
    (hnonroot : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2)
    {v w : Fin N} (hne : v ≠ w) {T : Finset V}
    (hv : B.ExposedAt G label v T) (hw : B.ExposedAt G label w T) :
    ∃ S : Set (Fin N), IsLowerSet S ∧ Set.InjOn label S ∧
      (∀ x : Fin N, x.val < R → x ∈ S) ∧
      ∃ a ∈ S, ∃ b ∈ S, B.ExtraEdge G label a b := by
  classical
  by_cases hinj : Function.Injective label
  · have hex : ∃ a b, B.ExtraEdge G label a b := by
      by_contra hn
      have hno : ∀ a b, ¬ B.ExtraEdge G label a b := by simpa only [not_exists] using hn
      exact B.no_repeated_exposure G label hinj hno hne hv hw
    obtain ⟨a,b,he⟩ := hex
    exact ⟨Set.univ,isLowerSet_univ,hinj.injOn,fun _ _ => Set.mem_univ _,
      a,Set.mem_univ _,b,Set.mem_univ _,he⟩
  · obtain ⟨z,u,huz,hzu,hpre⟩ := exists_first_repeat label hinj
    have hz : R ≤ z.val := by
      by_contra hn
      have hzR : z.val < R := Nat.lt_of_not_ge hn
      have huR : u.val < R := lt_trans huz hzR
      exact (ne_of_lt huz) (hroots hzR huR hzu).symm
    obtain ⟨a,b,ha,hb,he⟩ :=
      B.first_label_repeat_extra G label hrules (hnonroot z hz) huz hzu
    exact ⟨Set.Iio z,isLowerSet_Iio z,hpre,fun x hx => lt_of_lt_of_le hx hz,
      a,ha,b,hb,he⟩

end SharpTerminalLeave.BirthGraph

end

end OAI
