import OAI.Probability.ContinuumTransition.FreeGeometry

namespace OAI

section
open scoped BigOperators
open Set
namespace ContinuumTemperature
open Classical

theorem freeConfig_roots {ι : Type} [Fintype ι] {t L : ℝ} {x : ι → Space}
    (ht : 2*(1+shellDelta)*Real.exp (-t) < 1) (hx : FreeConfig t x)
    (hL : ∀ i, x i ∈ cube L) :
    ∃ s : Finset ι, s.card ≤ packingNumber L ∧ Fintype.card ι ≤ 4*s.card ∧
      ∀ j, ∃ i ∈ s, ‖x j-x i‖ ≤ (1+shellDelta)*Real.exp (-t) := by
  let Q := Quotient (freeSetoid ht hx)
  let s : Finset ι := Finset.univ.image (fun c : Q => c.out)
  have ho : Function.Injective (fun c : Q => c.out) := by
    intro a b hab
    have he := congrArg (Quotient.mk (freeSetoid ht hx)) hab
    simpa only [Quotient.out_eq] using he
  have hs : s.card = Fintype.card Q := by
    exact (Finset.card_image_of_injective _ ho).trans (Finset.card_univ)
  have hc (j : ι) : ∃ i ∈ s, j ∈ freeCluster x i := by
    refine ⟨(Quotient.mk (freeSetoid ht hx) j).out, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Quotient.mk (freeSetoid ht hx) j, Finset.mem_univ _, rfl⟩
    · apply mem_freeCluster.mpr
      exact Quotient.exact (Quotient.out_eq (Quotient.mk (freeSetoid ht hx) j))
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [hs]
    exact free_component_card_le_packing ht hx hL
  · have hu : Finset.univ ⊆ s.biUnion (freeCluster x) := by
      intro j _
      obtain ⟨i,hi,hj⟩ := hc j
      exact Finset.mem_biUnion.mpr ⟨i,hi,hj⟩
    calc
      Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
      _ ≤ (s.biUnion (freeCluster x)).card := Finset.card_le_card hu
      _ ≤ ∑ i ∈ s, (freeCluster x i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ s, 4 := Finset.sum_le_sum (fun i _ => freeCluster_card_le_four ht hx i)
      _ = 4*s.card := by simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  · intro j
    obtain ⟨i,hi,hj⟩ := hc j
    exact ⟨i,hi,by simpa only [norm_sub_rev] using freeCluster_close_root hx hj⟩

end ContinuumTemperature
end

end OAI
