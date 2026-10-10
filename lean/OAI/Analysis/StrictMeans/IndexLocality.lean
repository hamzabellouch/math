import OAI.Analysis.StrictMeans.HeightIndex

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

def meshStar (x y v : V) : Finset V := {v,v+x,v+x+y,v+y,v-x,v-(x+y),v-y}

lemma mem_meshStar_self (x y v : V) : v ∈ meshStar x y v := by simp [meshStar]

lemma meshStar_symm (x y v w : V) : w ∈ meshStar x y v ↔ v ∈ meshStar x y w := by
  simp only [meshStar,Finset.mem_insert,Finset.mem_singleton]
  constructor <;> intro h
  · rcases h with h|h|h|h|h|h|h <;> subst w <;>
      simp only [add_sub_cancel_right,add_sub_cancel_left,sub_add_cancel,add_assoc,
        sub_add_eq_add_sub,sub_sub,add_sub_assoc] <;> abel_nf <;> tauto
  · rcases h with h|h|h|h|h|h|h <;> subst v <;>
      simp only [add_sub_cancel_right,add_sub_cancel_left,sub_add_cancel,add_assoc,
        sub_add_eq_add_sub,sub_sub,add_sub_assoc] <;> abel_nf <;> tauto

lemma heightIndex_congr_star {u w : V → ℝ} {x y v : V}
    (h : ∀ a ∈ meshStar x y v, u a = w a) : heightIndex u x y v = heightIndex w x y v := by
  have hv := h v (by simp [meshStar])
  have h₀ := h (v+x) (by simp [meshStar])
  have h₁ := h (v+x+y) (by simp [meshStar])
  have h₂ := h (v+y) (by simp [meshStar])
  have h₃ := h (v-x) (by simp [meshStar])
  have h₄ := h (v-(x+y)) (by simp [meshStar])
  have h₅ := h (v-y) (by simp [meshStar])
  simp only [heightIndex,meshIndex_eq_linkIndex,heightRank,hv,h₀,h₁,h₂,h₃,h₄,h₅]
  rfl

def meshBoundary (x y : V) (S : Finset V) : Finset V :=
  (S.biUnion (meshStar x y)).filter (fun v => ¬ meshStar x y v ⊆ S)

lemma mem_meshBoundary (x y v : V) (S : Finset V) : v ∈ meshBoundary x y S ↔
    (∃ w ∈ meshStar x y v, w ∈ S) ∧ ¬ meshStar x y v ⊆ S := by
  simp only [meshBoundary,Finset.mem_filter,Finset.mem_biUnion]
  aesop (add simp [meshStar_symm])

lemma meshStar_subset_of_mem_not_boundary {x y v : V} {S : Finset V}
    (hv : v ∈ S) (hb : v ∉ meshBoundary x y S) : meshStar x y v ⊆ S := by
  by_contra hh
  exact hb ((mem_meshBoundary x y v S).mpr ⟨⟨v,mem_meshStar_self _ _ _,hv⟩,hh⟩)

lemma meshStar_disjoint_of_not_mem_not_boundary {x y v : V} {S : Finset V}
    (hv : v ∉ S) (hb : v ∉ meshBoundary x y S) : ∀ w ∈ meshStar x y v, w ∉ S := by
  intro w hw hs
  apply hb
  rw [mem_meshBoundary]
  exact ⟨⟨w,hw,hs⟩,fun h => hv (h (mem_meshStar_self _ _ _))⟩

lemma heightIndex_local_change {u w : V → ℝ} {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (S : Finset V)
    (hu : ∀ v ∈ meshBoundary x y S, heightIndex u x y v = 0)
    (hw : ∀ v ∈ meshBoundary x y S, heightIndex w x y v = 0)
    (hm : ∀ v ∈ meshBoundary x y S,
      heightIndex (fun a => if a ∈ S then w a else u a) x y v = 0) :
    ∑ v ∈ S, heightIndex u x y v = ∑ v ∈ S, heightIndex w x y v := by
  let q : V → ℝ := fun a => if a ∈ S then w a else u a
  have hf : {v | q v ≠ u v}.Finite := S.finite_toSet.subset (by
    intro v hv
    by_contra hh
    change v ∉ S at hh
    exact hv (by simp [q,hh]))
  have hout (v : V) (hv : v ∉ S) : heightIndex q x y v = heightIndex u x y v := by
    by_cases hb : v ∈ meshBoundary x y S
    · exact (hm v hb).trans (hu v hb).symm
    · apply heightIndex_congr_star
      intro a ha
      simp [q,meshStar_disjoint_of_not_mem_not_boundary hv hb a ha]
  have hin (v : V) (hv : v ∈ S) : heightIndex q x y v = heightIndex w x y v := by
    by_cases hb : v ∈ meshBoundary x y S
    · exact (hm v hb).trans (hw v hb).symm
    · apply heightIndex_congr_star
      intro a ha
      simp [q,meshStar_subset_of_mem_not_boundary hv hb ha]
  have he := heightIndex_finite_change hf hx hy hd
  rw [finsum_eq_sum_of_support_subset _ (s := S)] at he
  · have hsum : ∑ v ∈ S, (heightIndex q x y v-heightIndex u x y v) =
        (∑ v ∈ S, heightIndex w x y v)-(∑ v ∈ S, heightIndex u x y v) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl hin
    rw [hsum] at he
    exact (sub_eq_zero.mp he).symm
  · intro v hv
    by_contra hh
    change v ∉ S at hh
    exact hv (sub_eq_zero.mpr (hout v hh))

end
end StrictInverseFirstPower.Grid

end

end OAI
