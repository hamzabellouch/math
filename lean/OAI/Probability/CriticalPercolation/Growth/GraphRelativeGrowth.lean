import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphApproximateNeighborhoods
import OAI.Probability.CriticalPercolation.Growth.CosetBounded

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def vertexStabilizer (o : X) : Subgroup (Γ ≃g Γ) where
  carrier := {g | g o=o}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a (b o)=o; rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.symm o=o
    calc
      a.symm o = a.symm (a o) := congrArg a.symm ha.symm
      _ = o := a.symm_apply_apply o

@[simp] lemma mem_vertexStabilizer (o : X) (a : Γ ≃g Γ) : a∈vertexStabilizer Γ o ↔ a o=o := Iff.rfl

def stabilizerCosetEmbedding (o : X) : ((Γ ≃g Γ) ⧸ vertexStabilizer Γ o) ↪ X where
  toFun := Quotient.lift (s:=QuotientGroup.leftRel (vertexStabilizer Γ o)) (fun g : Γ ≃g Γ => g o) (by
    intro a b hab
    have hab' : a⁻¹*b ∈ vertexStabilizer Γ o := (QuotientGroup.leftRel_apply).mp hab
    change a.symm (b o)=o at hab'
    have hh := congrArg a hab'
    simpa using hh.symm)
  inj' := Quotient.ind₂' (by
    intro a b h
    apply QuotientGroup.eq.mpr
    change a.symm (b o)=o
    change a o=b o at h
    rw [←h]
    exact a.symm_apply_apply o)
@[simp] lemma stabilizerCosetEmbedding_mk (o : X) (g : Γ ≃g Γ) :
    stabilizerCosetEmbedding Γ o (QuotientGroup.mk g)=g o := rfl

lemma displacement_pow_subset (o : X) (n : ℕ) :
    displacement Γ o 1^n⊆displacement Γ o n := by
  induction n with
  | zero =>
    intro g hg
    have he : g=1 := by simpa only [pow_zero,Set.mem_one] using hg
    subst g
    exact one_mem_displacement Γ o 0
  | succ n ih =>
    rw [pow_succ]
    exact (Set.mul_subset_mul_right ih).trans (displacement_mul_subset Γ o n 1)

lemma stabilizer_coset_ball_image_subset (o : X) (n : ℕ) :
    stabilizerCosetEmbedding Γ o '' RelativeGrowth.ball (vertexStabilizer Γ o) (displacement Γ o 1) n
      ⊆reachBall Γ o n := by
  rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
  exact displacement_pow_subset Γ o n hg

lemma displacement_relativeDegree (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    RelativeGrowth.HasDegree (vertexStabilizer Γ o) (displacement Γ o 1) d := by
  have hf (n : ℕ) : (RelativeGrowth.ball (vertexStabilizer Γ o) (displacement Γ o 1) n).Finite := by
    apply Set.Finite.of_finite_image (f:=stabilizerCosetEmbedding Γ o)
    · exact (reachBall_finite Γ hl o n).subset (stabilizer_coset_ball_image_subset Γ o n)
    · exact (stabilizerCosetEmbedding Γ o).injective.injOn
  refine ⟨hf,1,?_⟩
  intro R
  obtain ⟨n,hn,hb⟩ := hpoly R
  refine ⟨n,hn,?_⟩
  rw [one_mul]
  apply le_trans _ hb
  rw [←Set.ncard_image_of_injective _ (stabilizerCosetEmbedding Γ o).injective]
  exact Set.ncard_le_ncard (stabilizer_coset_ball_image_subset Γ o n) (reachBall_finite Γ hl o n)

lemma vertexStabilizer_bounded (o : X) :
    RelativeGrowth.Bounded (displacement Γ o 1) (vertexStabilizer Γ o:Set (Γ ≃g Γ)) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro g hg
  change g o∈reachBall Γ o 1
  rw [(mem_vertexStabilizer Γ o g).mp hg]
  exact reachBall_self Γ o 1

end CriticalPercolation.GraphTopology
end
end

end OAI
