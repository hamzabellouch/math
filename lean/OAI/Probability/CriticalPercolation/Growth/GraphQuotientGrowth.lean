import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphGeneratingNeighborhood

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma image_displacement_ncard_le {B : Type*} [Group B]
    (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X)
    (f : (Γ ≃g Γ) →* B)
    (hB : (f '' {g : Γ ≃g Γ | g o=o}).Finite) (r : ℕ) :
    (f '' displacement Γ o r).ncard ≤
      (reachBall Γ o r).ncard * (f '' {g : Γ ≃g Γ | g o=o}).ncard := by
  let a : X → (Γ ≃g Γ) := fun x => (ht o x).choose
  have ha : ∀ x, a x o=x := fun x => (ht o x).choose_spec
  let U := reachBall Γ o r ×ˢ (f '' {g : Γ ≃g Γ | g o=o})
  let m : X × B → B := fun z => f (a z.1)*z.2
  have hU : U.Finite := (reachBall_finite Γ hl o r).prod hB
  have hs : f '' displacement Γ o r ⊆ m '' U := by
    rintro b ⟨g,hg,rfl⟩
    refine ⟨(g o,f ((a (g o))⁻¹*g)),⟨hg,?_⟩,?_⟩
    · refine ⟨(a (g o))⁻¹*g,?_,rfl⟩
      change (a (g o)).symm (g o)=o
      calc
        (a (g o)).symm (g o) = (a (g o)).symm ((a (g o)) o) :=
          congrArg (a (g o)).symm (ha (g o)).symm
        _ = o := (a (g o)).symm_apply_apply o
    · dsimp only [m]
      rw [←map_mul,mul_inv_cancel_left]
  calc
    (f '' displacement Γ o r).ncard ≤ (m '' U).ncard :=
      Set.ncard_le_ncard hs (hU.image m)
    _ ≤ U.ncard := Set.ncard_image_le hU
    _ = (reachBall Γ o r).ncard * (f '' {g : Γ ≃g Γ | g o=o}).ncard :=
      Set.ncard_prod

theorem quotient_powers_ncard_le
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X)
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (ho : @IsOpen (Γ ≃g Γ) (autTopology Γ) (H : Set (Γ ≃g Γ))) :
    let T := (QuotientGroup.mk' H) '' displacement Γ o 1
    ∃ M : ℕ, 1≤M ∧ T.Finite ∧ (1 : (Γ ≃g Γ) ⧸ H)∈T ∧ T⁻¹=T ∧
      Subgroup.closure T=⊤ ∧ ∀ n : ℕ, 1≤n →
        (T^n).ncard ≤ (reachBall Γ o n).ncard*M := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  let _ : DiscreteTopology ((Γ ≃g Γ) ⧸ H) := QuotientGroup.discreteTopology ho
  let f := QuotientGroup.mk' H
  let B := f '' {g : Γ ≃g Γ | g o=o}
  have hB : B.Finite := isCompact_iff_finite.mp
    ((compact_stabilizer Γ hc hl o).image QuotientGroup.continuous_mk)
  have hB1 : (1 : (Γ ≃g Γ) ⧸ H)∈B := ⟨1,rfl,map_one f⟩
  have hM : 1≤B.ncard := (Set.ncard_pos hB).mpr ⟨1,hB1⟩
  dsimp only
  refine ⟨B.ncard,hM,?_,⟨1,one_mem_displacement Γ o 1,map_one f⟩,?_,?_,?_⟩
  · exact isCompact_iff_finite.mp
      ((compact_displacement Γ hc hl o 1).image QuotientGroup.continuous_mk)
  · rw [←Set.image_inv]
    congr 1
    ext g
    exact displacement_inv Γ
  · rw [←MonoidHom.map_closure,displacement_generates Γ hc ht o]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
  · intro n hn
    rw [←Set.image_pow,←show displacement Γ o n=displacement Γ o 1^n by
      simpa only [Nat.sub_add_cancel hn] using displacement_eq_pow Γ ht o (n-1)]
    exact image_displacement_ncard_le Γ hl ht o f hB n

end CriticalPercolation.GraphTopology
end
end

end OAI
