import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphApproximateNeighborhoods

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma displacement_eq_pow (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v)
    (o : X) (n : ℕ) : displacement Γ o (n+1)=displacement Γ o 1^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨p,hp⟩ := hg
      rw [pow_succ']
      generalize hx : g o=x at p
      cases p with
      | nil =>
        have hg1 : g∈displacement Γ o 1 := by
          change g o∈reachBall Γ o 1
          rw [hx]
          exact reachBall_self Γ o 1
        refine Set.mem_mul.mpr ⟨g,hg1,1,?_,mul_one g⟩
        rw [←ih]
        exact one_mem_displacement Γ o _
      | @cons a b c hab p =>
        obtain ⟨f,hf⟩ := ht o b
        have hfmem : f∈displacement Γ o 1 := by
          change f o∈reachBall Γ o 1
          rw [hf]
          exact ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil,by simp⟩
        have hrem : f⁻¹*g∈displacement Γ o (n+1) := by
          have hwalk : g o∈reachBall Γ b (n+1) := by
            rw [hx]
            exact ⟨p,by simpa using hp⟩
          have hh := iso_reachBall Γ f.symm hwalk
          rw [←hf] at hh
          change f.symm (g o)∈reachBall Γ o (n+1)
          simpa using hh
        refine Set.mem_mul.mpr ⟨f,hfmem,f⁻¹*g,?_,by simp⟩
        rw [←ih]
        exact hrem
    · rw [pow_succ',←ih]
      simpa only [show 1+(n+1)=n+1+1 by omega] using
        displacement_mul_subset Γ o 1 (n+1)

lemma displacement_powers_cover (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (g : Γ ≃g Γ) :
    ∃ n : ℕ, g∈displacement Γ o 1^(n+1) := by
  obtain ⟨p⟩ := hc o (g o)
  refine ⟨p.length,?_⟩
  rw [←displacement_eq_pow Γ ht]
  exact ⟨p,Nat.le_succ _⟩

lemma displacement_generates (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) :
    Subgroup.closure (displacement Γ o 1)=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := displacement_powers_cover Γ hc ht o g
  have hpow : ∀ k : ℕ, displacement Γ o 1^k ⊆
      (Subgroup.closure (displacement Γ o 1) : Set (Γ ≃g Γ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      rintro a ⟨b,hb,c,hc,rfl⟩
      exact (Subgroup.closure _).mul_mem (ih hb) (Subgroup.subset_closure hc)
  exact hpow (n+1) hn

theorem compact_open_generating_approximate_powers
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    let S := displacement Γ o 1
    IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧ S⁻¹=S ∧
      Subgroup.closure S=⊤ ∧
      ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
        IsApproximateSubgroup (5^(d+1) : ℝ) (S^n) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  refine ⟨compact_displacement Γ hc hl o 1,open_displacement Γ o 1,
    one_mem_displacement Γ o 1,?_,displacement_generates Γ hc ht o,?_⟩
  · ext g
    change g⁻¹∈displacement Γ o 1 ↔ g∈displacement Γ o 1
    exact displacement_inv Γ
  · intro R
    obtain ⟨n,hn,hcomp,hopen,happrox⟩ :=
      compact_open_approximate_scales Γ hc hl ht o d hpoly (max R 1)
    have he : displacement Γ o (2*n)=displacement Γ o 1^(2*n) := by
      have hpos : 0<2*n := by omega
      simpa only [Nat.sub_add_cancel (show 1≤2*n by omega)] using
        displacement_eq_pow Γ ht o (2*n-1)
    refine ⟨2*n,by omega,?_,?_,?_⟩ <;> rwa [←he]

end CriticalPercolation.GraphTopology
end
end

end OAI
