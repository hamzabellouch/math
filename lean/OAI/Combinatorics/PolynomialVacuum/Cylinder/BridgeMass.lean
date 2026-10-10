import OAI.Combinatorics.PolynomialVacuum.Cylinder.BridgeRenewal

namespace OAI

namespace PolynomialVacuumBridge.Corridor.BridgeWord

noncomputable def cylinderMassBound (M : ℕ) : ℝ := (1-renewalRatio M)⁻¹

theorem cylinder_bridge_finite_sum_bound (M : ℕ) (hM : 0<M) (S : Finset BridgeWord)
    (hS : ∀ A∈S,CylinderSafe M A) : (∑ A∈S,mass A) ≤ cylinderMassBound M := by
  classical
  let T := S.biUnion (fun A => (factors A).toFinset)
  let K := S.sup (fun A => (factors A).length)
  let U := S.image factors
  have hT : ∀ A∈T,A.IsPrimitive ∧ CylinderSafe M A := by
    intro A hA
    obtain ⟨B,hB,ha⟩ := Finset.mem_biUnion.mp hA
    have hab := List.mem_toFinset.mp ha
    exact ⟨factors_primitive B A hab,factors_safe B (hS B hB) A hab⟩
  have hU : ∀ L∈U,L.length∈Finset.range (K+1) := by
    intro L hL
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hL
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun A : BridgeWord => (factors A).length) hA))
  have hUT : ∀ L∈U,∀ A∈L,A∈T := by
    intro L hL A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hL
    exact Finset.mem_biUnion.mpr ⟨B,hB,List.mem_toFinset.mpr hA⟩
  have he : (∑ A∈S,mass A)=(∑ L∈U,mass L.prod) := by
    rw [Finset.sum_image]
    · simp only [factors_prod]
    · intro A hA B hB he
      simpa using congrArg List.prod he
  rw [he,← Finset.sum_fiberwise_of_maps_to hU (fun L => mass L.prod)]
  calc
    _ ≤ ∑ k∈Finset.range (K+1), ∑ L∈sequences T k,mass L.prod := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro L hL
        obtain ⟨hL,hk⟩ := Finset.mem_filter.mp hL
        exact (mem_sequences_iff T k L).mpr ⟨hk,hUT L hL⟩
      · intro L _ _; exact (mass_pos L.prod).le
    _ = ∑ k∈Finset.range (K+1),(∑ A∈T,mass A)^k := by simp only [sequences_mass]
    _ ≤ ∑ k∈Finset.range (K+1),renewalRatio M^k := by
      apply Finset.sum_le_sum
      intro k hk
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun A _ => (mass_pos A).le))
        (safe_primitive_finite_sum_bound M hM T hT) k
    _ ≤ ∑' k : ℕ,renewalRatio M^k := by
      exact (summable_geometric_of_lt_one (renewalRatio_nonneg M) (renewalRatio_lt_one M)).sum_le_tsum
        _ (fun _ _ => pow_nonneg (renewalRatio_nonneg M) _)
    _ = cylinderMassBound M := tsum_geometric_of_lt_one (renewalRatio_nonneg M) (renewalRatio_lt_one M)

abbrev CylinderBridge (M : ℕ) := {A : BridgeWord // CylinderSafe M A}

theorem cylinder_bridge_mass_summable (M : ℕ) (hM : 0<M) :
    Summable (fun A : CylinderBridge M => mass A.val) := by
  refine summable_of_sum_le (c:=cylinderMassBound M) (fun A => (mass_pos A.val).le) ?_
  intro S
  rw [← Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
  exact cylinder_bridge_finite_sum_bound M hM _ (by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact B.property)

theorem cylinder_bridge_mass_le (M : ℕ) (hM : 0<M) :
    (∑' A : CylinderBridge M,mass A.val) ≤ cylinderMassBound M := by
  apply Real.tsum_le_of_sum_le (f := fun A : CylinderBridge M => mass A.val) (fun A => (mass_pos A.val).le)
  intro S
  rw [← Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
  exact cylinder_bridge_finite_sum_bound M hM _ (by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact B.property)

end PolynomialVacuumBridge.Corridor.BridgeWord

end OAI
