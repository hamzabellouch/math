import OAI.MeasureTheory.Falconer.Recursion.DescriptorMasks
import OAI.MeasureTheory.Falconer.Estimates.Assembly

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def sourceSmoothingLevels (sig kap : ℝ) : ℕ :=
  Nat.ceil (100*(1/sig+1/kap)+100)

noncomputable def sourcePolicyBlock (N : ℕ) (kap : ℝ) : ℕ := Nat.ceil (kap*(N:ℝ))

noncomputable def outerEntry (m₁ m₂ : ℝ → ℝ) (N : ℕ) (β : ℝ) : ℕ := by
  classical
  exact ((Finset.range (N+1)).filter fun (n : ℕ) =>
    min (m₁ n-(n:ℝ)/(N:ℝ)) (m₂ n-(n:ℝ)/(N:ℝ)) ≤ β).sup id

noncomputable def outerDescriptorList (m : ℝ → ℝ) (N q c : ℕ) : Finset PolicyDescriptor :=
  insert (.parallel 0 c) (policyDescriptorList (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) N q c N)

noncomputable def outerEndpointMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) : Plane → UnitCircle → ℝ :=
  descriptorListMask Q ρ m N lam sig (sourceSmoothingLevels sig kap) 0
    (outerDescriptorList m N (sourcePolicyBlock N kap) c)

theorem sourceSmoothingLevels_pos {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    0 < sourceSmoothingLevels sig kap := by
  unfold sourceSmoothingLevels
  exact Nat.ceil_pos.mpr (by positivity)

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

theorem outerEntry_spec (m₁ m₂ : ℝ → ℝ) (N : ℕ) {β : ℝ}
    (h₁ : m₁ 0 = 0) (h₂ : m₂ 0 = 0) (hβ : 0 ≤ β) :
    outerEntry m₁ m₂ N β ≤ N ∧
      min (m₁ (outerEntry m₁ m₂ N β)-(outerEntry m₁ m₂ N β:ℝ)/(N:ℝ))
        (m₂ (outerEntry m₁ m₂ N β)-(outerEntry m₁ m₂ N β:ℝ)/(N:ℝ)) ≤ β ∧
      ∀ n : ℕ, outerEntry m₁ m₂ N β < n → n ≤ N →
        β < min (m₁ n-(n:ℝ)/(N:ℝ)) (m₂ n-(n:ℝ)/(N:ℝ)) := by
  classical
  let S := (Finset.range (N+1)).filter fun (n : ℕ) => min (m₁ n-(n:ℝ)/(N:ℝ)) (m₂ n-(n:ℝ)/(N:ℝ)) ≤ β
  have h0 : 0 ∈ S := by simp [S,h₁,h₂,hβ]
  have he : outerEntry m₁ m₂ N β = S.max' ⟨0,h0⟩ := by
    change S.sup id = S.max' ⟨0,h0⟩
    apply le_antisymm
    · exact Finset.sup_le (fun n hn => S.le_max' n hn)
    · exact Finset.le_sup (f := id) (S.max'_mem ⟨0,h0⟩)
  have hm := Finset.mem_filter.mp (S.max'_mem ⟨0,h0⟩)
  rw [he]
  refine ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hm.1),hm.2,?_⟩
  intro n hn hnN
  by_contra hh
  have hnS : n ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),not_lt.mp hh⟩
  exact (not_le_of_gt hn) (S.le_max' n hnS)

theorem outerDescriptorList_valid (m : ℝ → ℝ) {N q c : ℕ} (hq : 0 < q) (hc : c ≤ N) :
    ∀ b ∈ outerDescriptorList m N q c, ValidDescriptor N b := by
  intro b hb
  obtain rfl | hb := Finset.mem_insert.mp hb
  · exact ⟨Nat.zero_le c,hc⟩
  · exact policyDescriptor_valid _ hq le_rfl hb

theorem outerDescriptorList_card (m : ℝ → ℝ) {N q c : ℕ} (hq : 0 < q) :
    (outerDescriptorList m N q c).card ≤ (N+1)^3+1 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (policyDescriptorList_card _ hq) 1)

theorem outerEndpointMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) (x : Plane) (dir : UnitCircle) :
    0 ≤ outerEndpointMask Q ρ m N lam sig kap c x dir ∧
      outerEndpointMask Q ρ m N lam sig kap c x dir ≤ 1 := descriptorListMask_bounds Q hQ _ _ _ _ _ _ _ _ _ _

@[fun_prop] theorem measurable_outerEndpointMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) :
    Measurable (fun z : Plane × UnitCircle => outerEndpointMask Q ρ m N lam sig kap c z.1 z.2) :=
  measurable_descriptorListMask _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
