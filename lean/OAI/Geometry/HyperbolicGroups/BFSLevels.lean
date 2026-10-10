import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- A median BFS level, with both strict exterior sides at most half.
This applies to any specified vertex subset, not just the full graph. -/
theorem median_level (U : Finset V) (depth : V → ℕ) :
    ∃ m : ℕ, 2*(U.filter (fun v => depth v < m)).card ≤ U.card ∧
      2*(U.filter (fun v => m < depth v)).card ≤ U.card := by
  have hex : ∃ m : ℕ, U.card ≤ 2*(U.filter (fun v => depth v ≤ m)).card := by
    refine ⟨U.sup depth,?_⟩
    have he : U.filter (fun v => depth v ≤ U.sup depth) = U :=
      Finset.filter_eq_self.mpr (fun v hv => Finset.le_sup hv)
    rw [he]; omega
  let m := Nat.find hex
  have hm : U.card ≤ 2*(U.filter (fun v => depth v ≤ m)).card := Nat.find_spec hex
  refine ⟨m,?_,?_⟩
  · by_cases hz : m = 0
    · simp [hz]
    · have hmin := Nat.find_min hex (show m-1 < m by omega)
      have he : U.filter (fun v => depth v ≤ m-1) = U.filter (fun v => depth v < m) := by
        ext v
        simp only [Finset.mem_filter]
        have hmpos : 0 < m := Nat.pos_of_ne_zero hz
        rw [Nat.le_sub_one_iff_lt hmpos]
      rw [he] at hmin
      omega
  · have hh := U.card_filter_add_card_filter_not (fun v => depth v ≤ m)
    simp only [not_le] at hh
    omega

lemma sparse_level_in_interval (U : Finset V) (depth : V → ℤ) (l h : ℤ) (hlh : l ≤ h) :
    ∃ t ∈ Finset.Icc l h, (Finset.Icc l h).card * (U.filter (fun v => depth v = t)).card ≤ U.card := by
  classical
  obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image (Finset.Icc l h)
    (fun t => (U.filter (fun v => depth v = t)).card) ⟨l,Finset.mem_Icc.mpr ⟨le_rfl,hlh⟩⟩
  refine ⟨t,ht,?_⟩
  calc
    _ = ∑ s ∈ Finset.Icc l h, (U.filter (fun v => depth v = t)).card := by simp
    _ ≤ ∑ s ∈ Finset.Icc l h, (U.filter (fun v => depth v = s)).card :=
      Finset.sum_le_sum (fun s hs => hmin s hs)
    _ = (U.filter (fun v => depth v ∈ Finset.Icc l h)).card :=
      Finset.sum_card_fiberwise_eq_card_filter U _ depth
    _ ≤ U.card := Finset.card_filter_le _ _

/-- Two sparse integer levels bracketing an arbitrary median. Negative
levels are permitted (their fibers are empty for graph distances), avoiding
an endpoint exception at the root. -/
theorem two_sparse_levels (U : Finset V) (depth : V → ℤ) (m : ℤ) (a : ℕ) :
    ∃ L H : ℤ, L ≤ m ∧ m ≤ H ∧ H-L ≤ 2*a ∧
      (a+1)*(U.filter (fun v => depth v = L)).card ≤ U.card ∧
      (a+1)*(U.filter (fun v => depth v = H)).card ≤ U.card := by
  have ha : (0 : ℤ) ≤ a := by positivity
  obtain ⟨L,hL,hLc⟩ := sparse_level_in_interval U depth (m-a) m (by omega)
  obtain ⟨H,hH,hHc⟩ := sparse_level_in_interval U depth m (m+a) (by omega)
  have hcardL : (Finset.Icc (m-(a : ℤ)) m).card = a+1 := by rw [Int.card_Icc]; omega
  have hcardH : (Finset.Icc m (m+(a : ℤ))).card = a+1 := by rw [Int.card_Icc]; omega
  rw [hcardL] at hLc
  rw [hcardH] at hHc
  have hLd := Finset.mem_Icc.mp hL
  have hHd := Finset.mem_Icc.mp hH
  exact ⟨L,H,hLd.2,hHd.1,by omega,hLc,hHc⟩

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
