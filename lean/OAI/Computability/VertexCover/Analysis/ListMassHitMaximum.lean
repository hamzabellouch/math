import Mathlib
import OAI.Computability.VertexCover.Reduction.IncrementNorm
import OAI.Computability.VertexCover.Reduction.ListHitMaximum
import OAI.Computability.VertexCover.Reduction.PairEventMean

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

noncomputable def incidence (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) :
    Fin d → Fin (Φ.WeightDimension d) → ℝ := fun j k =>
  truthValue (∃ a : (Φ.query seed j).LocalLabel,
    (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I ∧ (Φ.query seed j).slot a = k)

theorem incidence_at_label (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) (j : Fin d) (a : (Φ.query seed j).LocalLabel) :
    Φ.incidence seed I j ((Φ.query seed j).slot a) =
      truthValue ((⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I) := by
  unfold incidence
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, heq⟩
    have : b = a := (Φ.query seed j).slot_injective heq
    simpa [this] using hb
  · intro ha; exact ⟨a, ha, rfl⟩

theorem incidence_eq_single (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d)
    (a : (Φ.query seed j).LocalLabel)
    (ha : (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I) (k : Fin (Φ.WeightDimension d)) :
    Φ.incidence seed I j k = truthValue ((Φ.query seed j).slot a = k) := by
  unfold incidence
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, hbk⟩
    have hab : b = a := by
      have := hI.1 ⟨_, b⟩ hb ⟨_, a⟩ ha rfl
      exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq
    simpa [hab] using hbk
  · intro h; exact ⟨a, ha, h⟩

theorem incidence_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (j : Fin d) :
    ∑ k, |Φ.incidence seed I j k| ≤ 1 := by
  classical
  by_cases h : ∃ a : (Φ.query seed j).LocalLabel,
      (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I
  · obtain ⟨a, ha⟩ := h
    simp_rw [Φ.incidence_eq_single seed hI j a ha]
    have ht : ∀ P, |truthValue P| = truthValue P := by
      intro P; by_cases hP : P <;> simp [truthValue, hP]
    simp_rw [ht]
    simp [truthValue, eq_comm]
  · have hz : ∀ k, Φ.incidence seed I j k = 0 := by
      intro k
      simp only [incidence, truthValue]
      rw [ite_eq_right (fun ⟨label, hlabel, _⟩ => h ⟨label, hlabel⟩)]
    simp [hz]

noncomputable def incidenceHull (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    Set (Fin d → Fin (Φ.WeightDimension d) → ℝ) :=
  convexHull ℝ {g | ∃ I, Φ.Compatible I ∧
    (g = Φ.incidence seed I ∨ g = -Φ.incidence seed I)}

noncomputable def listMass (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    (g : Fin d → Fin (Φ.WeightDimension d) → ℝ) : ℝ :=
  ∑ j ∈ J, ∑ a ∈ (L (Φ.query seed j)).toFinset, |g j ((Φ.query seed j).slot a)|

theorem listMass_convex_sublevel (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) (C : ℝ) :
    Convex ℝ {g | Φ.listMass L seed J g ≤ C} := by
  classical
  intro x hx y hy a b ha hb hab
  change Φ.listMass L seed J (a • x + b • y) ≤ C
  calc
    _ ≤ ∑ j ∈ J, ∑ z ∈ (L (Φ.query seed j)).toFinset,
        (a * |x j ((Φ.query seed j).slot z)| + b * |y j ((Φ.query seed j).slot z)|) := by
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro z hz
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hb] using
        abs_add_le (a*x j ((Φ.query seed j).slot z)) (b*y j ((Φ.query seed j).slot z))
    _ = a * Φ.listMass L seed J x + b * Φ.listMass L seed J y := by
      simp [listMass, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a*C + b*C := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = C := by rw [← add_mul, hab, one_mul]

theorem listMass_incidence (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) :
    Φ.listMass L seed J (Φ.incidence seed I) = (Φ.hitPositions L seed I J).card := by
  classical
  have hblock : ∀ j, (∑ a ∈ (L (Φ.query seed j)).toFinset,
      |Φ.incidence seed I j ((Φ.query seed j).slot a)|) =
      truthValue (Φ.ListHit L seed I j) := by
    intro j
    by_cases h : Φ.ListHit L seed I j
    · obtain ⟨a, haL, haI⟩ := h
      have honly : ∀ b : (Φ.query seed j).LocalLabel,
          (⟨Φ.query seed j, b⟩ : Φ.Coordinate d) ∈ I ↔ b = a := by
        intro b
        constructor
        · intro hb
          have := hI.1 ⟨_, b⟩ hb ⟨_, a⟩ haI rfl
          exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq
        · rintro rfl; exact haI
      simp_rw [Φ.incidence_at_label, honly]
      have ht : ∀ P, |truthValue P| = truthValue P := by
        intro P; by_cases hP : P <;> simp [truthValue, hP]
      simp_rw [ht]
      rw [show truthValue (Φ.ListHit L seed I j) = 1 by
        simp [truthValue, show Φ.ListHit L seed I j from ⟨a, haL, haI⟩]]
      rw [Finset.sum_eq_single a]
      · simp [truthValue]
      · intro b hb hba; simp [truthValue, hba]
      · intro ha; exact (ha (List.mem_toFinset.mpr haL)).elim
    · have hz : ∀ a ∈ (L (Φ.query seed j)).toFinset,
          (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∉ I := by
        intro a ha haI
        exact h ⟨a, List.mem_toFinset.mp ha, haI⟩
      rw [show truthValue (Φ.ListHit L seed I j) = 0 by simp [truthValue, h]]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Φ.incidence_at_label]
      simp [truthValue, hz a ha]
  simp only [listMass, hblock]
  rw [hitPositions, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : Φ.ListHit L seed I j <;> simp [truthValue, h]

theorem listMass_le_hitMaximum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d))
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) :
    Φ.listMass L seed J g ≤ Φ.listHitMaximum L seed J := by
  classical
  apply convexHull_min (t := {g | Φ.listMass L seed J g ≤
    (Φ.listHitMaximum L seed J : ℝ)}) ?_ (Φ.listMass_convex_sublevel L seed J _) hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · change Φ.listMass L seed J (Φ.incidence seed I) ≤ _
    rw [Φ.listMass_incidence L seed J hI]
    exact_mod_cast (Finset.le_sup (f := fun I => (Φ.hitPositions L seed I J).card)
      (show I ∈ Φ.compatibleSelections d from by
      simp [compatibleSelections, hI]))
  · change Φ.listMass L seed J (-Φ.incidence seed I) ≤ _
    have hn : Φ.listMass L seed J (-Φ.incidence seed I) =
        Φ.listMass L seed J (Φ.incidence seed I) := by simp [listMass]
    rw [hn, Φ.listMass_incidence L seed J hI]
    exact_mod_cast (Finset.le_sup (f := fun I => (Φ.hitPositions L seed I J).card)
      (show I ∈ Φ.compatibleSelections d from by
      simp [compatibleSelections, hI]))

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
