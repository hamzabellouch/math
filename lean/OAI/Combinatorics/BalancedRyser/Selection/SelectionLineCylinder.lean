import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailPotential

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.Selection

variable {I V W : Type*} [Fintype I] [Fintype V]

theorem observableCylinder_eq_zero_of_unavailable {G : Input I V}
    (law : OutputLaw G) (f : V → W) (J : Finset I) (prescribed : I → W)
    (hbad : ∃ i ∈ J, ∀ v, G.slot v = i → f v ≠ prescribed i) :
    (∑ a ∈ Finset.univ.filter
      (fun a : I → V => ∀ i ∈ J, f (a i) = prescribed i), law.weight a) = 0 := by
  classical
  obtain ⟨i, hi, himpossible⟩ := hbad
  apply Finset.sum_eq_zero
  intro a ha
  apply le_antisymm _ (law.nonnegative a)
  apply le_of_not_gt
  intro hp
  exact himpossible (a i) ((law.supported a hp).1 i)
    ((Finset.mem_filter.mp ha).2 i hi)

theorem observableCylinder_empty {G : Input I V} (law : OutputLaw G)
    (f : V → W) (prescribed : I → W) :
    (∑ a ∈ Finset.univ.filter
      (fun a : I → V => ∀ i ∈ (∅ : Finset I), f (a i) = prescribed i), law.weight a) =
      successMass law := by
  simp [successMass]

theorem observableCylinder_le {G : Input I V} (law : OutputLaw G)
    (f : V → W)
    (hf : ∀ v w, G.slot v = G.slot w → f v = f w → v = w)
    (J : Finset I) (prescribed : I → W) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a : I → V, cylinderMass law J a ≤ B) :
    (∑ a ∈ Finset.univ.filter
      (fun a : I → V => ∀ i ∈ J, f (a i) = prescribed i), law.weight a) ≤ B := by
  classical
  by_cases hex : ∃ a : I → V, 0 < law.weight a ∧
      ∀ i ∈ J, f (a i) = prescribed i
  · obtain ⟨a, ha, hap⟩ := hex
    have heq : (∑ b ∈ Finset.univ.filter
        (fun b : I → V => ∀ i ∈ J, f (b i) = prescribed i), law.weight b) =
        cylinderMass law J a := by
      unfold cylinderMass
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hz : law.weight b = 0
      · simp [hz]
      · have hpos : 0 < law.weight b :=
          lt_of_le_of_ne (law.nonnegative b) (Ne.symm hz)
        have hiff : (∀ i ∈ J, f (b i) = prescribed i) ↔
            (∀ i ∈ J, b i = a i) := by
          constructor
          · intro h i hi
            exact hf (b i) (a i)
              (((law.supported b hpos).1 i).trans ((law.supported a ha).1 i).symm)
              ((h i hi).trans (hap i hi).symm)
          · intro h i hi
            rw [h i hi]
            exact hap i hi
        simp only [hiff]
    exact heq.trans_le (hbound a)
  · have hz : (∑ a ∈ Finset.univ.filter
        (fun a : I → V => ∀ i ∈ J, f (a i) = prescribed i), law.weight a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply le_antisymm _ (law.nonnegative a)
      exact le_of_not_gt (fun hp => hex ⟨a, hp, (Finset.mem_filter.mp ha).2⟩)
    exact hz.trans_le hB

theorem lineCylinder_le {G : Input I V} (law : OutputLaw G)
    {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : LineAssignment G A index line) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (J : Finset I) (a : I → V),
      cylinderMass law J a ≤ (K / (q : ℝ)) ^ J.card)
    (J : Finset I) (prescribed : I → L) :
    (∑ a ∈ Finset.univ.filter
      (fun a : I → V => ∀ i ∈ J, line (a i) = prescribed i), law.weight a) ≤
      (K / (q : ℝ)) ^ J.card := by
  exact observableCylinder_le law line hline.2 J prescribed _
    (pow_nonneg (div_nonneg hK (Nat.cast_nonneg q)) _) (hbound J)

namespace Process

theorem lineCylinder_outputLaw_source_bound (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (index : I ≃ D × Bool) (line : V → L)
    (hline : LineAssignment G A index line) (J : Finset I) (prescribed : I → L) :
    (∑ a ∈ Finset.univ.filter
      (fun a : I → V => ∀ i ∈ J, line (a i) = prescribed i),
        (outputLaw p q G hG.2.1).weight a) ≤
      (cylinderConstant p / q) ^ J.card := by
  exact lineCylinder_le (outputLaw p q G hG.2.1) A index line hline _
    (cylinderConstant_pos p).le
    (cylinderMass_outputLaw_source_bound p q G hp hq hPq hG) J prescribed

end Process
end Balanced.Selection

end

end OAI
