import OAI.Analysis.BoundedHochschild.ProperlyInfiniteCorners

namespace OAI

/-! Increasing chains of pairs implementing properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Two embeddings of a common projection into orthogonal subprojections. -/
def IsInfinitePair (a : PartialIso M × PartialIso M) : Prop :=
  a.1.initial = a.2.initial ∧ a.1.final ≤ a.1.initial ∧
    a.2.final ≤ a.1.initial ∧ a.1.final * a.2.final = 0

lemma infinitePair_cross_orthogonal {C : Set (PartialIso M × PartialIso M)}
    (hC : ∀ a ∈ C, IsInfinitePair a) (hchain : IsChain (· ≤ ·) C)
    {a b : PartialIso M × PartialIso M} (ha : a ∈ C) (hb : b ∈ C) :
    a.1.final * b.2.final = 0 := by
  rcases hchain.total ha hb with h | h
  · calc
      _ = (a.1.final * b.1.final) * b.2.final := by
        rw [(a.1.final_proj.le_iff_mul_eq_left b.1.final_proj).mp (PartialIso.final_mono h.1)]
      _ = 0 := by rw [mul_assoc, (hC b hb).2.2.2, mul_zero]
  · calc
      _ = a.1.final * (a.2.final * b.2.final) := by
        rw [(b.2.final_proj.le_iff_mul_eq_right a.2.final_proj).mp (PartialIso.final_mono h.2)]
      _ = 0 := by rw [← mul_assoc, (hC a ha).2.2.2, zero_mul]

/-- The pair order preserves both common initial supports and orthogonality
at a chain supremum. -/
theorem infinitePair_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (C : Set (PartialIso M × PartialIso M)) (hC : ∀ a ∈ C, IsInfinitePair a)
    (hchain : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    ∃ a : PartialIso M × PartialIso M, IsInfinitePair a ∧ ∀ b ∈ C, b ≤ a := by
  let L := Prod.fst '' C
  let R := Prod.snd '' C
  have hL : IsChain (· ≤ ·) L := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.1) (fun h => h.1)
  have hR : IsChain (· ≤ ·) R := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.2) (fun h => h.2)
  obtain ⟨v, hv, _, hvi, hvf⟩ := exists_partialIso_chain_supremum e L hL (hne.image _)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e R hR (hne.image _)
  have hV (a) (ha : a ∈ C) : a.1 ≤ v := hv a.1 ⟨a, ha, rfl⟩
  have hW (a) (ha : a ∈ C) : a.2 ≤ w := hw a.2 ⟨a, ha, rfl⟩
  have hi : v.initial = w.initial := by
    apply le_antisymm
    · apply hvi _ w.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [(hC a ha).1]
      exact (hW a ha).1
    · apply hwi _ v.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [← (hC a ha).1]
      exact (hV a ha).1
  have hfv : v.final ≤ v.initial := by
    apply hvf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.1.trans (hV a ha).1
  have hfw : w.final ≤ v.initial := by
    apply hwf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.2.1.trans (hV a ha).1
  have hcross (a) (ha : a ∈ C) : a.1.final * w.final = 0 := by
    have hbound : w.final ≤ 1 - a.1.final := by
      apply hwf _ a.1.final_proj.one_sub
      rintro _ ⟨b, hb, rfl⟩
      have ho := infinitePair_cross_orthogonal hC hchain ha hb
      apply projection_le_complement_of_mul_zero b.2.final_proj a.1.final_proj
      simpa only [star_mul, a.1.final_proj.isSelfAdjoint.star_eq,
        b.2.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star ho
    exact HochschildTypeII.projection_orthogonal_of_le_complement a.1.final_proj
      w.final_proj hbound
  have hfinal : v.final ≤ 1 - w.final := by
    apply hvf _ w.final_proj.one_sub
    rintro _ ⟨a, ha, rfl⟩
    exact projection_le_complement_of_mul_zero a.1.final_proj w.final_proj (hcross a ha)
  have ho : v.final * w.final = 0 := by
    have h := (v.final_proj.le_iff_mul_eq_left w.final_proj.one_sub).mp hfinal
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  exact ⟨(v, w), ⟨hi, hfv, hfw, ho⟩, fun a ha => ⟨hV a ha, hW a ha⟩⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
