import Mathlib
import OAI.Computability.VertexCover.Reduction.ListHitMaximum
import OAI.Computability.VertexCover.Reduction.FiniteMeanUnionBound

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

open scoped Classical in
theorem pairEvents_card_eq_sum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    ((Φ.pairEvents L seed J).card : ℝ) =
      ∑ e : ↥(internalPairs J), VertexCover.truthValue (Φ.PairSeedHit L seed e.1) := by
  classical
  rw [← Finset.sum_subtype (internalPairs J) (fun _ => Iff.rfl)
    (fun e : PositionPair d => VertexCover.truthValue (Φ.PairSeedHit L seed e))]
  simp only [pairEvents, internalPairs, Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hj : e.1.1 ∈ J <;> by_cases hk : e.1.2 ∈ J <;>
    by_cases hh : Φ.PairSeedHit L seed e <;> simp [VertexCover.truthValue, hj, hk, hh]

theorem decoding_upper_bound (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d) (hL : ∀ i, (L i).length ≤ ell)
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) :
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      (Φ.listHitMaximum L (Φ.spliceSeeds J frozen hidden) J : ℝ)) ≤
      1 + (J.card.choose 2 : ℝ) * (ell : ℝ)^2 * σ := by
  classical
  let : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  have h := VertexCover.finiteMean_union_bound
    (fun hidden : Φ.HiddenSeeds J => (Φ.listHitMaximum L (Φ.spliceSeeds J frozen hidden) J : ℝ))
    (fun (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J)) =>
      VertexCover.truthValue (Φ.PairSeedHit L (Φ.spliceSeeds J frozen hidden) e.1))
    ((ell : ℝ)^2 * σ) ?_ (fun e => Φ.pairEvent_mean_le hval L hL J frozen e)
  · simpa only [Fintype.card_coe, internalPairs_card, mul_assoc] using h
  · intro hidden
    have hpoint := Nat.cast_le (α := ℝ).mpr
      (Φ.listHitMaximum_le L (Φ.spliceSeeds J frozen hidden) J)
    simpa only [Nat.cast_add, Nat.cast_one, Φ.pairEvents_card_eq_sum] using hpoint

end VertexCover.LabelCover

namespace VertexCover.LabelCover

theorem norm_sub_rev (Φ : LabelCover) {d : ℕ} (x y : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (x-y) = Φ.compatibilityNorm (y-x) := by
  rw [← Φ.norm_neg (y-x)]
  congr 1
  funext p
  simp

theorem norm_sub_triangle (Φ : LabelCover) {d : ℕ} (x y z : Φ.Coordinate d → ℝ) :
    Φ.compatibilityNorm (x-z) ≤ Φ.compatibilityNorm (x-y) + Φ.compatibilityNorm (y-z) := by
  have h := Φ.norm_add_le (x-y) (y-z)
  simpa only [sub_add_sub_cancel] using h

noncomputable def distanceTo (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) : ℝ :=
  A.inf' hA (fun a => Φ.compatibilityNorm (x-a))

theorem distanceTo_nonneg (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) :
    0 ≤ Φ.distanceTo A hA x := by
  exact Finset.le_inf' _ _ (fun _ _ => Φ.norm_nonneg _)

theorem distanceTo_le (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x a : Φ.Coordinate d → ℝ)
    (ha : a ∈ A) : Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-a) := by
  exact Finset.inf'_le _ ha

theorem distanceTo_self (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ)
    (hx : x ∈ A) : Φ.distanceTo A hA x = 0 := by
  apply le_antisymm _ (Φ.distanceTo_nonneg A hA x)
  have h := Φ.distanceTo_le A hA x x hx
  rw [sub_self] at h
  exact h.trans_eq (Φ.norm_zero d)

theorem distanceTo_triangle (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x y : Φ.Coordinate d → ℝ) :
    Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-y) + Φ.distanceTo A hA y := by
  obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_inf' hA
    (fun a => Φ.compatibilityNorm (y-a))
  calc
    Φ.distanceTo A hA x ≤ Φ.compatibilityNorm (x-a) := Φ.distanceTo_le A hA x a ha
    _ ≤ Φ.compatibilityNorm (x-y) + Φ.compatibilityNorm (y-a) := Φ.norm_sub_triangle x y a
    _ = Φ.compatibilityNorm (x-y) + Φ.distanceTo A hA y := by rw [← heq]; rfl

noncomputable def separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) : ℝ :=
  (Φ.distanceTo A hA (-x) - Φ.distanceTo A hA x) / 2

theorem separator_odd (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x : Φ.Coordinate d → ℝ) :
    Φ.separator A hA (-x) = -Φ.separator A hA x := by
  simp only [separator, neg_neg]
  ring

theorem separator_zero (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Φ.separator A hA 0 = 0 := by simp [separator]

theorem separator_lipschitz (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (x y : Φ.Coordinate d → ℝ) :
    |Φ.separator A hA x - Φ.separator A hA y| ≤ Φ.compatibilityNorm (x-y) := by
  have hxy := Φ.distanceTo_triangle A hA x y
  have hyx := Φ.distanceTo_triangle A hA y x
  have hnxy := Φ.distanceTo_triangle A hA (-x) (-y)
  have hnyx := Φ.distanceTo_triangle A hA (-y) (-x)
  have hn : -x - -y = y-x := by abel
  have hn' : -y - -x = x-y := by abel
  rw [hn, ← Φ.norm_sub_rev x y] at hnxy
  rw [hn'] at hnyx
  rw [← Φ.norm_sub_rev x y] at hyx
  unfold separator
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem separator_pos_on (Φ : LabelCover) {d : ℕ} {t : ℝ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, 2*t < Φ.compatibilityNorm (x+y))
    (x : Φ.Coordinate d → ℝ) (hx : x ∈ A) : t < Φ.separator A hA x := by
  have hdist : 2*t < Φ.distanceTo A hA (-x) := by
    obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf' hA
      (fun y => Φ.compatibilityNorm (-x-y))
    rw [distanceTo, heq]
    have hn : -x-y = -(x+y) := by abel
    rw [hn, Φ.norm_neg]
    exact hsep x hx y hy
  rw [separator, Φ.distanceTo_self A hA x hx]
  linarith

noncomputable def highVectors (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Finset (Φ.Vertex d)) : Finset (Φ.Coordinate d → ℝ) := by
  classical
  exact (A.filter (fun v => t < Φ.compatibilityNorm (Φ.sumVector v))).image Φ.sumVector

theorem highVectors_separated (Φ : LabelCover) {d : ℕ} (t : ℝ)
    (A : Finset (Φ.Vertex d)) (hA : (Φ.graph d t).IsIndepSet (A : Set (Φ.Vertex d))) :
    ∀ x ∈ Φ.highVectors t A, ∀ y ∈ Φ.highVectors t A,
      2*t < Φ.compatibilityNorm (x+y) := by
  classical
  intro x hx y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hvA, hv⟩ := Finset.mem_filter.mp hv
  obtain ⟨hwA, _⟩ := Finset.mem_filter.mp hw
  by_cases heq : v = w
  · subst w
    have htwice : Φ.sumVector v + Φ.sumVector v = fun p => (2 : ℝ) * Φ.sumVector v p := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [htwice, Φ.norm_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · have hn := (SimpleGraph.isIndepSet_iff _).mp hA hvA hwA heq
    exact lt_of_not_ge (fun h => hn ⟨heq, h⟩)

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
