import OAI.Analysis.IrrationalRotation.Analysis.RecursiveReturnTowerFits
import OAI.Analysis.IrrationalRotation.Rotation.RotationReturnTowers
import OAI.Analysis.IrrationalRotation.Rotation.RotationShrinkingBases

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace Invariant233.Rotation

theorem iterate_addRight_rotation (θ : ℝ) (n : ℕ) (x : Circle) :
    ((MeasurableEquiv.addRight (θ : Circle) : Circle ≃ᵐ Circle) : Circle → Circle)^[n] x =
      x + n • (θ : Circle) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [add_nsmul, add_assoc]

theorem exists_finiteReturnTower_of_hitting (θ : ℝ) (B : Set Circle)
    (hB : MeasurableSet B) (M : ℕ)
    (hreturn : ∀ x ∈ B, ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ x + n • (θ : Circle) ∈ B)
    (hback : ∀ z : Circle, ∃ k : ℕ, z - k • (θ : Circle) ∈ B) :
    ∃ P : FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)),
      P.returnBase = B ∧ ∀ i, (P.base i).Nonempty := by
  classical
  let I := {n : Fin (M + 1) // (ReturnTowers.returnBase (θ : Circle) B n.val).Nonempty}
  let h : I → ℕ := fun i => i.val.val
  let s : I → Set Circle := fun i => ReturnTowers.returnBase (θ : Circle) B (h i)
  have hpos (i : I) : 0 < h i := by
    obtain ⟨x, hx⟩ := i.property
    exact hx.2.1
  have hlevels (i : I) (k : Fin (h i)) :
      TowerItinerary.level (MeasurableEquiv.addRight (θ : Circle)) s h i k =
        ReturnTowers.level (θ : Circle) B (h i) k.val := by
    unfold TowerItinerary.level ReturnTowers.level
    congr 1
    funext x
    exact iterate_addRight_rotation θ k.val x
  let P : FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)) := {
    Index := I
    indexFintype := inferInstance
    height := h
    height_pos := hpos
    base := s
    returnBase := B
    base_measurable := fun i => ReturnTowers.measurableSet_returnBase _ hB (h i)
    bases_cover := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact hi.1
      · intro hx
        obtain ⟨n, hnM, hn⟩ := ReturnTowers.exists_returnBase hx (hreturn x hx)
        exact ⟨⟨⟨n, by omega⟩, x, hn⟩, hn⟩
    top_mem := by
      intro i x hx
      rw [iterate_addRight_rotation]
      exact hx.2.2.1
    no_return := by
      intro i x hx k hk hki
      rw [iterate_addRight_rotation]
      exact hx.2.2.2 k hk hki
    disjoint := by
      intro a b hab
      change Disjoint (TowerItinerary.level _ s h a.1 a.2)
        (TowerItinerary.level _ s h b.1 b.2)
      rw [hlevels, hlevels]
      apply ReturnTowers.level_disjoint a.2.isLt b.2.isLt
      intro heq
      have hheight : h a.1 = h b.1 := congrArg Prod.fst heq
      have hi : a.1 = b.1 := Subtype.ext (Fin.ext hheight)
      cases a with
      | mk i k =>
        cases b with
        | mk j l =>
          dsimp at hi hheight heq
          subst j
          have hk : k = l := Fin.ext (congrArg Prod.snd heq)
          exact hab (by cases hk; rfl)
    covers := by
      intro x
      obtain ⟨n, k, hn, hnM, hkn, hx⟩ :=
        ReturnTowers.exists_level_of_hitting hreturn hback x
      have hne : (ReturnTowers.returnBase (θ : Circle) B n).Nonempty := by
        obtain ⟨z, hz, _⟩ := hx
        exact ⟨z, hz⟩
      let i : I := ⟨⟨n, by omega⟩, hne⟩
      refine ⟨i, ⟨k, hkn⟩, ?_⟩
      rw [hlevels]
      exact hx }
  exact ⟨P, rfl, fun i => i.property⟩

theorem exists_raw_finiteReturnTowers {θ : ℝ} (hθ : Irrational θ) :
    ∃ raw : ℕ → FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)),
      Antitone (fun n => (raw n).returnBase) ∧
      (∀ n i, n + 1 ≤ (raw n).height i) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        ∀ x ∈ (raw n).returnBase, ∀ y ∈ (raw n).returnBase, dist x y < δ) := by
  obtain ⟨B, hB, hnest, _hclosure, hmesh, _hdisj, hshort, hhit⟩ :=
    exists_nested_open_bases hθ
  have hex (n : ℕ) : ∃ P : FiniteReturnTower (MeasurableEquiv.addRight (θ : Circle)),
      P.returnBase = B n ∧ ∀ i, (P.base i).Nonempty := by
    obtain ⟨M, hM⟩ := hhit n
    apply exists_finiteReturnTower_of_hitting θ (B n) (hB n).1.measurableSet M
    · exact fun x _ => (hM x).1
    · intro x
      obtain ⟨k, _, _, hk⟩ := (hM x).2
      exact ⟨k, hk⟩
  choose raw hraw hne using hex
  refine ⟨raw, ?_, ?_, ?_⟩
  · intro m n hmn
    simpa only [hraw] using hnest hmn
  · intro n i
    obtain ⟨x, hx⟩ := hne n i
    have hxB : x ∈ B n := by
      rw [← hraw n, ← (raw n).bases_cover]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hret := (raw n).top_mem i x hx
    rw [iterate_addRight_rotation, hraw n] at hret
    have hp := (raw n).height_pos i
    by_contra hn
    exact (hshort n x hxB ((raw n).height i) hp (by omega)).1 hret
  · intro δ hδ
    obtain ⟨N, hN⟩ := hmesh δ hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [hraw] using hN n hn

end Invariant233.Rotation

end

end OAI
