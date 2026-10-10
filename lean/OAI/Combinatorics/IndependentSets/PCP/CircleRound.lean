import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LabelCoverData

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

lemma tupleExtension_odd {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) :
    tupleExtension S A q (torusAntipode x) = -tupleExtension S A q x := by
  classical
  exact finiteOddExtension_odd _ _ _ _ torusAntipode_involutive _

lemma tupleExtension_lipschitz {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) : LipschitzWith 64 (tupleExtension S A q) := by
  classical
  exact finiteOddExtension_lipschitz _ _ _ _ torusAntipode_isometry

lemma tupleExtension_on_grid {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A)
    (q : Q) (u : M q → ZMod D) :
    tupleExtension S (location '' A) q (torusGrid u) = gridBump S (location '' A) ⟨q, u⟩ := by
  classical
  obtain ⟨hb, ho, _, _, hl⟩ := grid_independent_bump S hD hnoclique location A hA
  apply finiteOddExtension_on_grid torusGrid _ 64 torusAntipode
    (fun x k => x k + ((D / 2 : ℕ) : ZMod D)) (torusGrid_antipode hD)
  · intro x y
    have h := hl q x y
    change |gridBump S (location '' A) ⟨q, x⟩ - gridBump S (location '' A) ⟨q, y⟩| ≤
      (64 : ℝ) * dist (torusGrid x) (torusGrid y)
    have hh : ENNReal.ofReal |gridBump S (location '' A) ⟨q, x⟩ - gridBump S (location '' A) ⟨q, y⟩| ≤
        ENNReal.ofReal (64 * dist (torusGrid x) (torusGrid y)) := by
      convert h using 1 <;> simp [edist_dist, Real.dist_eq, ENNReal.ofReal_mul]
      rfl
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) dist_nonneg)).mp hh
  · intro x
    exact hb ⟨q, x⟩
  · intro x
    exact ho ⟨q, x⟩

lemma circle_dist_coe_le (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x - y)
  simpa only [← AddCircle.coe_sub, dist_eq_norm, Real.norm_eq_abs] using h

noncomputable def circleRound (D : ℕ) (x : UnitAddCircle) : ZMod D :=
  (⌊(D : ℝ) * circleRep x⌋₊ : ZMod D)

lemma circleRound_close (D : ℕ) [NeZero D] (x : UnitAddCircle) :
    dist x (ZMod.toAddCircle (circleRound D x)) < 1 / (D : ℝ) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast (NeZero.pos D)
  have h₁ := Nat.floor_le (mul_nonneg hD.le (circleRep_nonneg x))
  have h₂ := Nat.lt_floor_add_one ((D : ℝ) * circleRep x)
  have ha : (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D ≤ circleRep x := by
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hb : circleRep x - (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D < 1 / D := by
    apply (lt_div_iff₀ hD).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
    nlinarith
  unfold circleRound
  rw [ZMod.toAddCircle_natCast]
  calc
    _ = dist (circleRep x : UnitAddCircle)
        (((⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / (D : ℝ) : ℝ) : UnitAddCircle) := by rw [circleRep_coe]
    _ ≤ |circleRep x - (⌊(D : ℝ) * circleRep x⌋₊ : ℝ) / D| := circle_dist_coe_le _ _
    _ < 1 / (D : ℝ) := by rw [abs_of_nonneg (sub_nonneg.mpr ha)]; exact hb

noncomputable def torusRound {ι : Type*} (D : ℕ) (x : ι → UnitAddCircle) : ι → ZMod D :=
  fun k => circleRound D (x k)

lemma torusRound_close {ι : Type*} [Fintype ι] (D : ℕ) [NeZero D]
    (x : ι → UnitAddCircle) : dist x (torusGrid (torusRound D x)) ≤ 1 / (D : ℝ) := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 1 / (D : ℝ))).mpr
  intro k
  exact (circleRound_close D (x k)).le

lemma pullback_dist_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : ι → κ) (x y : κ → UnitAddCircle) : dist (x ∘ π) (y ∘ π) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  exact dist_le_pi_dist x y (π k)

theorem tupleExtension_compatibility {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (hnoclique : ∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8))
    {V : Type*} (location : V → GridLocation M D) (A : Set V)
    (hA : (gridGraph S hD location).IsIndepSet A)
    {q q' : Q} (π : M q → M q')
    (hpath : ∀ v : M q' → ZMod D,
      pathDistance S.linkLength ⟨q, v ∘ π⟩ ⟨q', v⟩ = 0)
    (x : M q' → UnitAddCircle) :
    |tupleExtension S (location '' A) q' x - tupleExtension S (location '' A) q (x ∘ π)| ≤
      2 * 64 / (D : ℝ) := by
  let y := torusRound D x
  have hy := torusRound_close D x
  have hπ := (pullback_dist_le π x (torusGrid y)).trans hy
  have heq : tupleExtension S (location '' A) q (torusGrid y ∘ π) =
      tupleExtension S (location '' A) q' (torusGrid y) := by
    rw [show torusGrid y ∘ π = torusGrid (y ∘ π) from rfl,
      tupleExtension_on_grid S hD hnoclique location A hA,
      tupleExtension_on_grid S hD hnoclique location A hA]
    let := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
    have hT : Isometry (gridAntipode : GridLocation M D → GridLocation M D) :=
      pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
        (linkLength_antipode S hD)
    have hf : LipschitzWith 64 (gridBump S (location '' A)) :=
      oddBump_lipschitz gridAntipode hT (location '' A)
    have h := hf ⟨q, y ∘ π⟩ ⟨q', y⟩
    change edist _ _ ≤ (64 : ℝ≥0∞) * pathDistance S.linkLength _ _ at h
    rw [hpath y, mul_zero] at h
    exact edist_eq_zero.mp (le_antisymm h bot_le)
  have h₁ := ((tupleExtension_lipschitz S (location '' A) q').dist_le_mul x (torusGrid y)).trans
    (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 64))
  have h₂ := ((tupleExtension_lipschitz S (location '' A) q).dist_le_mul (x ∘ π) (torusGrid y ∘ π)).trans
    (mul_le_mul_of_nonneg_left hπ (by norm_num : (0 : ℝ) ≤ 64))
  rw [heq] at h₂
  simp only [Real.dist_eq, NNReal.coe_ofNat] at h₁ h₂
  have h := abs_sub_le (tupleExtension S (location '' A) q' x)
    (tupleExtension S (location '' A) q' (torusGrid y))
    (tupleExtension S (location '' A) q (x ∘ π))
  rw [abs_sub_comm (tupleExtension S (location '' A) q' (torusGrid y))] at h
  calc
    _ ≤ _ := h.trans (add_le_add h₁ h₂)
    _ = 2 * 64 / (D : ℝ) := by ring

end LargeIndependentSets

end OAI
