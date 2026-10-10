import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction

namespace OAI

/-!+# The two product charts of the space of quasi-inverse pairs

Target normalization gives `G × X`; inverse normalization gives `X × G`,
where the latter copy of `X` represents inverse maps. Their transition is
an actual homeomorphism. This is the geometric coordinate change used for
the inverse-coupling measure, before any disintegration or fiber averaging.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- All pairs with the fixed coarse bounds, without basepoint normalization. -/
abbrev CoarsePair (G : Type*) [MetricSpace G] (Λ : ℝ≥0) :=
  {p : C(G, G) × C(G, G) // LipschitzPairBounds G Λ p}

def targetTranslatePair (z : G) (p : C(G, G) × C(G, G)) : C(G, G) × C(G, G) :=
  (⟨fun t => z * p.1 t, continuous_const.mul p.1.continuous⟩,
    ⟨fun t => p.2 (z⁻¹ * t), p.2.continuous.comp (continuous_const.mul continuous_id)⟩)

omit [ProperSpace G] in
theorem targetTranslatePair_bounds (z : G) (p : CoarsePair G Λ) :
    LipschitzPairBounds G Λ (targetTranslatePair z p.val) := by
  obtain ⟨hF, hB, hlF, hlB, hBF, hFB⟩ := p.property
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (z * p.val.1 t) (z * p.val.1 u) ≤ _
    simpa only [dist_mul_left] using hF.dist_le_mul t u
  · apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (p.val.2 (z⁻¹ * t)) (p.val.2 (z⁻¹ * u)) ≤ _
    simpa only [dist_mul_left] using hB.dist_le_mul (z⁻¹ * t) (z⁻¹ * u)
  · intro t u
    change _ ≤ dist (z * p.val.1 t) (z * p.val.1 u)
    simpa only [dist_mul_left] using hlF t u
  · intro t u
    change _ ≤ dist (p.val.2 (z⁻¹ * t)) (p.val.2 (z⁻¹ * u))
    simpa only [dist_mul_left] using hlB (z⁻¹ * t) (z⁻¹ * u)
  · intro t
    change dist (p.val.2 (z⁻¹ * (z * p.val.1 t))) t ≤ Λ
    simpa only [inv_mul_cancel_left] using hBF t
  · intro t
    change dist (z * p.val.1 (p.val.2 (z⁻¹ * t))) t ≤ Λ
    rw [← dist_mul_left z⁻¹]
    simpa only [inv_mul_cancel_left] using hFB (z⁻¹ * t)

def targetTranslate (z : G) (p : CoarsePair G Λ) : CoarsePair G Λ :=
  ⟨targetTranslatePair z p.val, targetTranslatePair_bounds z p⟩

omit [IsIsometricSMul G G] in
theorem continuous_targetTranslatePair :
    Continuous (fun q : G × (C(G, G) × C(G, G)) => targetTranslatePair q.1 q.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.1 * q.1.2.1 q.2)
    fun_prop
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.2.2 (q.1.1⁻¹ * q.2))
    fun_prop

/-- Swapping the two maps preserves all six bounds. -/
def swapCoarsePair : CoarsePair G Λ ≃ₜ CoarsePair G Λ where
  toFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.2.1, p.property.2.2.1, p.property.2.2.2.2.2, p.property.2.2.2.2.1⟩
  invFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.2.1, p.property.2.2.1, p.property.2.2.2.2.2, p.property.2.2.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _
  continuous_invFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _

/-- The first global product chart is target translation of a normalized pair. -/
def pairTargetChart : (G × NormalizedPair G Λ) ≃ₜ CoarsePair G Λ where
  toFun q := targetTranslate q.1 ⟨q.2.val, q.2.property.1⟩
  invFun p := (p.val.1 1, normalizePair p.val p.property)
  left_inv q := by
    apply Prod.ext
    · change q.1 * q.2.val.1 1 = q.1
      rw [q.2.property.2, mul_one]
    · apply Subtype.ext
      apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
        simp [targetTranslate, targetTranslatePair, normalizePair, translatePair, q.2.property.2]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
      simp [targetTranslate, targetTranslatePair, normalizePair, translatePair]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_targetTranslatePair.comp
      (continuous_fst.prodMk continuous_snd.subtype_val)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (continuous_eval_const 1).comp continuous_subtype_val.fst
    · apply Continuous.subtype_mk
      exact continuous_translatePair.comp (continuous_const.prodMk continuous_subtype_val)

/-- The second product chart parametrizes inverse-normalized pairs. It is
obtained by swapping maps, with the inverse on the group coordinate. -/
def pairSourceChart : (NormalizedPair G Λ × G) ≃ₜ CoarsePair G Λ :=
  ((Homeomorph.prodComm _ _).trans
    ((Homeomorph.inv G).prodCongr (Homeomorph.refl _))).trans
      (pairTargetChart.trans swapCoarsePair)

/-- The exact coordinate change underlying the inverse coupling. -/
def pairChartTransition : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) :=
  pairTargetChart.trans pairSourceChart.symm

theorem pairSourceChart_forward (p : NormalizedPair G Λ) (x t : G) :
    (pairSourceChart (p, x)).val.1 t = p.val.2 (x * t) := by
  change p.val.2 (x⁻¹⁻¹ * t) = _
  rw [inv_inv]

theorem pairSourceChart_inverse (p : NormalizedPair G Λ) (x t : G) :
    (pairSourceChart (p, x)).val.2 t = x⁻¹ * p.val.1 t := rfl

theorem pairChartTransition_group (z : G) (p : NormalizedPair G Λ) :
    (pairChartTransition (z, p)).2 = (p.val.2 z⁻¹)⁻¹ := by
  change (p.val.2 (z⁻¹ * 1))⁻¹ = _
  rw [mul_one]

theorem pairChartTransition_forward (z : G) (p : NormalizedPair G Λ) (t : G) :
    (pairChartTransition (z, p)).1.val.1 t =
      (p.val.2 z⁻¹)⁻¹ * p.val.2 (z⁻¹ * t) := by
  change (p.val.2 (z⁻¹ * 1))⁻¹ * p.val.2 (z⁻¹ * (1 * t)) = _
  simp only [mul_one, one_mul]

theorem pairChartTransition_inverse (z : G) (p : NormalizedPair G Λ) (t : G) :
    (pairChartTransition (z, p)).1.val.2 t =
      z * p.val.1 (p.val.2 z⁻¹ * t) := by
  change (1 : G)⁻¹ * (z * p.val.1 (p.val.2 (z⁻¹ * 1) * t)) = _
  simp only [mul_one, inv_one, one_mul]

end PolycyclicRecognition

end

end OAI
