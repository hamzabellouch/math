import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductPacking

namespace OAI

/-! # Exact composition of a probe path and its bridge -/

namespace PolycyclicRecognition

variable {N D G : Type*} [Group N] [Group D] [Group G]

theorem factorTranslate_assoc (φ : D →* MulAut N) (p q z : N × D) :
    factorTranslate φ (factorTranslate φ p q) z =
      factorTranslate φ p (factorTranslate φ q z) := by
  apply Prod.ext
  · simp only [factorTranslate, map_mul, MulAut.mul_apply]
    exact mul_assoc _ _ _
  · exact mul_assoc _ _ _

theorem factor_bridge_projection (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u₂ ub : N) (d₂ db : D) (g : G) (hg : ι ub * κ db = g) :
    ι (u₂ * φ d₂ ub) * κ (d₂ * db) = (ι u₂ * κ d₂) * g := by
  exact (factorTranslate_projection φ ι κ hc (u₂, d₂) (ub, db)).trans (by rw [hg])

theorem factor_bridge_right_coordinate (φ : D →* MulAut N)
    (u₂ ub : N) (d₂ db : D) (z : N × D) :
    (u₂ * φ d₂ ub) * φ (d₂ * db) z.1 = u₂ * φ d₂ (ub * φ db z.1) := by
  exact congrArg Prod.fst (factorTranslate_assoc φ (u₂, d₂) (ub, db) z)

/-- Composition preserves a uniform right-cell restriction after the
bridge's exponential error has been absorbed. -/
theorem exists_thickened_factor_bridge {V I Q : Type*}
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (Exp : V → N) (ExpI : I → N) (qsec : Q → N)
    (small : V → Prop) (ideal : I → Prop) (DB DF : D → Prop)
    (cell : Set (N × D)) (u₂ : N) (d₂ : D) (g : G)
    (habsorb : ∀ v, small v → ∃ i q,
      u₂ * φ d₂ (Exp v) = ExpI i * qsec q ∧ ideal i)
    (hD : ∀ d, DB d → DF (d₂ * d))
    (hbridge : ∃ ub db, ι ub * κ db = g ∧ ∀ z ∈ cell,
      (∃ v, Exp v = ub * φ db z.1 ∧ small v) ∧ DB (db * z.2)) :
    ∃ u d, ι u * κ d = (ι u₂ * κ d₂) * g ∧ ∀ z ∈ cell,
      (∃ i q, u * φ d z.1 = ExpI i * qsec q ∧ ideal i) ∧ DF (d * z.2) := by
  obtain ⟨ub, db, hg, hb⟩ := hbridge
  refine ⟨u₂ * φ d₂ ub, d₂ * db,
    factor_bridge_projection φ ι κ hc u₂ ub d₂ db g hg, ?_⟩
  intro z hz
  obtain ⟨⟨v, hv, hs⟩, hd⟩ := hb z hz
  obtain ⟨i, q, he, hi⟩ := habsorb v hs
  refine ⟨⟨i, q, ?_, hi⟩, ?_⟩
  · rw [factor_bridge_right_coordinate, ← hv]
    exact he
  · simpa only [mul_assoc] using hD (db * z.2) hd

end PolycyclicRecognition

end OAI
