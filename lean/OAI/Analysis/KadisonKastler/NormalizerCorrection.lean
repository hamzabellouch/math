import OAI.Analysis.KadisonKastler.NormalizerAveraging

namespace OAI

/-! # Quadratic correction while preserving normalizers

Averages are corrected inside the algebra and its commutant before they
are multiplied. The iteration therefore takes place in the complete space
of normalizing families, not in all ambient unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

private theorem product_defect_of_near_averages
    {B : Type*} [CStarAlgebra B] (u v w : unitary B) (a b c : B)
    {r s : ℝ} (hu : ‖(u : B) - a‖ ≤ r)
    (hv : ‖(v : B) - b‖ ≤ r) (hw : ‖(w : B) - c‖ ≤ r)
    (ha : ‖a‖ ≤ 1) (hprod : ‖a * b - c‖ ≤ s) :
    ‖(u : B) * (v : B) - (w : B)‖ ≤ 3 * r + s := by
  have hid : (u : B) * (v : B) - (w : B) =
      ((u : B) - a) * (v : B) + a * ((v : B) - b) + (a * b - c) + (c - (w : B)) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖((u : B) - a) * (v : B)‖ + ‖a * ((v : B) - b)‖ +
        ‖a * b - c‖ + ‖c - (w : B)‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ r + r + s + r := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (by simpa only [CStarRing.norm_mul_coe_unitary] using hu)
            ((norm_mul_le _ _).trans
              ((mul_le_mul ha hv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
        · exact hprod
      · simpa only [norm_sub_rev] using hw
    _ = _ := by ring

private theorem scaled_normalizer_estimates {e f a : ℝ} (he : 0 ≤ e)
    (hf : f ≤ 580 * e ^ 2) (ha : a ≤ e + 192 * e ^ 2) :
    64 * f ≤ 16 * (64 * e) ^ 2 ∧ a ≤ 64 * e + 4 * (64 * e) ^ 2 := by
  constructor <;> nlinarith only [he, hf, ha, sq_nonneg e]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance normalizerCorrectionCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- One averaging step stays in the normalizer group and has quadratic
multiplicative defect. -/
theorem exists_normalizing_quadratic_step
    (hpub : PublishedNormalizerFactorization (H := H)) (P : VonNeumannAlgebra H)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (H →L[ℂ] H))) g f) = m.toCLM f)
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (V : unitary (G →ᵇ (H →L[ℂ] H)))
    (hV : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) V g) P P)
    (hsmall : 4 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V < 1) :
    ∃ W : unitary (G →ᵇ (H →L[ℂ] H)),
      (∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) W g) P P) ∧
      unitaryCocycleDefect (B := H →L[ℂ] H) 1 W ≤ 580 * (unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) ^ 2 ∧
      dist V W ≤ unitaryCocycleDefect (B := H →L[ℂ] H) 1 V + 192 * (unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) ^ 2 := by
  let α : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := 1
  let X := boundedBoundaryTransport α V
  let e := unitaryCocycleDefect (B := H →L[ℂ] H) α V
  have he : 0 ≤ e := unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) α V
  have hX (g t : G) : Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) (X g) t) P P := by
    have h := (hV (g⁻¹ * t)).symm.trans (hV t)
    exact h
  have hnear (g t : G) : ‖(X g).val t - (unitaryFamilyEval (B := H →L[ℂ] H) V g : H →L[ℂ] H)‖ ≤ e :=
    norm_boundaryTransport_sub_le α (unitaryFamilyEval (B := H →L[ℂ] H) V)
      (norm_unitaryCocycleError_le α V) g t
  have hex (g : G) := exists_normalizer_near_mean hpub P m hpres (X g)
    (hX g) (unitaryFamilyEval (B := H →L[ℂ] H) V g) (hV g) he hsmall (hnear g)
  choose w hw hwm using hex
  let W := boundedUnitaryFamily w
  have hAnorm (g : G) : ‖m.toCLM (X g).val‖ ≤ 1 :=
    (m.norm_le _).trans (norm_unitary_le_one (X g))
  have hmean (g k : G) : ‖m.toCLM (X (g * k)).val -
      m.toCLM (X g).val * m.toCLM (X k).val‖ ≤ 4 * e ^ 2 := by
    exact m.norm_averaged_defect_le_four_mul_sq (fun g => α g) (boundaryTranslate α)
      (by intro g f; exact hm g f) (boundaryTranslate_constant α) X
      (unitaryFamilyEval (B := H →L[ℂ] H) V) (boundedBoundaryTransport_factor α V) he
      (norm_boundedBoundaryTransport_sub_le α V) g k
  have hnew (g k : G) : ‖(w g : H →L[ℂ] H) * (w k : H →L[ℂ] H) -
      (w (g * k) : H →L[ℂ] H)‖ ≤ 580 * e ^ 2 := by
    have h := product_defect_of_near_averages (w g) (w k) (w (g * k))
      (m.toCLM (X g).val) (m.toCLM (X k).val) (m.toCLM (X (g * k)).val)
      (hwm g) (hwm k) (hwm (g * k))
      (hAnorm g) (by simpa only [norm_sub_rev] using hmean g k)
    convert h using 1
    ring
  refine ⟨W, hw, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    rintro ⟨g, k⟩
    exact hnew g k
  · simp only [Subtype.dist_eq, dist_eq_norm]
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have hmnear := m.norm_sub_le (X g).val (V.val g)
      (norm_boundedBoundaryTransport_sub_le α V g)
    have hn := norm_sub_le_norm_sub_add_norm_sub (w g : H →L[ℂ] H)
      (m.toCLM (X g).val) (V.val g)
    have hh := hn.trans (add_le_add (hwm g) hmnear)
    change ‖V.val g - (w g : H →L[ℂ] H)‖ ≤ e + 192 * e ^ 2
    rw [norm_sub_rev]
    exact hh.trans_eq (add_comm _ _)

/-- Uniform iteration corrects the selected normalizers to an exact group
representation, still inside the normalizer group at every parameter. -/
theorem exists_normalizing_representation
    (hpub : PublishedNormalizerFactorization (H := H)) (P : VonNeumannAlgebra H)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (H →L[ℂ] H))) g f) = m.toCLM f)
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (V : unitary (G →ᵇ (H →L[ℂ] H)))
    (hV : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) V g) P P)
    (hsmall : unitaryCocycleDefect (B := H →L[ℂ] H) 1 V ≤ 1 / 4096) :
    ∃ z : G →* unitary (H →L[ℂ] H),
      (∀ g : G, Conjugates (z g) P P) ∧
      ∀ g, ‖(z g : H →L[ℂ] H) - V.val g‖ ≤ 128 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V := by
  let d : NormalizingFamily (G := G) P → ℝ := fun X => 64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val
  have hd : Continuous d := continuous_const.mul
    ((continuous_unitaryCocycleDefect (B := H →L[ℂ] H) 1).comp continuous_subtype_val)
  have hd0 (X : NormalizingFamily (G := G) P) : 0 ≤ d X :=
    mul_nonneg (by norm_num) (unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) 1 X.val)
  have hstep (X : NormalizingFamily (G := G) P) (hX : d X ≤ 1 / 64) :
      ∃ Y, d Y ≤ 16 * (d X) ^ 2 ∧ dist X Y ≤ d X + 4 * (d X) ^ 2 := by
    have he := unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) 1 X.val
    have hXe : unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val ≤ 1 / 4096 := by
      change 64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val ≤ _ at hX
      linarith only [hX]
    obtain ⟨W, hW, hn, hdist⟩ := exists_normalizing_quadratic_step hpub P m hm hpres
      X.val X.property (by linarith)
    refine ⟨⟨W, hW⟩, ?_, ?_⟩
    · exact (scaled_normalizer_estimates he hn hdist).1
    · exact (scaled_normalizer_estimates he hn hdist).2
  let X₀ : NormalizingFamily (G := G) P := ⟨V, hV⟩
  obtain ⟨Y, hY, hdist⟩ := exists_zero_of_quadratic_improvement d hd hd0 hstep X₀
    (by change 64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V ≤ _; linarith)
  have hzero : unitaryCocycleDefect (B := H →L[ℂ] H) 1 Y.val = 0 := by
    change 64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 Y.val = 0 at hY
    linarith
  have hlaw := (unitaryCocycleDefect_eq_zero_iff (B := H →L[ℂ] H) 1 Y.val).mp hzero
  let z : G →* unitary (H →L[ℂ] H) :=
    { toFun := unitaryFamilyEval (B := H →L[ℂ] H) Y.val
      map_one' := by
        apply mul_left_cancel (a := unitaryFamilyEval (B := H →L[ℂ] H) Y.val 1)
        apply Subtype.ext
        have h := hlaw 1 1
        simp only [MonoidHom.one_apply, StarAlgEquiv.one_apply, one_mul] at h
        exact h
      map_mul' g k := by
        apply Subtype.ext
        exact (hlaw g k).symm }
  refine ⟨z, Y.property, ?_⟩
  intro g
  have hn := (V.val - Y.val.val).norm_coe_le_norm g
  have hb : ‖V.val - Y.val.val‖ ≤ 128 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V := by
    have hh : ‖V.val - Y.val.val‖ ≤
        2 * (64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) := by
      change dist V Y.val ≤ _ at hdist
      simpa only [d, X₀, Subtype.dist_eq, dist_eq_norm] using hdist
    linarith
  change ‖Y.val.val g - V.val g‖ ≤ _
  rw [norm_sub_rev]
  exact hn.trans hb

end

end KadisonKastler

end OAI
