import OAI.Analysis.ModularTheory.CoreIntegrals

namespace OAI

/-! The character unitaries that implement the dual action of the real
modular crossed product. The two covariance formulas are on actual L²
operators; no dual weight or trace is postulated. -/

noncomputable section
open Filter MeasureTheory

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure ℝ)

lemma memLp_modularDual (r : ℝ) (f : Lp H 2 μ) :
    MemLp (fun t => BoundedRecovery.spectralCharacter r t • f t) 2 μ := by
  have hm : AEStronglyMeasurable
      (fun t => BoundedRecovery.spectralCharacter r t • f t) μ :=
    (BoundedRecovery.spectralCharacter r).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f)
  exact (Lp.memLp f).congr_norm hm (Eventually.of_forall fun t => by
    rw [norm_smul, BoundedRecovery.spectralCharacter_norm, one_mul])

def modularDual (r : ℝ) (f : Lp H 2 μ) : Lp H 2 μ :=
  (memLp_modularDual μ r f).toLp (fun t => BoundedRecovery.spectralCharacter r t • f t)

lemma modularDual_ae (r : ℝ) (f : Lp H 2 μ) :
    modularDual μ r f =ᵐ[μ] fun t => BoundedRecovery.spectralCharacter r t • f t :=
  MemLp.coeFn_toLp _

lemma modularDual_norm (r : ℝ) (f : Lp H 2 μ) : ‖modularDual μ r f‖ = ‖f‖ := by
  rw [modularDual, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (memLp_modularDual μ r f).aestronglyMeasurable
    (Lp.aestronglyMeasurable f)
  filter_upwards [] with t
  simp only [norm_smul, BoundedRecovery.spectralCharacter_norm, one_mul]

lemma modularDual_add (r : ℝ) (f g : Lp H 2 μ) :
    modularDual μ r (f + g) = modularDual μ r f + modularDual μ r g := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ r (f + g), modularDual_ae μ r f,
    modularDual_ae μ r g, Lp.coeFn_add f g,
    Lp.coeFn_add (modularDual μ r f) (modularDual μ r g)] with t hfg hf hg ha hb
  simp only [hfg, ha, smul_add, hb, hf, hg, Pi.add_apply]

lemma modularDual_smul (r : ℝ) (a : ℂ) (f : Lp H 2 μ) :
    modularDual μ r (a • f) = a • modularDual μ r f := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ r (a • f), modularDual_ae μ r f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (modularDual μ r f)] with t haf hf ha hb
  rw [haf, ha, Pi.smul_apply, hb, Pi.smul_apply, hf]
  exact smul_comm _ _ _

lemma modularDual_comp (r s : ℝ) (f : Lp H 2 μ) :
    modularDual μ r (modularDual μ s f) = modularDual μ (r + s) f := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ r (modularDual μ s f), modularDual_ae μ s f,
    modularDual_ae μ (r + s) f] with t hr hs hrs
  rw [hr, hs, hrs, smul_smul, BoundedRecovery.spectralCharacter_add]
  rfl

@[simp] lemma modularDual_zero (f : Lp H 2 μ) : modularDual μ 0 f = f := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ 0 f] with t ht
  simpa only [BoundedRecovery.spectralCharacter_zero,
    BoundedContinuousFunction.coe_one, Pi.one_apply, one_smul] using ht

def modularDualUnitary (r : ℝ) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := modularDual μ r
  invFun := modularDual μ (-r)
  left_inv f := by rw [modularDual_comp, neg_add_cancel, modularDual_zero]
  right_inv f := by rw [modularDual_comp, add_neg_cancel, modularDual_zero]
  map_add' := modularDual_add μ r
  map_smul' a f := by simpa only [RingHom.id_apply] using modularDual_smul μ r a f
  norm_map' := modularDual_norm μ r

variable [CompleteSpace H]

lemma modularDual_coefficient (D : BoundedRecovery.RealSpectralCalculus H)
    (r : ℝ) (T : H →L[ℂ] H) (f : Lp H 2 μ) :
    modularDual μ r (modularLpRepresentation μ D T f) =
      modularLpRepresentation μ D T (modularDual μ r f) := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ r (modularLpRepresentation μ D T f),
    modularLpRepresentation_ae μ D T f,
    modularLpRepresentation_ae μ D T (modularDual μ r f), modularDual_ae μ r f]
    with t hleft hT hright hf
  rw [hleft, hT, hright, hf]
  simp only [map_smul]

lemma spectralCharacter_translation (r t s : ℝ) :
    BoundedRecovery.spectralCharacter r s *
        BoundedRecovery.spectralCharacter (-r) (s - t) =
      BoundedRecovery.spectralCharacter r t := by
  simp only [BoundedRecovery.spectralCharacter_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [CompleteSpace H] in
lemma modularDual_translation [Measure.IsAddRightInvariant μ]
    (r t : ℝ) (f : Lp H 2 μ) :
    modularDual μ r (modularLpTranslate μ t (modularDual μ (-r) f)) =
      BoundedRecovery.spectralCharacter r t • modularLpTranslate μ t f := by
  apply Lp.ext
  filter_upwards [modularDual_ae μ r (modularLpTranslate μ t (modularDual μ (-r) f)),
    modularLpTranslate_ae μ t (modularDual μ (-r) f),
    (measurePreserving_sub_right μ t).quasiMeasurePreserving.ae (modularDual_ae μ (-r) f),
    Lp.coeFn_smul (BoundedRecovery.spectralCharacter r t) (modularLpTranslate μ t f),
    modularLpTranslate_ae μ t f] with s hleft hshift hf hsmul hright
  rw [hleft, hshift, hf, smul_smul, spectralCharacter_translation, hsmul, Pi.smul_apply, hright]

end WeakPureInfiniteness

end

end OAI
