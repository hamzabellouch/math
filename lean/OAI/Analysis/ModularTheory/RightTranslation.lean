import OAI.Analysis.ModularTheory.CoreDualAction

namespace OAI

/-! The commuting right regular translations in the concrete modular
representation. These are the commutant operators used to analyze the
compression to scalar functions times the distinguished modular vector. -/

noncomputable section
open MeasureTheory

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (D : BoundedRecovery.RealSpectralCalculus H)

def modularRightTranslation (s : ℝ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  pointwiseLpRepresentation μ (D.unitary s) *
    (modularLpTranslateEquiv (H := H) μ (-s) : Lp H 2 μ →L[ℂ] Lp H 2 μ)

lemma modularRightTranslation_ae (s : ℝ) (f : Lp H 2 μ) :
    modularRightTranslation μ D s f =ᵐ[μ] fun t => D.unitary s (f (t + s)) := by
  filter_upwards [(D.unitary s).coeFn_compLpL (p := 2) (μ := μ)
      (modularLpTranslate μ (-s) f), modularLpTranslate_ae μ (-s) f] with t hD hf
  change ((D.unitary s).compLpL 2 μ (modularLpTranslate μ (-s) f)) t = _
  rw [hD, hf, sub_neg_eq_add]

lemma modularRightTranslation_norm (s : ℝ) (f : Lp H 2 μ) :
    ‖modularRightTranslation μ D s f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have he : eLpNorm (modularRightTranslation μ D s f) 2 μ =
      eLpNorm (modularLpTranslate μ (-s) f) 2 μ := by
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _)
    filter_upwards [(D.unitary s).coeFn_compLpL (p := 2) (μ := μ)
      (modularLpTranslate μ (-s) f)] with t ht
    change ‖((D.unitary s).compLpL 2 μ (modularLpTranslate μ (-s) f)) t‖ = _
    rw [ht, D.norm_unitary_apply]
  rw [he]
  change ‖modularLpTranslate μ (-s) f‖ = ‖f‖
  exact (modularLpTranslate μ (-s)).norm_map f

lemma modularRightTranslation_comp (s t : ℝ) (f : Lp H 2 μ) :
    modularRightTranslation μ D s (modularRightTranslation μ D t f) =
      modularRightTranslation μ D (s + t) f := by
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ D s (modularRightTranslation μ D t f),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (modularRightTranslation_ae μ D t f),
    modularRightTranslation_ae μ D (s + t) f] with r hs ht hst
  rw [hs, ht, hst, D.unitary_add, mul_apply_eq_comp]
  congr 3
  ring

@[simp] lemma modularRightTranslation_zero (f : Lp H 2 μ) :
    modularRightTranslation μ D 0 f = f := by
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ D 0 f] with t ht
  simpa only [add_zero, D.unitary_zero, one_apply_eq_self] using ht

def modularRightTranslationEquiv (s : ℝ) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := modularRightTranslation μ D s
  invFun := modularRightTranslation μ D (-s)
  left_inv f := by rw [modularRightTranslation_comp, neg_add_cancel, modularRightTranslation_zero]
  right_inv f := by rw [modularRightTranslation_comp, add_neg_cancel, modularRightTranslation_zero]
  map_add' := map_add (modularRightTranslation μ D s)
  map_smul' c f := by simp only [map_smul, RingHom.id_apply]
  norm_map' := modularRightTranslation_norm μ D s

lemma modularRightTranslation_star (s : ℝ) :
    star (modularRightTranslation μ D s) = modularRightTranslation μ D (-s) := by
  change star ((modularRightTranslationEquiv μ D s) : Lp H 2 μ →L[ℂ] Lp H 2 μ) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  rfl

lemma modularRightTranslation_coefficient (s : ℝ) (T : H →L[ℂ] H) :
    Commute (modularRightTranslation μ D s) (modularLpRepresentation μ D T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ D s (modularLpRepresentation μ D T f),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (modularLpRepresentation_ae μ D T f),
    modularLpRepresentation_ae μ D T (modularRightTranslation μ D s f),
    modularRightTranslation_ae μ D s f] with t hr hT hT' hr'
  change (modularRightTranslation μ D s (modularLpRepresentation μ D T f)) t =
    (modularLpRepresentation μ D T (modularRightTranslation μ D s f)) t
  rw [hr, hT, hT', hr']
  have hl : D.unitary s * D.unitary (-(t + s)) = D.unitary (-t) := by
    rw [← D.unitary_add]
    congr 1
    ring
  have hu : D.unitary (t + s) = D.unitary t * D.unitary s := D.unitary_add t s
  change (D.unitary s * D.unitary (-(t + s))) (T (D.unitary (t + s) (f (t + s)))) = _
  rw [hl, hu, mul_apply_eq_comp]

lemma modularRightTranslation_translate (s t : ℝ) :
    Commute (modularRightTranslation μ D s)
      (modularLpTranslateEquiv (H := H) μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ D s (modularLpTranslate μ t f),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (modularLpTranslate_ae μ t f),
    modularLpTranslate_ae μ t (modularRightTranslation μ D s f),
    (measurePreserving_sub_right μ t).quasiMeasurePreserving.ae
      (modularRightTranslation_ae μ D s f)] with r hs ht ht' hs'
  change (modularRightTranslation μ D s (modularLpTranslate μ t f)) r =
    (modularLpTranslate μ t (modularRightTranslation μ D s f)) r
  rw [hs, ht, ht', hs']
  congr 2
  ring

lemma modularRightTranslation_star_translate (s t : ℝ) :
    Commute (modularRightTranslation μ D s)
      (star (modularLpTranslateEquiv (H := H) μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
  rw [LinearIsometryEquiv.star_eq_symm]
  change Commute (modularRightTranslation μ D s)
    (modularLpTranslateEquiv (H := H) μ (-t) : Lp H 2 μ →L[ℂ] Lp H 2 μ)
  exact modularRightTranslation_translate μ D s (-t)

variable (S : BoundedRecovery.StandardModularData H)

/-- The right regular translations commute with the entire von Neumann
closure, not only its displayed generators. -/
theorem modularRightTranslation_mem_commutant (s : ℝ) :
    modularRightTranslation μ S.D s ∈ (modularCrossedProduct μ S).commutant := by
  let R := modularRightTranslation μ S.D s
  let N : StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    StarSubalgebra.centralizer ℂ {R}
  have hgen : modularCoreGenerators μ S ⊆ N := by
    intro T hT
    have h : Commute R T ∧ Commute R (star T) := by
      rcases hT with ⟨a, rfl⟩ | ⟨t, rfl⟩
      · refine ⟨modularRightTranslation_coefficient μ S.D s _, ?_⟩
        rw [← map_star]
        exact modularRightTranslation_coefficient μ S.D s _
      · exact ⟨modularRightTranslation_translate μ S.D s t,
          modularRightTranslation_star_translate μ S.D s t⟩
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = R := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨h.1.eq, by simpa only [star_star] using h.2.star_star.eq⟩
  have halg : algebraicModularCore μ S ≤ N := StarAlgebra.adjoin_le hgen
  rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant,
    modularCrossedProduct_carrier, Set.centralizer_centralizer_centralizer]
  intro T hT
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (halg hT) R (Set.mem_singleton R)).1.symm

end WeakPureInfiniteness

end

end OAI
