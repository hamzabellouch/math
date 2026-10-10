import OAI.MeasureTheory.Falconer.Measures.TestNormDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_rnDeriv_eLpNorm_le (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceTestNorm q γ ≠ ∞) :
    eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength ≤
      sourceTestNorm q γ := by
  let R := γ.rnDeriv sourceArcLength
  let F : ℕ → UnitCircle → ℝ := fun n x => min (R x).toReal n
  have hm (n : ℕ) : Measurable (F n) :=
    (Measure.measurable_rnDeriv γ sourceArcLength).ennreal_toReal.min measurable_const
  have hpos (n : ℕ) (x : UnitCircle) : 0 ≤ F n x :=
    le_min ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hb (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) sourceArcLength ≤ sourceTestNorm q γ := by
    have h := sourceTestNorm_bounded_density_lower γ hpq hN
      (fun x => ENNReal.ofReal (F n x)) (hm n).ennreal_ofReal ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      (Eventually.of_forall (fun x =>
        (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (ENNReal.ofReal_toReal_le)))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top (hm n).aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.nonneg]
    simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hpos n _)] using h
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)
    (fun index => (hm index).aestronglyMeasurable)
    (Measure.measurable_rnDeriv γ sourceArcLength).ennreal_toReal.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (R x).toReal
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (min_eq_left (hn.trans (by exact_mod_cast hm))).symm

theorem sourceTestNorm_exists_Lp_density (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceTestNorm q γ ≠ ∞) :
    ∃ g : UnitCircle → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      MemLp g (ENNReal.ofReal p) sourceArcLength ∧
      sourceArcLength.withDensity (fun x => ENNReal.ofReal (g x)) = γ ∧
      eLpNorm g (ENNReal.ofReal p) sourceArcLength ≤ sourceTestNorm q γ := by
  let g := fun x => (γ.rnDeriv sourceArcLength x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv γ sourceArcLength).ennreal_toReal
  have hb := sourceTestNorm_rnDeriv_eLpNorm_le γ hpq hN
  refine ⟨g, hg, fun _ => ENNReal.toReal_nonneg, hb.trans_lt hN.lt_top, ?_, hb⟩
  have he : (fun x => ENNReal.ofReal (g x)) =ᵐ[sourceArcLength] γ.rnDeriv sourceArcLength := by
    filter_upwards [Measure.rnDeriv_lt_top γ sourceArcLength] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq γ sourceArcLength
    (sourceTestNorm_absolutelyContinuous γ (Real.holderConjugate_iff.mp hpq.symm).1.le hN)

end PlanarFalconer

end OAI
