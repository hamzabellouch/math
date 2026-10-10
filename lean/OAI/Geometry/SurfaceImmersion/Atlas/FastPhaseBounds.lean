import OAI.Geometry.SurfaceImmersion.Atlas.WeightedPhaseExpressions
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVector
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFastEvaluation

namespace OAI

/-! Uniform weighted bounds after substituting the fast circle phase. Local
real lifts keep the constants independent of the number of oscillations. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open_domain {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hb : WeightedBound U s m C f) : WeightedBound V s m C f := by
  intro j hj p hp
  rw [iteratedFDerivWithin_of_isOpen j hV hp]
  have h := hb j hj p (hVU hp)
  rwa [iteratedFDerivWithin_of_isOpen j hU (hVU hp)] at h

lemma weighted_shifted_phase {U : Set E} (hU : IsOpen U) (ℓ : E →L[ℝ] ℝ)
    (c : ℝ) {z P : ℝ} (hz : 0 < z) (hP : 2 ≤ P) (hℓ : ‖ℓ‖ ≤ P)
    (ht : Set.MapsTo (fun p => ℓ p / z - c) U (Set.Icc (-1) 2)) (m : ℕ) :
    WeightedBound U z m P (fun p => ℓ p / z - c) := by
  intro j _ p hp
  rw [iteratedFDerivWithin_of_isOpen j hU hp]
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [(ht hp).1], (ht hp).2⟩).trans hP
  | succ n =>
    have hd : fderiv ℝ (fun p => ℓ p / z - c) = fun _ => z⁻¹ • ℓ := by
      funext q
      simp only [fderiv_sub_const]
      have he : (fun p => ℓ p / z) = ⇑(z⁻¹ • ℓ) := by
        funext x
        simp [div_eq_mul_inv, mul_comm]
      rw [he, ContinuousLinearMap.fderiv]
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero, pow_one]
      calc
        z * ‖z⁻¹ • ℓ‖ = ‖ℓ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
          field_simp
        _ ≤ P := hℓ
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, mul_zero]; linarith

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates CovarianceCorrector

/-- A periodic function represented by an actual jet expression retains its
slow-scale loss after evaluation at a fast linear phase. -/
theorem compact_periodic_fast_bound {S : Set Base} (hS : IsOpen S) {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + e.order) B (lowJet G) →
      ∀ (H : Base → Period → ℝ),
        (∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = H p (t : Period)) →
        WeightedBound S z m (D / s ^ e.loss)
          (fun p => H p ((ℓ p / z : ℝ) : Period)) := by
  obtain ⟨D, hD, hd⟩ := Expression.compact_phase_bound hO hK hKO
    e he m B (2 + ‖ℓ‖) hB (by linarith [norm_nonneg ℓ])
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hb H hR j hj p hp
  let a : ℝ := AddCircle.equivIco 1 0 ((ℓ p / z : ℝ) : Period)
  have ha : a ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 ((ℓ p / z : ℝ) : Period)).property
  have hca : (a : Period) = ((ℓ p / z : ℝ) : Period) := AddCircle.coe_equivIco
  let c : ℝ := ℓ p / z - a
  let t : Base → ℝ := fun q => ℓ q / z - c
  have hcz : (c : Period) = 0 := by
    rw [show c = ℓ p / z - a from rfl, AddCircle.coe_sub, hca, sub_self]
  have hct (q : Base) : (t q : Period) = ((ℓ q / z : ℝ) : Period) := by
    rw [show t q = ℓ q / z - c from rfl, AddCircle.coe_sub, hcz, sub_zero]
  have ht : ContDiff ℝ ∞ t := (ℓ.contDiff.div_const z).sub contDiff_const
  let V : Set Base := (S : Set Base) ∩ t ⁻¹' Set.Ioo (-1) 2
  have hV : IsOpen V := hS.inter (isOpen_Ioo.preimage ht.continuous)
  have hVS : V ⊆ S := Set.inter_subset_left
  have hpV : p ∈ V := by
    refine ⟨hp, ?_⟩
    change -1 < ℓ p / z - (ℓ p / z - a) ∧ ℓ p / z - (ℓ p / z - a) < 2
    constructor <;> linarith [ha.1, ha.2]
  have htV : Set.MapsTo t V (Set.Icc (-1) 2) := fun _ hx => ⟨hx.2.1.le, hx.2.2.le⟩
  have hbt := weighted_shifted_phase hV ℓ c hz (by linarith [norm_nonneg ℓ])
    (by linarith : ‖ℓ‖ ≤ 2 + ‖ℓ‖) htV m
  have hh := hd V hV G t s z hz hzs hs1 hG ht.contDiffOn
    (fun _ hx => hGK (hVS hx)) htV (hb.restrict_open_domain hS hV hVS) hbt
  have heq : (fun q => e.eval G (q, t q)) =ᶠ[𝓝 p]
      (fun q => H q ((ℓ q / z : ℝ) : Period)) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [hR q hq (t q), hct q]
  have hjet := (heq.iteratedFDeriv ℝ j).self_of_nhds
  have h := hh j hj p hpV
  rw [iteratedFDerivWithin_of_isOpen j hV hpV, hjet] at h
  rwa [iteratedFDerivWithin_of_isOpen j hS hp]


end ClosedSurfaceR4.JetPolynomial.Expression

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

/-- Each actual periodic coefficient has a fast-scale bound with the same
slow-scale loss as its jet polynomial. -/
theorem compact_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : VectorExpression) (hRs : R.SmoothCoeffs O) (i : Fin 4)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (R i).order) B (lowJet G) →
      ∀ (U : Family S R4), Represents G R U →
        WeightedBound S z m (D / s ^ (R i).loss)
          (fun p => U.fastValue ℓ z p i) := by
  obtain ⟨D, hD, hd⟩ := Expression.compact_periodic_fast_bound S.isOpen hO hK hKO
    (R i) (hRs i) ℓ m B hB
  exact ⟨D, hD, fun G s z hz hzs hs1 hG hGK hb U hR =>
    hd G s z hz hzs hs1 hG hGK hb (fun p t => U.val p t i) (hR i)⟩

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
