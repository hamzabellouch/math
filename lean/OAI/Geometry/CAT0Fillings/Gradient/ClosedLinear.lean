import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.CyclePairing

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma exists_inverse_coordinates (i : ℕ) :
    ∃ (F : Fin n → X → ℝ) (K : ℝ≥0), (∀ a, LipschitzWith K (F a)) ∧
      ∀ᵐ z ∂volume.restrict (q.chart i).domain,
        ∀ a, q.covector i (F a) z = (1 : Matrix (Fin n) (Fin n) ℝ) a := by
  obtain ⟨K₁,K₂,hK₁,hK₂⟩ := (q.chart i).bilipschitz
  have hrow : ∀ a y (hy : y ∈ (q.chart i).domain) z (hz : z ∈ (q.chart i).domain),
      |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤
        (K₂ : ℝ)*dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hz⟩) := by
    intro a y hy z hz
    have h := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (y-z) a
    have he : |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤ dist y z := by
      change |y.ofLp a-z.ofLp a| ≤ ‖y-z‖
      simpa only [Real.norm_eq_abs,PiLp.sub_apply] using h
    exact he.trans (hK₂.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩)
  obtain ⟨F,hF,hFeq,_⟩ := (q.chart i).exists_inverse_coordinate_tests
    (q.chart i).borel subset_rfl (fun a => EuclideanSpace.proj a) K₂ hrow
  refine ⟨F,K₂,hF,?_⟩
  rw [eventually_all]
  intro a
  have h := (q.chart i).ae_fderivWithin_scalar_eq_linear (q.chart i).borel subset_rfl
    (hF a) (EuclideanSpace.proj a) (hFeq a)
  filter_upwards [h] with z hz
  ext b
  unfold covector
  rw [hz]
  change (EuclideanSpace.single b (1 : ℝ)).ofLp a = (1 : Matrix (Fin n) (Fin n) ℝ) a b
  simp [Matrix.one_apply]

lemma ae_coordinate_density_pos (i : ℕ) :
    ∀ᵐ z ∂q.coordinateMeasure i, 0 < q.density i z := by
  apply (ae_withDensity_iff' (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal).mpr
  exact Eventually.of_forall fun z hz => lt_of_not_ge (fun h => hz (ENNReal.ofReal_eq_zero.mpr h))

lemma ae_multiplicity_ne_zero (i : ℕ) :
    ∀ᵐ z ∂q.coordinateMeasure i, ((q.chart i).multiplicity z : ℝ) ≠ 0 := by
  filter_upwards [q.ae_coordinate_density_pos i] with z hz
  intro he
  simp only [density,he,abs_zero,zero_mul] at hz
  exact lt_irrefl 0 hz

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma eq_zero_of_pairing_null (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hnull : ∀ (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0),
      (∀ j, LipschitzWith (K j) (π j)) → ∀ b, BoundedLip b → q.pairing π b L = 0) :
    L = 0 := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero (Euc (k+1)) 2 q.atlasMeasure).symm
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  obtain ⟨F,K,hF,hrows⟩ := q.exists_inverse_coordinates i
  have hzero : ∀ᵐ z ∂q.coordinateMeasure i, ∀ a : Fin (k+1),
      q.testWeight (fun j => F (Equiv.swap 0 a j.succ)) L (i,z) = 0 := by
    rw [eventually_all]
    intro a
    have hh := q.testWeight_eq_zero_of_pairings (fun j => F (Equiv.swap 0 a j.succ))
      (fun _ => K) (fun j => hF _) L (hnull _ _ (fun j => hF _))
    exact (measurableEmbedding_prodMk_left i).ae_map_iff.mp (Measure.ae_sum_iff.mp hh i)
  have hrows' := (withDensity_absolutelyContinuous _ (fun z => ENNReal.ofReal (q.density i z))).ae_le hrows
  have hdiff := (withDensity_absolutelyContinuous _ (fun z => ENNReal.ofReal (q.density i z))).ae_le (q.differential i)
  filter_upwards [hzero,hrows',hdiff,q.ae_multiplicity_ne_zero i] with z hz hr hd hθ
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hd.2.2 hd.2.1
  have hJ : Real.sqrt (q.gram i z).det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  have hraw : rawCovector (q.gram i z) (L (i,z)) = 0 := by
    funext a
    apply component_zero_of_omitted_det _ a
    have hh := hz a
    change ((_ : ℝ)/abs _) * normalizedDet _ _ _ = 0 at hh
    have hh' := (mul_eq_zero.mp hh).resolve_left (div_ne_zero hθ (abs_ne_zero.mpr hθ))
    unfold normalizedDet at hh'
    have he : (fun j : Fin k => q.covector i (F (Equiv.swap 0 a j.succ)) z) =
        fun j => (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Equiv.swap 0 a j.succ) := by
      funext j
      exact hr _
    rw [he] at hh'
    exact (div_eq_zero_iff.mp hh').resolve_right hJ
  have he := normalize_rawCovector (q.gram i z) hG (L (i,z))
  rw [hraw,Matrix.mulVec_zero] at he
  apply (WithLp.equiv 2 (Fin (k+1) → ℝ)).injective
  exact he.symm

theorem gradient_closable (hz : IsCycle T)
    (u : ℕ → X → ℝ) (Ku : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (Ku j) (u j))
    (hu0 : Tendsto (fun j => lpNorm (u j) 2 (MassMeasure.currentMassMeasure hT)) atTop (𝓝 0))
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure)
    (hL : Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 L)) : L = 0 := by
  apply q.eq_zero_of_pairing_null L
  intro π K hπ b hb
  exact q.pairing_eq_zero_of_gradient_limit hz u Ku hu hu0 L hL π K hπ hb

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradient_add {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.gradient (hu.add hv) = q.gradient hu + q.gradient hv := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  have hea := (q.memLp_gradientFunction (hu.add hv)).coeFn_toLp
  have heb := (q.memLp_gradientFunction hu).coeFn_toLp
  have hec := (q.memLp_gradientFunction hv).coeFn_toLp
  have he : q.gradientFunction (fun x => u x+v x) =ᵐ[q.atlasMeasure]
      fun w => q.gradientFunction u w+q.gradientFunction v w := by
    apply Measure.ae_sum_iff.mpr
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_uniqueDiffWithinAt volume (q.chart i).domain,
      (q.chart i).ae_differentiableWithinAt_scalar hu,
      (q.chart i).ae_differentiableWithinAt_scalar hv] with z hz hdu hdv
    have hs : (q.chart i).scalar (fun x => u x+v x) =
        (q.chart i).scalar u+(q.chart i).scalar v := by
      funext z
      by_cases hz : z ∈ (q.chart i).domain <;> simp [IntegerChart.scalar,hz]
    change q.normalizedCovector i (fun x => u x+v x) z =
      q.normalizedCovector i u z+q.normalizedCovector i v z
    unfold normalizedCovector covector
    rw [hs,fderivWithin_add hz hdu hdv]
    have he : differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z +
        fderivWithin ℝ ((q.chart i).scalar v) (q.chart i).domain z) =
        differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z)+
        differentialRow (fderivWithin ℝ ((q.chart i).scalar v) (q.chart i).domain z) := rfl
    rw [he,Matrix.mulVec_add,WithLp.toLp_add]
  filter_upwards [hea,heb,hec,he] with w ha hb hc he
  change (q.gradient (hu.add hv)) w = (q.gradient hu) w+(q.gradient hv) w
  exact ha.trans (he.trans (congrArg₂ (·+·) hb.symm hc.symm))

lemma gradient_smul {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    q.gradient ((lipschitzWith_smul c).comp hu) = c • q.gradient hu := by
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_smul c _).symm
  have hea := (q.memLp_gradientFunction ((lipschitzWith_smul c).comp hu)).coeFn_toLp
  have heb := (q.memLp_gradientFunction hu).coeFn_toLp
  have he : q.gradientFunction (fun x => c • u x) =ᵐ[q.atlasMeasure]
      fun w => c • q.gradientFunction u w := by
    apply Measure.ae_sum_iff.mpr
    intro i
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_uniqueDiffWithinAt volume (q.chart i).domain,
      (q.chart i).ae_differentiableWithinAt_scalar hu] with z hz hdu
    have hs : (q.chart i).scalar (fun x => c • u x) = c • (q.chart i).scalar u := by
      funext z
      by_cases hz : z ∈ (q.chart i).domain <;> simp [IntegerChart.scalar,hz]
    change q.normalizedCovector i (fun x => c • u x) z = c • q.normalizedCovector i u z
    unfold normalizedCovector covector
    rw [hs,fderivWithin_const_smul hz hdu]
    have he : differentialRow (c • fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z) =
        c • differentialRow (fderivWithin ℝ ((q.chart i).scalar u) (q.chart i).domain z) := rfl
    rw [he,Matrix.mulVec_smul,WithLp.toLp_smul]
  filter_upwards [hea,heb,he] with w ha hb he
  change (q.gradient ((lipschitzWith_smul c).comp hu)) w = c • (q.gradient hu) w
  exact ha.trans (he.trans (congrArg (c • ·) hb.symm))

noncomputable def value {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  ((Foundations.boundedLip_of_lipschitz hu).memLp 2).toLp u

lemma value_add {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    value (hT := hT) (hu.add hv) = value hu + value hv :=
  MemLp.toLp_add _ _

lemma value_smul {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (c : ℝ) :
    value (hT := hT) ((lipschitzWith_smul c).comp hu) = c • value hu :=
  MemLp.toLp_const_smul c ((Foundations.boundedLip_of_lipschitz hu).memLp 2)

lemma norm_value {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖value (hT := hT) hu‖ = lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  rw [value,Lp.norm_toLp,toReal_eLpNorm]

end CAT0Fillings.ChartGeometry
end

end OAI
