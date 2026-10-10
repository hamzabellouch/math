import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.DyadicPrecision
import OAI.Combinatorics.IndependentSets.Reduction.PairEnergy

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set
open scoped BigOperators Classical NNReal

abbrev Circle := AddCircle (1:ℝ)
instance circleProbability : IsProbabilityMeasure (volume : Measure Circle) where
  measure_univ := by simp [Circle]
noncomputable def realToTorus {n : ℕ} (x : Fin n → ℝ) : Fin n → Circle := fun i => (x i : Circle)

lemma circle_quotient_lipschitz : LipschitzWith 1 (fun x : ℝ => (x : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma realToTorus_lipschitz (n : ℕ) : LipschitzWith 1 (@realToTorus n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact (circle_quotient_lipschitz.dist_le_mul (x i) (y i)).trans
    (by simpa using dist_le_pi_dist x y i)

lemma circle_quotient_preserving : MeasurePreserving (fun x : ℝ => (x : Circle)) BooleanJunta.unitLaw volume := by
  have h := AddCircle.measurePreserving_mk (1:ℝ) 0
  simpa only [zero_add, restrict_Ioc_eq_restrict_Icc, BooleanJunta.unitLaw] using h

lemma realToTorus_preserving (n : ℕ) : MeasurePreserving (@realToTorus n) (BooleanJunta.unitCubeLaw n) volume :=
  measurePreserving_pi (fun _ => BooleanJunta.unitLaw) (fun _ => (volume : Measure Circle))
    (fun _ => circle_quotient_preserving)

lemma torus_average_lift {n : ℕ} (S : Finset (Fin n)) {H : (Fin n → Circle) → ℝ}
    (hH : Measurable H) (x : Fin n → ℝ) :
    ProductAveraging.average BooleanJunta.unitLaw S (H ∘ realToTorus) x =
      ProductAveraging.average (volume : Measure Circle) S H (realToTorus x) := by
  unfold ProductAveraging.average
  have he (y : Fin n → ℝ) : realToTorus (ProductAveraging.mix S (x,y)) =
      ProductAveraging.mix S (realToTorus x,realToTorus y) := by
    funext i
    by_cases hi : i ∈ S <;> simp [realToTorus, ProductAveraging.mix, hi]
  simp only [Function.comp_def, he]
  have hm : Measurable (fun y : Fin n → Circle => H (ProductAveraging.mix S (realToTorus x,y))) :=
    hH.comp ((ProductAveraging.mix_measurable S).comp (measurable_const.prodMk measurable_id))
  exact ProductAveraging.integral_preserving (realToTorus_preserving n) hm.aestronglyMeasurable

theorem torus_junta_uniform (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ H : (Fin n → Circle) → ℝ,
      LipschitzWith L H → (∀ x, |H x| ≤ 1) →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        (∫ x, (H x-ProductAveraging.average (volume : Measure Circle) S H x)^2) < u := by
  obtain ⟨J,hJ,hall⟩ := BooleanJunta.real_cube_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro n H hH hb
  have hf : LipschitzWith L (H ∘ realToTorus (n:=n)) := by simpa using hH.comp (realToTorus_lipschitz n)
  obtain ⟨S,hS,hi,he⟩ := hall n _ hf (fun x => hb _)
  refine ⟨S,hS,?_⟩
  simp only [torus_average_lift S hH.continuous.measurable] at he
  have ham := ProductAveraging.average_measurable (volume : Measure Circle) S hH.continuous.measurable
  have hm : AEStronglyMeasurable (fun x => (H x-ProductAveraging.average (volume : Measure Circle) S H x)^2) volume :=
    ((hH.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have ha := ProductAveraging.integral_preserving (realToTorus_preserving n) hm
  change (∫ x, ((H ∘ realToTorus) x-
    ProductAveraging.average (volume : Measure Circle) S H (realToTorus x))^2 ∂BooleanJunta.unitCubeLaw n) = _ at ha
  rw [ha] at he
  exact he

noncomputable def circleInfluence {n : ℕ} (i : Fin n) (H : (Fin n → Circle) → ℝ) : ℝ :=
  Real.sqrt (ProductAveraging.influenceSq (volume : Measure Circle) i H)

theorem torus_influences (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ n : ℕ, ∀ H : (Fin n → Circle) → ℝ,
        LipschitzWith L H → (∀ x, |H x| ≤ 1) →
        (((∫ x, H x) = 0 ∧ ε < ∫ x, (H x)^2) → ∃ i, β ≤ circleInfluence i H) ∧
        (Finset.univ.filter (fun i => β/2 ≤ circleInfluence i H)).card ≤ K := by
  obtain ⟨J,hJ,HJ⟩ := torus_junta_uniform L (u:=ε/12) (by positivity)
  let b : ℝ := ε/(4*(4:ℝ)^J*J)
  have hJp : (0:ℝ)<J := by exact_mod_cast (by omega : 0<J)
  have hb : 0 < b := by dsimp [b]; positivity
  let β := Real.sqrt b
  have hβ : 0 < β := Real.sqrt_pos.mpr hb
  have hβsq : β^2=b := Real.sq_sqrt hb.le
  obtain ⟨K,hK,HK⟩ := torus_junta_uniform L (u:=(β/2)^2) (sq_pos_of_pos (by positivity))
  refine ⟨β,hβ,K,hK,?_⟩
  intro n H hH hbound
  have hm := hH.continuous.measurable
  constructor
  · intro ⟨hz,hv⟩
    obtain ⟨S,hS,he⟩ := HJ n H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    obtain ⟨i,hi⟩ := ProductAveraging.exists_influence_of_junta (volume : Measure Circle)
      hJ S hS hm hGm hbound hGb hdep hε hz hv he
    refine ⟨i,?_⟩
    exact Real.sqrt_le_sqrt hi
  · obtain ⟨S,hS,he⟩ := HK n H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    have hcard := ProductAveraging.influential_card_le (volume : Measure Circle) S hm hGm hbound hGb hdep he
    have hsub : Finset.univ.filter (fun i => β/2 ≤ circleInfluence i H) ⊆
        Finset.univ.filter (fun i => (β/2)^2 ≤ ProductAveraging.influenceSq (volume : Measure Circle) i H) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have h := (Finset.mem_filter.mp hi).2
      have hsq := (sq_le_sq₀ (by positivity : 0≤β/2) (Real.sqrt_nonneg _)).mpr h
      simpa only [circleInfluence, Real.sq_sqrt (ProductAveraging.influenceSq_nonneg _ _ _)] using hsq
    exact (Finset.card_le_card hsub).trans (hcard.trans hS)

end LargeIndependentSets

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical NNReal
noncomputable def reindex {ι κ α : Type*} (e : ι ≃ κ) (x : ι → α) : κ → α := x ∘ e.symm
lemma reindex_preserving {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : ι ≃ κ) :
    MeasurePreserving (reindex (α:=α) e) (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : κ => μ) e using 1
  funext x i
  simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
lemma reindex_lipschitz {ι κ α : Type*} [Fintype ι] [Fintype κ] [PseudoMetricSpace α]
    (e : ι ≃ κ) : LipschitzWith 1 (reindex (α:=α) e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y (e.symm i)
lemma reindex_mix {ι κ α : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (S : Finset ι) (x y : ι → α) :
    reindex e (mix S (x,y)) = mix (S.image e) (reindex e x,reindex e y) := by
  funext i
  have hi : i ∈ S.image e ↔ e.symm i ∈ S := by
    constructor
    · rintro h
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      simpa [← he] using hj
    · intro h
      exact Finset.mem_image.mpr ⟨e.symm i,h,e.apply_symm_apply i⟩
  simp only [reindex,Function.comp_def,mix,hi]

lemma average_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (e : ι ≃ κ)
    (S : Finset ι) {f : (κ → α) → ℝ} (hf : Measurable f) (x : ι → α) :
    average μ S (f ∘ reindex e) x = average μ (S.image e) f (reindex e x) := by
  have hm : Measurable (fun y => f (mix (S.image e) (reindex e x,y))) :=
    hf.comp ((mix_measurable _).comp (measurable_const.prodMk measurable_id))
  have h := integral_preserving (reindex_preserving μ e) hm.aestronglyMeasurable
  unfold average
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Function.comp_def, reindex_mix]

end LargeIndependentSets.ProductAveraging

end OAI
