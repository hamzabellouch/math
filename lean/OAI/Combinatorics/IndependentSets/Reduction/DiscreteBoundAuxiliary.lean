import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.FullAbsorptionSquare

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient BooleanJunta
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ τ : Type} [Fintype κ]

theorem discrete_bound_of_auxiliary (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hq : ∀ j k, q j (p j k) = r k) (a : τ → ι) {m : ℕ} (hm : 0 < m)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {L : ℝ≥0}
    (hrare : (1-levelMass m ρ ⟨m,by omega⟩)^Fintype.card ι < ε)
    (hgrid : 2*L*Fintype.card ι*(1/2:ℝ)^k < ε)
    (F : (κ → Circle) → ℝ) (hF : LipschitzWith L F) (hb : ∀ x, |F x| ≤ 1)
    (haux : (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
      ∂(volume : Measure (ι → Circle)) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε) :
    (∑ t : ι → Fin (m+1), mass m ρ t *
      𝔼 v : Sigma M → Cube k, (F (phase p (fun j => value (t j))
        (fun c => scalarCell (v c) 0)))^2) < 6*ε := by
  let A (t : ι → Fin (m+1)) : ℝ := ∫ θ, (F (phase p (fun j => value (t j)) θ))^2
    ∂Measure.pi (fun _ : Sigma M => rotationLaw)
  let B (t : ι → Fin (m+1)) : ℝ := 𝔼 v : Sigma M → Cube k,
    (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0)))^2
  let e : ℝ := 2*L*Fintype.card ι*(1/2:ℝ)^k
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hB (t : ι → Fin (m+1)) : B t ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro v _
    have hh := hb (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0))
    nlinarith [sq_abs (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0))), abs_nonneg (F (phase p (fun j => value (t j)) (fun c => scalarCell (v c) 0)))]
  have hAB (t : ι → Fin (m+1)) : B t ≤ A t + e :=
    discrete_square_le_continuous p _ (fun j => value_abs_le_one hm _) k F hF hb
  have hpoint (t : ι → Fin (m+1)) : B t ≤
      (if Full t then A t else 0) + e + (if Full t then 0 else 1) := by
    by_cases ht : Full t
    · simpa only [ite_eq_left ht, add_zero] using hAB t
    · simp only [ite_eq_right ht, zero_add]
      linarith [hB t]
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun t _ => mul_le_mul_of_nonneg_left (hpoint t) (mass_nonneg m hρ t))
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one] at hs
  have hmass : (∑ t : ι → Fin (m+1), mass m ρ t * e) = e := by
    rw [← Finset.sum_mul, mass_total m hρ, one_mul]
  rw [hmass, no_full_mass hρ] at hs
  have hfull := continuous_full_bound p q r hq a hm hρ F hF.continuous.measurable hb haux
  simp only [Finset.sum_filter] at hfull
  change (∑ t, if Full t then mass m ρ t * A t else 0) < 4*ε at hfull
  change (∑ t, mass m ρ t * B t) < 6*ε
  linarith
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
theorem arbitrary_torus_junta (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ f : (ι → Circle) → ℝ, LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset ι, S.card ≤ J ∧
        (∫ x, (f x-average (volume : Measure Circle) S f x)^2
          ∂Measure.pi (fun _ : ι => (volume : Measure Circle))) < u := by
  obtain ⟨J,hJ,H⟩ := torus_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hb
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g := f ∘ reindex (α:=Circle) e
  have hg : LipschitzWith L g := by simpa only [mul_one] using hf.comp (reindex_lipschitz e)
  obtain ⟨S,hS,he⟩ := H _ g hg (fun x => hb _)
  refine ⟨S.image e,(Finset.card_image_le).trans hS,?_⟩
  have ham := average_measurable (volume : Measure Circle) (S.image e) hf.continuous.measurable
  have h := integral_preserving (reindex_preserving (volume : Measure Circle) e)
    ((hf.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have hp (x : Fin (Fintype.card ι) → Circle) :
      (f (reindex e x)-average (volume : Measure Circle) (S.image e) f (reindex e x))^2 =
      (g x-average (volume : Measure Circle) S g x)^2 := by
    rw [← average_reindex (volume : Measure Circle) e S hf.continuous.measurable]
    rfl
  change (∫ x, (f (reindex e x)-average (volume : Measure Circle) (S.image e) f (reindex e x))^2
    ∂Measure.pi (fun _ : Fin (Fintype.card ι) => (volume : Measure Circle))) =
    (∫ x, (f x-average (volume : Measure Circle) (S.image e) f x)^2
      ∂Measure.pi (fun _ : ι => (volume : Measure Circle))) at h
  simp only [hp] at h
  rw [← h]
  exact he

theorem arbitrary_torus_influences (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ H : (ι → Circle) → ℝ,
        LipschitzWith L H → (∀ x, |H x| ≤ 1) →
        (((∫ x, H x) = 0 ∧ ε < ∫ x, (H x)^2) → ∃ i, β ≤ influenceNorm (volume : Measure Circle) i H) ∧
        (Finset.univ.filter (fun i => β/2 ≤ influenceNorm (volume : Measure Circle) i H)).card ≤ K := by
  obtain ⟨J,hJ,HJ⟩ := arbitrary_torus_junta L (u:=ε/12) (by positivity)
  let b : ℝ := ε/(4*(4:ℝ)^J*J)
  have hJp : (0:ℝ)<J := by exact_mod_cast (by omega : 0<J)
  have hb : 0 < b := by dsimp [b]; positivity
  let β := Real.sqrt b
  have hβ : 0 < β := Real.sqrt_pos.mpr hb
  have hβsq : β^2=b := Real.sq_sqrt hb.le
  obtain ⟨K,hK,HK⟩ := arbitrary_torus_junta L (u:=(β/2)^2) (sq_pos_of_pos (by positivity))
  refine ⟨β,hβ,K,hK,?_⟩
  intro ι _ _ H hH hbound
  have hm := hH.continuous.measurable
  constructor
  · intro ⟨hz,hv⟩
    obtain ⟨S,hS,he⟩ := HJ ι H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    obtain ⟨i,hi⟩ := ProductAveraging.exists_influence_of_junta (volume : Measure Circle)
      hJ S hS hm hGm hbound hGb hdep hε hz hv he
    refine ⟨i,?_⟩
    exact Real.sqrt_le_sqrt hi
  · obtain ⟨S,hS,he⟩ := HK ι H hH hbound
    let G := ProductAveraging.average (volume : Measure Circle) S H
    have hGm : Measurable G := ProductAveraging.average_measurable _ S hm
    have hGb : ∀ x, |G x| ≤ 1 := ProductAveraging.average_bound _ S hbound
    have hdep : ∀ x y, (∀ i ∈ S, x i = y i) → G x = G y := ProductAveraging.average_depends _ S H
    have hcard := ProductAveraging.influential_card_le (volume : Measure Circle) S hm hGm hbound hGb hdep he
    have hsub : Finset.univ.filter (fun i => β/2 ≤ influenceNorm (volume : Measure Circle) i H) ⊆
        Finset.univ.filter (fun i => (β/2)^2 ≤ ProductAveraging.influenceSq (volume : Measure Circle) i H) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have h := (Finset.mem_filter.mp hi).2
      have hsq := (sq_le_sq₀ (by positivity : 0≤β/2) (Real.sqrt_nonneg _)).mpr h
      simpa only [influenceNorm, Real.sq_sqrt (ProductAveraging.influenceSq_nonneg _ _ _)] using hsq
    exact (Finset.card_le_card hsub).trans (hcard.trans hS)

end LargeIndependentSets
namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal
theorem arbitrary_coefficient_mean_square (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 0 < m) (ρ γ c : ℝ),
    0 ≤ ρ → 0 ≤ c → c < γ →
    (L:ℝ)/m < β/2 →
    (1-levelMass m ρ ⟨m,by omega⟩)^Fintype.card ι < ε →
    ρ*K < ε → (Fintype.card ι : ℝ)*(2*γ)^2/β^2 < ε →
    ∀ (M : ι → Type) [∀ j, Fintype (M j)]
      (κ τ : Type) [Fintype κ],
    ∀ (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ),
    (∀ j k, q j (p j k) = r k) →
    ∀ (F : (κ → Circle) → ℝ), LipschitzWith L F →
    (∀ x, |F x| ≤ 1) →
    (∀ x, F (fun k => x k + ((1/2:ℝ):Circle)) = -F x) →
    ∀ (κ' : ι → Type) [∀ i, Fintype (κ' i)]
      (p' : ∀ i, ∀ j : {j : ι // j ≠ i}, κ' i → M j.val)
      (e : ∀ i, κ → κ' i),
    (∀ i j k, p j.val k = p' i j (e i k)) →
    ∀ (F' : ∀ i, (κ' i → Circle) → ℝ),
    (∀ i, Measurable (F' i)) → (∀ i x, |F' i x| ≤ 1) →
    (∀ i y, |F (y ∘ e i)-F' i y| ≤ c) →
    ∀ (S : ∀ i, ({j : ι // j ≠ i} → Fin (m+1)) →
      Finset (Sigma fun j : {j : ι // j ≠ i} => M j.val)),
    (∀ i t, (∫ θ,
      (F' i (phase (p' i) (fun j => value (t j)) θ) -
        average rotationLaw (S i t) (fun φ => F' i (phase (p' i) (fun j => value (t j)) φ)) θ)^2
      ∂Measure.pi (fun _ : Sigma (fun j : {j : ι // j ≠ i} => M j.val) => rotationLaw)) < γ^2) →
    ∀ (a : τ → ι),
    (∀ i t d, d ∈ S i t → a (q d.1.val d.2) ≠ i) →
    (∑ t : ι → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
        ∂(volume : Measure (ι → Circle))
        ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε := by
  obtain ⟨β,hβ,K,hK,HT⟩ := arbitrary_torus_influences L hε
  refine ⟨β,hβ,K,hK,?_⟩
  intro ι _ _ m hm ρ γ c hρ hc hcγ hstep hrare hpos hzero
    M _ κ τ _ p q r hq F hF hb hodd κ' _ p' e hp F' hF'm hF'b hcompat S hjunta a halign
  let H (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) (z : ι → Circle) :=
    F (auxiliary p r a (fun j => value (t j)) θ z)
  let X (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) := ∫ z, (H t θ z)^2
  let D (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) (i : ι) :=
    influenceNorm volume i (H t θ)
  have hHlip (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) : LipschitzWith L (H t θ) := by
    simpa only [H, Function.comp_def, mul_one] using hF.comp (auxiliary_lipschitz p r a (fun j => value (t j)) θ)
  have hHm (t : ι → Fin (m+1)) : Measurable (fun v : (Sigma M → ℝ) × (ι → Circle) => H t v.1 v.2) :=
    hF.continuous.measurable.comp (auxiliary_joint_measurable p r a _)
  have hXB (t : ι → Fin (m+1)) (θ : Sigma M → ℝ) : 0 ≤ X t θ ∧ X t θ ≤ 1 := by
    constructor
    · exact integral_nonneg (fun z => sq_nonneg _)
    · calc
        _ ≤ ∫ _ : ι → Circle, (1:ℝ) :=
          integral_mono (bounded_sq_integrable (hHlip t θ).continuous.measurable (fun z => hb _))
            (integrable_const _) (fun z => by
              have hh : |H t θ z| ≤ 1 := hb _
              nlinarith [sq_abs (H t θ z), abs_nonneg (H t θ z)])
        _ = 1 := by simp
  apply coefficient_mean_square_ae (Measure.pi (fun _ : Sigma M => rotationLaw)) hρ hβ (hc.trans_lt hcγ) hε
    (by simpa using hrare) hpos (by simpa using hzero) X D
  · intro t
    exact ((hHm t).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  · exact hXB
  · intro t i
    exact (influenceSq_param_measurable volume i (hHm t)).sqrt
  · intro t θ i
    dsimp only [D, influenceNorm]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by
      simpa using influenceSq_le_bound volume i (hHlip t θ).continuous.measurable (fun z => hb (auxiliary p r a (fun j => value (t j)) θ z))⟩
  · intro t θ hx
    exact (HT ι (H t θ) (hHlip t θ) (fun z => hb _)).1
      ⟨auxiliary_mean_zero p r a _ θ F hF.continuous.measurable hodd,hx⟩
  · filter_upwards [rotations_bounded_ae (C:=Sigma M)] with θ hθ
    intro t i hti
    have h := auxiliary_influence_step p r a (fun j => value (t j))
      (fun j => value (lower i t j)) i
      (fun j hji => by simp [lower, hji]) θ hθ
      (by positivity : 0 ≤ 1/(m:ℝ)) (le_of_eq (value_lower hm i t hti)) F hF hb
    exact h.trans_lt (by simpa [div_eq_mul_inv] using hstep)
  · intro t θ
    exact_mod_cast (HT ι (H t θ) (hHlip t θ) (fun z => hb _)).2
  · intro t i ht hi
    obtain ⟨j,hj⟩ := ht
    have hz := deleted_zero_from_junta i j p (p' i) (e i) (hp i) q r hq a
      (fun k => value (t k)) (value_zero _ hi) (value_full hm _ hj)
      F (F' i) hF.continuous.measurable (hF'm i) hb (hF'b i) hc hcγ (hcompat i)
      (S i (fun k => t k.val)) (fun d hd _ => halign i _ d hd) (hjunta i (fun k => t k.val))
    simpa only [D, influenceNorm, Real.sq_sqrt (influenceSq_nonneg _ _ _)] using hz

end LargeIndependentSets.PhaseTest

end OAI
