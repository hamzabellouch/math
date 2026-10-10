import Mathlib
import OAI.Probability.SKFluctuations.GaussianSmallScale

namespace OAI

/-! Martingale Compensator Lp. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem boundedMartingale_compensator_Lp {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {X : ℕ → Ω → E} (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N ω^p ∂μ)^((p:ℝ)⁻¹) ≤
      (p:ℝ)*(∫ ω, ‖X N ω‖^(2*p) ∂μ)^((p:ℝ)⁻¹) := by
  have h := boundedMartingale_compensator_moment hX hR hp N
  have hU := boundedMartingale_sq_submartingale hX hR
  have hA : 0 ≤ ∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N ω^p ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [finiteCompensator_monotone hU] with ω hm
    apply pow_nonneg
    simpa only [finiteCompensator_zero] using hm (Nat.zero_le N)
  have hN : 0 ≤ ∫ ω, ‖X N ω‖^(2*p) ∂μ := integral_nonneg (fun ω => pow_nonneg (norm_nonneg _) _)
  have hh := Real.rpow_le_rpow hA h (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg p) _) hN,
    Real.pow_rpow_inv_natCast (Nat.cast_nonneg p) (Nat.ne_of_gt hp)] at hh
  exact hh

 
 theorem boundedDoob_compensator_moment (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Ω → E) {R : ℝ} (hR : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖(μ[Y | 𝒢 j]) ω‖^2) N ω^p ∂μ) ≤
      (p:ℝ)^p*∫ ω, ‖(μ[Y | 𝒢 N]) ω‖^(2*p) ∂μ := by
  exact boundedMartingale_compensator_moment (martingale_condExp Y 𝒢 μ)
    (fun _ => ae_bdd_norm_condExp_of_ae_bdd_norm hR) hp N

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 
noncomputable def conditionalSquareSum (μ : Measure Ω)
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → E) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range N, (μ[fun ω => ‖X (j+1) ω-X j ω‖^2 | 𝒢 j]) ω

 theorem boundedMartingale_conditionalSquareSum_eq
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (N : ℕ) :
    conditionalSquareSum μ 𝒢 X N =ᵐ[μ]
      finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N := by
  have h : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      (μ[fun ω => ‖X (j+1) ω-X j ω‖^2 | 𝒢 j]) ω =
        (μ[(fun ω => ‖X (j+1) ω‖^2)-(fun ω => ‖X j ω‖^2) | 𝒢 j]) ω :=
    ae_all_iff.mpr fun j => boundedMartingale_conditional_square_increment hX hR j
  filter_upwards [h] with ω hω
  exact Finset.sum_congr rfl (fun j _ => hω j)

 

 theorem boundedMartingale_conditionalSquareSum_moment
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R)
    {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, conditionalSquareSum μ 𝒢 X N ω^p ∂μ) ≤
      (p:ℝ)^p*∫ ω, ‖X N ω‖^(2*p) ∂μ := by
  have he := boundedMartingale_conditionalSquareSum_eq hX hR N
  have hi : (∫ ω, conditionalSquareSum μ 𝒢 X N ω^p ∂μ) =
      (∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N ω^p ∂μ) := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
  rw [hi]
  exact boundedMartingale_compensator_moment hX hR hp N

 theorem boundedMartingale_conditionalSquareSum_Lp
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R)
    {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, conditionalSquareSum μ 𝒢 X N ω^p ∂μ)^((p:ℝ)⁻¹) ≤
      (p:ℝ)*(∫ ω, ‖X N ω‖^(2*p) ∂μ)^((p:ℝ)⁻¹) := by
  have he := boundedMartingale_conditionalSquareSum_eq hX hR N
  have hi : (∫ ω, conditionalSquareSum μ 𝒢 X N ω^p ∂μ) =
      (∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N ω^p ∂μ) := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
  rw [hi]
  exact boundedMartingale_compensator_Lp hX hR hp N

 

 theorem boundedDoob_conditionalSquareSum_Lp
    (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) (Y : Ω → E)
    {R : ℝ} (hR : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, conditionalSquareSum μ 𝒢 (fun j => μ[Y | 𝒢 j]) N ω^p ∂μ)^((p:ℝ)⁻¹) ≤
      (p:ℝ)*(∫ ω, ‖(μ[Y | 𝒢 N]) ω‖^(2*p) ∂μ)^((p:ℝ)⁻¹) := by
  exact boundedMartingale_conditionalSquareSum_Lp (martingale_condExp Y 𝒢 μ)
    (fun _ => ae_bdd_norm_condExp_of_ae_bdd_norm hR) hp N

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

noncomputable def slopeTangent (a b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (p.1,a*p.1+b*p.2)
  invFun p := (p.1,(p.2-a*p.1)/b)
  left_inv p := by ext; dsimp; field_simp; ring
  right_inv p := by ext; dsimp; field_simp; ring
  map_add' p q := by
    apply Prod.ext
    · rfl
    · dsimp; ring
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · dsimp; ring
  continuous_toFun := continuous_fst.prodMk ((continuous_const.mul continuous_fst).add
    (continuous_const.mul continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((continuous_snd.sub
    (continuous_const.mul continuous_fst)).div_const b)

theorem fderiv_apply_eq_partials (g : ℝ × ℝ → ℝ) (p q : ℝ × ℝ) :
    fderiv ℝ g p q = timePartial g p*q.1+spacePartial g p*q.2 := by
  have he : q = q.1 • ((1,0) : ℝ × ℝ)+q.2 • ((0,1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,timePartial,spacePartial]
  ring

noncomputable def inverseSlope (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Function.invFun (fun x => g (p.1,x)) p.2

noncomputable def inverseSlopeMap (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1,inverseSlope g p)

theorem inverseSlope_left {g : ℝ × ℝ → ℝ} {t : ℝ}
    (ht : Function.Injective (fun x => g (t,x))) (x : ℝ) :
    inverseSlope g (t,g (t,x)) = x := Function.leftInverse_invFun ht x

private theorem ImplicitSlope_slopeMap_hasFDerivAt {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : DifferentiableAt ℝ g p) (hb : spacePartial g p ≠ 0) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1,g q))
      (slopeTangent (timePartial g p) (spacePartial g p) hb : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  convert hasFDerivAt_fst.prodMk hg.hasFDerivAt using 1; try rfl
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · rfl
  · exact (fderiv_apply_eq_partials g p q).symm

theorem inverseSlopeMap_hasFDerivAt {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g {p : ℝ × ℝ | 0 < p.1})
    (hi : ∀ t, 0 < t → Function.Injective (fun x => g (t,x)))
    {t x : ℝ} (ht : 0 < t) (hb : spacePartial g (t,x) ≠ 0) :
    HasFDerivAt (inverseSlopeMap g)
      ((slopeTangent (timePartial g (t,x)) (spacePartial g (t,x)) hb).symm :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (t,g (t,x)) := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hga := (hg (t,x) ht).contDiffAt (hS.mem_nhds ht)
  have hf : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (p.1,g p)) (t,x) := contDiffAt_fst.prodMk hga
  have hd := ImplicitSlope_slopeMap_hasFDerivAt (hga.differentiableAt one_ne_zero) hb
  apply HasStrictFDerivAt.hasFDerivAt
  apply (hf.hasStrictFDerivAt' hd one_ne_zero).to_local_left_inverse
  filter_upwards [hS.mem_nhds ht] with q hq
  exact Prod.ext rfl (inverseSlope_left (hi q.1 hq) q.2)

theorem inverseSlopeMap_contDiffAt {g : ℝ × ℝ → ℝ}
    (hg : ∀ k : ℕ, ContDiffOn ℝ k g {p : ℝ × ℝ | 0 < p.1})
    (hi : ∀ t, 0 < t → Function.Injective (fun x => g (t,x)))
    {t x : ℝ} (ht : 0 < t) (hb : spacePartial g (t,x) ≠ 0) (k : ℕ) :
    ContDiffAt ℝ k (inverseSlopeMap g) (t,g (t,x)) := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hga := (hg (k+1) (t,x) ht).contDiffAt (hS.mem_nhds ht)
  have hn : (k+1 : ℕ) ≠ (0 : WithTop ℕ∞) := by simp
  have hf : ContDiffAt ℝ (k+1 : ℕ) (fun p : ℝ × ℝ => (p.1,g p)) (t,x) := contDiffAt_fst.prodMk hga
  have hd := ImplicitSlope_slopeMap_hasFDerivAt (hga.differentiableAt hn) hb
  have hh := hf.to_localInverse hd hn
  have he := (hf.hasStrictFDerivAt' hd hn).localInverse_unique
    (g := inverseSlopeMap g) (by
      filter_upwards [hS.mem_nhds ht] with q hq
      exact Prod.ext rfl (inverseSlope_left (hi q.1 hq) q.2))
  exact (hh.congr_of_eventuallyEq he).of_le (by simp)

theorem inverseSlope_time_hasDerivAt {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g {p : ℝ × ℝ | 0 < p.1})
    (hi : ∀ t, 0 < t → Function.Injective (fun x => g (t,x)))
    {t x : ℝ} (ht : 0 < t) (hb : spacePartial g (t,x) ≠ 0) :
    HasDerivAt (fun s => inverseSlope g (s,g (t,x)))
      (-timePartial g (t,x)/spacePartial g (t,x)) t := by
  have hh := (inverseSlopeMap_hasFDerivAt hg hi ht hb).snd.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (g (t,x))))
  convert hh using 1 <;> try rfl
  change -timePartial g (t,x)/spacePartial g (t,x) =
    (0-timePartial g (t,x)*1)/spacePartial g (t,x)
  ring

theorem inverseSlope_space_hasDerivAt {g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g {p : ℝ × ℝ | 0 < p.1})
    (hi : ∀ t, 0 < t → Function.Injective (fun x => g (t,x)))
    {t x : ℝ} (ht : 0 < t) (hb : spacePartial g (t,x) ≠ 0) :
    HasDerivAt (fun b => inverseSlope g (t,b)) (spacePartial g (t,x))⁻¹ (g (t,x)) := by
  have hh := (inverseSlopeMap_hasFDerivAt hg hi ht hb).snd.comp_hasDerivAt (g (t,x))
    ((hasDerivAt_const (g (t,x)) t).prodMk (hasDerivAt_id (g (t,x))))
  convert hh using 1 <;> try rfl
  change (spacePartial g (t,x))⁻¹ =
    (1-timePartial g (t,x)*0)/spacePartial g (t,x)
  simp

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open Filter Set
open scoped Topology

theorem monotone_initial_ratio_uniform_bounds {f : ℝ → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (ht : Tendsto (fun u => f u/u) (𝓝[>] 0) (𝓝 κ))
    (hm : MonotoneOn f (Ioc (0:ℝ) 1))
    (hp : ∀ u ∈ Ioo (0:ℝ) 1, 0 < f u)
    (hupp : ∀ u ∈ Ioo (0:ℝ) 1, f u ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u ∈ Ioo (0:ℝ) 1, c*u ≤ f u ∧ f u ≤ C*u := by
  have he : ∀ᶠ u in 𝓝[>] 0, κ/2 < f u/u ∧ f u/u < 2*κ :=
    ht.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhdsWithin_iff.mp he
  let δ := min (ε/2) (1/2:ℝ)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ ≤ ε/2 := min_le_left _ _
  have hfd : 0 < f δ := hp δ ⟨hδ,hδ1⟩
  refine ⟨min (κ/2) (f δ),max (2*κ) (1/δ),lt_min (half_pos hκ) hfd,
    (mul_pos (by norm_num) hκ).trans_le (le_max_left _ _),?_⟩
  intro u hu
  obtain hud | hud := lt_or_ge u δ
  · have hd : dist u (0:ℝ) < ε := by rw [Real.dist_eq,sub_zero,abs_of_pos hu.1]; linarith
    have hb := hεb ⟨hd,hu.1⟩
    constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans
        ((le_div_iff₀ hu.1).mp hb.1.le)
    · exact ((div_le_iff₀ hu.1).mp hb.2.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)
  · have hmono := hm ⟨hδ,hδ1.le⟩ ⟨hu.1,hu.2.le⟩ hud
    constructor
    · calc
        min (κ/2) (f δ)*u ≤ f δ*u := mul_le_mul_of_nonneg_right (min_le_right _ _) hu.1.le
        _ ≤ f δ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2.le hfd.le
        _ ≤ f u := hmono
    · calc
        f u ≤ 1 := hupp u hu
        _ ≤ (1/δ)*u := by
          have hh : (1:ℝ) ≤ u/δ := (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hud)
          simpa only [one_div_mul_eq_div] using hh
        _ ≤ max (2*κ) (1/δ)*u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.1.le

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

 theorem scalarPlantedGapCurvature_root {R : GaussianResidual} (hR : R.residual.Cone)
    {α : NonnegativeMassProfile} (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m T s : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (hs : s ∈ Ioo 0 T)
    (hzero : scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
      ((scalarProfileHeatJet α hα l t).scalarGapCurvature m T s) = 0) :
    0 < scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
      ((scalarProfileHeatJet α hα l t).scalarGapThird m T s) := by
  let J := scalarProfileHeatJet α hα l t
  have hG (k : ℕ) (i : Fin 1) : BddSmooth k (J.G i) := scalarProfileJet_bddSmooth_all α hα l t k 0
  have hA := (J.gapJet hG hm (T-s)).smoothA
  have hz := J.plantedGap_test R hm hs hA
  change scalarWeightedMoment (J.plantedIncoming R m T) (J.scalarGapCurvature m T s) = _ at hz
  rw [hz] at hzero
  have hc (k) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k (T-s)
  have hB := (((hc 3).pow 2).sub (((hc 1).mul ((hc 2).pow 2)).const_mul (12*m))).add (((hc 1).pow 4).const_mul (6*m^2))
  have hg := J.plantedGap_test R hm hs hB
  change scalarWeightedMoment (J.plantedIncoming R m T) (J.scalarGapThird m T s) = _ at hg
  change 0 < scalarWeightedMoment (J.plantedIncoming R m T) (J.scalarGapThird m T s)
  rw [hg]
  have hr : (Real.toNNReal (T-s):ℝ) = T-s := Real.coe_toNNReal _ (sub_nonneg.mpr hs.2.le)
  have he (k : ℕ) (x : ℝ) : scalarClockProfileJet α hα l t m (Real.toNNReal (T-s)) k x =
      J.scalarClockJet m k (T-s) (fun _ => x) := by
    unfold scalarClockProfileJet
    rw [hr]
  have h0 (x : ℝ) : J.scalarClockJet m 0 (T-s) (fun _ => x) =
      clockContinuation m J.F (T-s) (fun _ => x) := rfl
  have hh := scalarClockProfile_residual_transversality α hα l t hm hmα (Real.toNNReal (T-s))
    (GaussianResidual.cone_heat hR hs.1.le)
  simp only [he,h0] at hh
  have hp := hh (by simpa only [GaussianResidual.plantedDensity,HeatJet.gapJet,HeatJet.gapTest0] using hzero)
  simpa only [GaussianResidual.plantedDensity,HeatJet.scalarClockJet,Nat.reduceAdd,mul_assoc] using hp
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

 theorem HeatJet.weightedSquare_bound (J : HeatJet 0) {m : ℝ} (hm : 0 < m) (T : ℝ) :
    AbsBounded (fun p : ℝ × ℝ => J.filledSquare hm T p.1 (fun _ => p.2)) := by
  obtain ⟨K,hK,hb⟩ := (J.family hm).square.boundedA
  exact ⟨K,hK,fun p => clockTest_abs_le (J.evolve hm (T-p.1)).lipschitz
    (J.evolve hm (T-p.1)).square.smoothA (fun y => hb (T-p.1,y)) m p.1 (fun _ => p.2)⟩

 theorem HeatJet.weightedSquare_continuous (J : HeatJet 0) {m : ℝ} (hm : 0 < m)
    {ρ : ℝ → ℝ} (hρ : Integrable ρ) (T : ℝ) :
    Continuous (fun s => scalarWeightedMoment ρ (J.filledSquare hm T s)) := by
  apply weighted_bounded_continuous hρ
  · intro s
    exact (clockTest_bddSmooth (J.evolve hm (T-s)).regular (J.evolve hm (T-s)).square.smoothA m s).continuous.comp
      (continuous_pi fun _ => continuous_id)
  · intro x
    exact J.continuous_filledSquare hm T (fun _ => x)
  · exact J.weightedSquare_bound hm T

 theorem HeatJet.weightedSquare_hasDerivAt (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hA : J.A = J.G 0) (hA₁ : J.A₁ 0 = J.H 0)
    {m : ℝ} (hm : 0 < m) {ρ : ℝ → ℝ} (hρ : Integrable ρ) {T s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => scalarWeightedMoment ρ (J.filledSquare hm T r))
      (scalarWeightedMoment ρ (J.scalarGapEnergy m T s)) s := by
  apply weighted_bounded_hasDerivAt hρ hs
  · intro r
    exact (clockTest_bddSmooth (J.evolve hm (T-r)).regular (J.evolve hm (T-r)).square.smoothA m r).continuous.comp
      (continuous_pi fun _ => continuous_id)
  · intro r
    exact (clockTest_bddSmooth (J.evolve hm (T-r)).regular
      (J.scalarJetTest hG hm 1 (T-r)).square.smoothA m r).continuous.comp (continuous_pi fun _ => continuous_id)
  · obtain ⟨K,hK,hb⟩ := J.weightedSquare_bound hm T
    exact ⟨K,hK,fun x => hb (s,x)⟩
  · exact J.scalarGapEnergy_bound hG hm T
  · intro r hr x
    rw [← J.filledEnergy_eq_scalarGapEnergy hA hA₁ hm]
    exact J.hasDerivAt_filledSquare hm hr (fun _ => x)

 

 theorem scalarPlanted_no_stationary_gap {R : GaussianResidual} (hR : R.residual.Cone)
    {α : NonnegativeMassProfile} (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m T : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (hT : 0 < T) (c : ℝ)
    (hend : scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
        ((scalarProfileHeatJet α hα l t).filledSquare hm T T) -
      scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
        ((scalarProfileHeatJet α hα l t).filledSquare hm T 0) = c*T)
    (hleft : scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
      ((scalarProfileHeatJet α hα l t).scalarGapEnergy m T 0) ≤ c)
    (hright : scalarWeightedMoment ((scalarProfileHeatJet α hα l t).plantedIncoming R m T)
      ((scalarProfileHeatJet α hα l t).scalarGapEnergy m T T) ≤ c) : False := by
  let J := scalarProfileHeatJet α hα l t
  let ρ := J.plantedIncoming R m T
  have hρ : Integrable ρ := J.plantedIncoming_integrable R hm T
  have hG (k : ℕ) (i : Fin 1) : BddSmooth k (J.G i) := scalarProfileJet_bddSmooth_all α hα l t k 0
  have hH (k : ℕ) (i : Fin 1) : BddSmooth k (J.H i) := scalarProfileJet_bddSmooth_all α hα l t k 1
  let q := fun s => scalarWeightedMoment ρ (J.filledSquare hm T s)-c*s
  let e := fun s => scalarWeightedMoment ρ (J.scalarGapEnergy m T s)-c
  let g := fun s => scalarWeightedMoment ρ (J.scalarGapCurvature m T s)
  let d := fun s => scalarWeightedMoment ρ (J.scalarGapThird m T s)
  have he : Continuous e := (J.weightedGapEnergy_continuous hG hm hρ T).sub continuous_const
  have hg : Continuous g := J.weightedGapCurvature_continuous hG hm hρ T
  have hq : Continuous q := (J.weightedSquare_continuous hm hρ T).sub (continuous_const.mul continuous_id)
  apply transverse_no_stationary_gap hT he.continuousOn hg.continuousOn
    (fun s hs => (J.weightedGapEnergy_hasDerivAt hG hm hH hρ hs).sub_const c)
    (fun s hs => J.weightedGapCurvature_hasDerivAt hG hm hH hρ hs)
    (fun s hs hz => scalarPlantedGapCurvature_root hR hα l t hm hmα hs hz) hq.continuousOn
  · intro s hs
    change HasDerivAt (fun r => scalarWeightedMoment ρ (J.filledSquare hm T r)-c*r)
      (scalarWeightedMoment ρ (J.scalarGapEnergy m T s)-c) s
    convert (J.weightedSquare_hasDerivAt hG rfl rfl hm hρ hs).sub ((hasDerivAt_id s).const_mul c) using 1 <;> first | rfl | simp only [mul_one]
  · dsimp only [q]
    simp only [mul_zero,sub_zero]
    change scalarWeightedMoment ρ (J.filledSquare hm T T)-scalarWeightedMoment ρ (J.filledSquare hm T 0) = c*T at hend
    linarith
  · exact sub_nonpos.mpr hleft
  · exact sub_nonpos.mpr hright
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalRootIntegral_lower {w : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    {c : ℝ} (hc : 0 < c) (hEc : ∀ x, c ≤ E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0))
    (hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0))
    (hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0))
    (hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0))
    (hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0))
    (hiG : IntegrableOn (fun x => w x*S.G x) (Ioi 0))
    (hiT : IntegrableOn (fun x => w x*S.thirdTest x) (Ioi 0))
    (hiF : IntegrableOn (fun x => S.rootPrimitive w x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0))
    (htz : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    (htF : Tendsto (fun x => S.rootPrimitive w x*S.R₀ x) atTop (𝓝 0))
    (htFlux : Tendsto (fun x => w x*S.generalFlux D x) atTop (𝓝 0))
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    c^2*(∫ x in Ioi 0, w x*S.Φ x*x^2) ≤ ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hEp (x) : 0 < E x := hc.trans_le (hEc x)
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hFt := S.rootPrimitive_tendsto hi hcenter
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds_general hD hD0 hEp hm (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) hFt htz hx
  obtain ⟨a,ha,hφa⟩ := centered_weight_exists_zero hw S.continuous_Φ
    (fun x _ => hwp x) (S.Φ_zero_neg hm) hi hcenter
  have hiRem : IntegrableOn (fun x => w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2)) (Ioi 0) := by
    apply (hi₂.sub (hiQ.mul_const (c^2/2))).congr
    filter_upwards [] with x
    dsimp only [Pi.sub_apply]
    ring
  have hRem : 0 ≤ ∫ x in Ioi 0, w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2) :=
    centered_weight_mul_nonneg (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn
      (potentialTerm_quadratic_monotone hD hE hD0 hc.le hEc hHn) ha.le hφa hi hiRem hcenter
  have h₂ : c^2/2*(∫ x in Ioi 0, w x*S.Φ x*x^2) ≤
      ∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x := by
    have he : (fun x => w x*S.Φ x*(potentialTerm D E x-c^2*x^2/2)) =
        fun x => w x*S.Φ x*potentialTerm D E x-(w x*S.Φ x*x^2)*(c^2/2) := by
      funext x; ring
    rw [he,integral_sub hi₂ (hiQ.mul_const _),integral_mul_const] at hRem
    linarith
  have h₁ : 0 ≤ ∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x := centered_weight_mul_nonneg
    (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn (S.generalR₁_monotone hD hD0 hEp)
    ha.le hφa hi hi₁ hcenter
  have hFi : IntegrableOn (fun x => -w x*S.Φ x*S.R₀ x+F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    apply (hi₀.neg.add hiF).congr
    filter_upwards [] with x
    simp only [Pi.add_apply,Pi.neg_apply,neg_mul,F]
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedPrimitive hdF x) hFi htF
  simp only [S.rootPrimitive_zero w,zero_mul,sub_zero] at hIBP
  have hIBP' : (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x) =
      ∫ x in Ioi 0, F x*(2*S.lam x-5*S.z x*S.κ x) := by
    simp_rw [neg_mul] at hIBP
    have hn : IntegrableOn (fun x => -(w x*S.Φ x*S.R₀ x)) (Ioi 0) := hi₀.neg
    rw [integral_add hn hiF,integral_neg] at hIBP
    linarith
  have hcor : 0 ≤ (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [hIBP',← integral_add hiF hiG]
    exact setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      S.correction_nonneg hm hx.le (hFb x hx.le).1 (hFb x hx.le).2)
  have he : (fun x => w x*S.generalIntegrand D E x) = fun x =>
      (w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x)+w x*S.G x := by
    funext x; dsimp only [generalIntegrand]; ring
  have hi21 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := hi₂.add hi₁
  have hi210 : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x+w x*S.Φ x*S.generalR₁ D x+w x*S.Φ x*S.R₀ x) (Ioi 0) := hi21.add hi₀
  have hroot : IntegrableOn (fun x => w x*S.generalIntegrand D E x) (Ioi 0) := by
    rw [he]
    exact hi210.add hiG
  have heq : (∫ x in Ioi 0, w x*S.generalIntegrand D E x) =
      (∫ x in Ioi 0, w x*S.Φ x*potentialTerm D E x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.generalR₁ D x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [he,integral_add hi210 hiG,integral_add hi21 hi₀,integral_add hi₂ hi₁]
  have hrlower : c^2/2*(∫ x in Ioi 0, w x*S.Φ x*x^2) ≤
      ∫ x in Ioi 0, w x*S.generalIntegrand D E x := by
    rw [heq]
    linarith
  have hfluxi : IntegrableOn (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) (Ioi 0) := by
    apply ((hiT.mul_const (1/2)).sub hroot).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]; ring
  have hfint := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedGeneralFlux hD hdw x) hfluxi htFlux
  simp only [S.generalFlux_zero hD0,mul_zero,sub_zero] at hfint
  have he : (fun x => w x*(S.thirdTest x/2-S.generalIntegrand D E x)) =
      fun x => (w x*S.thirdTest x)*(1/2)-w x*S.generalIntegrand D E x := by funext x; ring
  rw [he,integral_sub (hiT.mul_const _) hroot,integral_mul_const] at hfint
  linarith

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open MeasureTheory Set Filter
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

theorem generalRootIntegral_lower_gaussian {w : ℝ → ℝ} (hm : 0 < m)
    {D E H : ℝ → ℝ} (hD : ∀ x, HasDerivAt D (E x) x)
    (hE : ∀ x, HasDerivAt E (H x) x) (hD0 : D 0 = 0)
    {c : ℝ} (hc : 0 < c) (hEc : ∀ x, c ≤ E x) (hHn : ∀ x, 0 ≤ x → H x ≤ 0)
    (hpD : PolyBounded D) (hpE : PolyBounded E)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-D x-S.A x-3*S.z x)) x)
    (hGauss : GaussianDominated w) (hB : PolyBounded S.B) (hC : PolyBounded S.C)
    (hz : PolyBounded S.z) (hκ : PolyBounded S.κ) (hlam : PolyBounded S.lam)
    (hcLam : Continuous S.lam)
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    c^2*(∫ x in Ioi 0, w x*S.Φ x*x^2) ≤ ∫ x in Ioi 0, w x*S.thirdTest x := by
  have hEp (x) : 0 < E x := hc.trans_le (hEc x)
  have hA : PolyBounded S.A := hz.sub (hB.const_mul m)
  have hΦ : PolyBounded S.Φ := ((hz.pow 2).const_mul 2).sub (hC.const_mul m)
  have hR₀ : PolyBounded S.R₀ := ((hκ.const_mul 2).sub ((hC.const_mul m).div_const 2)).sub
    ((hz.pow 2).div_const 2)
  have hR₁ : PolyBounded (S.generalR₁ D) := (hA.mul hpD).add ((hA.pow 2).div_const 2)
  have hRV : PolyBounded (potentialTerm D E) := ((hpD.pow 2).sub hpE).div_const 2
  have hG : PolyBounded S.G := (hz.const_mul 2).mul (((hz.const_mul 3).mul hκ).sub hlam)
  have hT : PolyBounded S.thirdTest :=
    (((((hz.pow 2).const_mul 4).sub (hC.const_mul (2*m))).sub (hκ.const_mul 2)).pow 2 |>.sub
      ((hC.const_mul (48*m)).mul (hz.pow 2))).add ((hC.pow 2).const_mul (6*m^2))
  have hRate : PolyBounded (fun x => 2*S.lam x-5*S.z x*S.κ x) :=
    (hlam.const_mul 2).sub ((hz.const_mul 5).mul hκ)
  have hFlux : PolyBounded (S.generalFlux D) :=
    (hz.mul ((hκ.const_mul 2).add (hC.const_mul (3*m)))).add
      ((((hpD.div_const 2).sub ((hz.const_mul 3).div_const 2)).add (hA.div_const 2)).mul hΦ)
  have hcD : Continuous D := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hcE : Continuous E := continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt
  have hcRV : Continuous (potentialTerm D E) := ((hcD.pow 2).sub hcE).div_const 2
  have hcB := S.continuous_B
  have hcC := S.continuous_C
  have hcz := S.continuous_z
  have hcκ := S.continuous_κ
  have hcA := S.continuous_A
  have hcR₀ : Continuous S.R₀ := by unfold R₀; fun_prop
  have hcR₁ : Continuous (S.generalR₁ D) := by unfold generalR₁; fun_prop
  have hcG : Continuous S.G := by unfold G; fun_prop
  have hcT : Continuous S.thirdTest := by unfold thirdTest; fun_prop
  have hcRate : Continuous (fun x => 2*S.lam x-5*S.z x*S.κ x) := by fun_prop
  have hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0) :=
    (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn
  have hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul (PolyBounded.id.pow 2))
      (hw.mul (S.continuous_Φ.mul (continuous_id.pow 2))).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₂ : IntegrableOn (fun x => w x*S.Φ x*potentialTerm D E x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hRV)
      (hw.mul (S.continuous_Φ.mul hcRV)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.generalR₁ D x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₁)
      (hw.mul (S.continuous_Φ.mul hcR₁)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul hR₀)
      (hw.mul (S.continuous_Φ.mul hcR₀)).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hiG := (hGauss.mul_poly_integrable hG (hw.mul hcG).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiT := (hGauss.mul_poly_integrable hT (hw.mul hcT).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have htz := hGauss.mul_poly_tendsto hz
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds_general hD hD0 hEp hm (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) (S.rootPrimitive_tendsto hi hcenter) htz hx
  have hiF : IntegrableOn (fun x => F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    have hh := (hGauss.mul_poly_integrable (hz.mul hRate)
      (hw.mul (S.continuous_z.mul hcRate)).aestronglyMeasurable).norm.integrableOn (s := Ioi 0)
    apply hh.mono' (hcF.mul hcRate).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx.le),
      abs_of_nonneg (hFb x hx.le).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx.le).2 (abs_nonneg (2*S.lam x-5*S.z x*S.κ x))
  have htF : Tendsto (fun x => F x*S.R₀ x) atTop (𝓝 0) := by
    have ht := (hGauss.mul_poly_tendsto (hz.mul hR₀)).norm
    rw [norm_zero] at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (hwp x),abs_of_nonneg (S.z_nonneg hm hx),
      abs_of_nonneg (hFb x hx).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hFb x hx).2 (abs_nonneg (S.R₀ x))
  exact S.generalRootIntegral_lower hm hD hE hD0 hc hEc hHn hw hwp hdw hi hiQ hi₂ hi₁ hi₀ hiG hiT hiF htz htF
    (hGauss.mul_poly_tendsto hFlux) hcenter

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

theorem scalarClockProfileSlice_residual_root_lower {R : GaussianResidual} (hR : R.residual.Cone)
    (hcenter : ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    (1/R.variance)^2 * (∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x*x^2) ≤ ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  have hdU : ∀ x, HasDerivAt U (S.B x) x := scalarClockProfileJet_deriv α hα l t hm r 0
  have hdw := R.rootWeight_deriv S hdU
  obtain ⟨hB,hC,hz,hκ,hlam⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  have hD (x : ℝ) : HasDerivAt (deriv R.potential) (deriv (deriv R.potential) x) x :=
    (R.potential_second_hasDerivAt x).differentiableAt.hasDerivAt
  have hE (x : ℝ) : HasDerivAt (deriv (deriv R.potential)) (deriv (deriv (deriv R.potential)) x) x :=
    (R.potential_third_hasDerivAt x).differentiableAt.hasDerivAt
  exact S.generalRootIntegral_lower_gaussian hm hD hE (GaussianResidual.potential_gradient_zero hR)
    (one_div_pos.mpr R.positive) (GaussianResidual.potential_curvature_lower hR)
    (fun x hx => (GaussianResidual.potential_shape hR hx).2.2)
    R.potential_gradient_polyBounded R.potential_curvature_polyBounded
    (continuous_iff_continuousAt.mpr fun x => (hdw x).continuousAt)
    (R.rootWeight_pos S U) hdw
    (GaussianResidual.rootWeight_dominated hR S hm.le
      (scalarClockProfileJet_zero_upper α hα l t hm r)
      (scalarClockProfileJet_absBounded α hα l t hm r 1))
    hB hC hz hκ hlam (scalarClockProfileSlice_lam_continuous α hα l t hm hmα r) hcenter

end
end SKFluctuations.Hierarchy

end

end OAI
