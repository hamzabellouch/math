import Mathlib
import OAI.Probability.Ballisticity.Estimates.IidListProcess
import OAI.Probability.Ballisticity.Estimates.GridOccupation
import OAI.Probability.Ballisticity.Estimates.SharedLimitPastIdentity
import OAI.Probability.Ballisticity.Estimates.TripleTestPerturbation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma product_law_of_uc_decorrelation {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (h : ∀ (F : E →ᵇ ℝ) (G : ℝ →ᵇ ℝ), UniformContinuous G →
      (∫ ω, F (Z ω)*(G (X ω)-(∫ z, G z ∂γ)) ∂μ)=0) :
    μ.map (fun ω => (Z ω,X ω))=(μ.map Z).prod γ := by
  apply Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro F G
  rw [integral_map (hZ.prodMk hX).aemeasurable (by fun_prop : Measurable (fun z : E × ℝ => F z.1*G z.2)).aestronglyMeasurable,
    integral_map hZ.aemeasurable F.continuous.aestronglyMeasurable]
  have hiF : Integrable (fun ω => F (Z ω)) μ :=
    Integrable.of_bound (F.continuous.measurable.comp hZ).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun ω => F.norm_coe_le_norm _))
  have hi (G' : ℝ →ᵇ ℝ) : Integrable (fun ω => F (Z ω)*G' (X ω)) μ := by
    apply integrable_bounded_mul μ _ _ (F.continuous.measurable.comp hZ)
      (G'.continuous.measurable.comp hX) ‖F‖ ‖G'‖ (norm_nonneg _) ?_ ?_
    · exact fun ω => F.norm_coe_le_norm _
    · exact fun ω => G'.norm_coe_le_norm _
  have he (n : ℕ) : (∫ ω, F (Z ω)*clippedBCF G n (X ω) ∂μ)=
      (∫ ω, F (Z ω) ∂μ)*(∫ z, clippedBCF G n z ∂γ) := by
    have hh := h F (clippedBCF G n) (clippedBCF_uniformContinuous G n)
    simp_rw [mul_sub] at hh
    rw [integral_sub (hi _) (hiF.mul_const _),integral_mul_const] at hh
    exact sub_eq_zero.mp hh
  have hl := integral_weighted_clippedBCF_tendsto μ X (fun ω => F (Z ω)) hX
    (F.continuous.measurable.comp hZ) ‖F‖ (norm_nonneg _) (fun ω => F.norm_coe_le_norm _) G
  have hr := (integral_clippedBCF_tendsto γ id measurable_id G).const_mul (∫ ω, F (Z ω) ∂μ)
  exact tendsto_nhds_unique hl (hr.congr (fun n => (he n).symm))

lemma uc_decorrelation_hasLaw {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (h : ∀ (F : E →ᵇ ℝ) (G : ℝ →ᵇ ℝ), UniformContinuous G →
      (∫ ω, F (Z ω)*(G (X ω)-(∫ z, G z ∂γ)) ∂μ)=0) : HasLaw X γ μ := by
  have hp := product_law_of_uc_decorrelation μ γ Z X hZ hX h
  have he := congrArg (fun ξ : Measure (E × ℝ) => ξ.map Prod.snd) hp
  rw [Measure.map_map measurable_snd (hZ.prodMk hX)] at he
  simpa using (show HasLaw X γ μ from ⟨hX.aemeasurable,by simpa [Measure.map_apply hZ, Function.comp_def] using he⟩)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_interior_past_identity {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0
        (Real.toNNReal (T*((t:ℝ)-s)/(2*commonMeanWidth ν ℓ))))
      (jointPastIncrementMap b (P,(v,s,t))) ∂(V : Measure RealPathPair))=0 := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let a := fun i => T*n i
  let H := fun i => ⌊(s:ℝ)*a i⌋₊+1
  let k := fun i => ⌊T*((t:ℝ)-s)*n i⌋₊
  let j := fun i z => ⌊(v z:ℝ)*a i⌋₊
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ha : Tendsto a atTop atTop := hn.const_mul_atTop hT
  have he := interiorPastGrid_eventually a ha v s t hv hst.le ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let u := fun i => i+N
  have hu : Tendsto u atTop atTop := tendsto_add_atTop_nat N
  have hgood (i : ℕ) := hN (u i) (Nat.le_add_left N i)
  have hnpos (i : ℕ) : 0 < n (u i) := (mul_pos_iff_of_pos_left hT).mp (hgood i).1
  have hk (i : ℕ) : (k (u i):ℝ) ≤ T*n (u i) := by
    have hh := (hgood i).2.2.1
    have hn0 : (0:ℝ) ≤ (H (u i):ℝ) := Nat.cast_nonneg _
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a]; ring
    rw [heq] at hh
    change ((H (u i)+k (u i):ℕ):ℝ) ≤ a (u i) at hh
    push_cast at hh
    exact le_trans (by linarith) hh
  have hkconv : Tendsto (fun i => (k (u i):ℝ)/n (u i)) atTop (𝓝 (T*((t:ℝ)-s))) :=
    ((tendsto_nat_floor_mul_div_atTop (mul_nonneg hT.le (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)))).comp hn).comp hu
  apply shared_limit_finite_past_identity ν hue e f hef htrans (r ∘ u) (hr.comp hu) hnpos T hT
    (k ∘ u) hk (T*((t:ℝ)-s)) hkconv (x ∘ u) (x ∘ u) (fun _ => rfl)
    (H ∘ u) (fun _ => Nat.succ_pos _) (j ∘ u) (fun i z => (hgood i).2.1 z)
    (fun i => interiorPastGrid (a (u i)) v s t) (v,s,t)
    ((interiorPastGrid_tendsto a ha v s t hst.le).comp hu)
    (μ ∘ u) V (hweak.comp hu) F G hG b
  · exact fun i z => (hgood i).2.2.2.1 z
  · exact fun i => (hgood i).2.2.2.2.1
  · intro i
    change a (u i)*(interiorPastGrid (a (u i)) v s t |>.2.2:ℝ) = (H (u i):ℝ)+(k (u i):ℝ)
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a]; ring
    simpa only [H,k,heq] using (hgood i).2.2.2.2.2
  · exact fun i => hμ (u i)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_abs_le_abs (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ |z| := by
  by_cases hz : |z| ≤ w
  · rw [symmetricClip_eq_self w hz]
  · exact (symmetricClip_bound w z).trans (le_of_not_ge hz)

lemma unit_clip_product_error (x y : ℝ) :
    |x*y-symmetricClip 1 x*symmetricClip 1 y| ≤ 2*(|x|^3+|y|^3) := by
  by_cases hx : |x| ≤ 1
  · by_cases hy : |y| ≤ 1
    · rw [symmetricClip_eq_self 1 (by simpa using hx),symmetricClip_eq_self 1 (by simpa using hy),sub_self,abs_zero]
      positivity
    · have hh : |x| * |y| ≤ |y|^3 := by nlinarith [abs_nonneg x,abs_nonneg y,sq_nonneg (|y|-1)]
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg x) 3]
  · by_cases hy : |y| ≤ |x|
    · have hx1 : 1 ≤ |x| := le_of_not_ge hx
      have hh : |x| * |y| ≤ |x|^3 := by
        have h1 := mul_le_mul_of_nonneg_left hy (abs_nonneg x)
        have h2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg |x|)
        nlinarith
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg y) 3]
    · have hy1 : 1 ≤ |y| := (le_of_not_ge hx).trans (le_of_not_ge hy)
      have hh : |x| * |y| ≤ |y|^3 := by
        have h1 := mul_le_mul_of_nonneg_right (le_of_not_ge hy) (abs_nonneg y)
        have h2 := mul_le_mul_of_nonneg_right hy1 (sq_nonneg |y|)
        nlinarith
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg x) 3]

lemma gaussian_absolute_moment_integrable (v : ℝ≥0) (k : ℕ) :
    Integrable (fun z : ℝ => |z|^k) (gaussianReal 0 v) := by
  exact integrable_pow_abs_of_mem_interior_integrableExpSet (X := id) (by simp) k

noncomputable def normalThirdMoment : ℝ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1

lemma normalThirdMoment_nonneg : 0 ≤ normalThirdMoment := integral_nonneg (fun z => by positivity)

lemma gaussian_absolute_third_moment (v : ℝ≥0) :
    (∫ z : ℝ, |z|^3 ∂gaussianReal 0 v)= (Real.sqrt v)^3*normalThirdMoment := by
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt v*z)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
    exact NNReal.eq (Real.sq_sqrt v.coe_nonneg)
  rw [← hm,integral_map (by fun_prop : Measurable (fun z => Real.sqrt v*z)).aemeasurable
    (by fun_prop : Measurable (fun z : ℝ => |z|^3)).aestronglyMeasurable]
  simp_rw [abs_mul,mul_pow,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact integral_const_mul _ _

end DirectionalTransience

end

end

end OAI
