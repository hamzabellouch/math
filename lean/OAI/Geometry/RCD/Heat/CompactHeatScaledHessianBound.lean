import OAI.Geometry.RCD.Heat.BoundedHeatQuantitativeHessian
import OAI.Geometry.RCD.Sobolev.CompactFactorScaledEnergy
import OAI.Geometry.RCD.Heat.CompactHeatOsmoticVanishing
import OAI.Geometry.RCD.Sobolev.HessianDensityMassBound

namespace OAI

/-! # A quantitative density bound for the actual scaled heat Hessian -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem scaled_hessian_density_bound (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    ∃ M C E : ℝ, 0 < M ∧ 0 ≤ C ∧ 0 < E ∧
      ∀ r : ℝ, 0 < r → ∃ (σ : Measure X) (_ : IsFiniteMeasure σ),
        σ.real (closedBall p r) ≤ M*Real.sqrt ((1+r⁻¹^2)*m.real (closedBall p (2*r))) ∧
        ∀ (k : ℕ) (t : InteriorHeatTime δ) (u v WU WV UV : SobolevSpace m q),
          (SobolevSpace.toLp m q u =ᵐ[m] hX.compactHeatFactor hn p μ (D.left k)
            (ε k/4*t.val) (mul_pos (div_pos (hε k) (by norm_num)) t.val.property.1)) →
          (SobolevSpace.toLp m q v =ᵐ[m] hX.compactHeatFactor hn p ν (D.right k)
            (ε k/4*(1-t.val)) (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.val.property.2))) →
          (SobolevSpace.toLp m q WU =ᵐ[m] localGamma m q w u) →
          (SobolevSpace.toLp m q WV =ᵐ[m] localGamma m q w v) →
          (SobolevSpace.toLp m q UV =ᵐ[m] localGamma m q u v) →
          ∀ᵐ x ∂m.restrict (closedBall p r),
            |(ε k/2)^2*localHessianAction m q w u v WU WV UV x| ≤
              D.interpolationDensity k t.val x*
                (Real.exp |K| *(4*C/δ+16*E*(R+dist p x)^2/δ^2))*
                (1+(σ.rnDeriv m x).toReal) := by
  intro m q w
  obtain ⟨M,hM,hmeasure⟩ := hX.bounded_heat_quantitative_hessian hn p hK f A hf ha
  obtain ⟨C,E,hC,hE,henergy⟩ := hX.compact_factor_scaled_energy hn p
  refine ⟨M,C,E,hM,hC,hE,?_⟩
  intro r hr
  obtain ⟨σ,hσ,hmass,hdata⟩ := hmeasure r hr
  let := hσ
  refine ⟨σ,hσ,hmass,?_⟩
  intro k t u v WU WV UV hu hv hWU hWV hUV
  have hs : 0 < ε k/4*(t.val:ℝ) := mul_pos (div_pos (hε k) (by norm_num)) t.val.property.1
  have ht : 0 < ε k/4*(1-(t.val:ℝ)) :=
    mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.val.property.2)
  obtain ⟨f₀,⟨A₀,hf₀⟩,he₀⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨f₁,⟨A₁,hf₁⟩,he₁⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hur : SobolevSpace.toLp m q u =ᵐ[m] kernelHeat m q hk _ f₀ :=
    hu.trans (Eventually.of_forall (he₀ _ hs))
  have hvr : SobolevSpace.toLp m q v =ᵐ[m] kernelHeat m q hk _ f₁ :=
    hv.trans (Eventually.of_forall (he₁ _ ht))
  have heu : u=heatSobolev m q _ hs f₀ := by
    apply Subtype.ext
    exact Lp.ext (hur.trans (kernelHeat_represents_L2 m q hk hs f₀))
  have hev : v=heatSobolev m q _ ht f₁ := by
    apply Subtype.ext
    exact Lp.ext (hvr.trans (kernelHeat_represents_L2 m q hk ht f₁))
  obtain ⟨hLu,_⟩ := hX.kernelHeat_bounded_regularity hn p hk f₀ A₀ hf₀ _ hs
  obtain ⟨hLv,_⟩ := hX.kernelHeat_bounded_regularity hn p hk f₁ A₁ hf₁ _ ht
  have huA : ∀ᵐ x ∂m, |SobolevSpace.toLp m q u x| ≤ A₀ := by
    rw [heu]
    exact (hX.bounded_heat_sobolev_data hn p f₀ A₀ hf₀ hs).1
  have hvA : ∀ᵐ x ∂m, |SobolevSpace.toLp m q v x| ≤ A₁ := by
    rw [hev]
    exact (hX.bounded_heat_sobolev_data hn p f₁ A₁ hf₁ ht).1
  have huq : IsWeakLaplacian m q u (-heatGenerator m q _ hs f₀) := by
    rw [heu]
    exact heatSobolev_weak_laplacian m q _ hs f₀
  have hvq : IsWeakLaplacian m q v (-heatGenerator m q _ ht f₁) := by
    rw [hev]
    exact heatSobolev_weak_laplacian m q _ ht f₁
  obtain ⟨WU',WV',UV',hWU',hWV',hUV',hbound⟩ := hdata u _ huq _ _ A₀ hLu hur huA
    v _ hvq _ _ A₁ hLv hvr hvA
  have hlocal := localHessianAction_congr m q
    (f := w) (f' := w) (u := u) (u' := u) (v := v) (v' := v)
    (EventuallyEq.refl _ _) (EventuallyEq.refl _ _) (EventuallyEq.refl _ _)
    (hWU'.trans (ae_restrict_of_ae (Filter.EventuallyEq.symm hWU)))
    (hWV'.trans (ae_restrict_of_ae (Filter.EventuallyEq.symm hWV)))
    (hUV'.trans (ae_restrict_of_ae (Filter.EventuallyEq.symm hUV)))
  have hεhalf : ε k/2 ≤ 1 := by linarith [hε1 k]
  have hu' : SobolevSpace.toLp m q u =ᵐ[m] hX.compactHeatFactor hn p μ (D.left k)
      ((ε k/2)*t.val/2) (div_pos (mul_pos (half_pos (hε k)) (hδ.trans_le t.property.1)) (by norm_num)) := by
    simpa only [show (ε k/2)*(t.val:ℝ)/2=ε k/4*t.val by ring] using hu
  have hv' : SobolevSpace.toLp m q v =ᵐ[m] hX.compactHeatFactor hn p ν (D.right k)
      ((ε k/2)*(1-t.val)/2) (div_pos (mul_pos (half_pos (hε k)) (hδ.trans_le t.property.2)) (by norm_num)) := by
    simpa only [show (ε k/2)*(1-(t.val:ℝ))/2=ε k/4*(1-t.val) by ring] using hv
  have hgu := henergy μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k) (D.left_pos k)
    (half_pos (hε k)) hεhalf hδ t.property.1 t.val.property.2.le p R hR hS
    (closedBall p r) (isCompact_closedBall p r) u hu'
  have hgv := henergy ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k) (D.right_pos k)
    (half_pos (hε k)) hεhalf hδ t.property.2 (by linarith [t.val.property.1]) p R hR hT
    (closedBall p r) (isCompact_closedBall p r) v hv'
  filter_upwards [hbound,hlocal,hgu,hgv,ae_restrict_of_ae hu,ae_restrict_of_ae hv,
    ae_restrict_of_ae (localGamma_self m q v)] with x hb hl hgu hgv hux hvx hself
  rw [hl] at hb
  let P := Real.exp |K| *(4*C/δ+16*E*(R+dist p x)^2/δ^2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hv0 : 0 ≤ localGamma m q v v x := by rw [hself]; positivity
  have hρ : D.interpolationDensity k t.val x=SobolevSpace.toLp m q u x*SobolevSpace.toLp m q v x := by
    rw [hux,hvx]
    rfl
  have hm := mul_le_mul hgu hgv (mul_nonneg (sq_nonneg _) hv0) (mul_nonneg (sq_nonneg _) hP)
  have hh : ((ε k/2)^2)^2*localGamma m q u u x*localGamma m q v v x ≤
      (D.interpolationDensity k t.val x*P)^2 := by
    rw [hρ]
    convert hm using 1 <;> ring
  simpa only [abs_mul,abs_of_nonneg (sq_nonneg (ε k/2))] using
    weighted_abs_le_one_add_density (sq_nonneg (ε k/2)) ENNReal.toReal_nonneg
      (mul_nonneg (D.interpolationDensity_pos k t.val x).le hP) hb hh

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
