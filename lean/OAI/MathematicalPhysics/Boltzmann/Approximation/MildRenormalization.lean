import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMildLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCurveContinuity
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.Topology.Order.Lattice

namespace OAI

section

/-! # A strongly continuous representative of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

def source (g : (ℝ × Position) × Velocity → ℝ) (p : (ℝ × Position) × Velocity) : ℝ :=
  CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p

def characteristicSource (g : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (source g))

def evolution (T : ℝ) (f₀ : Density) (g : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  TorusFlight.eulerianProfile (volume.restrict (Icc 0 T)) f₀ (characteristicSource g)

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem source_measurable (S : MildCollisionSolution T f₀ g) : Measurable (source g) :=
  (CollisionCompactness.gainDensity_measurable S.measurable).sub
    (CollisionCompactness.lossDensity_measurable S.measurable)

theorem characteristicSource_measurable (S : MildCollisionSolution T f₀ g) :
    Measurable (characteristicSource g) :=
  (S.source_measurable.comp MeasurableEquiv.prodAssoc.symm.measurable).comp
    (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem characteristicSource_integrable (S : MildCollisionSolution T f₀ g) :
    Integrable (characteristicSource g) ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hterms := CollisionCompactness.gainLoss_integrable S.measurable S.nonnegative S.pair_integrable
  have hi := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable
      (hterms.1.sub hterms.2)
  have hr : Integrable (TorusFlight.regroup (source g))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
    rw [Measure.volume_eq_prod]
    exact hi
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hr

theorem evolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => evolution T f₀ g z.1 z.2) := by
  have h := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.characteristic
  filter_upwards [h] with z hz
  change TorusFlight.regroup g (z.1,TorusFlight.flight z.1 (TorusFlight.flight (-z.1) z.2)) = _ at hz
  rw [TorusFlight.neg_flight] at hz
  exact hz

theorem evolution_strong_continuity (S : MildCollisionSolution T f₀ g)
    (hT : 0 ≤ T) (hf₀ : Integrable f₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Filter.Tendsto (fun s => eLpNorm (fun p => evolution T f₀ g s p-evolution T f₀ g t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) :=
  TorusFlight.eulerianProfile_L1_continuous hT hf₀ S.characteristicSource_measurable
    S.characteristicSource_integrable ht

theorem evolution_initial (hT : 0 ≤ T) (p : Phase) : evolution T f₀ g 0 p = f₀ p := by
  change f₀ (TorusFlight.flight (-0) p)+Published.timePrimitive (volume.restrict (Icc 0 T))
    (characteristicSource g) (0,TorusFlight.flight (-0) p) = f₀ p
  simp only [neg_zero,TorusFlight.flight_zero]
  rw [Published.timePrimitive_eq_interval ⟨le_rfl,hT⟩,intervalIntegral.integral_same,add_zero]

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # Renormalization along almost every actual mild characteristic -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continuous_path_nonnegative_of_ae {T : ℝ} {u : ℝ → ℝ}
    (hT : 0 < T) (hu : ContinuousOn u (Icc 0 T))
    (hn : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ u t) :
    ∀ t ∈ Icc 0 T, 0 ≤ u t := by
  have he : u =ᵐ[volume.restrict (Icc 0 T)] (fun t => max (u t) 0) := by
    filter_upwards [hn] with t ht
    exact (max_eq_left ht).symm
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne he hu (hu.sup continuousOn_const)
  intro t ht
  rw [heq ht]
  exact le_max_right _ _

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem nonnegative_integral_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T) :
    ∀ᵐ p : Phase, ∀ t ∈ Icc 0 T, 0 ≤ entropyPath f₀ (characteristicSource g) t p := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hp : ∀ᵐ z ∂μ.prod (volume : Measure Phase),
      0 ≤ f₀ z.2+Published.timePrimitive μ (characteristicSource g) z := by
    filter_upwards [S.characteristic] with z hz
    change TorusFlight.along (TorusFlight.regroup g) z =
      f₀ z.2+Published.timePrimitive μ (characteristicSource g) z at hz
    rw [← hz]
    exact S.nonnegative _
  have hp' := (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hp',S.characteristicSource_integrable.prod_left_ae] with p hpos hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hc : ContinuousOn (fun t => entropyPath f₀ (characteristicSource g) t p) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT.le] at h
    exact continuousOn_const.add h
  apply continuous_path_nonnegative_of_ae hT hc
  filter_upwards [hpos,ae_restrict_mem measurableSet_Icc] with t ht hmem
  change 0 ≤ f₀ p+Published.timePrimitive (volume.restrict (Icc 0 T)) (characteristicSource g) (t,p) at ht
  rwa [Published.timePrimitive_eq_interval hmem] at ht

theorem renormalized_integral_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (β : Renormalization) :
    ∀ᵐ p : Phase,
      (∫ t in (0:ℝ)..T, derivWithin β.toFun (Ici 0)
        (entropyPath f₀ (characteristicSource g) t p/maxwellian p.2)*characteristicSource g (t,p)) =
      maxwellian p.2*β.toFun (entropyPath f₀ (characteristicSource g) T p/maxwellian p.2)-
        maxwellian p.2*β.toFun (f₀ p/maxwellian p.2) := by
  filter_upwards [S.nonnegative_integral_paths hT,S.characteristicSource_integrable.prod_left_ae] with p hn hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f₀ p) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hpath : AbsolutelyContinuousOnInterval (fun t => entropyPath f₀ (characteristicSource g) t p) 0 T :=
    hconst.add hp
  have hd : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun t => entropyPath f₀ (characteristicSource g) t p) (characteristicSource g (t,p)) t := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT.le] using hmem) 0 left_mem_uIcc).const_add (f₀ p)
  simpa only [entropyPath,intervalIntegral.integral_same,add_zero] using
    β.weighted_chain_rule hT.le (maxwellian_pos p.2) hpath hn hd

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The actual mild solution satisfies the tested renormalized path identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem renormalized_tested_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (β : Renormalization) (φ : KineticTest) :
    ∀ᵐ p : Phase,
      (∫ t in (0:ℝ)..T,
        derivWithin β.toFun (Ici 0) (entropyPath f₀ (characteristicSource g) t p/maxwellian p.2)*
          characteristicSource g (t,p)*φ.toFun t (TorusFlight.flight t p).1 p.2+
        maxwellian p.2*β.toFun (entropyPath f₀ (characteristicSource g) t p/maxwellian p.2)*
          φ.transportDerivative t (TorusFlight.flight t p)) =
        maxwellian p.2*β.toFun (entropyPath f₀ (characteristicSource g) T p/maxwellian p.2)*
          φ.toFun T (TorusFlight.flight T p).1 p.2-
        maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2 := by
  filter_upwards [S.nonnegative_integral_paths hT,S.characteristicSource_integrable.prod_left_ae]
    with p hn hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f₀ p) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hpath : AbsolutelyContinuousOnInterval (fun t => entropyPath f₀ (characteristicSource g) t p) 0 T :=
    hconst.add hp
  have hd : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun t => entropyPath f₀ (characteristicSource g) t p) (characteristicSource g (t,p)) t := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT.le] using hmem) 0 left_mem_uIcc).const_add (f₀ p)
  have hφ : AbsolutelyContinuousOnInterval
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2) 0 T :=
    ((φ.contDiff_along p).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2)
      (φ.transportDerivative t (TorusFlight.flight t p)) t :=
    ae_of_all _ (fun t _ => φ.hasDerivAt_along p t)
  simpa only [entropyPath,intervalIntegral.integral_same,add_zero,TorusFlight.flight_zero] using
    β.weighted_tested_chain_rule hT.le (maxwellian_pos p.2) hpath hn hd hφ hφ'

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The unrenormalized local mass test identity on each mild characteristic -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem tested_absolutelyContinuous_path {T : ℝ} {F r ψ ψ' : ℝ → ℝ}
    (hT : 0 ≤ T) (hF : AbsolutelyContinuousOnInterval F 0 T)
    (hr : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ 0 T)
    (hψ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt ψ (ψ' t) t) :
    (∫ t in (0:ℝ)..T, r t*ψ t+F t*ψ' t) = F T*ψ T-F 0*ψ 0 := by
  calc
    _ = ∫ t in (0:ℝ)..T, deriv F t*ψ t+F t*deriv ψ t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hr,hψ'] with t ht hpt hmem
      have htcc : t ∈ Icc 0 T := by
        exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hT] using hmem)
      rw [(ht htcc).deriv,(hpt htcc).deriv]
    _ = _ := hF.integral_deriv_mul_eq_sub hψ

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem mass_tested_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T) (φ : MassTest) :
    ∀ᵐ p : Phase,
      (∫ t in (0:ℝ)..T, characteristicSource g (t,p)*φ.toFun t (TorusFlight.flight t p).1+
        entropyPath f₀ (characteristicSource g) t p*φ.transportDerivative t (TorusFlight.flight t p)) =
        entropyPath f₀ (characteristicSource g) T p*φ.toFun T (TorusFlight.flight T p).1-
          f₀ p*φ.toFun 0 p.1 := by
  filter_upwards [S.characteristicSource_integrable.prod_left_ae] with p hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f₀ p) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hpath : AbsolutelyContinuousOnInterval (fun t => entropyPath f₀ (characteristicSource g) t p) 0 T :=
    hconst.add hp
  have hd : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun t => entropyPath f₀ (characteristicSource g) t p) (characteristicSource g (t,p)) t := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT.le] using hmem) 0 left_mem_uIcc).const_add (f₀ p)
  have hφ : AbsolutelyContinuousOnInterval (fun t => φ.toFun t (TorusFlight.flight t p).1) 0 T :=
    ((φ.contDiff_along p).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt (fun t => φ.toFun t (TorusFlight.flight t p).1)
      (φ.transportDerivative t (TorusFlight.flight t p)) t :=
    ae_of_all _ (fun t _ => φ.hasDerivAt_along p t)
  simpa only [entropyPath,intervalIntegral.integral_same,add_zero,TorusFlight.flight_zero] using
    tested_absolutelyContinuous_path hT.le hpath hd hφ hφ'

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
