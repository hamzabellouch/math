import Mathlib
import OAI.Probability.LogConcave.Sampling.HarmonicMeanDefect

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal RealInnerProductSpace

lemma growth_vector_memLp {d e : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {f : Point d → Point e} (hg : Appell.HasGrowth f) (hm : AEStronglyMeasurable f μ)
    (hμ : Appell.HasMoments μ) : MemLp f 2 μ := by
  exact (memLp_two_iff_integrable_sq_norm hm).mpr ((hg.norm.pow 2).integrable (hm.norm.pow 2) hμ)

lemma centering_lipschitz_memLp {d e : ℕ} {F : Point d → ℝ} {lam K : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {f : Point (d+d) → Point e} (hf : LipschitzWith K f) :
    MemLp f 2 (gibbs (centeringPotential F x r T)) := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact growth_vector_memLp (Appell.HasGrowth.lipschitz hf) hf.continuous.aestronglyMeasurable
    (ht.hasExpMoments hH.smooth.continuous).hasMoments

lemma stationary_sq_integral {d e : ℕ} {μ : Measure (Point d)}
    {f : Point d → Point e} (hf : Measurable f) (hi : MemLp f 2 μ)
    {Ψ : Point d → Point d} (hm : Measurable Ψ) (hlaw : μ.map Ψ=μ) :
    Integrable (fun y => ‖f (Ψ y)‖^2) μ ∧
    (∫y,‖f (Ψ y)‖^2 ∂μ)=∫y,‖f y‖^2 ∂μ := by
  have hmap : MeasurePreserving Ψ μ μ := ⟨hm,hlaw⟩
  refine ⟨(hi.comp_measurePreserving hmap).integrable_norm_pow (by norm_num : (2:ℕ)≠0),?_⟩
  exact (integral_map hm.aemeasurable (hf.norm.pow_const 2).aestronglyMeasurable).symm.trans
    (by rw [hlaw])

def harmonicStationaryMoment {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) : ℝ :=
  ∫y,‖conditionalFieldMean F x r T (productPointEquiv d d y).1‖^2
    ∂gibbs (centeringPotential F x r T)

lemma harmonicStationaryMoment_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) :
    0≤harmonicStationaryMoment F x r T := integral_nonneg (fun _ => sq_nonneg _)

lemma harmonicMean_stationary_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {Ψ : Point (d+d) → Point (d+d)} (hm : Measurable Ψ)
    (hlaw : (gibbs (centeringPotential F x r T)).map Ψ=gibbs (centeringPotential F x r T)) :
    Integrable (fun y => ‖conditionalFieldMean F x r T (productPointEquiv d d (Ψ y)).1‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖conditionalFieldMean F x r T (productPointEquiv d d (Ψ y)).1‖^2
      ∂gibbs (centeringPotential F x r T))=harmonicStationaryMoment F x r T := by
  have hL := (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).comp
    (LipschitzWith.prod_fst.comp (productPointEquiv d d).toContinuousLinearMap.lipschitzWith)
  exact stationary_sq_integral hL.continuous.measurable
    (centering_lipschitz_memLp hF x hr hlam hl hT0 hT1 hL) hm hlaw

lemma harmonicFree_initial_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T z : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (hc : ∀y,Continuous (Ξ y))
    (hinit : ∀y,Ξ y 0=y)
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r T))
    (hz : 0≤z) (hz1 : z≤1) (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    Integrable (fun y => ‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2)
        (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2
        ∂gibbs (centeringPotential F x r T))≤(r*T)^2*harmonicStationaryMoment F x r T := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let q := z*probabilityNodes n i
  have hi := probabilityNodes_mem hn i
  have hq : q∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz hi.1,(mul_le_of_le_one_right hz hi.2).trans hz1⟩
  let μ := volume.restrict (Ioc (0:ℝ) q)
  let M := fun v y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y v)).1
  have hMm : Measurable (fun p : ℝ × Point (d+d) => M p.1 p.2) := by
    simpa only [one_mul,M] using harmonicMean_measurable (z:=1) hF x hr.le hl hT0 hT1 Ξ hm
  have hs : ∀ᵐv ∂μ,Integrable (fun y => ‖M v y‖^2) (gibbs (centeringPotential F x r T)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (harmonicMean_stationary_sq hF x hr hlam hl hT0 hT1
      (hm.comp (measurable_const.prodMk measurable_id)) (hlaw v ⟨hv.1.le,hv.2.trans hq.2⟩)).1
  have hb : ∀ᵐv ∂μ,(∫y,‖M v y‖^2 ∂gibbs (centeringPotential F x r T))≤
      harmonicStationaryMoment F x r T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (harmonicMean_stationary_sq hF x hr hlam hl hT0 hT1
      (hm.comp (measurable_const.prodMk measurable_id)) (hlaw v ⟨hv.1.le,hv.2.trans hq.2⟩)).2.le
  have he := RMSIntegral.weighted_time_seed hMm.aestronglyMeasurable
    (show AEStronglyMeasurable (fun v => Real.sin (q-v)) μ from by fun_prop)
    (harmonicStationaryMoment_nonneg F x r T)
    (Filter.Eventually.of_forall (fun v => Real.abs_sin_le_one (q-v))) hs hb
  have hid (y : Point (d+d)) : harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1=
      (r*T) • (∫v,Real.sin (q-v) • M v y ∂μ) := by
    have hh := conditional_harmonic_integral hF x hr.le hl hT0 hT1 Ξ hc hder y hq
    dsimp only at hh
    rw [hinit,intervalIntegral.integral_of_le hq.1] at hh
    change _=harmonicFree n z (productPointEquiv d d y) i- (r*T) • _ at hh
    rw [hh]
    abel
  have hnorm (v : Point d) : ‖(r*T) • v‖^2=(r*T)^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  change Integrable (fun y => ‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1‖^2) _ ∧
    (∫y,‖harmonicFree n z (productPointEquiv d d y) i-
      (productPointEquiv d d (Ξ y q)).1‖^2 ∂gibbs (centeringPotential F x r T))≤_
  simp_rw [hid,hnorm]
  refine ⟨he.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=q := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 q)=q
    rw [Real.volume_real_Ioc_of_le hq.1,sub_zero]
  rw [hμ,one_pow,mul_one] at he
  exact mul_le_mul_of_nonneg_left (he.2.trans
    (mul_le_of_le_one_left (harmonicStationaryMoment_nonneg F x r T)
      (pow_le_one₀ hq.1 hq.2))) (sq_nonneg _)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma meanCell_error_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a : ℝ) :
    Measurable (fun p : ℝ × Point d =>
      meanPathJet hF x hr hl b 0 (a+(b-a)*p.1) p.2-
      interpolation (probabilityNodes n)
        (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) p.2) p.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (u:=fun t z =>
    meanPathJet hF x hr hl b 0 (a+(b-a)*t) z-
    interpolation (probabilityNodes n)
      (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) t)
  · intro z
    exact ((meanPathJet_time_continuous hF x hr hl hb0 hb1 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).sub
      (interpolation_continuous _ _)
  · intro t
    apply Continuous.measurable
    apply (meanPathJet_space_continuous hF x hr hl hb0 hb1 0 _).sub
    apply continuous_finsetSum
    intro i _
    exact (meanPathJet_space_continuous hF x hr hl hb0 hb1 0 _).const_smul (basis (probabilityNodes n) i t)

theorem mean_cell_quadrature_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀θ∈Icc (0:ℝ) 1,
      Integrable (fun z => ‖(b-a) • (∫t in 0..θ,meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z)-
        cellQuadrature (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) (b-a) θ‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖(b-a) • (∫t in 0..θ,meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z)-
        cellQuadrature (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) (b-a) θ‖^2
        ∂stdGaussian (Point d))≤(b-a)^2*θ^2*
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_interpolation_rms n hn
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell θ hθ
  apply cellQuadrature_error_rms _ _ _ hθ.1
  · intro z
    exact ((meanPathJet_time_continuous hF x hr.le hl (ha.trans hab) hb 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 θ
  · exact (meanCell_error_measurable hF x hr.le hl (ha.trans hab) hb n a).aestronglyMeasurable
  · intro t ht
    exact (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).1
  · intro t ht
    exact (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def meanCellResidual {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (n : ℕ) (a b θ : ℝ) (z : Point d) : Point d :=
  ∫t in 0..θ,meanPathJet hF x hr hl b 0 (a+(b-a)*t) z-
    interpolation (probabilityNodes n)
      (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) t

lemma meanCellResidual_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b θ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a : ℝ) (hθ : 0≤θ) :
    StronglyMeasurable (meanCellResidual hF x hr hl n a b θ) := by
  unfold meanCellResidual
  simp only [intervalIntegral.integral_of_le hθ]
  exact (meanCell_error_measurable hF x hr hl hb0 hb1 n a).stronglyMeasurable.integral_prod_left'

lemma meanCellResidual_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a θ : ℝ) (z : Point d) :
    meanCellResidual hF x hr hl n a b θ z=
      (∫t in 0..θ,meanPathJet hF x hr hl b 0 (a+(b-a)*t) z)-
        cellQuadrature (probabilityNodes n)
          (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) 1 θ := by
  rw [cellQuadrature_eq_integral,one_smul,meanCellResidual,intervalIntegral.integral_sub]
  · exact ((meanPathJet_time_continuous hF x hr hl hb0 hb1 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 θ
  · exact (interpolation_continuous _ _).intervalIntegrable 0 θ

theorem mean_cell_residual_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀θ∈Icc (0:ℝ) 1,
      Integrable (fun z => ‖meanCellResidual hF x hr.le hl n a b θ z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanCellResidual hF x hr.le hl n a b θ z‖^2 ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_interpolation_rms n hn
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell θ hθ
  have he := cellQuadrature_error_rms (ν:=stdGaussian (Point d)) (probabilityNodes n)
    (fun t z => meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z) 1 hθ.1
    (fun z => ((meanPathJet_time_continuous hF x hr.le hl (ha.trans hab) hb 0 z).comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 θ)
    (meanCell_error_measurable hF x hr.le hl (ha.trans hab) hb n a).aestronglyMeasurable
    (fun t ht => (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).1)
    (fun t ht => (hk hF x hr hlam hl hd a b h ha hab hb hh hcell t ⟨ht.1.le,ht.2.trans hθ.2⟩).2)
  simp only [one_smul,one_pow,one_mul] at he
  simp_rw [meanCellResidual_eq hF x hr.le hl (ha.trans hab) hb]
  refine ⟨he.1,he.2.trans ?_⟩
  apply mul_le_of_le_one_left (sq_nonneg _)
  nlinarith [hθ.1,hθ.2]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma affineUnit_mem {a b s : ℝ} (hab : a≤b) (hs : s∈Icc (0:ℝ) 1) :
    a+(b-a)*s∈Icc a b := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs.1,
    mul_le_mul_of_nonneg_left hs.2 (sub_nonneg.mpr hab)]

lemma meanPathJet_cutoff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hbT : b≤T) (ht : t∈Icc 0 b) (n : ℕ) (z : Point d) :
    meanPathJet hF x hr hl T n t z=meanPathJet hF x hr hl b n t z := by
  rw [meanPathJet_eq hF x hr hl ⟨ht.1,ht.2.trans hbT⟩,meanPathJet_eq hF x hr hl ht]

lemma meanCellResidual_cutoff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r a b T θ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ha : 0≤a) (hab : a≤b) (hbT : b≤T)
    (n : ℕ) (hn : 0<n) (hθ : θ∈Icc (0:ℝ) 1) (z : Point d) :
    (∫s in 0..θ,meanPathJet hF x hr hl T 0 (a+(b-a)*s) z-
      interpolation (probabilityNodes n)
        (fun j => meanPathJet hF x hr hl T 0 (a+(b-a)*probabilityNodes n j) z) s)=
      meanCellResidual hF x hr hl n a b θ z := by
  have ht {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : a+(b-a)*s∈Icc 0 b :=
    ⟨ha.trans (affineUnit_mem hab hs).1,(affineUnit_mem hab hs).2⟩
  have he : (fun j => meanPathJet hF x hr hl T 0 (a+(b-a)*probabilityNodes n j) z)=
      (fun j => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n j) z) :=
    funext (fun j => meanPathJet_cutoff hF x hr hl hbT (ht (probabilityNodes_mem hn j)) 0 z)
  rw [he]
  unfold meanCellResidual
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hθ.1] at hs
  dsimp only
  rw [meanPathJet_cutoff hF x hr hl hbT (ht ⟨hs.1,hs.2.trans hθ.2⟩)]

def probabilityMeanDefect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h n) (z : Point d) : Point d :=
  (∫t in 0..probabilityNodeTime T h n i,meanPathJet hF x hr hl T 0 t z)-
    ∑j,probabilityWeight T h n i j • meanPathJet hF x hr hl T 0 (probabilityNodeTime T h n j) z

lemma probabilityMeanDefect_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (i : ProbabilityNode T h n) (z : Point d) :
    probabilityMeanDefect hF x hr hl T h n i z=
      ∑c,probabilityCellLength T h c • meanCellResidual hF x hr hl n
        (logMeshNode T h c.val) (logMeshNode T h (c.val+1)) (compositeAngle (probabilityNodes n) i c) z := by
  have he := compositeQuadrature_defect (probabilityNodes n) (logMeshNode T h)
    (fun t => meanPathJet hF x hr hl T 0 t z)
    (meanPathJet_time_continuous hF x hr hl hT0.le hT1 0 z) i
  simp only [logMeshNode_zero] at he
  change probabilityMeanDefect hF x hr hl T h n i z=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro c hc
  apply congrArg (fun v => probabilityCellLength T h c • v)
  exact meanCellResidual_cutoff hF x hr hl
    (logMeshNode_mem hT0 hT1 hh c.2.le).1
    (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _)).le
    (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2 n hn
    (compositeAngle_mem (probabilityNodes_mem hn) i c) z

theorem probability_mean_defect_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},0<T → T<1 → 0<h → h≤Real.log 2 → ∀i : ProbabilityNode T h n,
      Integrable (fun z => ‖probabilityMeanDefect hF x hr.le hl T h n i z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖probabilityMeanDefect hF x hr.le hl T h n i z‖^2 ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_residual_rms n hn
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall i
  simp_rw [probabilityMeanDefect_eq hF x hr.le hl hT0 hT1 hh n hn]
  have hcell (c : Fin (logMeshCount T h)) := hk hF x hr hlam hl hd
    (logMeshNode T h c.val) (logMeshNode T h (c.val+1)) (2*h)
    (logMeshNode_mem hT0 hT1 hh c.2.le).1
    (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _)).le
    ((logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1)
    (by positivity) (logMeshCell_upper_right hT0 hT1 hh hsmall c.val)
    (compositeAngle (probabilityNodes n) i c) (compositeAngle_mem (probabilityNodes_mem hn) i c)
  apply composite_error_rms _ _ (fun c => (probabilityCellLength_pos hT0 hT1 hh c).le)
    (by rw [probabilityCellLength_sum hT0 hT1 hh]; exact hT1.le) (sq_nonneg _)
  · intro c
    exact (meanCellResidual_measurable hF x hr.le hl
      (logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).1
      ((logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt c.2)).2.trans_lt hT1) n _
      (compositeAngle_mem (probabilityNodes_mem hn) i c).1).aestronglyMeasurable
  · exact fun c => (hcell c).1
  · exact fun c => (hcell c).2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma meanMaterialVector_zero {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r t : ℝ) (y : Point d) :
    meanMaterialVector F x r 0 (t,y)=conditionalFieldMean F x r t y := by
  ext i
  change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r t y)=_
  simp only [EuclideanSpace.basisFun_inner]

lemma meanPathJet_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 T) (z : Point d) :
    meanPathJet hF x hr hl T 0 t z=
      conditionalFieldMean F x r t (fullProbabilityFlow hF x hr hl t z) := by
  rw [meanPathJet_eq hF x hr hl ht,meanMaterialVector_zero]

lemma probabilityFlow_mean_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (ht : t∈Icc 0 T) (z : Point d) :
    fullProbabilityFlow hF x hr hl t z=z-r • (∫s in 0..t,meanPathJet hF x hr hl T 0 s z) := by
  have hc := meanPathJet_time_continuous hF x hr hl hT0 hT1 0 z
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (fullProbabilityFlow_time_continuous hF x hr hl z).continuousOn
    (f':=fun s => -r • meanPathJet hF x hr hl T 0 s z)
    (fun s hs => by
      rw [meanPathJet_zero hF x hr hl ⟨hs.1.le,hs.2.le.trans ht.2⟩]
      exact (fullProbabilityFlow_deriv hF x z hr hl hs.1.le ((hs.2.trans_le ht.2).trans hT1)).hasDerivAt
        (Icc_mem_nhds hs.1 ((hs.2.trans_le ht.2).trans hT1)))
    ((hc.const_smul (-r)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_smul,fullProbabilityFlow_initial] at he
  simp only [Function.id_def,neg_smul] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (by abel)

lemma probabilityPicard_exact_defect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (i : ProbabilityNode T h n) (z : Point d) :
    FinitePicard.step (probabilityWeight T h n)
      (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
      (fun _ => z) (fun j => fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z) i-
      fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n i) z=
      r • probabilityMeanDefect hF x hr hl T h n i z := by
  have hj (j : ProbabilityNode T h n) := probabilityNodeTime_mem hT0 hT1 hh hn j
  have hv (j : ProbabilityNode T h n) :
      probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
        (fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z)=
      -r • meanPathJet hF x hr hl T 0 (probabilityNodeTime T h n j) z := by
    rw [meanPathJet_zero hF x hr hl (hj j)]
    rfl
  change z+∑j,probabilityWeight T h n i j •
    probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
        (fullProbabilityFlow hF x hr hl (probabilityNodeTime T h n j) z)-_=_
  simp_rw [hv,smul_comm (probabilityWeight T h n i _) (-r)]
  rw [←Finset.smul_sum,probabilityFlow_mean_integral hF x hr hl hT0.le hT1 (hj i)]
  unfold probabilityMeanDefect
  rw [smul_sub,neg_smul]
  abel
end LogConcaveSampling

end

end

end

end OAI
