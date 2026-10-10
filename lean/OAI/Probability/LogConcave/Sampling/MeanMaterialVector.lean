import Mathlib
import OAI.Probability.LogConcave.Sampling.MeanMaterialL2
import OAI.Probability.LogConcave.Numerics.ChainTaylor
import OAI.Probability.LogConcave.JetEstimates.LogDegree

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem mean_material_polylog (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ : ℝ},0 < r → 0 < lam →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫y,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,y))^2 ∂interpolationLaw F x r ρ)≤
          C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨A,hA⟩ := mean_material_l2 n
  let C := A.logCoefficient 1 2+Real.sqrt (interpolationHessianBudget:ℝ)*A.logCoefficient 0 2
  let k := A.logDegree 1+A.logDegree 0
  refine ⟨C,add_nonneg (A.logCoefficient_nonneg 1 2)
    (mul_nonneg (Real.sqrt_nonneg _) (A.logCoefficient_nonneg 0 2)), k,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  have ht : 1≤1+Real.log ((d:ℝ)+1) := by
    have hh := Real.log_nonneg (show 1≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    linarith
  have hB (j : ℕ) (hj : A.logDegree j≤k) :
      (A.momentBudget d j 2).toReal≤A.logCoefficient j 2*(1+Real.log ((d:ℝ)+1))^k :=
    (A.momentBudget_polylog d j 2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hj) (A.logCoefficient_nonneg j 2))
  have hb : (A.momentBudget d 1 2).toReal+Real.sqrt (interpolationHessianBudget:ℝ)*(A.momentBudget d 0 2).toReal≤
      C*(1+Real.log ((d:ℝ)+1))^k := by
    have hh := add_le_add (hB 1 (Nat.le_add_right _ _))
      (mul_le_mul_of_nonneg_left (hB 0 (Nat.le_add_left _ _)) (Real.sqrt_nonneg (interpolationHessianBudget:ℝ)))
    simpa only [C,add_mul,mul_assoc] using hh
  apply (hA hF x hr hlam hl h0 h1 hd).trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (show 0≤(lam:ℝ)*r*Real.sqrt (d:ℝ) by positivity))
    (show 0≤((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) by positivity)
  convert hh using 1
  ring

theorem mean_path_polylog (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam, ∀(x : Point d) {r ρ : ℝ},∀hr : 0 < r,
        0 < lam → ∀hl : (lam:ℝ)*r^2≤1/2,0≤ρ → ρ<1 → 1≤d →
        Real.sqrt (∑i : Fin d,∫z,
          (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
            (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2 ∂stdGaussian (Point d))≤
          C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
            ((Real.sqrt (1-ρ^2))⁻¹)^(2*n+2) := by
  obtain ⟨C,hC,k,hk⟩ := mean_material_polylog n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r ρ hr hlam hl h0 h1 hd
  rw [mean_material_path_energy hF x hr.le hl h0 h1]
  exact hk hF x hr hlam hl h0 h1 hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

def meanMaterialVector {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (n : ℕ)
    (p : ℝ × Point d) : Point d :=
  WithLp.toLp 2 (fun i => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
    (jointMean F x r i) p)

lemma meanMaterialVector_norm_sq {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (n : ℕ) (p : ℝ × Point d) :
    ‖meanMaterialVector F x r n p‖^2=∑i : Fin d,
      (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
        (jointMean F x r i) p)^2 := EuclideanSpace.real_norm_sq_eq _

lemma meanMaterial_slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    PolySmooth (fun y => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y)) := by
  cases n with
  | zero => exact conditionalFieldMean_component_polySmooth hF x hr hlam hl h0 h1 i
  | succ n =>
    obtain ⟨A,_,he⟩ := mean_material_representation n
    have hp := (interpolationPotential_polySmooth hF x hr hlam hl h0 h1).tensorAdjoint
      (fun j => A.slice_polySmooth hF x hr hlam hl h0 h1 (Sum.elim (fun _ => i) (fun _ => j)))
      (EuclideanSpace.basisFun (Fin d) ℝ)
    have heq : (fun y => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) (n+1)
        (jointMean F x r i) (ρ,y))=
        fun y => ((lam:ℝ)*r)*tensorAdjoint (interpolationPotential F x r ρ)
          (EuclideanSpace.basisFun (Fin d) ℝ)
          (fun j => A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => i) (fun _ => j))) y := by
      funext y
      rw [he hF x hr hlam hl h0 h1 i y,A.outer_slice hF x hr hlam hl h0 h1]
    rw [heq]
    exact (PolySmooth.const _).mul hp

lemma meanMaterial_square_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    Integrable (fun y => (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,y))^2) (interpolationLaw F x r ρ) := by
  have hp := meanMaterial_slice_polySmooth hF x hr hlam hl h0 h1 i n
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith : (lam:ℝ)*r^2<1)
    (by nlinarith : ρ^2<1)]
  simpa only [pow_two] using (hp.mul hp).integrable
    (interpolationPotential_smooth hF x hr.le hl h0 h1).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) h0 h1)

lemma meanMaterial_path_square_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (i : Fin d) (n : ℕ) :
    Integrable (fun z => (JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2) (stdGaussian (Point d)) := by
  have hm := fullProbabilityFlow_interpolation_closed hF x hr.le hl h0 h1
  have hc := (fullProbabilityFlow_lipschitz hF x hr.le hl ⟨h0,h1.le⟩).continuous.measurable
  have hg := (((meanMaterial_slice_polySmooth hF x hr hlam hl h0 h1 i n).smooth.continuous).pow 2).aestronglyMeasurable (μ:=(stdGaussian (Point d)).map (fullProbabilityFlow hF x hr.le hl ρ))
  apply (integrable_map_measure hg hc.aemeasurable).mp
  rw [hm]
  exact meanMaterial_square_integrable hF x hr hlam hl h0 h1 i n

lemma meanMaterial_path_norm_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    Integrable (fun z => ‖meanMaterialVector F x r n
      (ρ,fullProbabilityFlow hF x hr.le hl ρ z)‖^2) (stdGaussian (Point d)) := by
  simp_rw [meanMaterialVector_norm_sq]
  exact integrable_finsetSum _ (fun i _ => meanMaterial_path_square_integrable hF x hr hlam hl h0 h1 i n)

lemma meanMaterial_path_norm_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1) (n : ℕ) :
    (∫z,‖meanMaterialVector F x r n (ρ,fullProbabilityFlow hF x hr.le hl ρ z)‖^2
      ∂stdGaussian (Point d))=
    ∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
      (jointMean F x r i) (ρ,fullProbabilityFlow hF x hr.le hl ρ z))^2 ∂stdGaussian (Point d) := by
  simp_rw [meanMaterialVector_norm_sq]
  exact integral_finsetSum _ (fun i _ => meanMaterial_path_square_integrable hF x hr hlam hl h0 h1 i n)

lemma meanMaterial_path_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : T<1) (ht : t∈Icc 0 T) (n : ℕ) :
    HasDerivWithinAt (fun u => meanMaterialVector F x r n (u,fullProbabilityFlow hF x hr hl u z))
      (meanMaterialVector F x r (n+1) (t,fullProbabilityFlow hF x hr hl t z)) (Icc 0 T) t := by
  have hd := hasDerivWithinAt_pi.mpr (fun i =>
    (mean_material_path_deriv hF x z hr hl ht.1 (ht.2.trans_lt hT) i n).mono
      (show Icc (0:ℝ) T⊆Icc 0 1 by intro u hu; exact ⟨hu.1,hu.2.trans hT.le⟩))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma meanMaterialVector_continuousAt {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (n : ℕ) {p : ℝ × Point d} (h0 : -1<p.1) (h1 : p.1<1) :
    ContinuousAt (meanMaterialVector F x r n) p := by
  have hc := continuousAt_pi.mpr (fun i =>
    (JetCalculus.materialIter_timeSmooth (1,0) jointSpace r (jointMean_timeSmooth hF x hr hl)
      (jointMean_timeSmooth hF x hr hl i) n p h0 h1).continuousAt)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.continuousAt.comp hc

def probabilityTimeClamp (T t : ℝ) : ℝ := min (max t 0) T

lemma probabilityTimeClamp_continuous (T : ℝ) : Continuous (probabilityTimeClamp T) :=
  (continuous_id.max continuous_const).min continuous_const

lemma probabilityTimeClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) :
    probabilityTimeClamp T t∈Icc 0 T := ⟨le_min (le_max_right _ _) hT,min_le_right _ _⟩

lemma probabilityTimeClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : probabilityTimeClamp T t=t := by
  dsimp [probabilityTimeClamp]
  rw [max_eq_left ht.1,min_eq_left ht.2]

def meanPathJet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (T : ℝ) (n : ℕ) (t : ℝ) (z : Point d) : Point d :=
  meanMaterialVector F x r n (probabilityTimeClamp T t,
    fullProbabilityFlow hF x hr hl (probabilityTimeClamp T t) z)

lemma meanPathJet_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 T) (n : ℕ) (z : Point d) :
    meanPathJet hF x hr hl T n t z=
      meanMaterialVector F x r n (t,fullProbabilityFlow hF x hr hl t z) := by
  simp only [meanPathJet,probabilityTimeClamp_eq ht]

lemma meanPathJet_time_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) (z : Point d) :
    Continuous (fun t => meanPathJet hF x hr hl T n t z) := by
  have hτ := probabilityTimeClamp_continuous T
  have hp := hτ.prodMk ((fullProbabilityFlow_time_continuous hF x hr hl z).comp hτ)
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (meanMaterialVector_continuousAt hF x hr hl n
    (by have hh := (probabilityTimeClamp_mem hT0 t).1; change -1<probabilityTimeClamp T t; linarith)
    ((probabilityTimeClamp_mem hT0 t).2.trans_lt hT1)).comp hp.continuousAt

lemma meanPathJet_space_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) (t : ℝ) :
    Continuous (meanPathJet hF x hr hl T n t) := by
  have ht := probabilityTimeClamp_mem hT0 t
  have hp : Continuous (fun z : Point d => (probabilityTimeClamp T t,
      fullProbabilityFlow hF x hr hl (probabilityTimeClamp T t) z)) :=
    continuous_const.prodMk (fullProbabilityFlow_lipschitz hF x hr hl
    (show probabilityTimeClamp T t∈Icc 0 1 from ⟨ht.1,ht.2.trans hT1.le⟩)).continuous
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (meanMaterialVector_continuousAt hF x hr hl n
    (by change -1<probabilityTimeClamp T t; linarith [ht.1]) (ht.2.trans_lt hT1)).comp hp.continuousAt

lemma meanPathJet_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (n : ℕ) :
    Measurable (fun p : ℝ × Point d => meanPathJet hF x hr hl T n p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (meanPathJet_time_continuous hF x hr hl hT0 hT1 n)
    (fun t => (meanPathJet_space_continuous hF x hr hl hT0 hT1 n t).measurable)

lemma meanPathJet_chain {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x z : Point d) {r T t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT1 : T<1) (ht : t∈Icc 0 T) (n : ℕ) :
    HasDerivWithinAt (fun u => meanPathJet hF x hr hl T n u z)
      (meanPathJet hF x hr hl T (n+1) t z) (Icc 0 T) t := by
  rw [meanPathJet_eq hF x hr hl ht]
  exact (meanMaterial_path_chain hF x z hr hl hT1 ht n).congr
    (fun u hu => meanPathJet_eq hF x hr hl hu n z) (meanPathJet_eq hF x hr hl ht n z)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma inverse_sqrt_time_mono {t T : ℝ} (h0 : 0≤t) (ht : t≤T) (hT : T<1) :
    (Real.sqrt (1-t^2))⁻¹≤(Real.sqrt (1-T^2))⁻¹ := by
  have hT0 : 0≤T := h0.trans ht
  have hpos : 0<1-T^2 := by nlinarith
  have hle : 1-T^2≤1-t^2 := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
    (Real.sqrt_le_sqrt hle)

theorem mean_path_taylor_rms (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r T : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,0≤T → T<1 → 1≤d →
      ∀a b : ℝ,0≤a → a≤b → b≤T →
      Integrable (fun z => ‖meanPathJet hF x hr.le hl T 0 b z-
        chainTaylor (fun j t => meanPathJet hF x hr.le hl T j t z) n a b‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl T 0 b z-
        chainTaylor (fun j t => meanPathJet hF x hr.le hl T j t z) n a b‖^2
        ∂stdGaussian (Point d))≤((b-a)^(n+1)/(n.factorial:ℝ))^2*
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*
          ((Real.sqrt (1-T^2))⁻¹)^(2*n+2))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_path_polylog n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r T hr hlam hl hT0 hT1 hd a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) T := by
    rw [uIcc_of_le hab]
    intro t ht; exact ⟨ha.trans ht.1,ht.2.trans hb⟩
  have htI {t : ℝ} (ht : t∈Ioc a b) : t∈Icc (0:ℝ) T := ⟨ha.trans ht.1.le,ht.2.trans hb⟩
  apply chainTaylor_remainder_rms hab (sq_nonneg _) hsub
    (fun z j _ ht => meanPathJet_chain hF x z hr.le hl hT1 ht j)
    (meanPathJet_measurable hF x hr.le hl hT0 hT1 (n+1)).aestronglyMeasurable
  · intro t ht
    simp_rw [meanPathJet_eq hF x hr.le hl (htI ht)]
    exact meanMaterial_path_norm_integrable hF x hr hlam hl (htI ht).1
      ((htI ht).2.trans_lt hT1) (n+1)
  · intro t ht
    simp_rw [meanPathJet_eq hF x hr.le hl (htI ht)]
    let q := ∫z,‖meanMaterialVector F x r (n+1)
      (t,fullProbabilityFlow hF x hr.le hl t z)‖^2 ∂stdGaussian (Point d)
    have hq : 0≤q := integral_nonneg (fun _ => sq_nonneg _)
    have hbnd : Real.sqrt q≤C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*
        (1+Real.log ((d:ℝ)+1))^k*((Real.sqrt (1-T^2))⁻¹)^(2*n+2) := by
      have he : q=∑i : Fin d,∫z,(JetCalculus.materialIter (1,0) jointSpace r
          (jointMean F x r) (n+1) (jointMean F x r i)
          (t,fullProbabilityFlow hF x hr.le hl t z))^2 ∂stdGaussian (Point d) :=
        meanMaterial_path_norm_integral hF x hr hlam hl (htI ht).1 ((htI ht).2.trans_lt hT1) (n+1)
      rw [he]
      apply (hk hF x hr hlam hl (htI ht).1 ((htI ht).2.trans_lt hT1) hd).trans
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (inverse_sqrt_time_mono (htI ht).1 (htI ht).2 hT1) _) _
      have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
      positivity
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg q) hbnd
    simpa only [←sq,Real.sq_sqrt hq] using hsq
end LogConcaveSampling

end

end

end

end OAI
