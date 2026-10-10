import Mathlib
import OAI.Probability.SKFluctuations.ScalarIntervalStrictArea

namespace OAI

/-! Root Square Convex. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.rootFilledEnergy_monotone {n : ℕ} (J : HeatJet n) (T : ℝ)
    (x : Fin (n+1) → ℝ) : MonotoneOn (fun t => J.rootFilledEnergy T t x) (Icc 0 T) := by
  intro r hr s hs hrs
  have he₁ : s-r+(T-s) = T-r := by ring
  have he₂ : r+(s-r) = s := by ring
  have hsq (i : Fin (n+1)) (v : ℝ) : BddSmooth 0 (fun y => (clockRoot (J.A₁ i) v y)^2) := by
    simpa only [pow_two] using (clockRoot_smooth (J.smoothA₁ i) v).mul (clockRoot_smooth (J.smoothA₁ i) v)
  dsimp only [HeatJet.rootFilledEnergy]
  rw [clockRoot_sum (fun i => hsq i (T-r)),clockRoot_sum (fun i => hsq i (T-s))]
  apply Finset.sum_le_sum
  intro i _
  calc
    clockRoot (fun y => (clockRoot (J.A₁ i) (T-r) y)^2) r x ≤
        clockRoot (clockRoot (fun y => (clockRoot (J.A₁ i) (T-s) y)^2) (s-r)) r x := by
      apply clockRoot_mono (hsq i (T-r)) (clockRoot_smooth (hsq i (T-s)) (s-r))
      intro y
      have hh := clockRoot_square_le (clockRoot_smooth (J.smoothA₁ i) (T-s)) (s-r) y
      rwa [clockRoot_add (J.smoothA₁ i) (sub_nonneg.mpr hrs) (sub_nonneg.mpr hs.2),he₁] at hh
    _ = clockRoot (fun y => (clockRoot (J.A₁ i) (T-s) y)^2) s x := by
      rw [clockRoot_add (hsq i (T-s)) hr.1 (sub_nonneg.mpr hrs),he₂]

theorem HeatJet.continuous_rootFilledSquare {n : ℕ} (J : HeatJet n) (T : ℝ)
    (x : Fin (n+1) → ℝ) : Continuous (fun t => J.rootFilledSquare T t x) := by
  simpa only [J.erased_filledSquare] using J.erasePotential.continuous_filledSquare (m:=1) zero_lt_one T x

theorem HeatJet.continuous_rootFilledEnergy {n : ℕ} (J : HeatJet n) (T : ℝ)
    (x : Fin (n+1) → ℝ) : Continuous (fun t => J.rootFilledEnergy T t x) := by
  simpa only [J.erased_filledEnergy] using J.erasePotential.continuous_filledEnergy (m:=1) zero_lt_one T x

theorem HeatJet.rootFilledSquare_convex {n : ℕ} (J : HeatJet n) (T : ℝ)
    (x : Fin (n+1) → ℝ) : ConvexOn ℝ (Icc 0 T) (fun t => J.rootFilledSquare T t x) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 T) (J.continuous_rootFilledSquare T x).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact (J.hasDerivAt_rootFilledSquare ht x).differentiableAt.differentiableWithinAt
  · intro r hr s hs hrs
    rw [interior_Icc] at hr hs
    rw [(J.hasDerivAt_rootFilledSquare hr x).deriv,(J.hasDerivAt_rootFilledSquare hs x).deriv]
    exact J.rootFilledEnergy_monotone T x ⟨hr.1.le,hr.2.le⟩ ⟨hs.1.le,hs.2.le⟩ hrs

 

theorem strict_integral_chord_of_derivative {f g : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt f (g t) t)
    (hc : ConvexOn ℝ (Icc 0 T) f) (hne : g 0 ≠ g T) :
    2*(∫ t in 0..T, f t) < T*(f 0+f T) := by
  let L := fun t : ℝ => (1-t/T)*f 0+(t/T)*f T
  have hLc : Continuous L := by fun_prop
  have hle (t : ℝ) (ht : t ∈ Icc 0 T) : f t ≤ L t := by
    have hh := hc.2 ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩
      (show 0 ≤ 1-t/T by rw [sub_nonneg,div_le_one hT]; exact ht.2)
      (div_nonneg ht.1 hT.le) (by ring : (1-t/T)+t/T = 1)
    simpa only [smul_eq_mul,mul_zero,zero_add,div_mul_cancel₀ _ hT.ne',L] using hh
  have hx : ∃ t ∈ Icc 0 T, f t < L t := by
    by_contra! hh
    have he : ∀ t ∈ Icc 0 T, f t = L t := fun t ht => le_antisymm (hle t ht) (hh t ht)
    have hconst : ∀ t ∈ Ioo 0 T, g t = (f T-f 0)/T := by
      intro t ht
      have he' : f =ᶠ[𝓝 t] L := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
        exact he u ⟨hu.1.le,hu.2.le⟩
      have hdl : HasDerivAt L ((f T-f 0)/T) t := by
        convert! (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const T)).mul_const (f 0)).add
          (((hasDerivAt_id t).div_const T).mul_const (f T)) using 1; ring
      exact (hd t ht).unique (hdl.congr_of_eventuallyEq he')
    have h0 : g 0 = (f T-f 0)/T := by
      apply tendsto_nhds_unique (l:=𝓝[>] (0:ℝ)) ((hg.tendsto 0).mono_left nhdsWithin_le_nhds)
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ t : ℝ in 𝓝 0, t < T from Iio_mem_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
      exact (hconst t ⟨ht,htT⟩).symm
    have h1 : g T = (f T-f 0)/T := by
      apply tendsto_nhds_unique (l:=𝓝[<] T) ((hg.tendsto T).mono_left nhdsWithin_le_nhds)
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ t : ℝ in 𝓝 T, 0 < t from Ioi_mem_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht ht0
      exact (hconst t ⟨ht0,ht⟩).symm
    exact hne (h0.trans h1.symm)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
    hf.continuousOn hLc.continuousOn (fun t ht => hle t ⟨ht.1.le,ht.2⟩) hx
  have he : (∫ t in 0..T, L t) = T*(f 0+f T)/2 := by
    have h1 : IntervalIntegrable (fun t : ℝ => (1-t/T)*f 0) volume 0 T :=
      (show Continuous (fun t : ℝ => (1-t/T)*f 0) by fun_prop).intervalIntegrable 0 T
    have h2 : IntervalIntegrable (fun t : ℝ => t/T*f T) volume 0 T :=
      (show Continuous (fun t : ℝ => t/T*f T) by fun_prop).intervalIntegrable 0 T
    have h3 : IntervalIntegrable (fun t : ℝ => t/T) volume 0 T :=
      (show Continuous (fun t : ℝ => t/T) by fun_prop).intervalIntegrable 0 T
    dsimp [L]
    rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub intervalIntegrable_const h3,
      intervalIntegral.integral_div,intervalIntegral.integral_const,integral_id]
    simp only [smul_eq_mul,sub_zero,zero_pow (by decide : 2 ≠ 0)]
    field_simp
    ring
  rw [he] at hi
  linarith

theorem HeatJet.rootFilledSquare_strict_chord {n : ℕ} (J : HeatJet n) {T : ℝ}
    (hT : 0 < T) (x : Fin (n+1) → ℝ)
    (hv : J.rootFilledEnergy T 0 x ≠ J.rootFilledEnergy T T x) :
    2*(∫ s in 0..T, J.rootFilledSquare T s x) <
      T*(J.rootFilledSquare T 0 x+J.rootFilledSquare T T x) :=
  strict_integral_chord_of_derivative hT (J.continuous_rootFilledSquare T x)
    (J.continuous_rootFilledEnergy T x) (fun _ ht => J.hasDerivAt_rootFilledSquare ht x)
    (J.rootFilledSquare_convex T x) hv

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalar_clockRoot_integral {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    clockRoot (fun x : Fin 1 → ℝ => f (x 0)) T 0 =
      ∫ z, f z ∂gaussianReal 0 (Real.toNNReal T) := by
  change (∫ z : Fin 1 → ℝ, f ((0+z) 0) ∂Measure.pi fun _ : Fin 1 => gaussianReal 0 (Real.toNNReal T)) = _
  simpa only [zero_add] using integral_gaussian_eval (0:Fin 1) (Real.toNNReal T) hf

theorem scalarProfileJet_curvature_nonconstant (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    ∃ x y, scalarProfileJet α l t 2 x ≠ scalarProfileJet α l t 2 y := by
  by_contra! he
  let c := scalarProfileJet α l t 2 0
  have hc : 0 < c := scalarProfileJet_curvature_pos α hα l t 0
  have hd (x : ℝ) : HasDerivAt (fun y => scalarProfileJet α l t 1 y-c*y) 0 x := by
    convert! (scalarProfileJet_hasDerivAt α hα l t 1 x).sub ((hasDerivAt_id x).const_mul c) using 1
    change 0 = scalarProfileJet α l t 2 x-c*1
    rw [he x 0,mul_one,sub_self]
  have hh := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) (3/c) 0
  have hz := scalarProfileJet_gradient_zero α hα l t
  have hb := scalarProfileJet_admissible α hα l t (3/c)
  rw [hz,mul_zero,sub_zero,mul_div_cancel₀ _ hc.ne'] at hh
  rcases hb with ⟨hb0,hb1⟩
  have hg : scalarProfileJet α l t 1 (3/c) = 3 := by linarith
  rw [hg] at hb1
  norm_num at hb1
  linarith

theorem scalarProfileRoot_energy_strict (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {T : ℝ} (hT : 0 < T) :
    (scalarProfileHeatJet α hα l t).rootFilledEnergy T 0 0 <
      (scalarProfileHeatJet α hα l t).rootFilledEnergy T T 0 := by
  have hc : Continuous (scalarProfileJet α l t 2) :=
    continuous_iff_continuousAt.mpr fun x => (scalarProfileJet_hasDerivAt α hα l t 2 x).continuousAt
  have hb : BddSmooth 0 (scalarProfileJet α l t 2) := by
    refine ⟨hc,1,zero_le_one,?_⟩
    intro x
    have hp := scalarProfileJet_curvature_pos α hα l t x
    rw [abs_of_pos hp]
    have hh := (scalarProfileJet_admissible α hα l t x).2
    linarith [sq_nonneg (scalarProfileJet α l t 1 x)]
  have hv := Scalar.variance_gaussian_pos hb (scalarProfileJet_curvature_nonconstant α hα l t)
    (ne_of_gt (Real.toNNReal_pos.mpr hT))
  simp only [HeatJet.rootFilledEnergy,sub_zero,sub_self,clockRoot_zero_time,
    scalarProfileHeatJet,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.reduceAdd,one_nsmul]
  rw [scalar_clockRoot_integral hc,scalar_clockRoot_integral (f:=fun z => (scalarProfileJet α l t 2 z)^2) (hc.pow 2)]
  linarith

theorem scalarProfileRoot_square_zero (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (T : ℝ) :
    (scalarProfileHeatJet α hα l t).rootFilledSquare T 0 0 = 0 := by
  have hc : Continuous (scalarProfileJet α l t 1) :=
    continuous_iff_continuousAt.mpr fun x => (scalarProfileJet_hasDerivAt α hα l t 1 x).continuousAt
  have ho : ∀ x, scalarProfileJet α l t 1 (-x) = -scalarProfileJet α l t 1 x := by
    intro x
    simpa only [pow_one,neg_one_mul] using scalarProfileJet_parity α hα l t 1 x
  have hh := integral_map_of_stronglyMeasurable (μ:=gaussianReal 0 (Real.toNNReal T))
    measurable_neg hc.stronglyMeasurable
  rw [gaussianReal_map_neg,neg_zero] at hh
  simp only [ho,integral_neg] at hh
  have hz : (∫ z, scalarProfileJet α l t 1 z ∂gaussianReal 0 (Real.toNNReal T)) = 0 := by linarith
  simp only [HeatJet.rootFilledSquare,sub_zero,clockRoot_zero_time,scalarProfileHeatJet]
  rw [scalar_clockRoot_integral hc,hz,zero_pow (by decide : 2 ≠ 0)]

theorem HeatJet.rootFilledSquare_endpoint {n : ℕ} (J : HeatJet n) (T : ℝ)
    (x : Fin (n+1) → ℝ) : J.rootFilledSquare T T x = J.observedSquare 0 T x := by
  simp only [HeatJet.rootFilledSquare,sub_self,clockRoot_zero_time,HeatJet.observedSquare,
    clockTest_zero_mass,HeatJet.square]

theorem scalarProfileRoot_strict_chord (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) {T : ℝ} (hT : 0 < T) :
    2*(∫ s in 0..T, (scalarProfileHeatJet α hα l t).rootFilledSquare T s 0) <
      T*(scalarProfileHeatJet α hα l t).observedSquare 0 T 0 := by
  have hh := HeatJet.rootFilledSquare_strict_chord (scalarProfileHeatJet α hα l t) hT 0
    (scalarProfileRoot_energy_strict α hα l t hT).ne
  simpa only [scalarProfileRoot_square_zero,HeatJet.rootFilledSquare_endpoint,zero_add] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

section
variable {J : HeatJet 0} (hJ : J.ScalarAdmissible) (hA : J.GradientTest)
include hJ hA

theorem HeatJet.mass_difference_root {b T : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    clockContinuation b J.F T x-clockRoot J.F T x =
      b/2*(∫ s in 0..T, J.massEnergy 0 hb T s x) := by
  have hp := shiftedContinuation_tendsto_zero_mass J.lipschitz
    (exponentialIncrement_gaussian (fun _ : Fin 1 => Real.toNNReal T)) x
  change Tendsto (fun a : ℝ => clockContinuation a J.F T x) (𝓝[>] 0)
    (𝓝 (clockRoot J.F T x)) at hp
  have hl := hp.sub_const (clockContinuation b J.F T x)
  have hr := (((continuous_id.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).sub_const b |>.div_const 2).mul
    (HeatJet.massEnergy_integral_zero_tendsto hJ hA hb hb1 hT x)
  have he : (fun a : ℝ => clockContinuation a J.F T x-clockContinuation b J.F T x) =ᶠ[𝓝[>] 0]
      (fun a => (a-b)/2*(∫ s in 0..T, J.massEnergy a hb T s x)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact J.mass_difference_integral ha hb hT x
  have hh := tendsto_nhds_unique hl (hr.congr' he.symm)
  simp only [id_eq,zero_sub,neg_div,neg_mul] at hh
  linarith

omit hJ hA in
theorem clockRoot_abs_sub_le {A B : (Fin 1 → ℝ) → ℝ} (hA : BddSmooth 0 A)
    (hB : BddSmooth 0 B) {c : ℝ} (hab : ∀ y, |A y-B y| ≤ c) (t : ℝ) (x : Fin 1 → ℝ) :
    |clockRoot A t x-clockRoot B t x| ≤ c := by
  have hc (c : ℝ) : clockRoot (fun _ : Fin 1 → ℝ => c) t x = c := by
    rw [← clockTest_zero_potential _ 1]
    exact clockTest_const (LipschitzWith.const _) c 1 t x
  have hadd : clockRoot (fun y => A y-B y) t x = clockRoot A t x-clockRoot B t x := by
    rw [← clockTest_zero_potential _ 1,← clockTest_zero_potential A 1,
      ← clockTest_zero_potential B 1]
    exact clockTest_sub_test (LipschitzWith.const _) hA hB 1 t x
  have h1 := clockRoot_mono (BddSmooth.const 0 (-c)) (hA.sub hB)
    (fun y => (abs_le.mp (hab y)).1) t x
  have h2 := clockRoot_mono (hA.sub hB) (BddSmooth.const 0 c)
    (fun y => (abs_le.mp (hab y)).2) t x
  rw [hc,hadd] at h1 h2
  exact abs_le.mpr ⟨h1,h2⟩

theorem HeatJet.massEnergy_inner_zero_bound {b T s : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hs : s ≤ T) (x : Fin 1 → ℝ) :
    |J.massEnergy 0 hb T s x-J.rootFilledSquare T s x| ≤ 8*b*(T-s) := by
  rw [HeatJet.massEnergy_eq_mixedSquare hA]
  unfold HeatJet.mixedSquare HeatJet.rootFilledSquare
  rw [clockTest_zero_mass]
  have hAt : ∀ y, |J.A y| ≤ 1 := fun y => by rw [hA.1]; exact hJ.gradient y
  have hR : BddSmooth 0 (fun y => (clockRoot J.A (T-s) y)^2) := by
    simpa only [pow_two] using (clockRoot_smooth J.smoothA (T-s)).mul (clockRoot_smooth J.smoothA (T-s))
  apply clockRoot_abs_sub_le (J.evolve hb (T-s)).square.smoothA hR
  intro y
  change |(clockTest b J.F J.A (T-s) y)^2-(clockRoot J.A (T-s) y)^2| ≤ _
  have hh := HeatJet.gradient_mass_zero_bound hJ hA hb hb1 (sub_nonneg.mpr hs) y
  have h1 := clockTest_abs_le J.lipschitz J.smoothA hAt b (T-s) y
  have h2 : |clockRoot J.A (T-s) y| ≤ 1 := by
    rw [← clockTest_zero_potential _ 1]
    exact clockTest_abs_le (LipschitzWith.const _) J.smoothA hAt 1 (T-s) y
  have he (u v : ℝ) : u^2-v^2 = (u-v)*(u+v) := by ring
  rw [he,abs_mul]
  have hsum : |clockTest b J.F J.A (T-s) y+clockRoot J.A (T-s) y| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hmul := mul_le_mul hh hsum (abs_nonneg _) (by positivity : 0 ≤ 4*b*(T-s))
  nlinarith

theorem HeatJet.massEnergy_root_integral_tendsto {T : ℝ} (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    Tendsto (fun b : ℝ => ∫ s in 0..T, if hb : 0 < b then J.massEnergy 0 hb T s x else 0)
      (𝓝[>] 0) (𝓝 (∫ s in 0..T, J.rootFilledSquare T s x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he : ∀ᶠ b : ℝ in 𝓝[>] 0, 0 < b ∧ b ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ b : ℝ in 𝓝 0, b < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with b hb hb1
    exact ⟨hb,hb1.le⟩
  have hc : Continuous (fun s => J.rootFilledSquare T s x) := by
    simpa only [J.erased_filledSquare] using J.erasePotential.continuous_filledSquare (m:=1) zero_lt_one T x
  have hbound : ∀ᶠ b : ℝ in 𝓝[>] 0,
      dist (∫ s in 0..T, if hb : 0 < b then J.massEnergy 0 hb T s x else 0)
        (∫ s in 0..T, J.rootFilledSquare T s x) ≤ 8*b*T*T := by
    filter_upwards [he] with b hb
    simp only [dite_eq_left hb.1]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=T) (C:=8*b*T)
      (f:=fun s => J.massEnergy 0 hb.1 T s x-J.rootFilledSquare T s x) (fun s hs => by
        rw [uIoc_of_le hT] at hs
        exact (HeatJet.massEnergy_inner_zero_bound hJ hA hb.1 hb.2 hs.2 x).trans
          (mul_le_mul_of_nonneg_left (by linarith [hs.1]) (mul_nonneg (by norm_num) hb.1.le)))
    rw [intervalIntegral.integral_sub ((J.continuous_massEnergy 0 hb.1 T x).intervalIntegrable 0 T)
      (hc.intervalIntegrable 0 T)] at hh
    simpa only [Real.norm_eq_abs,Real.dist_eq,sub_zero,abs_of_nonneg hT] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound
  simpa only [id_eq,mul_zero,zero_mul] using
    ((((continuous_id.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).const_mul 8).mul_const T |>.mul_const T)

 
theorem HeatJet.tendsto_root_mass_quotient {T : ℝ} (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    Tendsto (fun b => (clockContinuation b J.F T x-clockRoot J.F T x)/b)
      (𝓝[>] 0) (𝓝 ((1/2:ℝ)*(∫ s in 0..T, J.rootFilledSquare T s x))) := by
  apply ((HeatJet.massEnergy_root_integral_tendsto hJ hA hT x).const_mul (1/2:ℝ)).congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ b : ℝ in 𝓝 0, b < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with b hb hb1
  have hb' : 0 < b := hb
  simp only [dite_eq_left hb']
  rw [HeatJet.mass_difference_root hJ hA hb' hb1.le hT x]
  field_simp

end
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarParisiValue_zero_head_error {T q r b d : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1) (α β : boundedMassProfiles)
    (hb0 : 0 < b)
    (hα : ∀ s ∈ Ico (0:ℝ) q, α.val s = 0)
    (hβ : ∀ s ∈ Ico (0:ℝ) q, β.val s = b)
    (hb : ∀ s ∈ Ioo q r, |β.val s-α.val s| ≤ d)
    (he : ∀ s ∈ Ioo r 1, β.val s = α.val s) :
    |scalarParisiValue hT β-scalarParisiValue hT α-
      (clockContinuation b (scalarTailJet hT α q).F (T*q) 0-
       clockRoot (scalarTailJet hT α q).F (T*q) 0-T*b*q^2/4)| ≤ T*d*(r-q) := by
  have hp := clockContinuation_abs_sub_le (scalarTailJet hT β q).lipschitz
    (scalarTailJet hT α q).lipschitz hb0 (scalarTailJet_error hT hqr hr α β hb he) (T*q) 0
  have hpen := scalarPenalty_tail_error hq.le hqr hr α β hα hβ hb he
  rw [scalarParisiValue_constant_head hT ⟨hq,hqr.trans hr⟩ β hb0 hβ,
    scalarParisiValue_zero_head hT ⟨hq,hqr.trans hr⟩ α hα]
  have heq : (clockContinuation b (scalarTailJet hT β q).F (T*q) 0-T/2*scalarPenalty β-T/4)-
      (clockRoot (scalarTailJet hT α q).F (T*q) 0-T/2*scalarPenalty α-T/4)-
      (clockContinuation b (scalarTailJet hT α q).F (T*q) 0-
       clockRoot (scalarTailJet hT α q).F (T*q) 0-T*b*q^2/4) =
      (clockContinuation b (scalarTailJet hT β q).F (T*q) 0-
       clockContinuation b (scalarTailJet hT α q).F (T*q) 0)-
       T/2*(scalarPenalty β-scalarPenalty α-(b-0)*q^2/2) := by ring
  rw [heq]
  calc
    |_ - _| ≤ |clockContinuation b (scalarTailJet hT β q).F (T*q) 0-
        clockContinuation b (scalarTailJet hT α q).F (T*q) 0|+
        |T/2*(scalarPenalty β-scalarPenalty α-(b-0)*q^2/2)| := abs_sub _ _
    _ ≤ T/2*d*(r-q)+(T/2)*(d*(r-q)) := by
      rw [abs_mul,abs_of_nonneg (div_nonneg hT.le (by norm_num))]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hpen (by positivity))
    _ = _ := by ring

theorem scalarMinimizer_zero_head_lower {T q r : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hmr : 0 < α.val r)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = 0)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    -T*(r-q) ≤ (1/2:ℝ)*(∫ s in 0..T*q,
      (scalarTailJet hT α q).rootFilledSquare (T*q) s 0)-T*q^2/4 := by
  have hd := (HeatJet.tendsto_root_mass_quotient (scalarTailJet_admissible hT α q)
    (scalarTailJet_gradientTest hT α q) (mul_nonneg hT.le hq.le) 0).sub_const (T*q^2/4)
  apply ge_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ b : ℝ in 𝓝[>] 0, b < α.val r from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hmr))] with b hb hbr
  have hb' : 0 < b := hb
  have hb1 : b ≤ 1 := hbr.le.trans (α.property.1 r).2
  let β := floorMassProfile α hb'.le hb1
  have hdiff := scalarParisiValue_zero_head_error hT hq hqr hr α β hb' hf
    (fun s hs => floorMassProfile_head α hb'.le hb1 hb'.le hf hs)
    (fun s hs => by
      simpa only [sub_zero] using floorMassProfile_bound α hb'.le hb1 hb'.le
        (hq.le.trans hs.1.le) (α.property.1 s).1)
    (fun s hs => floorMassProfile_tail α (hq.le.trans hqr) hb'.le hb1 hbr.le hs.1.le)
  have hminβ := hmin β (floorMassProfile_mem hα hb'.le hb1)
  have hlo : -T*b*(r-q) ≤ clockContinuation b (scalarTailJet hT α q).F (T*q) 0-
      clockRoot (scalarTailJet hT α q).F (T*q) 0-T*b*q^2/4 := by
    have hh := (abs_le.mp hdiff).2
    linarith
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ hb').mpr
  nlinarith

theorem scalarMinimizer_zero_head_balance {T q : ℝ} (hT : 0 < T)
    (hq : q ∈ Ioo (0:ℝ) 1) (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = 0)
    (hrise : ∀ r ∈ Ioc q 1, 0 < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    T*q^2 ≤ 2*(∫ s in 0..T*q, (scalarTailJet hT α q).rootFilledSquare (T*q) s 0) := by
  have hlim : Tendsto (fun r : ℝ => -T*(r-q)) (𝓝[>] q) (𝓝 0) := by
    simpa only [sub_self,mul_zero] using
      (tendsto_const_nhds.mul ((tendsto_id.mono_left nhdsWithin_le_nhds).sub_const q) :
        Tendsto (fun r : ℝ => -T*(r-q)) (𝓝[>] q) (𝓝 (-T*(q-q))))
  have hD : 0 ≤ (1/2:ℝ)*(∫ s in 0..T*q,
      (scalarTailJet hT α q).rootFilledSquare (T*q) s 0)-T*q^2/4 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq.2))] with r hqr hr
    exact scalarMinimizer_zero_head_lower hT hq.1 hqr.le hr.le α hα (hrise r ⟨hqr,hr.le⟩) hf hmin
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem clockContinuation_tendsto_root {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (t : ℝ) (x : ι → ℝ) :
    Tendsto (fun a => clockContinuation a F t x) (𝓝[>] 0) (𝓝 (clockRoot F t x)) :=
  shiftedContinuation_tendsto_zero_mass hF
    (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)) x

 
theorem clockRoot_potential_abs_sub_le {ι : Type*} [Fintype ι]
    {F G : (ι → ℝ) → ℝ} {C D : ℝ≥0} (hF : LipschitzWith C F) (hG : LipschitzWith D G)
    {K : ℝ} (he : ∀ y, |F y-G y| ≤ K) (t : ℝ) (x : ι → ℝ) :
    |clockRoot F t x-clockRoot G t x| ≤ K := by
  apply le_of_tendsto (((clockContinuation_tendsto_root hF t x).sub
    (clockContinuation_tendsto_root hG t x)).abs)
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact clockContinuation_abs_sub_le hF hG ha he t x

theorem HeatJet.observedSquare_tendsto_zero {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) {t : ℝ} (ht : 0 ≤ t) (x : Fin 1 → ℝ) :
    Tendsto (fun a => J.observedSquare a t x) (𝓝[>] 0) (𝓝 (J.observedSquare 0 t x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ᶠ a : ℝ in 𝓝[>] 0, dist (J.observedSquare a t x) (J.observedSquare 0 t x) ≤ 5*a*t := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ a : ℝ in 𝓝 0, a < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with a ha ha1
    dsimp only [HeatJet.observedSquare]
    rw [clockTest_zero_mass,Real.dist_eq]
    exact HeatJet.gradient_square_mass_zero_bound hJ hA ha ha1.le ht x
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hb
  simpa only [id_eq,mul_zero,zero_mul] using
    (((continuous_id.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).const_mul 5 |>.mul_const t)

theorem clockExcess_continuous (cs : List HeatClock) : Continuous (fun a => clockExcess a cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih =>
    change Continuous (fun a : ℝ => (c.mass-a)*(c.time:ℝ)+clockExcess a cs)
    exact ((continuous_const.sub continuous_id).mul_const (c.time:ℝ)).add ih

theorem clockMass_eventually_lower (cs : List HeatClock) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ c ∈ cs, a ≤ c.mass := by
  induction cs with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,eventually_true]
  | cons c cs ih =>
    filter_upwards [ih,
      (show ∀ᶠ a : ℝ in 𝓝 0, a < c.mass from Iio_mem_nhds c.positive).filter_mono nhdsWithin_le_nhds] with a ha hc
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc.le
    · exact ha d hd

 

theorem HeatJet.flatten_root_schedule_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (cs : List HeatClock) {A : ℝ}
    (hc : ∀ c ∈ cs, c.mass ≤ 1) (hA0 : 0 ≤ A) (x : Fin 1 → ℝ) :
    |clockRoot (J.schedule cs).F A x-clockRoot J.F (A+clockLength cs) x-
      (clockExcess 0 cs/2)*J.observedSquare 0 (A+clockLength cs) x| ≤
      2*clockLength cs*clockExcess 0 cs := by
  have hw : Tendsto (fun a => clockExcess a cs) (𝓝[>] 0) (𝓝 (clockExcess 0 cs)) :=
    ((clockExcess_continuous cs).tendsto 0).mono_left nhdsWithin_le_nhds
  have hval := (clockContinuation_tendsto_root (J.schedule cs).lipschitz A x).sub
    (clockContinuation_tendsto_root J.lipschitz (A+clockLength cs) x)
  have he := HeatJet.observedSquare_tendsto_zero hJ hA (add_nonneg hA0 (clockLength_nonneg cs)) x
  apply le_of_tendsto_of_tendsto ((hval.sub ((hw.div_const 2).mul he)).abs)
    (hw.const_mul (2*clockLength cs))
  filter_upwards [self_mem_nhdsWithin,clockMass_eventually_lower cs,
    (show ∀ᶠ a : ℝ in 𝓝 0, a < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds] with a ha hac ha1
  exact HeatJet.flatten_schedule_error hJ hA cs ha ha1.le (fun c hm => ⟨hac c hm,hc c hm⟩) hA0 x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJet.flatten_root_profile_error {J K : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    {A l : ℝ} (t : ℝ≥0)
    (hA0 : 0 ≤ A) (hK : K.F = J.nonnegativeProfileValue α l t) (x : Fin 1 → ℝ) :
    |clockRoot K.F A x-clockRoot J.F (A+t) x-
      ((∫ s in l..l+t, α.mass s)/2)*J.observedSquare 0 (A+t) x| ≤
      2*(t:ℝ)*(∫ s in l..l+t, α.mass s) := by
  have hg (k : ℕ) (y : Fin 1 → ℝ) :
      |(J.schedule ((α.cappedApprox k).grid l t k)).F y-K.F y| ≤ (t:ℝ)*(1/2:ℝ)^k := by
    rw [hK,(α.cappedApprox k).grid_eq_linear]
    have he : ((2^k:ℕ):ℝ≥0)*(t/(2^k:ℝ≥0)) = t := by simp only [Nat.cast_pow,Nat.cast_ofNat]; field_simp
    have hh := J.capped_linear_error (fun _ => 1) (fun i y => by rw [Fin.eq_zero i]; exact hJ.gradient y) α hα k l (t/(2^k:ℝ≥0)) (2^k) y
    rw [he] at hh
    apply hh.trans_eq
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.reduceAdd,
      nsmul_eq_mul,Nat.cast_one,one_pow,one_mul,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_ofNat,
      Nat.cast_pow,Nat.cast_ofNat,div_pow,one_div]
    field_simp
    ring
  have ht : Tendsto (fun k => clockRoot (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
      atTop (𝓝 (clockRoot K.F A x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hdist (k : ℕ) : dist (clockRoot (J.schedule ((α.cappedApprox k).grid l t k)).F A x)
        (clockRoot K.F A x) ≤ (t:ℝ)*(1/2:ℝ)^k := by
      rw [Real.dist_eq]
      exact clockRoot_potential_abs_sub_le (J.schedule _).lipschitz K.lipschitz (hg k) A x
    exact squeeze_zero (fun _ => dist_nonneg) hdist
      (by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul (t:ℝ))
  have hw := capped_grid_excess_tendsto α 0 l t
  simp only [sub_zero] at hw
  apply le_of_tendsto_of_tendsto ((ht.sub_const _).sub ((hw.div_const 2).mul_const _)).abs
    (hw.const_mul (2*(t:ℝ)))
  apply Eventually.of_forall
  intro k
  have hh := HeatJet.flatten_root_schedule_error hJ hA ((α.cappedApprox k).grid l t k)
    (fun c hc => ((α.cappedApprox k).grid_mass_bounds l t k hc).2.trans
      (α.cappedApprox_le_one hα k _)) hA0 x
  simpa only [clockLength,PositiveMassProfile.grid_total_time] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_root_flatten_error {T q r : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) :
    |clockRoot (scalarTailJet hT α q).F (T*q) 0-
      clockRoot (scalarTailJet hT α r).F (T*r) 0-
      (T/2*(∫ s in q..r, α.val s))*(scalarTailJet hT α r).observedSquare 0 (T*r) 0| ≤
      2*T^2*(r-q)*(∫ s in q..r, α.val s) := by
  have hs : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr)
  have he : T*q+T*(r-q)=T*r := by ring
  have hi : (∫ s in T*q..T*r, (rescaledMassProfile α hT).mass s) =
      T*(∫ s in q..r, α.val s) := by
    change (∫ s in T*q..T*r, (fun z => α.val z) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul]
  have hh := HeatJet.flatten_root_profile_error (scalarTailJet_admissible hT α r)
    (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (A:=T*q) (l:=T*q)
    (Real.toNNReal (T*(r-q))) (mul_nonneg hT.le hq) (scalarTailJet_restart hT hqr hr α) (0:Fin 1 → ℝ)
  simp only [Real.coe_toNNReal _ hs,he,hi] at hh
  rw [show T*(∫ s in q..r, α.val s)/2 = T/2*(∫ s in q..r, α.val s) by ring] at hh
  exact hh.trans_eq (by ring)

theorem scalarMinimizer_zero_flatten_endpoint_bound {T q r : ℝ} (hT : 0 < T)
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles)
    (hα : α ∈ scalarProfiles)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = 0)
    (hW : 0 < ∫ s in q..r, α.val s)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (scalarTailJet hT α r).observedSquare 0 (T*r) 0 ≤ r+4*T*(r-q) := by
  have hmq : 0 ≤ α.val q := (α.property.1 q).1
  have hmr : 0 ≤ α.val r := hmq.trans (α.property.2 hqr)
  let β := replaceHeadProfile α (le_refl (0:ℝ)) (zero_le_one : (0:ℝ) ≤ 1) hmr
  have hb := hmin β (replaceHeadProfile_mem hα hr (le_refl (0:ℝ)) (zero_le_one : (0:ℝ) ≤ 1) hmr)
  have ht : (scalarTailJet hT β r).F = (scalarTailJet hT α r).F :=
    scalarTailJet_congr hT hr (fun s hs => replaceHeadProfile_tail α (hq.le.trans hqr) (le_refl (0:ℝ)) (zero_le_one : (0:ℝ) ≤ 1) hmr hs.1.le)
  rw [scalarParisiValue_zero_head hT ⟨hq,hqr.trans hr⟩ α hf,
    scalarParisiValue_zero_head hT ⟨hq.trans_le hqr,hr⟩ β
      (fun s hs => replaceHeadProfile_head α (le_refl (0:ℝ)) (zero_le_one : (0:ℝ) ≤ 1) hmr hs),ht] at hb
  have hp := scalarPenalty_flatten_bound hq.le hqr hr α (le_refl (0:ℝ)) (zero_le_one : (0:ℝ) ≤ 1) hmr hf hmq
  simp only [sub_zero] at hp
  have he := abs_le.mp (scalarTailJet_root_flatten_error hT hq.le hqr hr α)
  have hpos : 0 < T/2*(∫ s in q..r, α.val s) := mul_pos (by positivity) hW
  have hh : (T/2*(∫ s in q..r, α.val s))*(scalarTailJet hT α r).observedSquare 0 (T*r) 0 ≤
      (T/2*(∫ s in q..r, α.val s))*(r+4*T*(r-q)) := by
    change scalarPenalty α-scalarPenalty β ≤ _ at hp
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ T/2)]
  exact (mul_le_mul_iff_right₀ hpos).mp hh

theorem scalarMinimizer_zero_endpoint_le {T q : ℝ} (hT : 0 < T) (hq : q ∈ Ioo (0:ℝ) 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ s ∈ Ico (0:ℝ) q, α.val s = 0)
    (hnext : ∀ r ∈ Ioo q 1, 0 < α.val r)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β) :
    (scalarTailJet hT α q).observedSquare 0 (T*q) 0 ≤ q := by
  have he : Tendsto (fun r => (scalarTailJet hT α r).observedSquare 0 (T*r) 0)
      (𝓝[>] q) (𝓝 ((scalarTailJet hT α q).observedSquare 0 (T*q) 0)) :=
    (scalarTailJet_observedSquare_continuous hT α 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun r : ℝ => r+4*T*(r-q)) (𝓝[>] q) (𝓝 q) := by
    have hc : Continuous (fun r : ℝ => r+4*T*(r-q)) := by fun_prop
    simpa only [sub_self,mul_zero,add_zero] using
      (hc.tendsto q).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto he hr
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq.2))] with r hqr hr1
  apply scalarMinimizer_zero_flatten_endpoint_bound hT hq.1 hqr.le hr1.le α hα hf _ hmin
  have hpos : ∀ s ∈ Ioo q r, 0 < α.val s := fun s hs => hnext s ⟨hs.1,hs.2.trans hr1⟩
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    α.property.2.intervalIntegrable hpos hqr

end SKFluctuations.Hierarchy

end

end OAI
