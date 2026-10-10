import Mathlib
import OAI.Probability.SKFluctuations.InverseControlMeasureCalculus

namespace OAI

/-! Inverse Constraint Nonempty. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def affineInverse (r₀ u₀ : ℝ) (r : ℝ) : ℝ :=
  u₀+((1-u₀)/(1-r₀))*(max r₀ (min 1 r)-r₀)

 theorem affineInverse_on {r₀ u₀ r : ℝ} (hr : r ∈ Icc r₀ 1) :
    affineInverse r₀ u₀ r=u₀+((1-u₀)/(1-r₀))*(r-r₀) := by
  simp [affineInverse,min_eq_right hr.2,max_eq_right hr.1]

 theorem affineInverse_monotone {r₀ u₀ : ℝ} (hr : r₀<1) (hu : u₀≤1) :
    Monotone (affineInverse r₀ u₀) := by
  intro s t hst
  unfold affineInverse
  have hp : 0≤(1-u₀)/(1-r₀) := div_nonneg (sub_nonneg.mpr hu) (sub_pos.mpr hr).le
  gcongr

 theorem affineInverse_range {r₀ u₀ r : ℝ} (hr : r₀<1) (hu : u₀≤1) :
    affineInverse r₀ u₀ r ∈ Icc u₀ 1 := by
  have hs : 0≤(1-u₀)/(1-r₀) := div_nonneg (sub_nonneg.mpr hu) (sub_pos.mpr hr).le
  constructor
  · unfold affineInverse
    have := le_max_left r₀ (min 1 r)
    nlinarith
  · have ht : max r₀ (min 1 r)-r₀≤1-r₀ := sub_le_sub_right (max_le hr.le (min_le_left _ _)) _
    have hn : 1-r₀≠0 := ne_of_gt (sub_pos.mpr hr)
    have he : ((1-u₀)/(1-r₀))*(1-r₀)=1-u₀ := div_mul_cancel₀ _ hn
    unfold affineInverse
    linarith [mul_le_mul_of_nonneg_left ht hs]

 def affineInverseProfile (r₀ u₀ : ℝ) (hr : r₀<1) (hu : u₀ ∈ Icc (0:ℝ) 1) : boundedMassProfiles :=
  ⟨affineInverse r₀ u₀,⟨fun r => ⟨hu.1.trans (affineInverse_range (r := r) hr hu.2).1,
    (affineInverse_range (r := r) hr hu.2).2⟩,affineInverse_monotone hr hu.2⟩⟩

 theorem affineInverseProfile_feasible {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hr : r₀<1) (hu : u₀ ∈ Icc (0:ℝ) 1)
    (hk : ContinuousOn k (Icc r₀ 1)) (hM : Continuous M)
    (hf : ∀ t ∈ Icc r₀ 1, k t≤(1-u₀)/(1-r₀))
    (hc : ∀ u ∈ Icc u₀ 1, (1-u₀)/(1-r₀)≤M u) :
    affineInverseProfile r₀ u₀ hr hu ∈ inverseIntegralConstraints r₀ u₀ k M := by
  have hn : 1-r₀≠0 := ne_of_gt (sub_pos.mpr hr)
  refine ⟨?_,?_,?_⟩
  · change affineInverse r₀ u₀ r₀=u₀
    rw [affineInverse_on ⟨le_rfl,hr.le⟩]
    ring
  · change affineInverse r₀ u₀ 1=1
    rw [affineInverse_on ⟨hr.le,le_rfl⟩,div_mul_cancel₀ _ hn]
    ring
  · intro x hx y hy hxy
    have he : (affineInverseProfile r₀ u₀ hr hu).val y-
        (affineInverseProfile r₀ u₀ hr hu).val x=((1-u₀)/(1-r₀))*(y-x) := by
      change affineInverse r₀ u₀ y-affineInverse r₀ u₀ x=_
      rw [affineInverse_on hx,affineInverse_on hy]
      ring
    rw [he]
    have hsub : Icc x y ⊆ Icc r₀ 1 := Icc_subset_Icc hx.1 hy.2
    have hαc : Continuous (affineInverse r₀ u₀) := by unfold affineInverse; fun_prop
    constructor
    · calc
        (∫ t in x..y, k t) ≤ ∫ t in x..y, ((1-u₀)/(1-r₀)) :=
          intervalIntegral.integral_mono_on hxy
            ((hk.mono hsub).intervalIntegrable_of_Icc hxy) intervalIntegrable_const
            (fun t ht => hf t (hsub ht))
        _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring
    · calc
        ((1-u₀)/(1-r₀))*(y-x) = ∫ t in x..y, ((1-u₀)/(1-r₀)) := by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring
        _ ≤ ∫ t in x..y, M ((affineInverseProfile r₀ u₀ hr hu).val t) := by
          apply intervalIntegral.integral_mono_on hxy intervalIntegrable_const
            ((hM.comp hαc).intervalIntegrable _ _)
          intro t _
          exact hc _ (affineInverse_range hr hu.2)

 theorem inverseIntegralConstraints_nonempty_of_affine {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hr : r₀<1) (hu : u₀ ∈ Icc (0:ℝ) 1)
    (hk : ContinuousOn k (Icc r₀ 1)) (hM : Continuous M)
    (hf : ∀ t ∈ Icc r₀ 1, k t≤(1-u₀)/(1-r₀))
    (hc : ∀ u ∈ Icc u₀ 1, (1-u₀)/(1-r₀)≤M u) :
    (inverseIntegralConstraints r₀ u₀ k M).Nonempty :=
  ⟨affineInverseProfile r₀ u₀ hr hu,affineInverseProfile_feasible hr hu hk hM hf hc⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem comparisonFloor_le_inv_cube {N δ U r : ℝ} (hN : 0<N) (hU : 0<U)
    (hr : 0≤r) : comparisonFloor N δ U r ≤ 1/(N^δ)^3 := by
  have hq : 0<N^δ := Real.rpow_pos_of_pos hN _
  have he : N^(2*δ)=(N^δ)^2 := by
    rw [mul_comm (2:ℝ) δ,Real.rpow_mul hN.le,Real.rpow_two]
  unfold comparisonFloor
  rw [he]
  have hb : 0<(N^δ)^2*U := by positivity
  calc
    N^δ*U^2/(r+(N^δ)^2*U)^2 ≤ N^δ*U^2/((N^δ)^2*U)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
      exact le_add_of_nonneg_left hr
    _ = 1/(N^δ)^3 := by field_simp

 theorem comparisonFloor_le_half {N δ U r : ℝ} (hN : 0<N) (hU : 0<U)
    (hr : 0≤r) (hq : 2≤N^δ) : comparisonFloor N δ U r≤1/2 := by
  apply (comparisonFloor_le_inv_cube hN hU hr).trans
  have hpos : 0<N^δ := Real.rpow_pos_of_pos hN _
  have hcube : 2≤(N^δ)^3 := by nlinarith [sq_nonneg (N^δ-2),sq_nonneg (N^δ)]
  apply (div_le_iff₀ (pow_pos hpos _)).mpr
  linarith

 theorem comparisonCap_ge {N δ U L E d u : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) :
    N^δ ≤ comparisonCap N δ U L E d u := by
  have hf : 1≤(u+U)/L := (le_div_iff₀ hL).mpr (by linarith)
  have hs : 0≤(d^3/E)*(u+U)^2 := by positivity
  unfold comparisonCap
  nlinarith [Real.rpow_pos_of_pos hN δ]

 theorem comparisonConstraints_nonempty {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/2)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/2)) :
    (inverseDifferentialConstraints r₀ u₀ (comparisonFloor N δ U)
      (comparisonCap N δ U L E d)).Nonempty := by
  have hr : r₀<1 := by linarith [hr₀.2]
  have hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,by linarith [hu₀.2]⟩
  have hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  have hc := comparisonCap_continuous N δ U L E d
  have hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
  have hc1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
  rw [inverseDifferentialConstraints_eq r₀ u₀ hr.le _ _ hk hc hm hc1]
  apply inverseIntegralConstraints_nonempty_of_affine hr hu hk hc
  · intro t ht
    apply (comparisonFloor_le_half hN hU (hr₀.1.trans ht.1) hq).trans
    apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
    linarith [hr₀.1,hu₀.2]
  · intro u hu
    have hs : (1-u₀)/(1-r₀)≤2 := by
      apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
      linarith [hu₀.1,hr₀.2]
    exact hs.trans (hq.trans (comparisonCap_ge hN hU hL hLU hE hd (hu₀.1.trans hu.1)))

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem comparisonFloor_lower_on {N δ U r₀ t : ℝ} (hN : 0<N) (hU : 0<U)
    (hr₀ : 0≤r₀) (ht : t ∈ Icc r₀ 1) :
    comparisonFloor N δ U 1 ≤ comparisonFloor N δ U t := by
  unfold comparisonFloor
  have hpos : 0<t+N^(2*δ)*U := add_pos_of_nonneg_of_pos (hr₀.trans ht.1)
    (mul_pos (Real.rpow_pos_of_pos hN _) hU)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr
  exact ht.2

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem comparisonFloor_measurable (N δ U : ℝ) : Measurable (comparisonFloor N δ U) := by
  unfold comparisonFloor
  fun_prop

 theorem comparisonCapSlope_continuous (N δ U L E d : ℝ) :
    Continuous (comparisonCapSlope N δ U L E d) := by
  unfold comparisonCapSlope
  fun_prop

 theorem comparisonCapSlope_nonneg {N δ U L E d u : ℝ} (hN : 0<N) (hU : 0≤U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) :
    0 ≤ comparisonCapSlope N δ U L E d u := by
  unfold comparisonCapSlope
  positivity

 theorem comparisonCapSlope_bound {N δ U L E d u : ℝ} (hN : 0<N) (hU : 0≤U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : u ∈ Icc (0:ℝ) 1) :
    |comparisonCapSlope N δ U L E d u| ≤ comparisonCapSlope N δ U L E d 1 := by
  rw [abs_of_nonneg (comparisonCapSlope_nonneg hN hU hL hE hd hu.1)]
  unfold comparisonCapSlope
  gcongr
  exact hu.2

 theorem comparisonCapSlope_times_le {N δ U L E d u : ℝ} (hN : 0<N) (hU : 0≤U)
    (hL : 0<L) (hu : 0≤u) :
    comparisonCapSlope N δ U L E d u*(u+U) ≤ 2*comparisonCap N δ U L E d u := by
  have hh : 0 ≤ N^δ*((u+U)/L) := by positivity
  have he : 2*comparisonCap N δ U L E d u-
      comparisonCapSlope N δ U L E d u*(u+U)=N^δ*((u+U)/L) := by
    unfold comparisonCapSlope comparisonCap
    ring
  linarith [he]

 theorem comparison_control_bounds {N δ U L E d r₀ u : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : 0≤r₀) (hu : u ∈ Icc (0:ℝ) 1) {r : ℝ} (hr : r ∈ Icc r₀ 1) :
    1 ≤ comparisonCap N δ U L E d u-comparisonFloor N δ U r ∧
      comparisonCap N δ U L E d u-comparisonFloor N δ U r ≤ comparisonCap N δ U L E d 1 ∧
      |comparisonCapSlope N δ U L E d u| ≤ comparisonCapSlope N δ U L E d 1 := by
  have hk := comparisonFloor_pos (δ:=δ) hN hU (hr₀.trans hr.1)
  have hk' := comparisonFloor_le_half hN hU (hr₀.trans hr.1) hq
  have hm := comparisonCap_ge (δ:=δ) hN hU hL hLU hE hd hu.1
  have hm' := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd hu
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) hu.2
  exact ⟨by linarith,by linarith,comparisonCapSlope_bound hN hU.le hL hE hd hu⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparison_minimum_potential {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (n : ℕ) (hn : 0<n) (g : ℝ → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g) (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    let G := radiusComparisonGradient g α.val.val (orderedPathS n b' h') (orderedPathB n b' h')
    let w := inverseControlWeight α.val.val k M
    let J := inverseControlFactor r₀ (fun r => w r*M' (α.val.val r))
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H r₀ 1 ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → HasDerivAt H (J r*G r) r) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 →
        (H r<0 → deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r → deriv α.val.val r=k r)) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → H r=0 → G r=0) := by
  dsimp only
  intro α hg b h hb hh hbn hhn hmin
  apply source_minimum_potential (le_trans hr₀.2 (by norm_num))
    ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    (comparisonFloor_pos hN hU (by norm_num))
    (comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1)
    (fun r hri => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri)
    (comparisonFloor_measurable N δ U)
    (comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd)
    (comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num))
    (comparisonCap_continuous N δ U L E d)
    (comparisonCapSlope_continuous N δ U L E d).measurable
    (fun u v => comparisonCap_tangent hN hE hd)
    (gap:=1) (U:=comparisonCap N δ U L E d 1)
    (L:=comparisonCapSlope N δ U L E d 1) (lo:=1/2) (hi:=2)
    (by norm_num)
    (comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num))
    (comparisonCapSlope_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num))
    α
    (fun r hri => comparison_control_bounds hN hU hL hLU hE hd hq hr₀.1 (α.val.property.1 r) hri)
    (fun r hri => comparisonFloor_le_half hN hU (hr₀.1.trans hri.1) hq)
    (fun r _ => hq.trans (comparisonCap_ge hN hU hL hLU hE hd (α.val.property.1 r).1))
    (by nlinarith [hr₀.1,hu₀.2]) (by nlinarith [hu₀.1,hr₀.2])
    hg n hn b h hb hh hbn hhn hmin

end SKFluctuations

 

 

namespace SKFluctuations
open Hierarchy MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
 theorem cumulativePair_SK_bounds [Nonempty ι] (n : ℕ) {w : Spin n → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    (ha : MassOrdered 0 as) (q : ℕ → ι → ℝ) (j : ℕ) :
    let S := cumulativePair w φ as q j (orderedOverlap n)
    let B := cumulativePair w φ as q j (fun σ τ => (orderedOverlap n σ τ)^2)
    0≤S ∧ S≤1 ∧ S^2≤B ∧ B≤1 := by
  have he (P : Spin n → Spin n → ℝ) : cumulativePair w φ as q j P =
      rootLevelPairMean w φ (fun i => (q 0 i).toNNReal) P
        (diagonalBoundarySteps as (q 0) (fun k => q (k+1))) j :=
    ClockTree.pairDisorder_eq_rootLevelPairMean hw φ as ha q j P
  dsimp only
  rw [he,he]
  apply rootLevelPairMean_SK_bounds n hw φ
  rw [←clockSteps_cumulative]
  exact clockSteps_ordered ha _

 theorem stepPairDisorder_SK_bounds (n : ℕ) {w : Spin n → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (A B : List (GaussianStep ι)) (ho : OrderedSteps 0 (A++B)) :
    let S := stepPairDisorder w φ q₀ A B (orderedOverlap n) 0
    let B₂ := stepPairDisorder w φ q₀ A B (fun σ τ => (orderedOverlap n σ τ)^2) 0
    0≤S ∧ S≤1 ∧ S^2≤B₂ ∧ B₂≤1 := by
  have hA : ∀ s ∈ A, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_left _ hs)
  have hB : ∀ s ∈ B, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_right _ hs)
  have he (P : Spin n → Spin n → ℝ) :
      stepPairDisorder w φ q₀ A B P 0 =
        cumulativePair w φ (positiveStepMasses A hA++positiveStepMasses B hB)
          (stepClockValues (fun i => (q₀ i:ℝ)) (A++B)) (positiveStepMasses A hA).length P :=
    (congr_fun (ClockTree.pairDisorder_coordinates hw φ A B hA hB ho q₀ P) 0).symm
  dsimp only
  rw [he,he]
  apply cumulativePair_SK_bounds n hw φ
  rw [←positiveStepMasses_append]
  exact positiveStepMasses_ordered ho _

 theorem pathPairMoment_SK_bounds (n : ℕ) {w : Spin n → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    let S := pathPairMoment w φ q (orderedOverlap n) u
    let B := pathPairMoment w φ q (fun σ τ => (orderedOverlap n σ τ)^2) u
    0≤S ∧ S≤1 ∧ S^2≤B ∧ B≤1 := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  have hS := retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 (orderedOverlap n) 0
  have hB := retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2
    (fun σ τ => (orderedOverlap n σ τ)^2) 0
  have hb (k : ℕ) :
      let S := retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses k) (orderedOverlap n) 0
      let B := retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses k) (fun σ τ => (orderedOverlap n σ τ)^2) 0
      0≤S ∧ S≤1 ∧ S^2≤B ∧ B≤1 :=
    stepPairDisorder_SK_bounds n hw φ _ _ _
      (retainedPairSample_ordered q ⟨u,hu.1⟩ hu.2 _ (uniformMasses_ordered k))
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hS (Eventually.of_forall fun k => (hb k).1),
    le_of_tendsto' hS (fun k => (hb k).2.1),
    le_of_tendsto_of_tendsto (hS.pow 2) hB (Eventually.of_forall fun k => (hb k).2.2.1),
    le_of_tendsto' hB (fun k => (hb k).2.2.2)⟩

end SKFluctuations

 

 

namespace SKFluctuations
open Hierarchy MeasureTheory Filter Set
open scoped Topology NNReal

 theorem orderedPath_SK_bounds (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    0≤orderedPathS n b h u ∧ orderedPathS n b h u≤1 ∧
      (orderedPathS n b h u)^2≤orderedPathB n b h u ∧ orderedPathB n b h u≤1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact pathPairMoment_SK_bounds n (uniformWeight_pos n) (orderedFeature n)
    (orderedPathClock n b h) (orderedPathClock_monotone n hb hh) hu

end SKFluctuations

 

 

namespace SKFluctuations
open Set

def comparisonStrength (f : ℝ → ℝ) (d lam r : ℝ) : ℝ := lam*f (lam*r/d^3)
def comparisonLogSlope (e : ℝ → ℝ) (r : ℝ) : ℝ := -r*deriv e r/e r
def comparisonRadiusField (h₀ e : ℝ → ℝ) (r : ℝ) : ℝ := h₀ r+e r*r

theorem hasDerivAt_radius_strength {e : ℝ → ℝ} {r : ℝ}
    (he : DifferentiableAt ℝ e r) (her : e r ≠ 0) :
    HasDerivAt (fun t => e t*t) ((1-comparisonLogSlope e r)*e r) r := by
  have hh := he.hasDerivAt.mul (hasDerivAt_id r)
  have heq : deriv e r*r+e r*1 = (1-comparisonLogSlope e r)*e r := by
    unfold comparisonLogSlope
    field_simp
    ring
  exact hh.congr_deriv (by simpa only [id_eq] using heq)

theorem radius_strength_growth {e : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b)
    (he : ∀ t ∈ Icc a b, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc a b, 0 < e t)
    (hemono : AntitoneOn e (Icc a b)) (hκ : 0 ≤ κ)
    (hp : ∀ t ∈ Icc a b, κ ≤ 1-comparisonLogSlope e t) :
    κ*e b*(b-a) ≤ e b*b-e a*a := by
  have hder t (ht : t ∈ Icc a b) := hasDerivAt_radius_strength (he t ht) (ne_of_gt (hepos t ht))
  apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  rw [(hder t (interior_subset ht)).deriv]
  exact mul_le_mul (hp t (interior_subset ht))
    (hemono (interior_subset ht) ⟨hab,le_rfl⟩ (interior_subset ht).2)
    (hepos b ⟨hab,le_rfl⟩).le
    (hκ.trans (hp t (interior_subset ht)))

theorem comparisonRadiusField_growth {h₀ e : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b)
    (hh₀ : MonotoneOn h₀ (Icc a b))
    (he : ∀ t ∈ Icc a b, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc a b, 0 < e t)
    (hemono : AntitoneOn e (Icc a b)) (hκ : 0 ≤ κ)
    (hp : ∀ t ∈ Icc a b, κ ≤ 1-comparisonLogSlope e t) :
    κ*e b*(b-a) ≤ comparisonRadiusField h₀ e b-comparisonRadiusField h₀ e a := by
  have hee := radius_strength_growth hab he hepos hemono hκ hp
  have hh := hh₀ ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  dsimp [comparisonRadiusField]
  linarith

theorem radius_clock_growth_of_approx {H h₀ e : ℝ → ℝ} {a b κ ε : ℝ}
    (hab : a ≤ b) (hh₀ : MonotoneOn h₀ (Icc a b))
    (he : ∀ t ∈ Icc a b, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc a b, 0 < e t)
    (hemono : AntitoneOn e (Icc a b)) (hκ : 0 ≤ κ)
    (hp : ∀ t ∈ Icc a b, κ ≤ 1-comparisonLogSlope e t)
    (ha : |H a-comparisonRadiusField h₀ e a| ≤ ε)
    (hb : |H b-comparisonRadiusField h₀ e b| ≤ ε) :
    κ*e b*(b-a)-2*ε ≤ H b-H a := by
  have hh := comparisonRadiusField_growth hab hh₀ he hepos hemono hκ hp
  rcases abs_le.mp ha with ⟨ha₁,ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁,hb₂⟩
  linarith

end SKFluctuations

 

 

namespace SKFluctuations
open Hierarchy Set

 theorem comparison_gradient_slope {g α S B : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hg : g r ≠ 0) :
    radiusComparisonGradient g α S B r =
      g r*((2-comparisonLogSlope g r)*r-
        2*(1-comparisonLogSlope g r)*S (α r)-comparisonLogSlope g r*B (α r)/r) := by
  unfold radiusComparisonGradient comparisonLogSlope
  field_simp
  ring

 theorem comparison_gradient_identity (g α S B : ℝ → ℝ) (r : ℝ) :
    radiusComparisonGradient g α S B r =
      2*g r*(r-S (α r))+deriv g r*((r-S (α r))^2+(B (α r)-S (α r)^2)) := by
  unfold radiusComparisonGradient
  ring

 theorem comparison_gradient_nonneg_geometry {g α S B : ℝ → ℝ} {r : ℝ}
    (hr : 0<r) (hg : 0<g r) (hp : comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (hS : 0≤S (α r)) (hB : S (α r)^2≤B (α r))
    (hG : 0≤radiusComparisonGradient g α S B r) :
    S (α r)≤r ∧ comparisonLogSlope g r*B (α r)≤2*r^2 := by
  have hd : deriv g r ≤ 0 := by
    have hh : (0:ℝ)*g r ≤ -r*deriv g r := (le_div_iff₀ hg).mp hp.1
    nlinarith
  have hI := comparison_gradient_identity g α S B r
  have he : 0≤(r-S (α r))^2+(B (α r)-S (α r)^2) := by nlinarith [sq_nonneg (r-S (α r))]
  have hSr : S (α r)≤r := by
    have hh := mul_nonpos_of_nonpos_of_nonneg hd he
    nlinarith
  refine ⟨hSr,?_⟩
  rw [comparison_gradient_slope hr.ne' hg.ne'] at hG
  have hb := (nonneg_of_mul_nonneg_right hG hg)
  have hh := mul_nonneg hr.le hb
  field_simp [hr.ne'] at hh
  have hh' : 0≤(2-comparisonLogSlope g r)*r^2-
      2*(1-comparisonLogSlope g r)*S (α r)*r-comparisonLogSlope g r*B (α r) := by
    convert hh using 1
    ring
  have hz : 0≤2*(1-comparisonLogSlope g r)*S (α r)*r :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.2)) hS) hr.le
  nlinarith [mul_nonneg hp.1 (sq_nonneg r)]

 theorem comparison_gradient_contact_mismatch {g α S B : ℝ → ℝ} {r : ℝ}
    (hr : 0<r) (hg : 0<g r) (hp : comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (hS : 0≤S (α r)) (hB : S (α r)^2≤B (α r))
    (hG : radiusComparisonGradient g α S B r=0) :
    S (α r)≤r ∧ (S (α r)-r)^2≤B (α r)-S (α r)^2 := by
  have hSr := (comparison_gradient_nonneg_geometry hr hg hp hS hB hG.ge).1
  refine ⟨hSr,?_⟩
  have hEq : 2*r*(r-S (α r))=comparisonLogSlope g r*
      ((r-S (α r))^2+(B (α r)-S (α r)^2)) := by
    rw [comparison_gradient_slope hr.ne' hg.ne'] at hG
    have hh := (mul_eq_zero.mp hG).resolve_left hg.ne'
    have hh' := congrArg (fun x : ℝ => x*r) hh
    field_simp [hr.ne'] at hh'
    nlinarith [hh']
  have hz : 0≤(r-S (α r))^2+(B (α r)-S (α r)^2) := by nlinarith [sq_nonneg (r-S (α r))]
  have hh := mul_le_of_le_one_left hz hp.2
  have ht := mul_nonneg hS (sub_nonneg.mpr hSr)
  nlinarith

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparison_minimum_contact_potential {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (n : ℕ) (hn : 0<n) (g : ℝ → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (hgpos : ∀ r ∈ Ioc r₀ 1, 0<g r)
    (hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    let G := radiusComparisonGradient g α.val.val (orderedPathS n b' h') (orderedPathB n b' h')
    let w := inverseControlWeight α.val.val k M
    let J := inverseControlFactor r₀ (fun r => w r*M' (α.val.val r))
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H r₀ 1 ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → HasDerivAt H (J r*G r) r) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 →
        (H r<0 → deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r → deriv α.val.val r=k r)) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → H r=0 → G r=0 ∧
        orderedPathS n b' h' (α.val.val r)≤r ∧
        (orderedPathS n b' h' (α.val.val r)-r)^2≤
          orderedPathB n b' h' (α.val.val r)-(orderedPathS n b' h' (α.val.val r))^2) := by
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_potential hN hU hL hLU hE hd
    hq hr₀ hu₀ n hn g α hg b h hb hh hbn hhn hmin
  refine ⟨H,hH,hD,hbang,?_⟩
  have hα := inverseConstraint_strictMonoOn
    (comparisonFloor_pos (δ:=δ) hN hU (show (0:ℝ)≤1 by norm_num))
    (comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1)
    (fun r hri => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri) α.property
  filter_upwards [hzero,volume.ae_ne r₀] with r hz hrne hri hhzero
  have hri' : r ∈ Ioc r₀ 1 := ⟨lt_of_le_of_ne hri.1 hrne.symm,hri.2⟩
  have hαr : α.val.val r ∈ Ioc (0:ℝ) 1 := by
    refine ⟨?_,(α.val.property.1 r).2⟩
    have hh' := hα ⟨rfl.le,le_trans hr₀.2 (by norm_num)⟩ hri hri'.1
    rw [α.property.1] at hh'
    exact hu₀.1.trans_lt hh'
  have hbs := orderedPath_SK_bounds n hn _ _
    (fun u hu v hv huv => Real.toNNReal_mono ((hb α) hu hv huv))
    (fun u hu v hv huv => Real.toNNReal_mono ((hh α) hu hv huv)) hαr
  exact ⟨hz hri hhzero,comparison_gradient_contact_mismatch
    (hr₀.1.trans_lt hri'.1) (hgpos r hri') (hp r hri') hbs.1 hbs.2.2.1 (hz hri hhzero)⟩

end SKFluctuations

end

end OAI
