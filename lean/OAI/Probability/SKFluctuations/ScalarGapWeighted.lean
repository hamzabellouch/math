import Mathlib
import OAI.Probability.SKFluctuations.WeightedClockPDE

namespace OAI

/-! Scalar Gap Weighted. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology

noncomputable def scalarWeightedMoment (ρ : ℝ → ℝ) (A : (Fin 1 → ℝ) → ℝ) : ℝ :=
  ∫ x, ρ x*A (fun _ => x)

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

private theorem ScalarGapWeighted_gap_energy_spatial (T s : ℝ) : BddSmooth 0 (J.scalarGapEnergy m T s) :=
  clockTest_bddSmooth (J.evolve hm (T-s)).regular ((J.scalarJetTest hG hm 1 (T-s)).square.smoothA) m s

private theorem ScalarGapWeighted_gap_curvature_spatial (T s : ℝ) : BddSmooth 0 (J.scalarGapCurvature m T s) :=
  clockTest_bddSmooth (J.evolve hm (T-s)).regular ((J.gapJet hG hm (T-s)).smoothA) m s

private theorem ScalarGapWeighted_gap_third_test_smooth (t : ℝ) : BddSmooth 0
    (fun y => (J.scalarClockJet m 4 t y)^2-12*m*(J.scalarClockJet m 2 t y*(J.scalarClockJet m 3 t y)^2)+
      6*m^2*(J.scalarClockJet m 2 t y)^4) := by
  have h (k) := J.scalarClockPlane_positiveJets_bddSmooth hG hm 0 k t
  exact (((h 3).pow 2).sub (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).add (((h 1).pow 4).const_mul (6*m^2))

private theorem ScalarGapWeighted_gap_third_spatial (T s : ℝ) : BddSmooth 0 (J.scalarGapThird m T s) :=
  clockTest_bddSmooth (J.evolve hm (T-s)).regular (ScalarGapWeighted_gap_third_test_smooth J hG hm (T-s)) m s

omit hG in
private theorem ScalarGapWeighted_clock_backward_bound {A : ℝ → (Fin 1 → ℝ) → ℝ}
    (hA : ∀ t, BddSmooth 0 (A t)) (hb : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => A p.1 p.2))
    (T : ℝ) : AbsBounded (fun p : ℝ × ℝ =>
      clockTest m (clockContinuation m J.F (T-p.1)) (A (T-p.1)) p.1 (fun _ => p.2)) := by
  obtain ⟨K,hK,hb⟩ := hb
  exact ⟨K,hK,fun p => clockTest_abs_le (J.evolve hm (T-p.1)).lipschitz (hA (T-p.1))
    (fun y => hb (T-p.1,y)) m p.1 (fun _ => p.2)⟩

 theorem HeatJet.scalarGapEnergy_bound (T : ℝ) :
    AbsBounded (fun p : ℝ × ℝ => J.scalarGapEnergy m T p.1 (fun _ => p.2)) := by
  exact ScalarGapWeighted_clock_backward_bound J hm (fun t => (J.scalarJetTest hG hm 1 t).square.smoothA)
    (((J.scalarJetFamily hG hm 1).square).boundedA) T

 theorem HeatJet.scalarGapCurvature_bound (T : ℝ) :
    AbsBounded (fun p : ℝ × ℝ => J.scalarGapCurvature m T p.1 (fun _ => p.2)) := by
  exact ScalarGapWeighted_clock_backward_bound J hm (fun t => (J.gapJet hG hm t).smoothA) (J.gapFamily hG hm).boundedA T

 theorem HeatJet.scalarGapThird_bound (T : ℝ) :
    AbsBounded (fun p : ℝ × ℝ => J.scalarGapThird m T p.1 (fun _ => p.2)) := by
  have h (k) := J.scalarClockJet_bound hG hm k
  exact ScalarGapWeighted_clock_backward_bound J hm (ScalarGapWeighted_gap_third_test_smooth J hG hm)
    ((((h 3).pow 2).sub (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).add (((h 1).pow 4).const_mul (6*m^2))) T

 theorem HeatJet.weightedGapEnergy_continuous {ρ : ℝ → ℝ} (hρ : Integrable ρ) (T : ℝ) :
    Continuous (fun s => scalarWeightedMoment ρ (J.scalarGapEnergy m T s)) := by
  apply weighted_bounded_continuous hρ
  · intro s
    exact (ScalarGapWeighted_gap_energy_spatial J hG hm T s).continuous.comp (continuous_pi fun _ => continuous_id)
  · intro x
    exact J.continuous_scalarGapEnergy hG hm T (fun _ => x)
  · exact J.scalarGapEnergy_bound hG hm T

 theorem HeatJet.weightedGapCurvature_continuous {ρ : ℝ → ℝ} (hρ : Integrable ρ) (T : ℝ) :
    Continuous (fun s => scalarWeightedMoment ρ (J.scalarGapCurvature m T s)) := by
  apply weighted_bounded_continuous hρ
  · intro s
    exact (ScalarGapWeighted_gap_curvature_spatial J hG hm T s).continuous.comp (continuous_pi fun _ => continuous_id)
  · intro x
    exact J.continuous_scalarGapCurvature hG hm T (fun _ => x)
  · exact J.scalarGapCurvature_bound hG hm T

 theorem HeatJet.weightedGapEnergy_hasDerivAt (hH : ∀ k i, BddSmooth k (J.H i))
    {ρ : ℝ → ℝ} (hρ : Integrable ρ) {T s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => scalarWeightedMoment ρ (J.scalarGapEnergy m T r))
      (scalarWeightedMoment ρ (J.scalarGapCurvature m T s)) s := by
  apply weighted_bounded_hasDerivAt hρ hs
  · intro r
    exact (ScalarGapWeighted_gap_energy_spatial J hG hm T r).continuous.comp (continuous_pi fun _ => continuous_id)
  · intro r
    exact (ScalarGapWeighted_gap_curvature_spatial J hG hm T r).continuous.comp (continuous_pi fun _ => continuous_id)
  · obtain ⟨K,hK,hb⟩ := J.scalarGapEnergy_bound hG hm T
    exact ⟨K,hK,fun x => hb (s,x)⟩
  · exact J.scalarGapCurvature_bound hG hm T
  · intro r hr x
    exact J.hasDerivAt_scalarGapEnergy hG hH hm hr (fun _ => x)

 theorem HeatJet.weightedGapCurvature_hasDerivAt (hH : ∀ k i, BddSmooth k (J.H i))
    {ρ : ℝ → ℝ} (hρ : Integrable ρ) {T s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => scalarWeightedMoment ρ (J.scalarGapCurvature m T r))
      (scalarWeightedMoment ρ (J.scalarGapThird m T s)) s := by
  apply weighted_bounded_hasDerivAt hρ hs
  · intro r
    exact (ScalarGapWeighted_gap_curvature_spatial J hG hm T r).continuous.comp (continuous_pi fun _ => continuous_id)
  · intro r
    exact (ScalarGapWeighted_gap_third_spatial J hG hm T r).continuous.comp (continuous_pi fun _ => continuous_id)
  · obtain ⟨K,hK,hb⟩ := J.scalarGapCurvature_bound hG hm T
    exact ⟨K,hK,fun x => hb (s,x)⟩
  · exact J.scalarGapThird_bound hG hm T
  · intro r hr x
    exact J.hasDerivAt_scalarGapCurvature hG hm hH hr (fun _ => x)
end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

 theorem HeatJet.regular_of_smoothG {n k : ℕ} (J : HeatJet n)
    (hG : ∀ i, BddSmooth k (J.G i)) : PotentialRegularity k J.F := by
  refine ⟨⟨J.C,J.lipschitz⟩,fun v => ?_⟩
  exact ⟨fun y => ∑ i, v i*J.G i y,
    BddSmooth.sum Finset.univ (fun i _ => (hG i).const_mul (v i)),fun x t => J.derivF x v t⟩

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

 theorem HeatJet.scalarGapEnergy_bddSmooth (k : ℕ) (T s : ℝ) :
    BddSmooth k (J.scalarGapEnergy m T s) :=
  clockTest_bddSmooth (clockContinuation_regular (J.regular_of_smoothG (hG k)) hm (T-s))
    ((J.scalarClockPlane_positiveJets_bddSmooth hG hm k 1 (T-s)).pow 2) m s

 theorem HeatJet.scalarGapCurvature_bddSmooth (k : ℕ) (T s : ℝ) :
    BddSmooth k (J.scalarGapCurvature m T s) :=
  clockTest_bddSmooth (clockContinuation_regular (J.regular_of_smoothG (hG k)) hm (T-s))
    (((J.scalarClockPlane_positiveJets_bddSmooth hG hm k 2 (T-s)).pow 2).sub
      (((J.scalarClockPlane_positiveJets_bddSmooth hG hm k 1 (T-s)).pow 3).const_mul (2*m))) m s

 theorem HeatJet.filledSquare_bddSmooth (hA : J.A=J.G 0) (k : ℕ) (T s : ℝ) :
    BddSmooth k (J.filledSquare hm T s) := by
  apply clockTest_bddSmooth (clockContinuation_regular (J.regular_of_smoothG (hG k)) hm (T-s))
  change BddSmooth k (fun y => (clockTest m J.F J.A (T-s) y)^2)
  rw [hA]
  exact (clockTest_bddSmooth (J.regular_of_smoothG (hG k)) (hG k 0) m (T-s)).pow 2

noncomputable def HeatJet.profileGapSquareJet (hA : J.A=J.G 0) (T s : ℝ) : HeatJet 0 :=
  (J.evolve hm T).withTest (J.filledSquare hm T s) (J.filledSquare_bddSmooth hG hm hA 2 T s)

noncomputable def HeatJet.profileGapEnergyJet (T s : ℝ) : HeatJet 0 :=
  (J.evolve hm T).withTest (J.scalarGapEnergy m T s) (J.scalarGapEnergy_bddSmooth hG hm 2 T s)

noncomputable def HeatJet.profileGapCurvatureJet (T s : ℝ) : HeatJet 0 :=
  (J.evolve hm T).withTest (J.scalarGapCurvature m T s) (J.scalarGapCurvature_bddSmooth hG hm 2 T s)

 theorem HeatJet.profileGapSquareJet_F (hA : J.A=J.G 0) (T s : ℝ) :
    (J.profileGapSquareJet hG hm hA T s).F=(J.evolve hm T).F := rfl

 theorem HeatJet.profileGapSquareJet_A (hA : J.A=J.G 0) (T s : ℝ) :
    (J.profileGapSquareJet hG hm hA T s).A=J.filledSquare hm T s := rfl

 theorem HeatJet.profileGapEnergyJet_F (T s : ℝ) :
    (J.profileGapEnergyJet hG hm T s).F=(J.evolve hm T).F := rfl

 theorem HeatJet.profileGapEnergyJet_A (T s : ℝ) :
    (J.profileGapEnergyJet hG hm T s).A=J.scalarGapEnergy m T s := rfl

 theorem HeatJet.profileGapCurvatureJet_F (T s : ℝ) :
    (J.profileGapCurvatureJet hG hm T s).F=(J.evolve hm T).F := rfl

 theorem HeatJet.profileGapCurvatureJet_A (T s : ℝ) :
    (J.profileGapCurvatureJet hG hm T s).A=J.scalarGapCurvature m T s := rfl
 theorem HeatJet.profileGapSquare_hasDerivAt
    (hH : ∀ k i, BddSmooth k (J.H i)) (hA : J.A=J.G 0) (hA₁ : J.A₁ 0=J.H 0)
    {T s : ℝ} (hs : s ∈ Ioo 0 T)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    HasDerivAt (fun u => (J.profileGapSquareJet hG hm hA T u).nonnegativeProfileTest α l t x)
      ((J.profileGapEnergyJet hG hm T s).nonnegativeProfileTest α l t x) s := by
  obtain ⟨M,_hM,hb⟩ := J.scalarGapCurvature_bound hG hm T
  apply HeatJet.nonnegativeProfileTest_hasDerivAt
    (J.profileGapSquareJet hG hm hA T) (J.profileGapEnergyJet hG hm T)
    (M:=M) hs (fun u => (J.profileGapSquareJet_F hG hm hA T u).trans
      (J.profileGapSquareJet_F hG hm hA T s).symm)
      ((J.profileGapEnergyJet_F hG hm T s).trans (J.profileGapSquareJet_F hG hm hA T s).symm)
      (J.scalarGapCurvature m T)
  · intro u hu y
    simp only [HeatJet.profileGapSquareJet_A,HeatJet.profileGapEnergyJet_A]
    rw [← J.filledEnergy_eq_scalarGapEnergy hA hA₁ hm]
    exact J.hasDerivAt_filledSquare hm hu y
  · intro u hu y
    simp only [HeatJet.profileGapEnergyJet_A]
    exact J.hasDerivAt_scalarGapEnergy hG hH hm hu y
  · intro u _ y
    have hy : (fun _ : Fin 1 => y 0) = y := by ext i; rw [Fin.eq_zero i]
    simpa only [hy] using hb (u,y 0)
  · exact hα

 theorem HeatJet.profileGapEnergy_hasDerivAt
    (hH : ∀ k i, BddSmooth k (J.H i)) {T s : ℝ} (hs : s ∈ Ioo 0 T)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    HasDerivAt (fun u => (J.profileGapEnergyJet hG hm T u).nonnegativeProfileTest α l t x)
      ((J.profileGapCurvatureJet hG hm T s).nonnegativeProfileTest α l t x) s := by
  obtain ⟨M,_hM,hb⟩ := J.scalarGapThird_bound hG hm T
  apply HeatJet.nonnegativeProfileTest_hasDerivAt
    (J.profileGapEnergyJet hG hm T) (J.profileGapCurvatureJet hG hm T)
    (M:=M) hs (fun u => (J.profileGapEnergyJet_F hG hm T u).trans
      (J.profileGapEnergyJet_F hG hm T s).symm)
      ((J.profileGapCurvatureJet_F hG hm T s).trans (J.profileGapEnergyJet_F hG hm T s).symm)
      (J.scalarGapThird m T)
  · intro u hu y
    simp only [HeatJet.profileGapEnergyJet_A,HeatJet.profileGapCurvatureJet_A]
    exact J.hasDerivAt_scalarGapEnergy hG hH hm hu y
  · intro u hu y
    simp only [HeatJet.profileGapCurvatureJet_A]
    exact J.hasDerivAt_scalarGapCurvature hG hm hH hu y
  · intro u _ y
    have hy : (fun _ : Fin 1 => y 0) = y := by ext i; rw [Fin.eq_zero i]
    simpa only [hy] using hb (u,y 0)
  · exact hα

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.massEnergy {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (T s : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockTest a (J.evolve hb (T-s)).F (J.evolve hb (T-s)).potentialEnergy s x

theorem HeatJet.continuous_massEnergy {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (T : ℝ) (x : Fin (n+1) → ℝ) :
    Continuous (fun s => J.massEnergy a hb T s x) := by
  let V := J.family hb
  have hc : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialEnergy p.2) := by
    unfold HeatJet.potentialEnergy
    exact continuous_finsetSum _ fun i _ => (V.continuousG i).pow 2
  have hbE : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialEnergy p.2) := by
    unfold HeatJet.potentialEnergy
    simpa only [pow_two] using AbsBounded.sum (fun i => (V.boundedG i).mul (V.boundedG i))
  obtain ⟨K,_,hK⟩ := hbE
  exact (dynamic_clockTest_continuous V.lipschitz V.continuousF hc
    (fun s y => hK (s,y)) a x).comp
    (continuous_id.prodMk (continuous_const.sub continuous_id))

 
theorem HeatJet.mass_difference_integral {n : ℕ} (J : HeatJet n) {a b T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hT : 0 ≤ T) (x : Fin (n+1) → ℝ) :
    clockContinuation a J.F T x-clockContinuation b J.F T x =
      (a-b)/2*(∫ s in 0..T, J.massEnergy a hb T s x) := by
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (J.continuous_potentialSplit a hb T x).continuousOn
    (fun s hs => J.hasDerivAt_potentialSplit ha hb hs x)
    (((J.continuous_massEnergy a hb T x).const_mul ((a-b)/2)).intervalIntegrable 0 T)
  rw [J.potentialSplit_terminal,J.potentialSplit_zero ha.ne'] at hd
  simpa only [HeatJet.potentialSplitResponse,HeatJet.massEnergy,
    intervalIntegral.integral_const_mul] using hd.symm

section Scalar
variable (J : HeatJet 0) (hS : ∀ k i, BddSmooth k (J.G i))
    (hG : ∀ y, |J.G 0 y| ≤ 1) {b : ℝ} (hb : 0 < b)

include hS hG

 

theorem HeatJet.massEnergy_mass_bound (hb1 : b ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a T s : ℝ}, 0 ≤ a → a ≤ 1 → 0 ≤ s → s ≤ T →
      ∀ x : Fin 1 → ℝ,
      |J.massEnergy a hb T s x-J.massEnergy b hb T s x| ≤ |a-b| *K*s := by
  obtain ⟨H,hH,hbH⟩ := J.scalarClockJet_bound hS hb 1
  refine ⟨2*H+3,by positivity,?_⟩
  intro a T s ha ha1 hs _ x
  let V := J.scalarJetTest hS hb 0 (T-s)
  have hA : ∀ y, |V.A y| ≤ 1 := by
    intro y
    change |J.scalarClockJet b 1 (T-s) y| ≤ 1
    rw [J.scalarClockJet_one hb]
    exact clockTest_abs_le J.lipschitz (J.smoothG 0) hG b (T-s) y
  have hA1 : ∀ i y, |V.A₁ i y| ≤ H := by
    intro i y
    exact hbH (T-s,y)
  have hG' : ∀ i y, |V.G i y| ≤ 1 := by
    intro i y
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact clockTest_abs_le J.lipschitz (J.smoothG 0) hG b (T-s) y
  have hSq : ∀ y, |V.square.A y| ≤ 1 := by
    intro y
    change |(V.A y)^2| ≤ 1
    rw [pow_two]
    rw [abs_mul]
    nlinarith [hA y,abs_nonneg (V.A y)]
  have hSq1 : ∀ i y, |V.square.A₁ i y| ≤ (2*H)*1*1 := by
    intro i y
    change |2*(V.A y*V.A₁ i y)| ≤ _
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [mul_le_mul (hA y) (hA1 i y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
  have hh := V.square.clock_mass_difference (fun _ => 1) (by norm_num) (by positivity)
    (fun _ => by norm_num) hSq hG' hSq1 ha ha1 hb hb1 hs x
  have he : ∀ y, V.square.A y = (J.evolve hb (T-s)).potentialEnergy y := by
    intro y
    change (J.scalarClockJet b 1 (T-s) y)^2 = _
    rw [J.scalarClockJet_one hb]
    change (J.evolve hb (T-s)).G 0 y ^ 2 = ∑ i : Fin 1, (J.evolve hb (T-s)).G i y ^ 2
    rw [Fin.sum_univ_one]
  rw [show V.square.A = (J.evolve hb (T-s)).potentialEnergy from funext he] at hh
  change |J.massEnergy a hb T s x-J.massEnergy b hb T s x| ≤
    (|a-b| *(2*H+3)*1*∑ _ : Fin 1, (1:ℝ)^2)*s at hh
  simpa only [Fin.sum_univ_one,one_pow,mul_one] using hh
theorem HeatJet.massEnergy_integral_continuousAt (hb1 : b < 1) {T : ℝ}
    (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    ContinuousAt (fun a => ∫ s in 0..T, J.massEnergy a hb T s x) b := by
  obtain ⟨K,hK,hbK⟩ := J.massEnergy_mass_bound hS hG hb hb1.le
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hev : ∀ᶠ a : ℝ in 𝓝 b, 0 < a ∧ a < 1 :=
    isOpen_Ioo.mem_nhds ⟨hb,hb1⟩
  have hbound : ∀ᶠ a : ℝ in 𝓝 b,
      dist (∫ s in 0..T, J.massEnergy a hb T s x)
        (∫ s in 0..T, J.massEnergy b hb T s x) ≤ |a-b| *K*T*T := by
    filter_upwards [hev] with a ha
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := T) (C := |a-b| *K*T)
      (f := fun s => J.massEnergy a hb T s x-J.massEnergy b hb T s x) (fun s hs => by
        rw [uIoc_of_le hT] at hs
        exact (hbK ha.1.le ha.2.le hs.1.le hs.2 x).trans
          (mul_le_mul_of_nonneg_left hs.2 (mul_nonneg (abs_nonneg _) hK)))
    rw [intervalIntegral.integral_sub ((J.continuous_massEnergy a hb T x).intervalIntegrable 0 T)
      ((J.continuous_massEnergy b hb T x).intervalIntegrable 0 T)] at hi
    simpa only [Real.norm_eq_abs,Real.dist_eq,sub_zero,abs_of_nonneg hT] using hi
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound
  simpa only [Pi.sub_apply,id_eq,sub_self,abs_zero,zero_mul] using
    ((((continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℝ => b) b)).abs.mul_const K).mul_const T).mul_const T).tendsto

 

theorem HeatJet.hasDerivAt_mass_clockContinuation (hb1 : b < 1) {T : ℝ}
    (hT : 0 ≤ T) (x : Fin 1 → ℝ) :
    HasDerivAt (fun a => clockContinuation a J.F T x)
      ((1/2:ℝ)*(∫ s in 0..T, J.massEnergy b hb T s x)) b := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht := ((J.massEnergy_integral_continuousAt hS hG hb hb1 hT x).const_mul (1/2:ℝ)).tendsto
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ a : ℝ in 𝓝 b, 0 < a from Ioi_mem_nhds hb).filter_mono nhdsWithin_le_nhds] with a ha hapos
  rw [slope_def_field,J.mass_difference_integral hapos hb hT]
  have hne : a-b ≠ 0 := sub_ne_zero.mpr ha
  field_simp [hne]

end Scalar
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.mixedSquare {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (T s : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  clockTest a (J.evolve hb (T-s)).F (J.evolve hb (T-s)).square.A s x

noncomputable def HeatJet.mixedSquareResponse {n : ℕ} (J : HeatJet n) (a b t : ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  clockTestDerivative a J.square.F J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ t x-
    clockGradient a J.F (J.potentialRate b) J.square.A (fun y => 2*(J.A y*J.testRate b y)) t x

theorem HeatJet.hasDerivAt_mixedSquare {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) {T t : ℝ} (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => J.mixedSquare a hb T s x)
      ((J.evolve hb (T-t)).mixedSquareResponse a b t x) t := by
  let V := J.family hb
  have hF : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.square.J q).F y) ((V.J s).potentialRate b y) s := by
    intro s hs y
    exact J.evolve_time_F hb hs.1 y
  have hA : ∀ s ∈ Ioo (0:ℝ) (T+1), ∀ y,
      HasDerivAt (fun q => (V.square.J q).A y) (2*((V.J s).A y*(V.J s).testRate b y)) s := by
    intro s hs y
    apply ((J.evolve_time_A hb hs.1 y).pow 2).congr_deriv
    simp only [pow_one,Nat.cast_ofNat,Nat.reduceSub]
    change 2*(V.J s).A y*(V.J s).testRate b y = _
    ring
  have hbt : T-t ∈ Ioo (0:ℝ) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  have hh := hasDerivAt_dynamic_clockTest V.square.J
    (D := fun s => (V.J s).potentialRate b)
    (B := fun s y => 2*((V.J s).A y*(V.J s).testRate b y)) a
    V.square.lipschitz V.square.continuousF V.square.continuousA
    (V.continuousPotentialRate b) ((V.continuousA.mul (V.continuousTestRate b)).const_mul 2)
    V.square.boundedA (V.boundedPotentialRate b) ((V.boundedA.mul (V.boundedTestRate b)).const_mul 2)
    (V.square.continuousP a) (V.square.continuousW a) (V.square.boundedP a) (V.square.boundedW a)
    hF hA x (hasDerivAt_id t) ((hasDerivAt_const t T).sub (hasDerivAt_id t)) ht.1 hbt
  apply hh.congr_deriv
  dsimp only [HeatJet.mixedSquareResponse]
  simp only [Pi.sub_apply,id_eq,zero_sub,mul_one,mul_neg_one]
  exact (sub_eq_add_neg _ _).symm

theorem HeatJet.square_testRate {n : ℕ} (J : HeatJet n) (b : ℝ) :
    J.square.testRate b = fun y => 2*(J.A y*J.testRate b y)+J.energy y := by
  funext y
  unfold HeatJet.square HeatJet.testRate HeatJet.energy
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem HeatJet.mixedSquareResponse_eq {n : ℕ} (J : HeatJet n) (a b t : ℝ)
    (x : Fin (n+1) → ℝ) :
    J.mixedSquareResponse a b t x =
      (clockTestDerivative a J.square.F J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ t x-
        clockGradient a J.F (J.potentialRate b) J.square.A (J.square.testRate b) t x)+
      clockTest a J.F J.energy t x := by
  unfold HeatJet.mixedSquareResponse clockGradient
  rw [J.square_testRate,clockTest_add_test J.lipschitz
    ((J.smoothA.mul (J.smoothTestRate b)).const_mul 2) J.smoothEnergy]
  ring

 
theorem HeatJet.mixedSquareResponse_bound (J : HeatJet 0) {H a b : ℝ}
    (hH : 0 ≤ H) (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1)
    (hA : ∀ y, |J.A y| ≤ 1) (hG : ∀ i y, |J.G i y| ≤ 1)
    (hD : ∀ i y, |J.A₁ i y| ≤ H) (t : ℝ) (x : Fin 1 → ℝ) :
    |J.mixedSquareResponse a b t x| ≤ H^2+2*H+1 := by
  have hSq (y) : |J.square.A y| ≤ 1 := by
    change |(J.A y)^2| ≤ 1
    rw [abs_pow]
    nlinarith [hA y,abs_nonneg (J.A y)]
  have hSqD (i) (y) : |J.square.A₁ i y| ≤ 2*H := by
    change |2*(J.A y*J.A₁ i y)| ≤ _
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul (hA y) (hD i y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
  have ht := J.square.mass_transfer_abs_le (fun _ => 1) (fun _ => 2*H)
    (by norm_num : (0:ℝ) ≤ 1) (fun _ => by norm_num) hSq hG hSqD a b t x
  have hE (y) : |J.energy y| ≤ H^2 := by
    unfold HeatJet.energy
    rw [Fin.sum_univ_one,abs_pow]
    exact (sq_le_sq₀ (abs_nonneg _) hH).2 (hD 0 y)
  have he := clockTest_abs_le J.lipschitz J.smoothEnergy hE a t x
  have hab : |a-b| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩
  norm_num only [one_mul,one_pow,mul_one,abs_of_nonneg ha.1,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,Nat.reduceAdd,nsmul_eq_mul,Nat.cast_one] at ht
  change |clockTestDerivative a J.square.F J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ t x-
    clockGradient a J.F (J.potentialRate b) J.square.A (J.square.testRate b) t x| ≤ _ at ht
  rw [J.mixedSquareResponse_eq]
  apply (abs_add_le _ _).trans
  have hx : |a-b| *(2*H+a) ≤ 2*H+1 := by
    calc
      _ ≤ 1*(2*H+a) := mul_le_mul_of_nonneg_right hab (by linarith [ha.1])
      _ ≤ 2*H+1 := by linarith [ha.2]
  linarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.GradientTest (J : HeatJet 0) : Prop := J.A = J.G 0 ∧ ∀ i, J.A₁ i = J.H i

theorem HeatJet.GradientTest.evolve {J : HeatJet 0} (hJ : J.GradientTest)
    {b : ℝ} (hb : 0 < b) (t : ℝ) : (J.evolve hb t).GradientTest := by
  constructor
  · change clockTest b J.F J.A t = clockTest b J.F (J.G 0) t
    rw [hJ.1]
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change clockGradient b J.F (J.G 0) J.A (J.A₁ 0) t = _
    rw [hJ.1,hJ.2]
    rfl

theorem HeatJet.GradientTest.schedule {J : HeatJet 0} (hJ : J.GradientTest)
    (cs : List HeatClock) : (J.schedule cs).GradientTest := by
  induction cs with
  | nil => exact hJ
  | cons c cs ih => exact ih.evolve c.positive c.time

theorem scalarProfileHeatJet_gradientTest (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) :
    (scalarProfileHeatJet α hα l t).GradientTest := ⟨rfl,fun _ => rfl⟩

theorem HeatJet.continuous_mixedSquare {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (T : ℝ) (x : Fin (n+1) → ℝ) :
    Continuous (fun s => J.mixedSquare a hb T s x) := by
  let V := (J.family hb).square
  obtain ⟨K,_,hK⟩ := V.boundedA
  exact (dynamic_clockTest_continuous V.lipschitz V.continuousF V.continuousA
    (fun t y => hK (t,y)) a x).comp
    (continuous_id.prodMk (continuous_const.sub continuous_id))

theorem HeatJet.mixedSquareResponse_le_four {J : HeatJet 0}
    (hJ : J.ScalarAdmissible) (hA : J.GradientTest) {a b : ℝ}
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (t : ℝ) (x : Fin 1 → ℝ) :
    |J.mixedSquareResponse a b t x| ≤ 4 := by
  have hg (i : Fin 1) (y : Fin 1 → ℝ) : |J.G i y| ≤ 1 := by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hJ.gradient y
  have hd (i : Fin 1) (y : Fin 1 → ℝ) : |J.A₁ i y| ≤ 1 := by
    rw [hA.2 i]
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [abs_of_nonneg (hJ y).1]
    exact hJ.curvature y
  have hh := J.mixedSquareResponse_bound (by norm_num : (0:ℝ) ≤ 1) ha hb
    (fun y => by rw [hA.1]; exact hg 0 y) hg hd t x
  norm_num only [one_pow, mul_one] at hh
  linarith

theorem HeatJet.mixedSquare_lipschitz {J : HeatJet 0}
    (hJ : J.ScalarAdmissible) (hA : J.GradientTest) {a b T r s : ℝ}
    (ha : a ∈ Icc (0:ℝ) 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hr : r ∈ Icc (0:ℝ) T) (hs : s ∈ Icc (0:ℝ) T) (x : Fin 1 → ℝ) :
    |J.mixedSquare a hb T s x-J.mixedSquare a hb T r x| ≤ 4*|s-r| := by
  have hcase {r s : ℝ} (hr : 0 ≤ r) (hs : s ≤ T) (hrs : r < s) :
      |J.mixedSquare a hb T s x-J.mixedSquare a hb T r x| ≤ 4*(s-r) := by
    obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope
      (fun s => J.mixedSquare a hb T s x)
      (fun s => (J.evolve hb (T-s)).mixedSquareResponse a b s x) hrs
      (J.continuous_mixedSquare a hb T x).continuousOn
      (fun u hu => J.hasDerivAt_mixedSquare a hb ⟨hr.trans_lt hu.1,hu.2.trans_le hs⟩ x)
    have huB := HeatJet.mixedSquareResponse_le_four (hJ.evolve hb hb1 (T-u))
      (hA.evolve hb (T-u)) ha ⟨hb.le,hb1⟩ u x
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hrs)] at huB
    exact (div_le_iff₀ (sub_pos.mpr hrs)).mp huB
  rcases lt_trichotomy r s with h | h | h
  · rw [abs_of_pos (sub_pos.mpr h)]
    exact hcase hr.1 hs.2 h
  · subst s
    simp only [sub_self,abs_zero,mul_zero,le_refl]
  · rw [abs_sub_comm (J.mixedSquare a hb T s x),abs_sub_comm s,
      abs_of_pos (sub_pos.mpr h)]
    exact hcase hs.1 hr.2 h

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.observedSquare {n : ℕ} (J : HeatJet n) (a t : ℝ)
    (x : Fin (n+1) → ℝ) : ℝ := clockTest a J.F J.square.A t x

theorem HeatJet.GradientTest.potentialEnergy {J : HeatJet 0} (hJ : J.GradientTest) :
    J.potentialEnergy = J.square.A := by
  funext y
  change (∑ i : Fin 1, (J.G i y)^2) = (J.A y)^2
  rw [Fin.sum_univ_one,hJ.1]

theorem HeatJet.mixedSquare_terminal {n : ℕ} (J : HeatJet n) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (T : ℝ) (x : Fin (n+1) → ℝ) :
    J.mixedSquare a hb T T x = J.observedSquare a T x := by
  unfold HeatJet.mixedSquare HeatJet.observedSquare
  simp only [HeatJet.square,HeatJet.evolve,sub_self,clockTest_zero]
  rw [show clockContinuation b J.F 0 = J.F from funext (clockContinuation_zero hb.ne')]

theorem HeatJet.flatten_one_energy {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) {a b A d : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hA0 : 0 ≤ A) (hd : 0 ≤ d) (x : Fin 1 → ℝ) :
    |(J.evolve hb d).observedSquare a A x-J.observedSquare a (A+d) x| ≤ 4*d := by
  have hh := HeatJet.mixedSquare_lipschitz hJ hA ha hb hb1
    (r:=A+d) (s:=A) (T:=A+d) ⟨by positivity,le_rfl⟩ ⟨hA0,by linarith⟩ x
  rw [J.mixedSquare_terminal] at hh
  unfold HeatJet.mixedSquare at hh
  rw [show A+d-A=d by ring,show A-(A+d)= -d by ring,abs_neg,abs_of_nonneg hd] at hh
  exact hh

theorem HeatJet.flatten_one_identity {J : HeatJet 0} (hA : J.GradientTest)
    {a b A d : ℝ} (ha : 0 < a) (hb : 0 < b) (hA0 : 0 ≤ A) (hd : 0 ≤ d)
    (x : Fin 1 → ℝ) :
    clockContinuation a (J.evolve hb d).F A x-clockContinuation a J.F (A+d) x =
      (b-a)/2*(∫ s in A..A+d, J.mixedSquare a hb (A+d) s x) := by
  have he (s : ℝ) : J.potentialSplitResponse a hb (A+d) s x =
      (a-b)/2*J.mixedSquare a hb (A+d) s x := by
    dsimp only [HeatJet.potentialSplitResponse,HeatJet.mixedSquare]
    rw [(hA.evolve hb (A+d-s)).potentialEnergy]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show A ≤ A+d by linarith)
    (J.continuous_potentialSplit a hb (A+d) x).continuousOn
    (fun s hs => J.hasDerivAt_potentialSplit ha hb ⟨hA0.trans_lt hs.1,hs.2⟩ x)
    (by simpa only [he] using
      (((J.continuous_mixedSquare a hb (A+d) x).const_mul ((a-b)/2)).intervalIntegrable A (A+d)))
  simp_rw [he] at hh
  rw [intervalIntegral.integral_const_mul,J.potentialSplit_terminal] at hh
  unfold HeatJet.potentialSplit at hh
  rw [show A+d-A=d by ring] at hh
  linarith

 

theorem HeatJet.flatten_one_error {J : HeatJet 0} (hJ : J.ScalarAdmissible)
    (hA : J.GradientTest) {a b A d : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hab : a ≤ b) (hA0 : 0 ≤ A) (hd : 0 ≤ d)
    (x : Fin 1 → ℝ) :
    |clockContinuation a (J.evolve hb d).F A x-clockContinuation a J.F (A+d) x-
      ((b-a)*d/2)*J.observedSquare a (A+d) x| ≤ 2*(b-a)*d^2 := by
  have hbE (s : ℝ) (hs : s ∈ uIoc A (A+d)) :
      |J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x| ≤ 4*d := by
    rw [uIoc_of_le (by linarith : A ≤ A+d)] at hs
    have hh := HeatJet.mixedSquare_lipschitz hJ hA ⟨ha.le,ha1⟩ hb hb1
      (r:=A+d) (s:=s) (T:=A+d) ⟨by positivity,le_rfl⟩ ⟨hA0.trans hs.1.le,hs.2⟩ x
    rw [J.mixedSquare_terminal,abs_of_nonpos (sub_nonpos.mpr hs.2)] at hh
    linarith [hs.1]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=A) (b:=A+d) (f:=fun s => J.mixedSquare a hb (A+d) s x-J.observedSquare a (A+d) x)
    (C:=4*d) (fun s hs => by simpa only [Real.norm_eq_abs] using hbE s hs)
  rw [intervalIntegral.integral_sub ((J.continuous_mixedSquare a hb (A+d) x).intervalIntegrable A (A+d)) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [add_sub_cancel_left,smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg hd] at hi
  rw [HeatJet.flatten_one_identity hA ha hb hA0 hd]
  have he : (b-a)/2*(∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-
      (b-a)*d/2*J.observedSquare a (A+d) x =
      ((b-a)/2)*((∫ s in A..A+d, J.mixedSquare a hb (A+d) s x)-d*J.observedSquare a (A+d) x) := by ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hab) (by norm_num) : 0 ≤ (b-a)/2)]
  calc
    _ ≤ ((b-a)/2)*(4*d*d) := mul_le_mul_of_nonneg_left hi (div_nonneg (sub_nonneg.mpr hab) (by norm_num))
    _ = _ := by ring

end SKFluctuations.Hierarchy

end

end OAI
