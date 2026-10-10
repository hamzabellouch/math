import Mathlib
import OAI.Probability.SKFluctuations.ResidualGradientBound

namespace OAI

/-! Scalar Gap Fourth. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

noncomputable def HeatJet.thirdTest0 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  ((((J.scalarClockJet m 4 t y))^2)-((12*m)*(((J.scalarClockJet m 2 t y))*(((J.scalarClockJet m 3 t y))^2))))+((6*m^2)*(((J.scalarClockJet m 2 t y))^4))

noncomputable def HeatJet.thirdTest1 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  (((2)*((((J.scalarClockJet m 4 t y))^1)*((J.scalarClockJet m 5 t y))))-((12*m)*((((J.scalarClockJet m 3 t y))*(((J.scalarClockJet m 3 t y))^2))+(((J.scalarClockJet m 2 t y))*((2)*((((J.scalarClockJet m 3 t y))^1)*((J.scalarClockJet m 4 t y))))))))+((6*m^2)*((4)*((((J.scalarClockJet m 2 t y))^3)*((J.scalarClockJet m 3 t y)))))

noncomputable def HeatJet.thirdTest2 (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  (((2)*((((1)*((((J.scalarClockJet m 4 t y))^0)*((J.scalarClockJet m 5 t y))))*((J.scalarClockJet m 5 t y)))+((((J.scalarClockJet m 4 t y))^1)*((J.scalarClockJet m 6 t y)))))-((12*m)*(((((J.scalarClockJet m 4 t y))*(((J.scalarClockJet m 3 t y))^2))+(((J.scalarClockJet m 3 t y))*((2)*((((J.scalarClockJet m 3 t y))^1)*((J.scalarClockJet m 4 t y))))))+((((J.scalarClockJet m 3 t y))*((2)*((((J.scalarClockJet m 3 t y))^1)*((J.scalarClockJet m 4 t y)))))+(((J.scalarClockJet m 2 t y))*((2)*((((1)*((((J.scalarClockJet m 3 t y))^0)*((J.scalarClockJet m 4 t y))))*((J.scalarClockJet m 4 t y)))+((((J.scalarClockJet m 3 t y))^1)*((J.scalarClockJet m 5 t y))))))))))+((6*m^2)*((4)*((((3)*((((J.scalarClockJet m 2 t y))^2)*((J.scalarClockJet m 3 t y))))*((J.scalarClockJet m 3 t y)))+((((J.scalarClockJet m 2 t y))^3)*((J.scalarClockJet m 4 t y))))))

noncomputable def HeatJet.thirdTimeTest (J : HeatJet 0) (m t : ℝ) (y : Fin 1 → ℝ) : ℝ :=
  (((2)*((((J.scalarClockJet m 4 t y))^1)*((((2:ℝ)⁻¹)*((J.scalarClockJet m 6 t y)))+((m)*((((3)*(((J.scalarClockJet m 3 t y))^2))+((4)*(((J.scalarClockJet m 2 t y))*((J.scalarClockJet m 4 t y)))))+(((J.scalarClockJet m 1 t y))*((J.scalarClockJet m 5 t y))))))))-((12*m)*((((((2:ℝ)⁻¹)*((J.scalarClockJet m 4 t y)))+((m)*((((J.scalarClockJet m 2 t y))^2)+(((J.scalarClockJet m 1 t y))*((J.scalarClockJet m 3 t y))))))*(((J.scalarClockJet m 3 t y))^2))+(((J.scalarClockJet m 2 t y))*((2)*((((J.scalarClockJet m 3 t y))^1)*((((2:ℝ)⁻¹)*((J.scalarClockJet m 5 t y)))+((m)*(((3)*(((J.scalarClockJet m 2 t y))*((J.scalarClockJet m 3 t y))))+(((J.scalarClockJet m 1 t y))*((J.scalarClockJet m 4 t y))))))))))))+((6*m^2)*((4)*((((J.scalarClockJet m 2 t y))^3)*((((2:ℝ)⁻¹)*((J.scalarClockJet m 4 t y)))+((m)*((((J.scalarClockJet m 2 t y))^2)+(((J.scalarClockJet m 1 t y))*((J.scalarClockJet m 3 t y)))))))))

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

private theorem ScalarGapFourth_thirdTest0_smooth (k : ℕ) (t : ℝ) : BddSmooth k (J.thirdTest0 m t) := by
  have h (i : ℕ) := J.scalarClockPlane_positiveJets_bddSmooth hG hm k (i-1) t
  convert (((((h 4)).pow 2).sub ((((h 2)).mul (((h 3)).pow 2)).const_mul (12*m))).add ((((h 2)).pow 4).const_mul (6*m^2))) using 1
  funext y
  dsimp only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.scalarClockJet]

private theorem ScalarGapFourth_thirdTest1_smooth (k : ℕ) (t : ℝ) : BddSmooth k (J.thirdTest1 m t) := by
  have h (i : ℕ) := J.scalarClockPlane_positiveJets_bddSmooth hG hm k (i-1) t
  convert (((((((h 4)).pow 1).mul ((h 5))).const_mul (2)).sub (((((h 3)).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((h 3))).const_mul (4)).const_mul (6*m^2))) using 1
  funext y
  dsimp only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.scalarClockJet]

private theorem ScalarGapFourth_thirdTest2_smooth (k : ℕ) (t : ℝ) : BddSmooth k (J.thirdTest2 m t) := by
  have h (i : ℕ) := J.scalarClockPlane_positiveJets_bddSmooth hG hm k (i-1) t
  convert ((((((((((h 4)).pow 0).mul ((h 5))).const_mul (1)).mul ((h 5))).add ((((h 4)).pow 1).mul ((h 6)))).const_mul (2)).sub ((((((h 4)).mul (((h 3)).pow 2)).add (((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).add ((((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2))).add (((h 2)).mul ((((((((h 3)).pow 0).mul ((h 4))).const_mul (1)).mul ((h 4))).add ((((h 3)).pow 1).mul ((h 5)))).const_mul (2))))).const_mul (12*m))).add (((((((((h 2)).pow 2).mul ((h 3))).const_mul (3)).mul ((h 3))).add ((((h 2)).pow 3).mul ((h 4)))).const_mul (4)).const_mul (6*m^2))) using 1
  funext y
  dsimp only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.scalarClockJet]

private theorem ScalarGapFourth_thirdTimeTest_smooth (k : ℕ) (t : ℝ) : BddSmooth k (J.thirdTimeTest m t) := by
  have h (i : ℕ) := J.scalarClockPlane_positiveJets_bddSmooth hG hm k (i-1) t
  convert (((((((h 4)).pow 1).mul ((((h 6)).const_mul ((2:ℝ)⁻¹)).add (((((((h 3)).pow 2).const_mul (3)).add ((((h 2)).mul ((h 4))).const_mul (4))).add (((h 1)).mul ((h 5)))).const_mul (m)))).const_mul (2)).sub (((((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m))).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((((h 5)).const_mul ((2:ℝ)⁻¹)).add ((((((h 2)).mul ((h 3))).const_mul (3)).add (((h 1)).mul ((h 4)))).const_mul (m)))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m)))).const_mul (4)).const_mul (6*m^2))) using 1
  funext y
  dsimp only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.scalarClockJet]

noncomputable def HeatJet.thirdJet (t : ℝ) : HeatJet 0 :=
  { J.evolve hm t with
    A := J.thirdTest0 m t
    A₁ := fun _ => J.thirdTest1 m t
    A₂ := fun _ => J.thirdTest2 m t
    smoothA := ScalarGapFourth_thirdTest0_smooth J hG hm 0 t
    smoothA₁ := fun _ => ScalarGapFourth_thirdTest1_smooth J hG hm 0 t
    smoothA₂ := fun _ => ScalarGapFourth_thirdTest2_smooth J hG hm 0 t
    derivA := by
      intro x v s
      have h (k) := J.scalarClockJet_line hG hm k t x v s
      apply (((((h 4)).pow 2).sub ((((h 2)).mul (((h 3)).pow 2)).const_mul (12*m))).add ((((h 2)).pow 4).const_mul (6*m^2))).congr_deriv
      simp only [Pi.pow_apply,HeatJet.thirdTest1,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,Nat.reduceAdd]
      ring
    derivA₁ := by
      intro i x s
      have h (k) := J.scalarClockJet_coord hG hm k t i x s
      apply (((((((h 4)).pow 1).mul ((h 5))).const_mul (2)).sub (((((h 3)).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((h 3))).const_mul (4)).const_mul (6*m^2))).congr_deriv
      simp only [Pi.pow_apply,Pi.mul_apply,HeatJet.thirdTest2,Nat.cast_ofNat,Nat.reduceSub,pow_one,pow_zero,Nat.reduceAdd]
      ring }

noncomputable def HeatJet.thirdFamily : HeatJetFamily 0 :=
  { J.family hm with
    J := J.thirdJet hG hm
    continuousA := by
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact ((((h 4)).pow 2).sub ((((h 2)).mul (((h 3)).pow 2)).const_mul (12*m))).add ((((h 2)).pow 4).const_mul (6*m^2))
    continuousA₁ := by
      intro i
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact ((((((h 4)).pow 1).mul ((h 5))).const_mul (2)).sub (((((h 3)).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((h 3))).const_mul (4)).const_mul (6*m^2))
    continuousA₂ := by
      intro i
      have h (k) := J.scalarClockJet_continuous hG hm k
      exact (((((((((h 4)).pow 0).mul ((h 5))).const_mul (1)).mul ((h 5))).add ((((h 4)).pow 1).mul ((h 6)))).const_mul (2)).sub ((((((h 4)).mul (((h 3)).pow 2)).add (((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).add ((((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2))).add (((h 2)).mul ((((((((h 3)).pow 0).mul ((h 4))).const_mul (1)).mul ((h 4))).add ((((h 3)).pow 1).mul ((h 5)))).const_mul (2))))).const_mul (12*m))).add (((((((((h 2)).pow 2).mul ((h 3))).const_mul (3)).mul ((h 3))).add ((((h 2)).pow 3).mul ((h 4)))).const_mul (4)).const_mul (6*m^2))
    boundedA := by
      have h (i : ℕ) := J.scalarClockJet_bound hG hm (i-1)
      simpa only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.thirdJet,HeatJet.scalarClockJet,Nat.reduceSub,Nat.reduceAdd] using ((((h 4)).pow 2).sub ((((h 2)).mul (((h 3)).pow 2)).const_mul (12*m))).add ((((h 2)).pow 4).const_mul (6*m^2))
    boundedA₁ := by
      intro i
      have h (i : ℕ) := J.scalarClockJet_bound hG hm (i-1)
      simpa only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.thirdJet,HeatJet.scalarClockJet,Nat.reduceSub,Nat.reduceAdd] using ((((((h 4)).pow 1).mul ((h 5))).const_mul (2)).sub (((((h 3)).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((h 3))).const_mul (4)).const_mul (6*m^2))
    boundedA₂ := by
      intro i
      have h (i : ℕ) := J.scalarClockJet_bound hG hm (i-1)
      simpa only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.thirdJet,HeatJet.scalarClockJet,Nat.reduceSub,Nat.reduceAdd] using (((((((((h 4)).pow 0).mul ((h 5))).const_mul (1)).mul ((h 5))).add ((((h 4)).pow 1).mul ((h 6)))).const_mul (2)).sub ((((((h 4)).mul (((h 3)).pow 2)).add (((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2)))).add ((((h 3)).mul (((((h 3)).pow 1).mul ((h 4))).const_mul (2))).add (((h 2)).mul ((((((((h 3)).pow 0).mul ((h 4))).const_mul (1)).mul ((h 4))).add ((((h 3)).pow 1).mul ((h 5)))).const_mul (2))))).const_mul (12*m))).add (((((((((h 2)).pow 2).mul ((h 3))).const_mul (3)).mul ((h 3))).add ((((h 2)).pow 3).mul ((h 4)))).const_mul (4)).const_mul (6*m^2)) }

private theorem ScalarGapFourth_thirdTimeTest_continuous : Continuous (fun p : ℝ × (Fin 1 → ℝ) => J.thirdTimeTest m p.1 p.2) := by
  have h (k) := J.scalarClockJet_continuous hG hm k
  exact ((((((h 4)).pow 1).mul ((((h 6)).const_mul ((2:ℝ)⁻¹)).add (((((((h 3)).pow 2).const_mul (3)).add ((((h 2)).mul ((h 4))).const_mul (4))).add (((h 1)).mul ((h 5)))).const_mul (m)))).const_mul (2)).sub (((((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m))).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((((h 5)).const_mul ((2:ℝ)⁻¹)).add ((((((h 2)).mul ((h 3))).const_mul (3)).add (((h 1)).mul ((h 4)))).const_mul (m)))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m)))).const_mul (4)).const_mul (6*m^2))

private theorem ScalarGapFourth_thirdTimeTest_bounded : AbsBounded (fun p : ℝ × (Fin 1 → ℝ) => J.thirdTimeTest m p.1 p.2) := by
  have h (i : ℕ) := J.scalarClockJet_bound hG hm (i-1)
  simpa only [HeatJet.thirdTest0,HeatJet.thirdTest1,HeatJet.thirdTest2,HeatJet.thirdTimeTest,HeatJet.thirdJet,HeatJet.scalarClockJet,Nat.reduceSub,Nat.reduceAdd] using ((((((h 4)).pow 1).mul ((((h 6)).const_mul ((2:ℝ)⁻¹)).add (((((((h 3)).pow 2).const_mul (3)).add ((((h 2)).mul ((h 4))).const_mul (4))).add (((h 1)).mul ((h 5)))).const_mul (m)))).const_mul (2)).sub (((((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m))).mul (((h 3)).pow 2)).add (((h 2)).mul (((((h 3)).pow 1).mul ((((h 5)).const_mul ((2:ℝ)⁻¹)).add ((((((h 2)).mul ((h 3))).const_mul (3)).add (((h 1)).mul ((h 4)))).const_mul (m)))).const_mul (2)))).const_mul (12*m))).add ((((((h 2)).pow 3).mul ((((h 4)).const_mul ((2:ℝ)⁻¹)).add (((((h 2)).pow 2).add (((h 1)).mul ((h 3)))).const_mul (m)))).const_mul (4)).const_mul (6*m^2))

noncomputable def HeatJet.scalarGapFourth (T s : ℝ) (x : Fin 1 → ℝ) : ℝ :=
  clockTest m (clockContinuation m J.F (T-s))
    (fun y => (J.thirdJet hG hm (T-s)).testRate m y-J.thirdTimeTest m (T-s) y) s x

theorem HeatJet.hasDerivAt_scalarGapThird (hH : ∀ k i, BddSmooth k (J.H i))
    {T s : ℝ} (hs : s ∈ Ioo 0 T) (x : Fin 1 → ℝ) :
    HasDerivAt (fun r => J.scalarGapThird m T r x) (J.scalarGapFourth hG hm T s x) s := by
  let V := J.thirdFamily hG hm
  have hdF : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).F y) ((V.J r).potentialRate m y) r := by
    intro r hr y
    exact J.evolve_time_F hm hr.1 y
  have hdA : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun q => (V.J q).A y) (J.thirdTimeTest m r y) r := by
    intro r hr y
    have hc := J.scalarClockPlane_contDiffOn hG hH hm
    have h2 := realJet_two_time hc
      (fun _ z hz => J.scalarClockPlane_timePDE hG hH hm hz z) (x := y 0) hr.1
    have h3 := realJet_three_time hc
      (fun _ z hz => J.scalarClockPlane_timePDE hG hH hm hz z) (x := y 0) hr.1
    have h4 := realJet_four_time hc
      (fun _ z hz => J.scalarClockPlane_timePDE hG hH hm hz z) (x := y 0) hr.1
    apply ((((h4.pow 2).sub ((h2.mul (h3.pow 2)).const_mul (12*m))).add ((h2.pow 4).const_mul (6*m^2)))).congr_deriv
    dsimp only [HeatJet.thirdTimeTest,HeatJet.scalarClockJet]
    simp only [Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one]
    ring
  exact V.hasDerivAt_backwardTest (ScalarGapFourth_thirdTimeTest_continuous J hG hm)
    (ScalarGapFourth_thirdTimeTest_bounded J hG hm) (ScalarGapFourth_thirdTimeTest_smooth J hG hm 0) hdF hdA hs x

theorem HeatJet.scalarGapFourth_bound (T : ℝ) :
    AbsBounded (fun p : ℝ × ℝ => J.scalarGapFourth hG hm T p.1 (fun _ => p.2)) := by
  obtain ⟨K,hK,hb⟩ := (J.thirdFamily hG hm).boundedTestRate m |>.sub (ScalarGapFourth_thirdTimeTest_bounded J hG hm)
  exact ⟨K,hK,fun p => clockTest_abs_le (J.evolve hm (T-p.1)).lipschitz
    (((J.thirdJet hG hm (T-p.1)).smoothTestRate m).sub (ScalarGapFourth_thirdTimeTest_smooth J hG hm 0 (T-p.1)))
      (fun y => hb (T-p.1,y)) m p.1 (fun _ => p.2)⟩

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m)
include hG hm

theorem HeatJet.scalarGapThird_bddSmooth (k : ℕ) (T s : ℝ) :
    BddSmooth k (J.scalarGapThird m T s) := by
  apply clockTest_bddSmooth (clockContinuation_regular (J.regular_of_smoothG (hG k)) hm (T-s))
  have h (i) := J.scalarClockPlane_positiveJets_bddSmooth hG hm k i (T-s)
  exact (((h 3).pow 2).sub (((h 1).mul ((h 2).pow 2)).const_mul (12*m))).add
    (((h 1).pow 4).const_mul (6*m^2))

noncomputable def HeatJet.profileGapThirdJet (T s : ℝ) : HeatJet 0 :=
  (J.evolve hm T).withTest (J.scalarGapThird m T s) (J.scalarGapThird_bddSmooth hG hm 2 T s)

theorem HeatJet.profileGapThirdJet_F (T s : ℝ) :
    (J.profileGapThirdJet hG hm T s).F=(J.evolve hm T).F := rfl

theorem HeatJet.profileGapThirdJet_A (T s : ℝ) :
    (J.profileGapThirdJet hG hm T s).A=J.scalarGapThird m T s := rfl

theorem HeatJet.profileGapCurvature_hasDerivAt
    (hH : ∀ k i, BddSmooth k (J.H i)) {T s : ℝ} (hs : s ∈ Ioo 0 T)
    (α : NonnegativeMassProfile) (hα : ∀ u, α.mass u ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin 1 → ℝ) :
    HasDerivAt (fun u => (J.profileGapCurvatureJet hG hm T u).nonnegativeProfileTest α l t x)
      ((J.profileGapThirdJet hG hm T s).nonnegativeProfileTest α l t x) s := by
  obtain ⟨M,_hM,hb⟩ := J.scalarGapFourth_bound hG hm T
  apply HeatJet.nonnegativeProfileTest_hasDerivAt
    (J.profileGapCurvatureJet hG hm T) (J.profileGapThirdJet hG hm T)
    (M:=M) hs (fun u => (J.profileGapCurvatureJet_F hG hm T u).trans
      (J.profileGapCurvatureJet_F hG hm T s).symm)
      ((J.profileGapThirdJet_F hG hm T s).trans (J.profileGapCurvatureJet_F hG hm T s).symm)
      (J.scalarGapFourth hG hm T)
  · intro u hu y
    simp only [HeatJet.profileGapCurvatureJet_A,HeatJet.profileGapThirdJet_A]
    exact J.hasDerivAt_scalarGapCurvature hG hm hH hu y
  · intro u hu y
    simp only [HeatJet.profileGapThirdJet_A]
    exact J.hasDerivAt_scalarGapThird hG hm hH hu y
  · intro u _ y
    have hy : (fun _ : Fin 1 => y 0)=y := by ext i; rw [Fin.eq_zero i]
    simpa only [hy] using hb (u,y 0)
  · exact hα

end
end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarTailJet_H_smooth {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    ∀ k i, BddSmooth k ((scalarTailJet hT α q).H i) := by
  intro k i
  exact scalarProfileJet_bddSmooth_all (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (T*q) (Real.toNNReal (T*(1-q))) k 1

 theorem scalarPlantedEnergy_hasDerivAt_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hq : q ∈ Ioo p r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    HasDerivAt (scalarPlantedEnergy hT α)
      (((scalarTailJet hT α r).profileGapEnergyJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0*T) q := by
  have hs : T*(q-p) ∈ Ioo (0:ℝ) (T*(r-p)) :=
    ⟨mul_pos hT (sub_pos.mpr hq.1),mul_lt_mul_of_pos_left (by linarith [hq.2]) hT⟩
  have hh := (scalarTailJet hT α r).profileGapSquare_hasDerivAt
    (scalarTailJet_G_smooth hT α r) hm (scalarTailJet_H_smooth hT α r)
    (scalarTailJet_gradientTest hT α r).1 ((scalarTailJet_gradientTest hT α r).2 0)
    hs (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2)
    0 (Real.toNNReal (T*p)) 0
  have hd : HasDerivAt (fun u : ℝ => T*(u-p)) T q := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id q).sub_const p).const_mul T
  apply (hh.comp q hd).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with u hu
  exact scalarPlantedEnergy_plateau hT hp hu.1 hu.2 hr α hm hm1 hf

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem parametric_clockTest_continuous_joint {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [FirstCountableTopology X]
    {F A : X → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : X × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : X × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) :
    Continuous (fun p : ℝ × (X × (ι → ℝ)) => clockTest m (F p.2.1) (A p.2.1) p.1 p.2.2) := by
  have hh := parametric_clockTest_continuous
    (F:=fun p : X × (ι → ℝ) => fun y => F p.1 (p.2+y))
    (A:=fun p : X × (ι → ℝ) => fun y => A p.1 (p.2+y))
    (fun p => by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      simpa only [dist_add_left] using (hF p.1).dist_le_mul (p.2+y) (p.2+z))
    (hcF.comp (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd)))
    (hcA.comp (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd)))
    (fun p y => hb p.1 (p.2+y)) m (0:ι → ℝ)
  apply hh.congr
  intro p
  simp only [clockTest,shiftedMean,tiltedMean,zero_add]

 theorem dynamic_clockTest_spatial_continuous {n : ℕ} {F A : ℝ → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (hc : Continuous c) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => clockTest m (F p.1) (A p.1) (c p.1) p.2) := by
  obtain ⟨K,_,hK⟩ := hb
  exact (parametric_clockTest_continuous_joint hF hcF hcA (fun r y => hK (r,y)) m).comp
    ((hc.comp continuous_fst).prodMk continuous_id)

 theorem dynamic_clockGradient_spatial_continuous {n : ℕ}
    {F G A A₁ : ℝ → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hbG : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (hc : Continuous c) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => clockGradient m (F p.1) (G p.1) (A p.1) (A₁ p.1) (c p.1) p.2) :=
  (dynamic_clockTest_spatial_continuous hF hcF hcA₁ hbA₁ m hc).add
    (((dynamic_clockTest_spatial_continuous (A:=fun r y => A r y*G r y) hF hcF (hcA.mul hcG) (hbA.mul hbG) m hc).sub
      ((dynamic_clockTest_spatial_continuous hF hcF hcA hbA m hc).mul
        (dynamic_clockTest_spatial_continuous hF hcF hcG hbG m hc))).const_mul m)

 theorem dynamic_clockSecond_spatial_continuous {n : ℕ}
    {F G H A A₁ A₂ : ℝ → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hcH : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hcA₂ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₂ p.1 p.2))
    (hbG : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hbH : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hbA₂ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₂ p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (hc : Continuous c) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => clockSecond m (F p.1) (G p.1) (H p.1) (A p.1) (A₁ p.1) (A₂ p.1) (c p.1) p.2) :=
  (dynamic_clockGradient_spatial_continuous hF hcF hcG hcA₁ hcA₂ hbG hbA₁ hbA₂ m hc).add
    (((dynamic_clockGradient_spatial_continuous (A:=fun r y => A r y*G r y)
      (A₁:=fun r y => A₁ r y*G r y+A r y*H r y) hF hcF hcG (hcA.mul hcG)
      ((hcA₁.mul hcG).add (hcA.mul hcH)) hbG (hbA.mul hbG)
      ((hbA₁.mul hbG).add (hbA.mul hbH)) m hc).sub
      (((dynamic_clockGradient_spatial_continuous hF hcF hcG hcA hcA₁ hbG hbA hbA₁ m hc).mul
        (dynamic_clockTest_spatial_continuous hF hcF hcG hbG m hc)).add
        ((dynamic_clockTest_spatial_continuous hF hcF hcA hbA m hc).mul
        (dynamic_clockGradient_spatial_continuous hF hcF hcG hcG hcH hbG hbG hbH m hc)))).const_mul m)

 theorem HeatJetFamily.evolve_A_continuous {n : ℕ} (V : HeatJetFamily n)
    {m : ℝ} (hm : 0 < m) {c : ℝ → ℝ} (hc : Continuous c) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => ((V.J p.1).evolve hm (c p.1)).A p.2) :=
  dynamic_clockTest_spatial_continuous (A:=fun r => (V.J r).A) V.lipschitz V.continuousF V.continuousA V.boundedA m hc

 theorem HeatJetFamily.evolve_A₁_continuous {n : ℕ} (V : HeatJetFamily n)
    {m : ℝ} (hm : 0 < m) {c : ℝ → ℝ} (hc : Continuous c) (i : Fin (n+1)) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => ((V.J p.1).evolve hm (c p.1)).A₁ i p.2) :=
  dynamic_clockGradient_spatial_continuous (G:=fun r => (V.J r).G i)
    (A:=fun r => (V.J r).A) (A₁:=fun r => (V.J r).A₁ i) V.lipschitz V.continuousF (V.continuousG i)
    V.continuousA (V.continuousA₁ i) (V.boundedG i) V.boundedA (V.boundedA₁ i) m hc

 theorem HeatJetFamily.evolve_A₂_continuous {n : ℕ} (V : HeatJetFamily n)
    {m : ℝ} (hm : 0 < m) {c : ℝ → ℝ} (hc : Continuous c) (i : Fin (n+1)) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => ((V.J p.1).evolve hm (c p.1)).A₂ i p.2) :=
  dynamic_clockSecond_spatial_continuous (G:=fun r => (V.J r).G i)
    (H:=fun r => (V.J r).H i) (A:=fun r => (V.J r).A)
    (A₁:=fun r => (V.J r).A₁ i) (A₂:=fun r => (V.J r).A₂ i) V.lipschitz V.continuousF (V.continuousG i)
    (V.continuousH i) V.continuousA (V.continuousA₁ i) (V.continuousA₂ i)
    (V.boundedG i) (V.boundedH i) V.boundedA (V.boundedA₁ i) (V.boundedA₂ i) m hc

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem boundedContinuous_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → E → ℝ}
    (hc : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × E => f p.1 p.2)) :
    BddSmooth 0 (fun x => ∫ s, f s x ∂μ) := by
  obtain ⟨K,hK,hbK⟩ := hb
  refine ⟨?_,K*μ.real univ,mul_nonneg hK measureReal_nonneg,?_⟩
  · exact continuous_of_dominated
      (fun x => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbK (s,x))
      (integrable_const K) (Eventually.of_forall fun s => hc.comp (continuous_const.prodMk continuous_id))
  · intro x
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (Eventually.of_forall fun s => show ‖f s x‖ ≤ K from by simpa only [Real.norm_eq_abs] using hbK (s,x))

 theorem hasDerivAt_integral_bounded {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f g : ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × ℝ => g p.1 p.2))
    (hbf : AbsBounded (fun p : ℝ × ℝ => f p.1 p.2))
    (hd : ∀ s x, HasDerivAt (f s) (g s x) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ s, f s y ∂μ) (∫ s, g s x ∂μ) x := by
  obtain ⟨K,_hK,hbK⟩ := hb
  obtain ⟨L,_hL,hbL⟩ := hbf
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (F:=fun y s => f s y) (F':=fun y s => g s y) (x₀:=x) (s:=univ) (bound:=fun _ => K)
    (univ_mem) _ _ _ _ (integrable_const K) _).2
  · exact Eventually.of_forall fun y => (hf.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (integrable_const L).mono'
      (hf.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hbL (s,x))
  · exact (hg.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun s y _ => by simpa only [Real.norm_eq_abs] using hbK (s,y)
  · exact Eventually.of_forall fun s y _ => hd s y

 noncomputable def HeatJetFamily.integralTest {n : ℕ} (V : HeatJetFamily n) (J : HeatJet n)
    (μ : Measure ℝ) [IsFiniteMeasure μ] : HeatJet n where
  F := J.F
  G := J.G
  H := J.H
  C := J.C
  lipschitz := J.lipschitz
  smoothG := J.smoothG
  smoothH := J.smoothH
  derivF := J.derivF
  derivG := J.derivG
  A x := ∫ s, (V.J s).A x ∂μ
  A₁ i x := ∫ s, (V.J s).A₁ i x ∂μ
  A₂ i x := ∫ s, (V.J s).A₂ i x ∂μ
  smoothA := boundedContinuous_integral μ V.continuousA V.boundedA
  smoothA₁ i := boundedContinuous_integral μ (V.continuousA₁ i) (V.boundedA₁ i)
  smoothA₂ i := boundedContinuous_integral μ (V.continuousA₂ i) (V.boundedA₂ i)
  derivA x v t := by
    have hb : AbsBounded (fun p : ℝ × ℝ => ∑ i, v i*(V.J p.1).A₁ i (x+p.2 • v)) := by
      apply AbsBounded.sum
      intro i
      obtain ⟨K,hK,hbK⟩ := V.boundedA₁ i
      refine ⟨|v i| *K,mul_nonneg (abs_nonneg _) hK,fun p => ?_⟩
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbK (p.1,x+p.2 • v)) (abs_nonneg _)
    have hbA : AbsBounded (fun p : ℝ × ℝ => (V.J p.1).A (x+p.2 • v)) := by
      obtain ⟨K,hK,hbK⟩ := V.boundedA
      exact ⟨K,hK,fun p => hbK (p.1,x+p.2 • v)⟩
    have hh := hasDerivAt_integral_bounded (μ:=μ)
      (V.continuousA.comp (continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const))))
      (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((V.continuousA₁ i).comp (continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const)))))
      hb hbA (fun s u => (V.J s).derivA x v u) t
    rw [integral_finsetSum] at hh
    · simpa only [integral_const_mul] using hh
    · intro i _
      obtain ⟨K,_hK,hbK⟩ := V.boundedA₁ i
      exact ((integrable_const K).mono'
        ((V.continuousA₁ i).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hbK (s,x+t • v))).const_mul (v i)
  derivA₁ i x t := by
    have compc : Continuous (fun p : ℝ × ℝ => (p.1,x+p.2 • Pi.single i 1)) :=
      continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const))
    have hb (f : ℝ → (Fin (n+1) → ℝ) → ℝ)
        (h : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => f p.1 p.2)) :
        AbsBounded (fun p : ℝ × ℝ => f p.1 (x+p.2 • Pi.single i 1)) := by
      obtain ⟨K,hK,hbK⟩ := h
      exact ⟨K,hK,fun p => hbK (p.1,x+p.2 • Pi.single i 1)⟩
    exact hasDerivAt_integral_bounded ((V.continuousA₁ i).comp compc)
      ((V.continuousA₂ i).comp compc) (hb (fun s => (V.J s).A₂ i) (V.boundedA₂ i)) (hb (fun s => (V.J s).A₁ i) (V.boundedA₁ i))
      (fun s u => (V.J s).derivA₁ i x u) t

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem AbsBounded.precomp {X Y : Type*} {f : X → ℝ} (hf : AbsBounded f) (g : Y → X) :
    AbsBounded (fun y => f (g y)) := by
  obtain ⟨K,hK,hb⟩ := hf
  exact ⟨K,hK,fun y => hb (g y)⟩

 theorem dynamic_clockTest_spatial_bound {n : ℕ} {F A : ℝ → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : ∀ r, LipschitzWith C (F r))
    (_hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (_hc : Continuous c) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => clockTest m (F p.1) (A p.1) (c p.1) p.2) := by
  obtain ⟨K,hK,hbK⟩ := hb
  exact ⟨K,hK,fun p => clockTest_abs_le (hF p.1)
    ⟨hcA.comp (continuous_const.prodMk continuous_id),K,hK,fun y => hbK (p.1,y)⟩
    (fun y => hbK (p.1,y)) m (c p.1) p.2⟩
 theorem dynamic_clockGradient_spatial_bound {n : ℕ}
    {F G A A₁ : ℝ → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hbG : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (hc : Continuous c) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => clockGradient m (F p.1) (G p.1) (A p.1) (A₁ p.1) (c p.1) p.2) :=
  (dynamic_clockTest_spatial_bound hF hcF hcA₁ hbA₁ m hc).add
    (((dynamic_clockTest_spatial_bound (A:=fun r y => A r y*G r y) hF hcF (hcA.mul hcG) (hbA.mul hbG) m hc).sub
      ((dynamic_clockTest_spatial_bound hF hcF hcA hbA m hc).mul
        (dynamic_clockTest_spatial_bound hF hcF hcG hbG m hc))).const_mul m)

 theorem dynamic_clockSecond_spatial_bound {n : ℕ}
    {F G H A A₁ A₂ : ℝ → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hcH : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hcA₁ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hcA₂ : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A₂ p.1 p.2))
    (hbG : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => G p.1 p.2))
    (hbH : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hbA₁ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₁ p.1 p.2))
    (hbA₂ : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A₂ p.1 p.2))
    (m : ℝ) {c : ℝ → ℝ} (hc : Continuous c) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => clockSecond m (F p.1) (G p.1) (H p.1) (A p.1) (A₁ p.1) (A₂ p.1) (c p.1) p.2) :=
  (dynamic_clockGradient_spatial_bound hF hcF hcG hcA₁ hcA₂ hbG hbA₁ hbA₂ m hc).add
    (((dynamic_clockGradient_spatial_bound (A:=fun r y => A r y*G r y)
      (A₁:=fun r y => A₁ r y*G r y+A r y*H r y) hF hcF hcG (hcA.mul hcG)
      ((hcA₁.mul hcG).add (hcA.mul hcH)) hbG (hbA.mul hbG)
      ((hbA₁.mul hbG).add (hbA.mul hbH)) m hc).sub
      (((dynamic_clockGradient_spatial_bound hF hcF hcG hcA hcA₁ hbG hbA hbA₁ m hc).mul
        (dynamic_clockTest_spatial_bound hF hcF hcG hbG m hc)).add
        ((dynamic_clockTest_spatial_bound hF hcF hcA hbA m hc).mul
        (dynamic_clockGradient_spatial_bound hF hcF hcG hcG hcH hbG hbG hbH m hc)))).const_mul m)

 noncomputable def HeatJetFamily.reparam {n : ℕ} (V : HeatJetFamily n)
    (c : ℝ → ℝ) (hc : Continuous c) : HeatJetFamily n where
  J s := V.J (c s)
  C := V.C
  lipschitz s := V.lipschitz (c s)
  continuousF := V.continuousF.comp ((hc.comp continuous_fst).prodMk continuous_snd)
  continuousG i := (V.continuousG i).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  continuousH i := (V.continuousH i).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  continuousA := V.continuousA.comp ((hc.comp continuous_fst).prodMk continuous_snd)
  continuousA₁ i := (V.continuousA₁ i).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  continuousA₂ i := (V.continuousA₂ i).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  boundedG i := (V.boundedG i).precomp (fun p : ℝ × (Fin (n+1) → ℝ) => (c p.1,p.2))
  boundedH i := (V.boundedH i).precomp (fun p : ℝ × (Fin (n+1) → ℝ) => (c p.1,p.2))
  boundedA := V.boundedA.precomp (fun p : ℝ × (Fin (n+1) → ℝ) => (c p.1,p.2))
  boundedA₁ i := (V.boundedA₁ i).precomp (fun p : ℝ × (Fin (n+1) → ℝ) => (c p.1,p.2))
  boundedA₂ i := (V.boundedA₂ i).precomp (fun p : ℝ × (Fin (n+1) → ℝ) => (c p.1,p.2))

  

 noncomputable def HeatJetFamily.evolveTest {n : ℕ} (V : HeatJetFamily n) (J : HeatJet n)
    {m : ℝ} (hm : 0 < m) (c : ℝ → ℝ) (hc : Continuous c) : HeatJetFamily n where
  J s := { J with A := ((V.J s).evolve hm (c s)).A
                  A₁ := ((V.J s).evolve hm (c s)).A₁
                  A₂ := ((V.J s).evolve hm (c s)).A₂
                  smoothA := ((V.J s).evolve hm (c s)).smoothA
                  smoothA₁ := ((V.J s).evolve hm (c s)).smoothA₁
                  smoothA₂ := ((V.J s).evolve hm (c s)).smoothA₂
                  derivA := ((V.J s).evolve hm (c s)).derivA
                  derivA₁ := ((V.J s).evolve hm (c s)).derivA₁ }
  C := J.C
  lipschitz _ := J.lipschitz
  continuousF := J.lipschitz.continuous.comp continuous_snd
  continuousG i := (J.smoothG i).continuous.comp continuous_snd
  continuousH i := (J.smoothH i).continuous.comp continuous_snd
  boundedG i := AbsBounded.precomp (J.smoothG i).bound (fun p : ℝ × (Fin (n+1) → ℝ) => p.2)
  boundedH i := AbsBounded.precomp (J.smoothH i).bound (fun p : ℝ × (Fin (n+1) → ℝ) => p.2)
  continuousA := V.evolve_A_continuous hm hc
  continuousA₁ i := V.evolve_A₁_continuous hm hc i
  continuousA₂ i := V.evolve_A₂_continuous hm hc i
  boundedA := dynamic_clockTest_spatial_bound (A:=fun r => (V.J r).A)
    V.lipschitz V.continuousF V.continuousA V.boundedA m hc
  boundedA₁ i := dynamic_clockGradient_spatial_bound (G:=fun r => (V.J r).G i)
    (A:=fun r => (V.J r).A) (A₁:=fun r => (V.J r).A₁ i)
    V.lipschitz V.continuousF (V.continuousG i) V.continuousA (V.continuousA₁ i)
    (V.boundedG i) V.boundedA (V.boundedA₁ i) m hc
  boundedA₂ i := dynamic_clockSecond_spatial_bound (G:=fun r => (V.J r).G i)
    (H:=fun r => (V.J r).H i) (A:=fun r => (V.J r).A)
    (A₁:=fun r => (V.J r).A₁ i) (A₂:=fun r => (V.J r).A₂ i)
    V.lipschitz V.continuousF (V.continuousG i) (V.continuousH i) V.continuousA
    (V.continuousA₁ i) (V.continuousA₂ i) (V.boundedG i) (V.boundedH i)
    V.boundedA (V.boundedA₁ i) (V.boundedA₂ i) m hc

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem clockTest_integral {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hc : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (m t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTest m F (fun y => ∫ s, A s y ∂μ) t x = ∫ s, clockTest m F (A s) t x ∂μ := by
  let ν := Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal t)
  have hi := (exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal t)).integrable_shift hF m x
  have hcF : Measurable (fun z => F (x+z)) := (hF.continuous.comp (continuous_const.add continuous_id)).measurable
  let τ := tiltedLaw ν m (fun z => F (x+z))
  have : IsProbabilityMeasure τ := tiltedLaw_isProbability hi
  obtain ⟨K,_hK,hbK⟩ := hb
  have hI : Integrable (fun p : (Fin (n+1) → ℝ) × ℝ => A p.2 (x+p.1)) (τ.prod μ) :=
    (integrable_const K).mono'
      (hc.comp (continuous_snd.prodMk (continuous_const.add continuous_fst))).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hbK (p.2,x+p.1))
  have he := integral_integral_swap (f:=fun z s => A s (x+z)) hI
  change tiltedMean ν m (fun z => F (x+z)) (fun z => ∫ s, A s (x+z) ∂μ) =
    ∫ s, tiltedMean ν m (fun z => F (x+z)) (fun z => A s (x+z)) ∂μ
  dsimp only [τ] at he
  simp_rw [integral_tiltedLaw (μ:=ν) (m:=m) hcF hi] at he
  exact he

 theorem heatSteps_positive {ι : Type*} (cs : List HeatClock) :
    ∀ st ∈ heatSteps (ι:=ι) cs, 0 < st.1 := by
  intro st hs
  obtain ⟨c,_hc,rfl⟩ := List.mem_map.mp hs
  exact c.positive

 theorem heatPrefixTest_joint_continuous {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {A : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hc : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (cs : List HeatClock) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => prefixTest (heatSteps cs) F (A p.1) p.2) := by
  obtain ⟨K,hK,hbK⟩ := hb
  induction cs with
  | nil => exact hc
  | cons c cs ih =>
    have hl := prefixContinuation_lipschitz hF (heatSteps cs) (heatSteps_positive cs)
    have hb' : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => prefixTest (heatSteps cs) F (A p.1) p.2) :=
      ⟨K,hK,fun p => prefixTest_abs_le hF
        ⟨hc.comp (continuous_const.prodMk continuous_id),K,hK,fun y => hbK (p.1,y)⟩
        (fun y => hbK (p.1,y)) _ (heatSteps_positive cs) p.2⟩
    have hh := dynamic_clockTest_spatial_continuous (F:=fun _ => prefixContinuation (heatSteps cs) F)
      (A:=fun r => prefixTest (heatSteps cs) F (A r)) (fun _ => hl)
      (hl.continuous.comp continuous_snd) ih hb' c.mass (continuous_const (y:=(c.time:ℝ)))
    simpa only [heatSteps,List.map_cons,prefixTest,clockTest,Real.toNNReal_coe] using hh

 theorem heatPrefixTest_integral {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hc : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (hb : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
    (cs : List HeatClock) (x : Fin (n+1) → ℝ) :
    prefixTest (heatSteps cs) F (fun y => ∫ s, A s y ∂μ) x =
      ∫ s, prefixTest (heatSteps cs) F (A s) x ∂μ := by
  obtain ⟨K,hK,hbK⟩ := hb
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    have hl := prefixContinuation_lipschitz hF (heatSteps cs) (heatSteps_positive cs)
    have hb' : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => prefixTest (heatSteps cs) F (A p.1) p.2) :=
      ⟨K,hK,fun p => prefixTest_abs_le hF
        ⟨hc.comp (continuous_const.prodMk continuous_id),K,hK,fun y => hbK (p.1,y)⟩
        (fun y => hbK (p.1,y)) _ (heatSteps_positive cs) p.2⟩
    have hh := clockTest_integral (A:=fun r => prefixTest (heatSteps cs) F (A r)) hl μ
      (heatPrefixTest_joint_continuous (A:=A) hF hc ⟨K,hK,hbK⟩ cs) hb' c.mass c.time x
    simp only [heatSteps,List.map_cons,prefixTest]
    simp only [heatSteps] at ih
    rw [funext ih]
    simpa only [heatSteps,clockTest,Real.toNNReal_coe] using hh

 theorem HeatJetFamily.nonnegativeProfileTest_integral {n : ℕ} (V : HeatJetFamily n) (J : HeatJet n)
    (hF : ∀ s, (V.J s).F=J.F) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    (V.integralTest J μ).nonnegativeProfileTest α l t x =
      ∫ s, (V.J s).nonnegativeProfileTest α l t x ∂μ := by
  obtain ⟨K,_hK,hbK⟩ := V.boundedA
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun s => ((V.J s).schedule ((α.cappedApprox k).grid l t k)).A x) μ := by
    simp only [HeatJet.schedule_A_prefix,hF]
    exact ((heatPrefixTest_joint_continuous (A:=fun s => (V.J s).A) J.lipschitz V.continuousA V.boundedA _).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hb (k : ℕ) : ∀ᵐ s ∂μ,
      ‖((V.J s).schedule ((α.cappedApprox k).grid l t k)).A x‖ ≤ K := by
    apply Eventually.of_forall
    intro s
    rw [HeatJet.schedule_A_prefix,Real.norm_eq_abs]
    exact prefixTest_abs_le (V.J s).lipschitz (V.J s).smoothA (fun y => hbK (s,y)) _
      (heatSteps_positive _) x
  have hh := tendsto_integral_of_dominated_convergence (fun _ => K) hm (integrable_const K) hb
    (Eventually.of_forall fun s => ((V.J s).capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply tendsto_nhds_unique (((V.integralTest J μ).capped_test_tendstoUniformly α hα l t).tendsto_at x)
  apply hh.congr'
  apply Eventually.of_forall
  intro k
  simp only [HeatJet.schedule_A_prefix,hF]
  exact (heatPrefixTest_integral (A:=fun s => (V.J s).A) J.lipschitz μ V.continuousA V.boundedA _ x).symm

end SKFluctuations.Hierarchy

end

end OAI
