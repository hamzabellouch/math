import OAI.Probability.DilutedSpin.MeasurableShapeEnergy
import OAI.Probability.DilutedSpin.PhysicalScheduledStep

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma centered_square_le_one (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ x, |f x|≤1) :
    P.expect (fun x => (f x-P.expect f)^2)≤1 := by
  have hs : P.expect (fun x => f x^2)≤1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using sq_le_sq.mpr (show |f x|≤|(1:ℝ)| by simpa using hf x))
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => (f x-P.expect f)^2)=P.expect (fun x => f x^2)-(P.expect f)^2 := by
    calc
      _ = P.expect (fun x => f x^2-2*P.expect f*f x+(P.expect f)^2) := P.expect_congr (fun x => by ring)
      _ = _ := by simp; ring
  rw [he]
  nlinarith [sq_nonneg (P.expect f)]

lemma covariance_sq_le_one (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) : (P.covariance f g)^2≤1 := by
  rw [P.covariance_centered]
  exact (P.expect_mul_sq_le _ _).trans (by
    have hh := mul_le_mul (P.centered_square_le_one f hf) (P.centered_square_le_one g hg)
      (P.expect_nonneg (fun x => sq_nonneg (g x-P.expect g))) zero_le_one
    simpa only [one_mul] using hh)

lemma covarianceEnergy_le_one {N : ℕ} (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤1 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact P.covariance_sq_le_one _ _ (fun x => hX x i) (fun x => hX x j)
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma shapeEnergyAt_le_one (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤1 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_one
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 1)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_le_one (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (X : FinitePath Ω L → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : scheduledShapeEnergy L d S q T X≤1 := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_le_one _ _ _ _ (fun _ index => hX _ index)
  · exact zero_le_one

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance scheduledEnergyBoundDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {p : ℕ}

/-- Unit bound for the actual physical covariance, including N=0, leaves,
inadmissible schedules and the countable variable-alphabet root. -/
lemma physicalScheduledEnergy_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    physicalScheduledEnergy M θB hB N L u S Q≤1 := by
  unfold physicalScheduledEnergy
  calc
    _ ≤ ∫ _, (1:ℝ) ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
        (markLaw (weights L) N) (M.alpha*N) (scoreRate N) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)
      · exact integrable_const _
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_le_one _ _ _ _ _
          (fun _ _ => readVector_bound _ _ _))
    _ = 1 := by simp

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
