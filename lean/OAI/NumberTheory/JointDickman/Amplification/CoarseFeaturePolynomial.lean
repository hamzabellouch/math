import OAI.NumberTheory.JointDickman.Amplification.CoarseFeatureAverage
import OAI.NumberTheory.JointDickman.Analysis.PolynomialLaplaceFeature
import OAI.NumberTheory.JointDickman.Amplification.LogIntervalSquareError
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCellBounds

namespace OAI

/-! # Finite multiplicative approximations to the actual coarse features -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem primeHalfLogInterval_upper
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 1/4 ≤ a → a ≤ b → b ≤ 16/5 →
      (∑ y : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B ∈ Set.Ioc a b then
          bernoulliSiteMass (fun p : auxiliaryPrimes B => 1/(2*(p.val : ℝ))) y else 0) ≤
        M*(b-a)+C*(B : ℝ)^(-(80 : ℝ)) := by
  obtain ⟨M,C,hM0,hC,hb⟩ := primeSite_interval_upper hSD hSW hM hMP (Or.inr rfl)
  refine ⟨M,C,hM0,hC,?_⟩
  filter_upwards [hb,eventually_ge_atTop 1] with B hb hB
  intro a b ha hab hb'
  have hq : ((1 : ℕ) : ℝ) ≤ (B : ℝ)^(100 : ℝ) := by
    simpa only [Nat.cast_one] using Real.one_le_rpow (by exact_mod_cast hB : (1 : ℝ) ≤ (B : ℝ)) (by norm_num : (0 : ℝ) ≤ 100)
  have hh := hb a b ha hab hb' 1 hq 1
  have hr (n : ℕ) : (n : ZMod 1) = ((1 : (ZMod 1)ˣ) : ZMod 1) := Subsingleton.elim _ _
  simpa only [hr,and_true,Nat.totient_one,Nat.cast_one,div_one,div_div] using hh

theorem coarseFeature_polynomial_error {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (d : Fin m) {δ η M C : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/8)
    (P : Polynomial ℝ)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |P.eval t-logIntervalRamp (channelLower m d) (channelUpper m d) δ t/channelMesh m| ≤ η)
    (hbound : ∀ a b : ℝ, 1/4 ≤ a → a ≤ b → b ≤ 16/5 →
      (∑ y : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B ∈ Set.Ioc a b then
          bernoulliSiteMass (fun p : auxiliaryPrimes B => 1/(2*(p.val : ℝ))) y else 0) ≤
        M*(b-a)+C*(B : ℝ)^(-(80 : ℝ))) :
    (∑ x, fullPrimeMass (auxiliaryPrimes B) x*
      (primeCoarseFeature m B d x-
        ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)^2) ≤
      4*M*δ/(channelMesh m)^2+4*C/(channelMesh m)^2*(B : ℝ)^(-(80 : ℝ))+2*η^2 := by
  let a := channelLower m d
  let b := channelUpper m d
  let D := channelMesh m
  let w := bernoulliSiteMass (fun p : auxiliaryPrimes B => 1/(2*(p.val : ℝ)))
  let s := fun y : auxiliaryPrimes B → Bool => Real.log (retainedPrimeProduct (auxiliaryPrimes B) y)/B
  have hD : 0 < D := channelMesh_pos hm
  have hab : a ≤ b := by have he := channel_width m d; dsimp [a,b]; linarith
  have ha : 1/2 ≤ a := channelLower_ge m d
  have hb : b ≤ 3 := channelUpper_le hm d
  have hw (y : auxiliaryPrimes B → Bool) : 0 ≤ w y := by
    apply bernoulliSiteMass_nonneg
    intro p
    have hp : (1 : ℝ) ≤ p.val := by exact_mod_cast (auxiliaryPrimes_prime B p.val p.property).one_lt.le
    exact ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩
  have he₁ := hbound (a-δ) a (by linarith) (by linarith) (by linarith)
  have he₂ := hbound b (b+δ) (by linarith) (by linarith) (by linarith)
  have hi := primeCoarseFeature_average_error hm hB d (fun s => P.eval (Real.exp (-s)))
  simp_rw [fairSplitAverage_polynomial (auxiliaryPrimes B) (auxiliaryPrimes_prime B)] at hi
  refine hi.trans ?_
  calc
    _ ≤ ∑ y, w y*(2/D^2*((if s y ∈ Set.Ioc (a-δ) a then (1 : ℝ) else 0)+
        (if s y ∈ Set.Ioc b (b+δ) then (1 : ℝ) else 0))+2*η^2) := by
      apply sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hw y)
      exact polynomial_log_interval_square_error hab hδ P hP
        (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    _ = 2/D^2*((∑ y, if s y ∈ Set.Ioc (a-δ) a then w y else 0)+
        (∑ y, if s y ∈ Set.Ioc b (b+δ) then w y else 0))+2*η^2 := by
      simp only [mul_add,sum_add_distrib,← sum_mul,
        show ∑ y, w y = 1 from bernoulliSiteMass_sum _,one_mul]
      congr 1
      congr 1 <;> {rw [mul_sum]; apply sum_congr rfl; intro y _; split_ifs <;> ring}
    _ ≤ 2/D^2*((M*δ+C*(B : ℝ)^(-(80 : ℝ)))+
        (M*δ+C*(B : ℝ)^(-(80 : ℝ))))+2*η^2 := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa only [sub_sub_cancel] using he₁
      · simpa only [add_sub_cancel_left] using he₂
    _ = _ := by dsimp [D]; ring

end JointDickman

end OAI
