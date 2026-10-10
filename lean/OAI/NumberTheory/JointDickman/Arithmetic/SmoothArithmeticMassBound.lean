import OAI.NumberTheory.JointDickman.Amplification.SchwartzArithmeticFeatures
import OAI.NumberTheory.JointDickman.Probability.UniformTensorApproximation
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeKernelMeanBound

namespace OAI

/-! # The positive mass controlling smooth tensor-approximation errors -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem smooth_arithmetic_mass_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      T*geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1) ≤
        ε B+C*(T/j)*singularSeries j := by
  let w := tensorPowerFactor 0
  have hw (x : ℝ) : w x = tensorBoxBump x := by simp [w,tensorPowerFactor_apply]
  have hs : ∀ x, x ≤ 1/4 ∨ 17/4 < x → w x = 0 := tensorPowerFactor_support 0
  obtain ⟨c,hc,_,H,ε,hε,hbound⟩ := schwartz_arithmetic_feature_comparison hSD hSW hM hMP
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 17/4)
    ht hη (by norm_num : (0 : ℝ) ≤ 1) w w w hs hs hs
  obtain ⟨m,hm,hcompare⟩ := hbound 1 (by norm_num)
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  let K₀ := (m : ℝ)^2*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(D*1*1*1)))*
    (Real.log (17/4)-Real.log (1/4)+2))/channelMesh m
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hwidth : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hwidth' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  refine ⟨1+K₀,by positivity,ε,hε,?_⟩
  filter_upwards [hcompare,hden,eventually_ge_atTop 1] with B hb hd hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog
  let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
  let K := geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
    (endpointSpatialWeight m B t (T/j) d w w w)
  let E := ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
    primeCoarseKernel m B K x y
  let A := geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
    (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1)
  have hdb : ∀ k ∈ S, |d k| ≤ D := by
    intro k hk
    apply hd.1
    apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
    nlinarith [(hlog k hk).1]
  have hwb (x : ℝ) : |w x| ≤ 1 := by
    rw [hw,abs_of_nonneg tensorBoxBump.nonneg]
    exact tensorBoxBump.le_one
  have hKb : ∀ x y, |primeCoarseKernel m B K x y| ≤ K₀ := by
    intro x y
    exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
      hD (by norm_num) (by norm_num) (by norm_num) S d w w w hdb hwb hwb hwb x y
  have hE : |E| ≤ K₀ := primeKernel_mean_abs_le B _ hKb
  have he := hb j Q hQ hscale hcut T hT hlag S hbox hlog
    (fun _ => 1) (by simp) (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  have hA : A = weightedGeometricArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
      (fun _ => 1) (fun _ => 1) (fun _ => 1) w w w := by
    calc
      A = geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T t S
          (fun _ x y z => 1*w x*w y*w z) (fun _ => 1) (fun _ => 1) := by
        dsimp only [A]
        congr 1
        funext k x y z
        simp [hw,tensorCutoff]
      _ = _ := geometricSmoothArithmeticSum_separated B j (1/4) (17/4) (1/4) (17/4) T t S
        (fun _ => 1) w w w (fun _ => 1) (fun _ => 1)
  have he' : T*|A-(singularSeries j/(j : ℝ))*E| ≤ ε B+(T/j)*singularSeries j := by
    simpa only [hA,d,K,E,mul_one,one_mul] using he
  have hSp := (singularSeries_bounds hMP j).1
  have hscalar : 0 ≤ singularSeries j/(j : ℝ) := div_nonneg hSp (Nat.cast_nonneg j)
  have hE' : (singularSeries j/(j : ℝ))*E ≤ (singularSeries j/(j : ℝ))*K₀ :=
    mul_le_mul_of_nonneg_left ((le_abs_self E).trans hE) hscalar
  have hlinear := le_abs_self (A-(singularSeries j/(j : ℝ))*E)
  have hdiff := mul_le_mul_of_nonneg_left hlinear hT.le
  have hlast := mul_le_mul_of_nonneg_left hE' hT.le
  change T*A ≤ _
  have hid : T*((singularSeries j/(j : ℝ))*K₀) = K₀*(T/j)*singularSeries j := by ring
  rw [hid] at hlast
  nlinarith

end JointDickman

end OAI
