import OAI.MeasureTheory.Falconer.Estimates.ParallelScaleMean
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

/-!
# Uniform exceptional mass of all-dimensional parallel tests

The numerical linear-subpower estimate is independent of dimension.
The parallel tests use the original class centers and the original sphere law.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem uniform_parallel_exceptional {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ sig*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^sig →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ g p : ℕ, g ≤ p → p ≤ N →
      ∀ P : CellPath d, P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ν (parallelGoodSet Q (sourceClass Q μ N B p₀) g p P
        ((2*((2:ℝ)^N)^(500*sig))/(2:ℝ)^p)
        (((2:ℝ)^N)^(PlanarFalconer.height
          (fun n : ℕ => sourceProfile Q μ N B p₀ n-((d:ℝ)/2)*(n:ℝ)/N) g p+
            1000*((d:ℝ)+1)*sig)))ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  let s : ℝ := (d:ℝ)/2
  let D : ℝ := parallelPackingConstant d
  let A : ℝ := 2*((d:ℝ)+1)+1+500*s
  let C : ℝ := 2*(6:ℝ)^s*D*(1+(2:ℝ)^s)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_linear_subpower C (by dsimp [C,D]; positivity) hsig
  obtain ⟨N₂,hroot⟩ := fixed_constant_absorbed (by positivity : 0 < 500*sig) (Real.sqrt d)
  obtain ⟨N₃,htwo⟩ := fixed_constant_absorbed hsig 2
  refine ⟨max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro N hN Q hQ μ inst B hB hwidth hlarge p₀ hp₀ g p hgp hpN P hP hocc ν hmass hball
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R : ℝ := (2:ℝ)^N
  let K := PlanarFalconer.height (fun n : ℕ => sourceProfile Q μ N B p₀ n-s*(n:ℝ)/N) g p
  let W := (2*R^(500*sig))/(2:ℝ)^p
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hK : 0 ≤ K := PlanarFalconer.height_nonneg _ hgp
  have hm := sourceClass_parallel_scale_mean Q hQ μ hNp hB hsig hs hwidth hlarge
    (hroot N hN₂) hp₀ hgp hpN hP ν hmass hball
  have hcoef : 2*(6:ℝ)^s*D*(1+(2:ℝ)^s*(p-g:ℕ)) ≤ R^sig := by
    apply (parallel_coefficient_bound (N := N) (show 0 ≤ D by dsimp [D]; positivity)
      (Nat.cast_nonneg (p-g)) (by exact_mod_cast (Nat.sub_le p g).trans hpN)).trans
    exact hpoly N hN₁
  have hmean : (∫⁻ w, (parallelTestCount Q (sourceClass Q μ N B p₀) g p P W w : ℝ≥0∞) ∂ν) ≤
      ENNReal.ofReal (R^(K+(A+2)*sig)) := by
    apply hm.trans
    calc
      _ ≤ 1+ENNReal.ofReal (R^sig*R^(K+A*sig)) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hcoef (by positivity)))
      _ = ENNReal.ofReal (1+R^(K+(A+1)*sig)) := by
        rw [← Real.rpow_add hRp]
        have he : sig+(K+A*sig) = K+(A+1)*sig := by ring
        rw [he,ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (R^(K+(A+2)*sig)) := by
        apply ENNReal.ofReal_le_ofReal
        have he : 0 ≤ K+(A+1)*sig := by dsimp [A]; positivity
        have hh := one_add_power_absorb hR he (htwo N hN₃)
        have heq : K+(A+1)*sig+sig = K+(A+2)*sig := by ring
        simpa only [heq] using hh
  apply (parallelGoodSet_exceptional Q (sourceClass Q μ N B p₀) g p P hocc W
    (show 0 < R^(K+1000*((d:ℝ)+1)*sig) by positivity) ν).trans
  apply (ENNReal.div_le_div_right hmean _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity),← Real.rpow_sub hRp]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  dsimp [A,s]
  have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  nlinarith

end Falconer.Regularization

end OAI
