import OAI.Geometry.RCD.Harmonic.ResidualSamplingError

namespace OAI

/-! # Collapse of the residual factor from sharp dimensional packing

This is a consequence of an actual product approximation. It does not
assume that the source is already close to Euclidean space, nor that the
residual metric factor is geodesic.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.residual_factor_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Z : Type*) (dZ : MetricSpace Z), letI := dZ
      ∀ (p : X) (z₀ : Z) (ρ : ℝ), 0 < ρ → -1 ≤ K*(4*ρ)^2 →
      ∀ f : X → WithLp 2 (Euclidean n × Z),
        IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) ρ 1 ε f →
        ∀ z₁ : Z, dist z₀ z₁ ≤ 1/4 → dist z₀ z₁ ≤ a := by
  by_cases ha4 : 1/4 ≤ a
  · exact ⟨1,by norm_num,fun _ _ _ _ _ _ _ _ _ _ hz => hz.trans ha4⟩
  have ha4' : a < 1/4 := lt_of_not_ge ha4
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  let C := Real.cosh 1^(n-1)*8^n
  let q := a/(8*(n:ℝ))
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (C/q^n))
  have hm' : 0 < (m:ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmN : 0 < m := by exact_mod_cast hm'
  have hmC : C < (m:ℝ)*q^n := by
    apply (div_lt_iff₀ (pow_pos hq n)).mp
    exact lt_of_le_of_lt (le_max_right _ _) hm
  let b := a/(4*(n:ℝ)*m)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : b ≤ 2 := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hmN
    apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ)*m)).mpr
    nlinarith
  obtain ⟨ε,he,hec,hes⟩ := exists_residual_sampling_accuracy hmN ha
    (lt_min (by norm_num : (0:ℝ)<1/16) (div_pos hb (by norm_num : (0:ℝ)<6)))
  have he16 : ε ≤ 1/16 := hec.trans (min_le_left _ _)
  have heb : ε ≤ b/6 := hec.trans (min_le_right _ _)
  refine ⟨ε,he,?_⟩
  intro Z dZ p z₀ ρ hρ hcurv f hf z₁ hD
  by_contra hsmall
  have haD : a < dist z₀ z₁ := lt_of_not_ge hsmall
  have hsample : 3*ε/(m:ℝ)+ε+2*Real.sqrt (14*ε*(dist z₀ z₁+7*ε)) ≤
      dist z₀ z₁/(2*m) :=
    ((residualSamplingError_bounds he.le hD).trans hes).trans
      (div_le_div_of_nonneg_right haD.le (by positivity))
  obtain ⟨z,hzD,hzsep⟩ := pointed_vertical_samples hX.geodesic hρ he.le hmN hf
    (by linarith) hsample
  have hbsep : b ≤ dist z₀ z₁/(2*m) := by
    calc
      b ≤ a/(2*m) := div_le_div_of_nonneg_left ha.le (by positivity) (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right haD.le (by positivity)
  have hroom : (n:ℝ)*m*b+(dist z₀ z₁+5*ε) ≤ 1-ε := by
    have heq : (n:ℝ)*m*b=a/4 := by dsimp only [b]; field_simp
    rw [heq]
    linarith
  have hpack := hX.product_grid_obstruction hn hρ hb hb2 heb hcurv z
    (fun i j hij => hbsep.trans (hzsep hij)) hzD hroom hf
  have hform : (m:ℝ)^(n+1)*(b/2)^n=(m:ℝ)*q^n := by
    have heq : b/2=q/(m:ℝ) := by dsimp only [b,q]; field_simp; ring
    rw [heq,div_pow,pow_succ]
    field_simp
  rw [hform] at hpack
  exact (not_le_of_gt hmC) hpack

end RegularPointCoordinates

end

end OAI
