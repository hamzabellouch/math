import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointMarginalSupport

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientRateLimit

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

theorem tendsto_log_succ_div_nat_of_ratio {n : ℕ → ℕ} {mass : ℝ}
    (hsize : Tendsto (fun N => (n N : ℝ) / (N : ℝ)) atTop (𝓝 mass)) :
    Tendsto (fun N => Real.log (n N + 1 : ℕ) / (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := |mass| + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hmC : mass < C := by dsimp [C]; linarith [le_abs_self mass]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log (C + 1) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ =>
      (Real.log (C + 1) + Real.log (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hc.add hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n N))))
        (Nat.cast_nonneg _)
  · filter_upwards [(tendsto_order.1 hsize).2 C hmC,
      eventually_ge_atTop (1 : ℕ)] with N hn hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
    have hsizeN := (div_lt_iff₀ hNp).mp hn
    have hbound : (n N + 1 : ℕ) ≤ (C + 1) * (N : ℝ) := by
      push_cast
      nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n N + 1 : ℕ)) hbound
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) hNp.ne'] at hl
    exact div_le_div_of_nonneg_right hl hNp.le

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem tendsto_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3) (h : H)
    (cap : ℕ → ℝ) (mass capRate marginalRate : ℝ)
    (hsize : Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 mass))
    (hcap : Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N)
      atTop (𝓝 capRate))
    (hmarginal : Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 marginalRate)) :
    Tendsto (fun N =>
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N) /
        (N : ℝ)) atTop (𝓝 (capRate - marginalRate)) := by
  let A : ℝ := (Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2
  have hlog := tendsto_log_succ_div_nat_of_ratio hsize
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal := (hcap.sub hmarginal).add
    (((hinv.add hlog).const_mul A).add (hlog.const_mul (Fintype.card Shape : ℝ)))
  simp only [add_zero, mul_zero] at htotal
  convert htotal using 1
  ext N
  dsimp only [classExponent, A, Positions]
  simp only [Fintype.card_fin, div_eq_mul_inv]
  ring

omit [DecidableEq H] in
theorem tendsto_sum_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3)
    (cap : ℕ → H → ℝ) (mass capRate marginalRate : H → ℝ)
    (hsize : ∀ h, Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 (mass h)))
    (hcap : ∀ h, Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N h)
      atTop (𝓝 (capRate h)))
    (hmarginal : ∀ h, Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 (marginalRate h))) :
    Tendsto (fun N => (∑ h,
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) /
        (N : ℝ)) atTop (𝓝 (∑ h, (capRate h - marginalRate h))) := by
  have hs := tendsto_finsetSum Finset.univ (fun h _ =>
    tendsto_classExponent_div_nat counts s h (fun N => cap N h)
      (mass h) (capRate h) (marginalRate h) (hsize h) (hcap h) (hmarginal h))
  simpa only [Finset.sum_div] using hs

theorem eventually_all_target_degree_upper
    (counts : ℕ → H → Shape → ℕ) (sum : H → ℕ)
    (cap : ℕ → H → ℝ) (sideRate : Fin 3 → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hentropy : ∀ᶠ N in atTop, ∀ h w, localAllowed (counts N) sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions (counts N) h)) ≤ cap N h)
    (hrate : ∀ s, Tendsto (fun N => (∑ h,
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) /
        (N : ℝ)) atTop (𝓝 (sideRate s)))
    (hside : ∀ s, sideRate s ≤ D) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, ∀ e : Target (counts N),
      Real.log ((neighbors (counts N) sum (triple (counts N) e)).card : ℝ) / (N : ℝ) ≤
        D + η := by
  have hs : ∀ᶠ N in atTop, ∀ s : Fin 3,
      (∑ h, classExponent (counts N) s
        (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) / (N : ℝ) ≤
          D + η / 2 := by
    rw [Filter.eventually_all]
    intro s
    filter_upwards [(tendsto_order.1 (hrate s)).2 (sideRate s + η / 2) (by linarith)]
      with N hN
    linarith [hside s]
  have hc : Tendsto (fun N : ℕ => Real.log 3 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hentropy, hs, (tendsto_order.1 hc).2 (η / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with N he hs hc hN
  intro e
  by_cases hz : (neighbors (counts N) sum (triple (counts N) e)).card = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero, zero_div]
    linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hupper (s : Fin 3) :
      (∑ h, classExponent (counts N) s (triple (counts N) e) h (cap N h)) ≤
        (N : ℝ) * (D + η / 2) := by
    simp_rw [classExponent_target_eq]
    simpa only [mul_comm] using (div_le_iff₀ hNp).mp (hs s)
  have hb := div_le_div_of_nonneg_right
    (log_neighbors_card_le (counts N) sum (triple (counts N) e) (cap N) he
      ((N : ℝ) * (D + η / 2)) hupper (Nat.pos_of_ne_zero hz)) hNp.le
  rw [add_div, mul_div_cancel_left₀ _ hNp.ne'] at hb
  linarith

end MatrixMultiplication.JointAmbientRateLimit

end
end

end MatrixAllFields

end OAI
