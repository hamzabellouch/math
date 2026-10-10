import OAI.NumberTheory.TotientAsymptotic.CollisionGrid

namespace OAI

/-!
Counting the finite paired-grid labels at a local PPT comparison scale.
The bound uses the local dimension and the actual mesh, independently of
the ambient Ford bands or a globally chosen normality cutoff.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The actual PPT mesh is at least the reciprocal of its local double
logarithm.  Doubling this mesh preserves the same lower bound. -/
lemma ppt_mesh_reciprocal_lower {t : ℝ} (ht0 : 0 < t) (ht : 1 ≤ Real.log t) :
    1/t ≤ (Real.log t)^5/Real.sqrt t := by
  have ht1 : 1 < t := (Real.log_pos_iff ht0.le).mp (zero_lt_one.trans_le ht)
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsqrtle : Real.sqrt t ≤ t := by
    nlinarith only [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t, ht1.le]
  have hlogpow : 1 ≤ (Real.log t)^5 := one_le_pow₀ ht
  calc
    1/t ≤ 1/Real.sqrt t := one_div_le_one_div_of_le hsqrt hsqrtle
    _ ≤ (Real.log t)^5/Real.sqrt t :=
      div_le_div_of_nonneg_right hlogpow hsqrt.le

/-- There are at most exponentially many grid labels in the square of
the logarithm of the local double-logarithmic scale. -/
theorem ppt_grid_card_bound {A t δ : ℝ} {b : ℕ}
    (ht0 : 0 < t) (ht : 1 ≤ Real.log t) (hδ : 0 < δ) (hmesh : 1/t ≤ δ)
    (hdim : (b : ℝ) ≤ A*Real.log t) :
    ((collisionGridFamilies δ b).card : ℝ) ≤
      Real.exp (2*A*(Real.log t)^2) := by
  have ht1 : 1 < t := (Real.log_pos_iff ht0.le).mp (zero_lt_one.trans_le ht)
  have hinverse : 1/δ ≤ t := by
    apply (div_le_iff₀ hδ).mpr
    have hh := (div_le_iff₀ ht0).mp hmesh
    nlinarith only [hh]
  have hbase : ((⌊1/δ⌋₊+1 : ℕ) : ℝ) ≤ 2*t := by
    have hf := Nat.floor_le (show 0 ≤ 1/δ by positivity)
    push_cast
    linarith only [hf, hinverse, ht1.le]
  have hlog : Real.log (2*t) ≤ 2*Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne']
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [htwo, ht]
  rw [collisionGridFamilies_card, Nat.cast_pow]
  calc
    _ ≤ (2*t)^b := pow_le_pow_left₀ (by positivity) hbase b
    _ = Real.exp ((b : ℝ)*Real.log (2*t)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 2*t)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        (b : ℝ)*Real.log (2*t) ≤ (b : ℝ)*(2*Real.log t) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ (A*Real.log t)*(2*Real.log t) :=
          mul_le_mul_of_nonneg_right hdim (by linarith only [ht])
        _ = 2*A*(Real.log t)^2 := by ring

/-- Removing arbitrary matched coordinates costs at most another
exponential-square factor; every subset is counted. -/
theorem ppt_grid_and_subsets_card_bound {A t δ : ℝ} {b H : ℕ}
    (ht0 : 0 < t) (ht : 1 ≤ Real.log t) (hδ : 0 < δ) (hmesh : 1/t ≤ δ)
    (hb : (b : ℝ) ≤ A*Real.log t) (hH : (H : ℝ) ≤ A*Real.log t) :
    ((collisionGridFamilies δ b).card : ℝ)*
        (((Finset.range H).powerset).card : ℝ) ≤
      Real.exp (3*A*(Real.log t)^2) := by
  have hgrid := ppt_grid_card_bound ht0 ht hδ hmesh hb
  have hlog0 : 0 ≤ Real.log t := zero_le_one.trans ht
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log t := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh, ht]
  have hsubsets : (((Finset.range H).powerset).card : ℝ) ≤
      Real.exp (A*(Real.log t)^2) := by
    rw [Finset.card_powerset, Finset.card_range, Nat.cast_pow, Nat.cast_ofNat]
    rw [show (2 : ℝ)^H = Real.exp ((H : ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    apply Real.exp_le_exp.mpr
    calc
      (H : ℝ)*Real.log 2 ≤ (H : ℝ)*Real.log t :=
        mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ ≤ (A*Real.log t)*Real.log t := mul_le_mul_of_nonneg_right hH hlog0
      _ = _ := by ring
  calc
    _ ≤ Real.exp (2*A*(Real.log t)^2)*Real.exp (A*(Real.log t)^2) :=
      mul_le_mul hgrid hsubsets (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TotientAsymptotic

end

end OAI
