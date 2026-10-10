import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Filter
open scoped Topology

lemma computable_rat_lt : Computable₂ (fun a b : ℚ => decide (a < b)) := by
  exact (Computable.cond (computable_rat_le.comp Computable.snd Computable.fst)
    (Computable.const false) (Computable.const true)).of_eq
      (fun p => by
        by_cases h : p.2 ≤ p.1
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h])

noncomputable def logBracket (q : ℚ) (n c : ℕ) : Prop :=
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k < q ∧
    q < expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k

noncomputable instance (q : ℚ) (n : ℕ) : DecidablePred (logBracket q n) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma computable_logBracket :
    Computable₂ (fun p : ℚ × ℕ => fun c => decide (logBracket p.1 p.2 c)) := by
  have hr : Computable (fun p : (ℚ × ℕ) × ℕ => Denumerable.ofNat ℚ p.2.unpair.1) :=
    (Computable.ofNat ℚ).comp (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd))
  have hk : Computable (fun p : (ℚ × ℕ) × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have he : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.1.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) (Computable.snd.comp Computable.fst)
  have hd : Computable (fun p : (ℚ × ℕ) × ℕ => (1 / 2 : ℚ) ^ p.2.unpair.2) :=
    computable_rat_pow.comp (Computable.const (1 / 2)) hk
  exact computable_decide_and
    (computable_rat_lt.comp
      (computable_rat_add.comp (computable_expApprox.comp (computable_rat_sub.comp hr he) hk) hd)
      (Computable.fst.comp Computable.fst))
    (computable_rat_lt.comp (Computable.fst.comp Computable.fst)
      (computable_rat_sub.comp (computable_expApprox.comp (computable_rat_add.comp hr he) hk) hd))

lemma cast_error (n : ℕ) : (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) = error n := by
  simp [error, one_div]

lemma error_tendsto : Tendsto error atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma exists_logBracket {q : ℚ} (hq : 0 < q) (n : ℕ) : ∃ c, logBracket q n c := by
  have he : 0 < error n := by unfold error; positivity
  obtain ⟨r, hr₀, hr₁⟩ := exists_rat_btwn
    (show Real.log (q : ℝ) - error n < Real.log (q : ℝ) + error n by linarith)
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ : Real.exp ((r : ℝ) - error n) < (q : ℝ) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have h₁ : (q : ℝ) < Real.exp ((r : ℝ) + error n) := by
    rw [← Real.exp_log hq', Real.exp_lt_exp]
    linarith
  have hd : Tendsto (fun k => 2 * error k) atTop (𝓝 0) := by
    simpa using error_tendsto.const_mul 2
  obtain ⟨k, hk₀, hk₁⟩ := ((hd.eventually_lt_const (sub_pos.mpr h₀)).and
    (hd.eventually_lt_const (sub_pos.mpr h₁))).exists
  refine ⟨Nat.pair (@Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable r) k, ?_⟩
  simp only [logBracket, Nat.unpair_pair, Denumerable.ofNat_encode]
  have hl := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).2
  have hu := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).1
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at hl hu
  constructor
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_add, cast_error]
    linarith
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [Rat.cast_sub, cast_error]
    linarith

lemma logBracket_spec {q : ℚ} (hq : 0 < q) {n c : ℕ} (hc : logBracket q n c) :
    |(Denumerable.ofNat ℚ c.unpair.1 : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  let r := Denumerable.ofNat ℚ c.unpair.1
  let k := c.unpair.2
  have he₀ := (abs_le.mp (expApprox_spec (r - (1 / 2 : ℚ) ^ n) k)).1
  have he₁ := (abs_le.mp (expApprox_spec (r + (1 / 2 : ℚ) ^ n) k)).2
  simp only [Rat.cast_sub, Rat.cast_add, cast_error] at he₀ he₁
  have hb₀ := (Rat.cast_lt (K := ℝ)).mpr hc.1
  have hb₁ := (Rat.cast_lt (K := ℝ)).mpr hc.2
  change ((expApprox (r - (1 / 2 : ℚ) ^ n) k + (1 / 2 : ℚ) ^ k : ℚ) : ℝ) < _ at hb₀
  change (q : ℝ) < ((expApprox (r + (1 / 2 : ℚ) ^ n) k - (1 / 2 : ℚ) ^ k : ℚ) : ℝ) at hb₁
  simp only [Rat.cast_add, Rat.cast_sub, cast_error] at hb₀ hb₁
  have hl : (r : ℝ) - error n < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (Rat.cast_pos.mpr hq)).mpr (by linarith)
  have hu : Real.log (q : ℝ) < (r : ℝ) + error n :=
    (Real.log_lt_iff_lt_exp (Rat.cast_pos.mpr hq)).mpr (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def logSearchPredicate (p : ℚ × ℕ) (c : ℕ) : Prop :=
  if 0 < p.1 then logBracket p.1 p.2 c else True

noncomputable instance : DecidableRel logSearchPredicate := by
  intro p c
  unfold logSearchPredicate
  infer_instance

lemma exists_logSearchPredicate (p : ℚ × ℕ) : ∃ c, logSearchPredicate p c := by
  by_cases hq : 0 < p.1
  · simpa [logSearchPredicate, hq] using exists_logBracket hq p.2
  · exact ⟨0, by simp [logSearchPredicate, hq]⟩

noncomputable def logCutoff (p : ℚ × ℕ) : ℕ := Nat.find (exists_logSearchPredicate p)

lemma computable_logCutoff : Computable logCutoff := by
  apply computable_find (hex := exists_logSearchPredicate)
  exact (Computable.cond (computable_rat_lt.comp (Computable.const 0)
    (Computable.fst.comp Computable.fst)) computable_logBracket (Computable.const true)).of_eq
      (fun p => by by_cases hq : 0 < p.1.1 <;> simp [logSearchPredicate, hq])

noncomputable def logApprox (q : ℚ) (n : ℕ) : ℚ :=
  if 0 < q then Denumerable.ofNat ℚ (logCutoff (q,n)).unpair.1 else 0

lemma computable_logApprox : Computable₂ logApprox := by
  exact computable_ite (computable_rat_lt.comp (Computable.const 0) Computable.fst)
    ((Computable.ofNat ℚ).comp (Computable.fst.comp
      (Primrec.unpair.to_comp.comp computable_logCutoff))) (Computable.const 0)

lemma logApprox_spec {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |(logApprox q n : ℝ) - Real.log (q : ℝ)| ≤ error n := by
  rw [logApprox, ite_eq_left hq]
  apply logBracket_spec hq
  have hh := Nat.find_spec (exists_logSearchPredicate (q,n))
  simpa only [logSearchPredicate, ite_eq_left hq, logCutoff] using hh

lemma log_abs_bound {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by
  have hq' : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have h₀ := Real.log_le_sub_one_of_pos hq'
  have h₁ := Real.log_le_sub_one_of_pos (inv_pos.mpr hq')
  rw [Real.log_inv] at h₁
  have ha := rat_abs_le_num q
  have hb := rat_abs_le_num q⁻¹
  rw [Rat.cast_inv] at hb
  rw [abs_of_pos hq'] at ha
  rw [abs_of_pos (inv_pos.mpr hq')] at hb
  apply abs_le.mpr
  push_cast
  constructor <;> linarith [Nat.cast_nonneg q.num.natAbs (α := ℝ),
    Nat.cast_nonneg q⁻¹.num.natAbs (α := ℝ)]

end BalancedTransport.Effectivity
end

end OAI
