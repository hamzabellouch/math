import OAI.Analysis.PeriodicLattice.EffectiveReals

namespace OAI

/-! Certified effective inversion, powers and exponential evaluation. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingElementaryFunctions {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace CertifiedReal
open Encodable Filter Topology
local instance elementaryFunctionsLocal1 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A : Type*} [Primcodable A]

theorem Effective.abs {f : A → ℝ} (hf : Effective f) : Effective (fun a => |f a|) := by
  obtain ⟨q,hq,bq⟩ := hf
  refine ⟨fun an => |q an|, by fun_prop, ?_⟩
  intro a n
  simpa only [Rat.cast_abs] using (abs_abs_sub_abs_le (f a) (q (a,n))).trans (bq a n)

theorem Effective.inv {f : A → ℝ} (hf : Effective f) (hzero : ∀ a, f a ≠ 0) :
    Effective (fun a => (f a)⁻¹) := by
  obtain ⟨q,hq,bq⟩ := hf
  let test (an : A × ℕ) (k : ℕ) : Prop :=
    qerror k < |q (an.1,k)| ∧
    qerror k / ((|q (an.1,k)| - qerror k) * |q (an.1,k)|) ≤ qerror an.2
  have existsGood : ∀ an : A × ℕ, ∃ k, test an k := by
    intro an
    have hq' := Effective.approximants_tendsto bq an.1
    have hpos : 0 < |f an.1| := abs_pos.mpr (hzero _)
    have hlt : ∀ᶠ k in atTop, error k < |(q (an.1,k) : ℝ)| :=
      Filter.Tendsto.eventually_lt error_tendsto hq'.abs hpos
    have hlim : Tendsto (fun k => error k /
        ((|(q (an.1,k) : ℝ)| - error k) * |(q (an.1,k) : ℝ)|)) atTop (𝓝 0) := by
      convert error_tendsto.div ((hq'.abs.sub error_tendsto).mul hq'.abs)
        (mul_ne_zero (by simpa using hpos.ne') hpos.ne') using 1
      simp
    obtain ⟨k,hk,hk'⟩ := (hlt.and (hlim.eventually (gt_mem_nhds (error_pos an.2)))).exists
    refine ⟨k, ?_, ?_⟩
    · exact_mod_cast (show (qerror k : ℝ) < |(q (an.1,k) : ℝ)| by simpa using hk)
    · exact_mod_cast (show (qerror k : ℝ) /
          ((|(q (an.1,k) : ℝ)| - (qerror k : ℝ)) * |(q (an.1,k) : ℝ)|) ≤ (qerror an.2 : ℝ) by
          simpa using hk'.le)
  have htest : Computable (fun p : (A × ℕ) × ℕ => decide (test p.1 p.2)) := by
    simp only [test, Bool.decide_and]
    apply (Primrec.and.to_comp.comp _ _)
    · exact RecursiveArithmetic.ratLT.decide.to_comp.comp (by fun_prop) (by fun_prop)
    · exact RecursiveArithmetic.ratLE.decide.to_comp.comp (by fun_prop) (by fun_prop)
  let pick (an : A × ℕ) := Nat.find (existsGood an)
  have hpick := computable_find (A := A × ℕ) (p := test) htest existsGood
  refine ⟨fun an => (q (an.1,pick an))⁻¹, by fun_prop, ?_⟩
  intro a n
  have htest' := Nat.find_spec (existsGood (a,n))
  let k := pick (a,n)
  have hk : error k < |(q (a,k) : ℝ)| := by
    rw [← cast_qerror]
    exact_mod_cast htest'.1
  have hk' : error k / ((|(q (a,k) : ℝ)| - error k) * |(q (a,k) : ℝ)|) ≤ error n := by
    rw [← cast_qerror k, ← cast_qerror n]
    exact_mod_cast htest'.2
  have hqne : (q (a,k) : ℝ) ≠ 0 := abs_pos.mp ((error_pos k).trans hk)
  have hlower : |(q (a,k) : ℝ)| - error k ≤ |f a| := by
    have hb := (abs_sub_abs_le_abs_sub (q (a,k) : ℝ) (f a)).trans
      (by simpa only [abs_sub_comm] using bq a k)
    linarith
  rw [Rat.cast_inv, inv_sub_inv (hzero a) hqne, abs_div, abs_mul, abs_sub_comm]
  calc
    |f a - (q (a,k) : ℝ)| / (|f a| * |(q (a,k) : ℝ)|) ≤
        error k / ((|(q (a,k) : ℝ)| - error k) * |(q (a,k) : ℝ)|) := by
      apply div_le_div₀ (error_pos k).le (bq a k) (mul_pos (sub_pos.mpr hk) ((error_pos k).trans hk))
      exact mul_le_mul_of_nonneg_right hlower (abs_nonneg _)
    _ ≤ _ := hk'

theorem Effective.div {f g : A → ℝ} (hf : Effective f) (hg : Effective g) (hz : ∀ a, g a ≠ 0) :
    Effective (fun a => f a / g a) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv hz)

theorem Effective.pow {f : A → ℝ} (hf : Effective f) {m : A → ℕ} (hm : Computable m) :
    Effective (fun a => f a ^ m a) := by
  obtain ⟨q,hq,bq⟩ := hf
  refine of_enclosures (q := fun an => q an ^ m an.1)
    (e := fun an => qerror an.2 * (m an.1 : ℚ) * (|q an| + qerror an.2) ^ (m an.1 - 1))
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro a n
    simp only [Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast, Rat.cast_add, Rat.cast_abs, cast_qerror]
    have hfbound : |f a| ≤ |(q (a,n) : ℝ)| + error n := by
      have ht := (abs_add_le (f a - (q (a,n) : ℝ)) (q (a,n) : ℝ)).trans
        (add_le_add (bq a n) le_rfl)
      rw [sub_add_cancel] at ht
      exact ht.trans_eq (add_comm _ _)
    apply (abs_pow_sub_pow_le (f a) (q (a,n)) (m a)).trans
    apply mul_le_mul (mul_le_mul_of_nonneg_right (bq a n) (Nat.cast_nonneg _))
      (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _))
        (max_le hfbound (le_add_of_nonneg_right (error_pos n).le)) _) (by positivity)
      (mul_nonneg (error_pos n).le (Nat.cast_nonneg _))
  · intro a
    have ha := Effective.approximants_tendsto bq a
    simpa using (error_tendsto.mul_const (m a : ℝ)).mul
      ((ha.abs.add error_tendsto).pow (m a - 1))

end
end CertifiedReal
namespace CertifiedReal
open Encodable Filter Topology
local instance elementaryFunctionsLocal2 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A B : Type*} [Primcodable A] [Primcodable B]

@[fun_prop] theorem computable_sum {m : A → ℕ} {f : A → ℕ → ℚ}
    (hm : Computable m) (hf : Computable₂ f) :
    Computable (fun a => ∑ i ∈ Finset.range (m a), f a i) := by
  have hv := hf.comp (g := fun p : A × (ℕ × ℚ) => p.1)
    (h := fun p => p.2.1) Computable.fst (Computable.fst.comp Computable.snd)
  have hstep := RecursiveArithmetic.rat_add.to_comp.comp
    (g := fun p : A × (ℕ × ℚ) => (p.2.2, f p.1 p.2.1))
    ((Computable.snd.comp Computable.snd).pair hv)
  exact (Computable.nat_rec hm (Computable.const 0) hstep.to₂).of_eq (fun a => by
    induction m a with
    | zero => simp
    | succ n ih => simp [Finset.sum_range_succ, ih])

theorem rat_abs_bound (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have heq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [heq, abs_div, abs_of_pos (show (0 : ℝ) < (q.den : ℝ) from Nat.cast_pos.mpr q.den_pos), ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]
  exact (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast q.den_pos)).trans le_rfl

theorem Effective.exp {f : A → ℝ} (hf : Effective f) : Effective (fun a => Real.exp (f a)) := by
  obtain ⟨q,hq,bq⟩ := hf
  let M (a : A) : ℕ := (q (a,0)).num.natAbs + 3
  have hM : Computable M := by unfold M; fun_prop
  have b (a : A) (n : ℕ) : |(q (a,n) : ℝ)| ≤ (M a : ℝ) := by
    have hf0 : |f a| ≤ (q (a,0)).num.natAbs + 1 := by
      have ht := (abs_add_le (f a - q (a,0)) (q (a,0))).trans
        (add_le_add ((bq a 0).trans (error_le_one 0)) (rat_abs_bound _))
      rw [sub_add_cancel] at ht
      linarith
    have ht := (abs_add_le ((q (a,n) : ℝ) - f a) (f a)).trans
      (add_le_add (by simpa only [abs_sub_comm] using (bq a n).trans (error_le_one n)) hf0)
    rw [sub_add_cancel] at ht
    dsimp [M]; push_cast; linarith
  have diff (a : A) (n : ℕ) :
      |Real.exp (f a) - Real.exp (q (a,n))| ≤ 2 * 3 ^ M a * error n := by
    have he := Real.abs_exp_sub_one_le ((bq a n).trans (error_le_one n))
    have hqM : Real.exp (q (a,n)) ≤ 3 ^ M a := by
      apply (Real.exp_le_exp.mpr ((le_abs_self _).trans (b a n))).trans
      simpa only [← Real.exp_nat_mul, mul_one] using
        (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le (M a))
    calc
      |Real.exp (f a) - Real.exp (q (a,n))| =
          |Real.exp (f a - q (a,n)) - 1| * Real.exp (q (a,n)) := by
        have heq : Real.exp (f a) - Real.exp (q (a,n)) =
            (Real.exp (f a - q (a,n)) - 1) * Real.exp (q (a,n)) := by
          rw [sub_mul, one_mul, ← Real.exp_add, sub_add_cancel]
        rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ (2 * error n) * 3 ^ M a :=
        mul_le_mul (he.trans (mul_le_mul_of_nonneg_left (bq a n) (by norm_num))) hqM
          (Real.exp_pos _).le (mul_nonneg (by norm_num) (error_pos n).le)
      _ = _ := by ring
  let N (a : A) (n : ℕ) := 2 * M a + 1 + n
  refine of_enclosures
    (q := fun an => ∑ i ∈ Finset.range (N an.1 an.2), q an ^ i / (i.factorial : ℚ))
    (e := fun an => 2 * 3 ^ M an.1 * qerror an.2 +
      2 * (M an.1 : ℚ) ^ N an.1 an.2 / (N an.1 an.2).factorial)
    (by
      apply computable_sum
      · unfold N; fun_prop
      · change Computable (fun p : (A × ℕ) × ℕ => q p.1 ^ p.2 / (p.2.factorial : ℚ))
        fun_prop)
    (by unfold N; fun_prop) ?_ ?_
  · intro a n
    have htail := Complex.exp_bound' (x := (q (a,n) : ℝ)) (n := N a n) (by
      rw [Complex.norm_real, Real.norm_eq_abs]
      apply (div_le_div_of_nonneg_right (b a n) (by positivity)).trans
      apply (div_le_iff₀ (by positivity)).mpr
      dsimp [N]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have htail' : |Real.exp (q (a,n)) - ∑ i ∈ Finset.range (N a n), (q (a,n) : ℝ)^i / i.factorial| ≤
        2 * (M a : ℝ) ^ N a n / (N a n).factorial := by
      have htailR : |Real.exp (q (a,n)) - ∑ i ∈ Finset.range (N a n), (q (a,n) : ℝ)^i / i.factorial| ≤
          |(q (a,n) : ℝ)| ^ N a n / (N a n).factorial * 2 := by
        simpa only [← Complex.ofReal_exp, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
          ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs] using htail
      apply htailR.trans
      rw [div_mul_eq_mul_div, mul_comm _ (2 : ℝ)]
      gcongr
      exact b a n
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_sum, cast_qerror]
    exact (abs_sub_le _ _ _).trans (add_le_add (diff a n) htail')
  · intro a
    have hn : Tendsto (fun n => N a n) atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => show n ≤ N a n by dsimp [N]; omega) tendsto_id
    have ht := (Real.summable_pow_div_factorial (M a : ℝ)).tendsto_atTop_zero.comp hn
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast,
      cast_qerror, Rat.cast_div, Function.comp_apply, mul_div_assoc, mul_zero, add_zero] using
      (error_tendsto.const_mul (2 * 3 ^ M a)).add (ht.const_mul 2)

end
end CertifiedReal

namespace CertifiedReal
open Encodable Filter Topology Finset
local instance elementaryFunctionsLocal3 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A : Type*} [Primcodable A]

@[fun_prop] theorem piTerm_recursive : Primrec (fun i : ℕ => (-1 : ℚ)^i / (2 * (i : ℚ) + 1)) := by
  have ht := RecursiveArithmetic.rat_pow.comp ((Primrec.const (-1)).pair Primrec.id)
  have hd := RecursiveArithmetic.rat_add.comp
    ((RecursiveArithmetic.rat_mul.comp ((Primrec.const 2).pair RecursiveArithmetic.ratNat)).pair (Primrec.const 1))
  exact RecursiveArithmetic.rat_div.comp (ht.pair hd)

@[fun_prop] theorem piApprox_recursive : Primrec (fun n : ℕ =>
    4 * ∑ i ∈ range (2*n), (-1 : ℚ)^i / (2*i+1)) := by
  have hm : Primrec (fun n : ℕ => 2*n) := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  have hs := RecursiveArithmetic.sumRangeRat hm (piTerm_recursive.comp Primrec.snd).to₂
  exact RecursiveArithmetic.rat_mul.comp ((Primrec.const 4).pair hs)

theorem pi : Effective (fun _ : A => Real.pi) := by
  refine of_enclosures
    (q := fun an => 4 * ∑ i ∈ range (2 * an.2), (-1 : ℚ) ^ i / (2 * i + 1))
    (e := fun an => 4 * qerror an.2)
    (piApprox_recursive.to_comp.comp Computable.snd) (by fun_prop) ?_ ?_
  · intro a n
    have hl : Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i * (1 / (2 * i + 1))) atTop (𝓝 (Real.pi / 4)) := by
      simpa only [mul_one_div] using Real.tendsto_sum_pi_div_four
    have hanti : Antitone (fun i : ℕ => (1 : ℝ) / (2 * i + 1)) := by
      intro k m hkm
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show 2*k+1 ≤ 2*m+1 from by omega))
    have hlo := hanti.alternating_series_le_tendsto hl n
    have hhi := hanti.tendsto_le_alternating_series hl n
    simp only [sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul] at hhi
    have hfrac : (1 : ℝ) / (2 * ↑(2*n) + 1) ≤ error n := by unfold error; push_cast; gcongr; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_neg, Rat.cast_one, Rat.cast_add, Rat.cast_natCast, cast_qerror]
    simp only [mul_one_div] at hlo hhi
    rw [abs_of_nonneg (by linarith)]
    linarith
  · intro a
    simpa using error_tendsto.const_mul 4

end
end CertifiedReal

end
end PeriodicLattice

end OAI
