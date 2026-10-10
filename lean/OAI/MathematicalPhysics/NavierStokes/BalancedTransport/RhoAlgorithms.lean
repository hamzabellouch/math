import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveExp
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RelativeForce

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

def rhoCoeffStep (cs : List ℤ) : List ℤ :=
  0 :: 0 :: (List.range cs.length).map (fun j =>
    cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0)

def rhoCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => rhoCoeffStep (rhoCoeffs n)

lemma primrec_rhoCoeffStep : Primrec rhoCoeffStep := by
  have h : Primrec₂ (fun cs : List ℤ => fun j : ℕ =>
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0) := by
    have h₁ : Primrec (fun p : List ℤ × ℕ => (p.2 + 1 : ℤ)) := by
      exact (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).of_eq
        (fun _ => by simp)
    exact (primrec_int_add.comp (Primrec.list_getD 0)
      (primrec_int_neg.comp (primrec_int_mul.comp h₁
        ((Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp Primrec.snd))))).of_eq
          (fun _ => (sub_eq_add_neg _ _).symm)
  exact Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp
    (Primrec.const 0) (Primrec.list_map (Primrec.list_range.comp Primrec.list_length) h))

lemma primrec_rhoCoeffs : Primrec rhoCoeffs := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => List ℤ)
      [1] (fun _ cs => rhoCoeffStep cs) n) :=
    Primrec.nat_rec (Primrec.const [1])
      (primrec_rhoCoeffStep.comp (Primrec.snd.comp Primrec.snd)).to₂
  refine (h.comp (Primrec.const ()) Primrec.id).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg rhoCoeffStep ih

lemma getD_zero_of_length_le {cs : List ℤ} {j : ℕ} (h : cs.length ≤ j) :
    cs.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma rhoCoeffStep_getD (cs : List ℤ) (j : ℕ) :
    (rhoCoeffStep cs).getD (j + 2) 0 =
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0 := by
  simp only [rhoCoeffStep, List.getD_cons_succ]
  by_cases hj : j < cs.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  · have hj' : cs.length ≤ j := le_of_not_gt hj
    rw [getD_zero_of_length_le (by simpa using hj'), getD_zero_of_length_le hj',
      getD_zero_of_length_le (by omega)]
    simp

lemma rhoCoeffs_spec (n j : ℕ) : (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  induction n generalizing j with
  | zero =>
    cases j <;> simp [rhoCoeffs, rhoPolynomial, List.getD_eq_getElem?_getD, coeff_one]
  | succ n ih =>
    cases j with
    | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial]
    | succ j =>
      cases j with
      | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial, coeff_X_pow_mul']
      | succ j =>
        rw [show j + 1 + 1 = j + 2 by omega, rhoCoeffs, rhoCoeffStep_getD,
          rhoPolynomial, coeff_X_pow_mul, coeff_sub, coeff_derivative, ← ih, ← ih]
        ring

lemma rhoCoeffs_length (n : ℕ) : (rhoCoeffs n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rhoCoeffs, rhoCoeffStep, List.length_cons, List.length_map,
      List.length_range, ih]; omega

lemma rhoPolynomial_coeff_zero (n j : ℕ) (h : (rhoCoeffs n).length ≤ j) :
    (rhoPolynomial n).coeff j = 0 := by
  rw [← rhoCoeffs_spec, getD_zero_of_length_le h]

lemma rhoPolynomial_support_subset (n : ℕ) :
    (rhoPolynomial n).support ⊆ Finset.range (rhoCoeffs n).length := by
  intro j hj
  rw [Finset.mem_range]
  by_contra h
  exact (mem_support_iff.mp hj) (rhoPolynomial_coeff_zero _ _ (le_of_not_gt h))

def rhoBound (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length,
    ((rhoCoeffs n).getD j 0).natAbs * (j + k).factorial

lemma primrec_sum_range_nat {α : Type*} [Primcodable α]
    {f : α → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Primrec₂ (fun a n => Nat.rec (motive := fun _ => ℕ) 0
      (fun j r => r + f a j) n) :=
    Primrec.nat_rec (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
        (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine hh.of_eq ?_
  intro a n
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

lemma primrec_rhoBound : Primrec₂ rhoBound := by
  have hh : Primrec₂ (fun p : ℕ × ℕ => fun j =>
      ((rhoCoeffs p.1).getD j 0).natAbs * (j + p.2).factorial) :=
    Primrec.nat_mul.comp
      (primrec_int_natAbs.comp ((Primrec.list_getD 0).comp
        (primrec_rhoCoeffs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (primrec_nat_factorial.comp (Primrec.nat_add.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)))
  exact (primrec_sum_range_nat hh).comp Primrec.id
    (Primrec.list_length.comp (primrec_rhoCoeffs.comp Primrec.fst))

lemma rhoBound_eq (n k : ℕ) : rhoBound n k = rhoWeight (rhoPolynomial n) k := by
  unfold rhoBound rhoWeight
  simp only [rhoCoeffs_spec]
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rhoJet_bound_computable (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoBound n 0 : ℝ) := by
  rw [rhoBound_eq]
  exact rhoJet_bound n x

def rhoPolyValue (n : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoCoeffs n).getD j 0 : ℚ) * q ^ j

lemma computable_rhoPolyValue : Computable₂ rhoPolyValue := by
  have hh : Computable₂ (fun p : ℕ × ℚ => fun j =>
      ((rhoCoeffs p.1).getD j 0 : ℚ) * p.2 ^ j) :=
    computable_rat_mul.comp
      (computable_rat_intCast.comp ((Primrec.list_getD 0).to_comp.comp
        (primrec_rhoCoeffs.to_comp.comp (Computable.fst.comp Computable.fst)) Computable.snd))
      (computable_rat_pow.comp (Computable.snd.comp Computable.fst) Computable.snd)
  exact (computable_sum_range hh).comp Computable.id
    (Primrec.list_length.to_comp.comp (primrec_rhoCoeffs.to_comp.comp Computable.fst))

lemma rhoPolyValue_cast (n : ℕ) (q : ℚ) :
    (rhoPolyValue n q : ℝ) = (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) (q : ℝ) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [rhoPolyValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow,
    rhoCoeffs_spec]
  change (∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoPolynomial n).coeff j : ℝ) * (q : ℝ) ^ j) = _
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  have ha : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs q.num)
  rw [← ha]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < q.den)).mpr
    (le_mul_of_one_le_right (by positivity) hden)

noncomputable def rhoApprox (n : ℕ) (q : ℚ) (p : ℕ) : ℚ :=
  if q ≤ 0 then 0 else
    rhoPolyValue n q⁻¹ * expApprox (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)

lemma computable_rhoApprox : Computable (fun s : ℕ × ℚ × ℕ => rhoApprox s.1 s.2.1 s.2.2) := by
  have hq : Computable (fun s : ℕ × ℚ × ℕ => s.2.1⁻¹) :=
    computable_rat_inv.comp (Computable.fst.comp Computable.snd)
  have hv : Computable (fun s : ℕ × ℚ × ℕ => rhoPolyValue s.1 s.2.1⁻¹) :=
    computable_rhoPolyValue.comp Computable.fst hq
  exact computable_ite (computable_rat_le.comp (Computable.fst.comp Computable.snd)
    (Computable.const 0)) (Computable.const 0)
    (computable_rat_mul.comp hv (computable_expApprox.comp (computable_rat_neg.comp hq)
      (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
        (primrec_int_natAbs.to_comp.comp (computable_rat_num.comp hv)))))

lemma rhoApprox_spec (n : ℕ) (q : ℚ) (p : ℕ) :
    |(rhoApprox n q p : ℝ) - rhoJet n (q : ℝ)| ≤ error p := by
  by_cases hq : q ≤ 0
  · simp [rhoApprox, hq, rhoJet_zero_of_nonpos n (Rat.cast_nonpos.mpr hq), error_nonneg]
  · have hqp : (0 : ℝ) < q := Rat.cast_pos.mpr (lt_of_not_ge hq)
    rw [rhoApprox, ite_eq_right hq, Rat.cast_mul]
    have hid : rhoJet n (q : ℝ) = (rhoPolyValue n q⁻¹ : ℝ) * Real.exp (-((q : ℝ)⁻¹)) := by
      rw [rhoJet, expNegInvGlue, ite_eq_right hqp.not_ge, rhoPolyValue_cast, Rat.cast_inv]
    rw [hid, ← mul_sub, abs_mul]
    have he := expApprox_spec (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)
    simp only [Rat.cast_neg, Rat.cast_inv] at he
    exact (mul_le_mul (rat_abs_le_num _) he (abs_nonneg _) (by positivity)).trans
      (nat_mul_error_shift _ _)

lemma rhoJet_lipschitz (n : ℕ) : LipschitzWith (rhoBound (n + 1) 0 : ℝ≥0) (rhoJet n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (rhoJet_hasDerivAt n x).differentiableAt)
  intro x
  rw [(rhoJet_hasDerivAt n x).deriv]
  exact_mod_cast rhoJet_bound_computable (n + 1) x

end BalancedTransport.Effectivity
end

end OAI
