import OAI.Analysis.PeriodicLattice.EffectiveProfiles

namespace OAI

/-! Effective planar estimates and periodic pressure operators. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEffectivePotentials {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic
open scoped ContDiff
local instance effectivePotentialsLocal1 : Primcodable ℚ := ratPrimcodable
local instance effectivePotentialsLocal2 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectivePotentialsLocal3 : Primcodable ValidInput := Primcodable.subtype inputWellFormed

theorem bi_diff {F : Input → ℝ → ℝ → ℝ} (hF : BiCertificate F)
    (hf : Effective (fun p : ValidInput × BiPoint => biValue (F p.1.1) p.2)) (i : Bool) :
    Effective (fun p : ValidInput × BiPoint => biValue (biD i (F p.1.1)) p.2) :=
  (bi_words hF hf).comp (Primrec.fst.pair ((Primrec.const [i]).pair Primrec.snd)).to_comp

theorem bi_estimate {F : Input → ℝ → ℝ → ℝ} (hF : BiCertificate F) (d : ValidInput)
    (w : List Bool) (n : ℕ) (hn : w.length ≤ n) (t : ℝ) (ht : 0 ≤ t) (y : ℝ) :
    |wordD w (F d.1) t y| ≤ (hF.budget (d.1,n,0) : ℝ) := by
  simpa only [pow_zero,one_mul,Real.norm_eq_abs] using hF.estimate d.1 d.2 w n 0 hn t ht y

theorem bi_mean {F : Input → ℝ → ℝ → ℝ} (hF : BiCertificate F)
    (hf : Effective (fun p : ValidInput × BiPoint => biValue (F p.1.1) p.2)) :
    Effective (fun p : ValidInput × BiPoint => biValue (PeriodicInverse.mean (F p.1.1)) p.2) := by
  have hv := hf.comp (g := fun p : (ValidInput × BiPoint) × ℚ => (p.1.1,p.1.2.1,p.2)) (by fun_prop)
  have harg : Primrec (fun p : ValidInput × BiPoint => (p.1.1,1,0)) :=
    (validData_recursive.comp Primrec.fst).pair (Primrec.const (1,0))
  refine integral (f := fun (p : ValidInput × BiPoint) s => F p.1.1 (time p.2.1) s) hv
    (fun p => ((hF.smooth p.1.1).continuous.comp (continuous_const.prodMk continuous_id)))
    (fun p : ValidInput × BiPoint => hF.budget (p.1.1,1,0))
    ((hF.recursive.comp harg).of_eq (fun _ => rfl)).to_comp ?_
  intro p x hx y hy
  have hd (s : ℝ) : HasDerivAt (F p.1.1 (time p.2.1)) (biD false (F p.1.1) (time p.2.1) s) s :=
    (((hF.smooth p.1.1).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s).hasDerivAt
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s _ => (hd s).hasDerivWithinAt)
    (fun s _ => bi_estimate hF p.1 [false] 1 le_rfl _ (time_nonneg _) s)
    (convex_Icc (0:ℝ) 1) hy hx

theorem bi_first {F : Input → ℝ → ℝ → ℝ} (hF : BiCertificate F)
    (hf : Effective (fun p : ValidInput × BiPoint => biValue (F p.1.1) p.2))
    (lam : ℝ) (hlam : lam ≠ 0) (he : Effective (fun _ : Unit => lam)) :
    Effective (fun p : ValidInput × BiPoint => biValue (PeriodicInverse.first lam (F p.1.1)) p.2) := by
  have hv : Effective (fun p : (ValidInput × BiPoint) × ℚ =>
      Real.exp (lam * (p.2:ℝ)) * F p.1.1.1 (time p.1.2.1) ((p.1.2.2:ℝ) - p.2)) := by
    have hl := he.comp (Computable.const ()) (A := ((ValidInput × BiPoint) × ℚ))
    have harg : Computable (fun p : (ValidInput × BiPoint) × ℚ => (p.1.1,p.1.2.1,p.1.2.2-p.2)) := by fun_prop
    exact ((hl.mul (rational Computable.snd)).exp.mul (hf.comp harg)).congr (fun p => by simp only [biValue,Rat.cast_sub])
  let M := ⌈Real.exp |lam| * (|lam|+1)⌉₊
  have hb : Real.exp |lam| * (|lam|+1) ≤ (M:ℝ) := Nat.le_ceil _
  have hbudget : Computable (fun p : ValidInput × BiPoint => M * hF.budget (p.1.1,1,0)) := by
    have ha : Primrec (fun p : ValidInput × BiPoint => (p.1.1,1,0)) :=
      (validData_recursive.comp Primrec.fst).pair (Primrec.const (1,0))
    exact ((Primrec.nat_mul.comp (Primrec.const M) (hF.recursive.comp ha)).of_eq (fun _ => rfl)).to_comp
  have hi := integral (f := fun (p : ValidInput × BiPoint) s => Real.exp (lam*s) * F p.1.1 (time p.2.1) ((p.2.2:ℝ)-s)) hv (fun p => by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((hF.smooth p.1.1).continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))))
    (fun p : ValidInput × BiPoint => M * hF.budget (p.1.1,1,0)) hbudget (by
      intro p x hx y hy
      have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (lam*s) * F p.1.1 (time p.2.1) ((p.2.2:ℝ)-s))
          (Real.exp (lam*s)*lam*F p.1.1 (time p.2.1) ((p.2.2:ℝ)-s) +
            Real.exp (lam*s)*(biD false (F p.1.1) (time p.2.1) ((p.2.2:ℝ)-s)*(-1))) s := by
        have hh : HasDerivAt (F p.1.1 (time p.2.1))
            (biD false (F p.1.1) (time p.2.1) ((p.2.2:ℝ)-s)) ((p.2.2:ℝ)-s) :=
          (((hF.smooth p.1.1).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _).hasDerivAt
        simpa only [mul_one, Function.comp_def, Pi.mul_def, id_eq] using
          (((hasDerivAt_id s).const_mul lam).exp).mul (hh.comp s ((hasDerivAt_id s).const_sub (p.2.2:ℝ)))
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s _ => (hd s).hasDerivWithinAt) _ (convex_Icc (0:ℝ) 1) hy hx
      intro s hs
      have he' : |Real.exp (lam*s)| ≤ Real.exp |lam| := by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          lam*s ≤ |lam| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs.1
          _ ≤ |lam| := mul_le_of_le_one_right (abs_nonneg _) hs.2
      have h0 := bi_estimate hF p.1 [] 1 (by simp) (time p.2.1) (time_nonneg p.2.1) ((p.2.2:ℝ)-s)
      have h1 := bi_estimate hF p.1 [false] 1 le_rfl (time p.2.1) (time_nonneg p.2.1) ((p.2.2:ℝ)-s)
      simp only [Real.norm_eq_abs]
      calc
        _ ≤ |Real.exp (lam*s)*lam*F p.1.1 (time p.2.1) ((p.2.2:ℝ)-s)| +
            |Real.exp (lam*s)*(biD false (F p.1.1) (time p.2.1) ((p.2.2:ℝ)-s)*(-1))| := abs_add_le _ _
        _ ≤ Real.exp |lam| * |lam| * (hF.budget (p.1.1,1,0):ℝ) +
            Real.exp |lam| * (hF.budget (p.1.1,1,0):ℝ) := by
          simp only [abs_mul, abs_neg, abs_one, mul_one]
          exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right he' (abs_nonneg _)) h0 (abs_nonneg _) (by positivity))
            (mul_le_mul he' h1 (abs_nonneg _) (by positivity))
        _ = (Real.exp |lam| * (|lam|+1)) * (hF.budget (p.1.1,1,0):ℝ) := by ring
        _ ≤ (M * hF.budget (p.1.1,1,0):ℕ) := by
          rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))
  have hh := (((constant (A := ValidInput × BiPoint) 1).sub ((he.comp (Computable.const ())).exp)).inv
    (fun _ => sub_ne_zero.mpr ((fun h => hlam (Real.exp_injective (by simpa only [Real.exp_zero,Rat.cast_one] using h.symm)))))).mul hi
  exact hh.congr (fun p => by dsimp only [biValue,PeriodicInverse.first]; norm_num)

theorem bdy_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.bdy p.1.1) p.2) :=
  bi_diff bCertificate b_base false

theorem pressureSource_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.pressureSource p.1.1) p.2) :=
  (bdy_base.mul bdy_base).sub (b_base.mul (bi_diff (bCertificate.diff false) bdy_base false))

theorem pressureBase_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.pressureBase p.1.1) p.2) := by
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,biValue,FluidLift.pressureBase,Pi.mul_def] using
    (constant (A := ValidInput × BiPoint) (1/2)).mul
      ((b_base.mul b_base).sub (bi_mean (bCertificate.mul bCertificate) (b_base.mul b_base)))

theorem pressureMode_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.pressureMode p.1.1) p.2) := by
  have he : Effective (fun _ : Unit => 4*Real.pi) := by
    simpa only [Rat.cast_ofNat] using (constant (A := Unit) 4).mul pi
  exact bi_first (pressureSourceCertificate.first (4*Real.pi))
    (bi_first pressureSourceCertificate pressureSource_base (4*Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero) he)
    (-(4*Real.pi)) (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) he.neg
end EffectiveFields
namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic
open scoped ContDiff
local instance effectivePotentialsLocal4 : Primcodable ℚ := ratPrimcodable
local instance effectivePotentialsLocal5 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectivePotentialsLocal6 : Primcodable ValidInput := Primcodable.subtype inputWellFormed

def fieldValue (F : ScalarField) (p : RationalPoint) : ℝ := F (time p.1) (torusMk (rationalVector p.2))

def fieldShift (i : Option (Fin 3)) (p : RationalPoint) (n : ℕ) : RationalPoint :=
  match i with
  | none => (max p.1 0 + qerror n, p.2)
  | some j => (p.1, fun k => if k = j then p.2 k + qerror n else p.2 k)

@[fun_prop] theorem fieldShift_recursive : Primrec (fun p : Option (Fin 3) × RationalPoint × ℕ => fieldShift p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Option (Fin 3) × RationalPoint × ℕ => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hx : Primrec (fun p : Option (Fin 3) × RationalPoint × ℕ => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have he : Primrec (fun p : Option (Fin 3) × RationalPoint × ℕ => qerror p.2.2) :=
    qerror_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : Option (Fin 3) × RationalPoint × ℕ => (max p.2.1.1 0 + qerror p.2.2,p.2.1.2)) :=
    (rat_add.comp ((ratMax.comp (ht.pair (Primrec.const 0))).pair he)).pair hx
  have hs : Primrec (fun p : (Option (Fin 3) × RationalPoint × ℕ) × Fin 3 =>
      (p.1.2.1.1,fun k => if k = p.2 then p.1.2.1.2 k + qerror p.1.2.2 else p.1.2.1.2 k)) := by
    refine (ht.comp Primrec.fst).pair (Primrec.fin_curry.mpr ?_)
    have hv : Primrec (fun p : ((Option (Fin 3) × RationalPoint × ℕ) × Fin 3) × Fin 3 => p.1.1.2.1.2 p.2) :=
      Primrec.fin_app.comp (hx.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
    exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (rat_add.comp (hv.pair (he.comp (Primrec.fst.comp Primrec.fst)))) hv
  exact (Primrec.option_casesOn Primrec.fst hn hs.to₂).of_eq (fun p => by cases p.1 <;> rfl)

def fieldLine (i : Option (Fin 3)) (t : ℝ) (q : Torus) (s : ℝ) : ℝ × Torus :=
  match i with
  | none => (t+s,q)
  | some j => (t,q+torusMk (EuclideanSpace.single j s))

@[simp] theorem fieldLine_zero (i : Option (Fin 3)) (t : ℝ) (q : Torus) : fieldLine i t q 0 = (t,q) := by
  cases i <;> simp [fieldLine,single_zero,mk_zero]

theorem fieldLine_nonneg (i : Option (Fin 3)) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (q : Torus) :
    0 ≤ (fieldLine i t q s).1 := by cases i <;> simp [fieldLine] <;> positivity

theorem fieldShift_value (i : Option (Fin 3)) (p : RationalPoint) (n : ℕ) (F : ScalarField) :
    fieldValue F (fieldShift i p n) =
      F (fieldLine i (time p.1) (torusMk (rationalVector p.2)) (error n)).1
        (fieldLine i (time p.1) (torusMk (rationalVector p.2)) (error n)).2 := by
  cases i with
  | none =>
    have h : 0 ≤ max (p.1:ℝ) 0 + error n := add_nonneg (le_max_right _ _) (error_pos n).le
    simp [fieldValue,fieldShift,fieldLine,max_eq_left h]
  | some j =>
    dsimp only [fieldValue,fieldShift,fieldLine]
    congr 2
    rw [← mk_add]
    congr 1
    ext k
    by_cases hk : k = j
    · subst k; simp [rationalVector]
    · simp [rationalVector,hk]

theorem fieldLine_deriv {F : ScalarField} (hF : ContDiff ℝ ∞ (lifted F))
    (i : Option (Fin 3)) (t : ℝ) (q : Torus) (s : ℝ) :
    HasDerivAt (fun z => F (fieldLine i t q z).1 (fieldLine i t q z).2)
      (coordD i F (fieldLine i t q s).1 (fieldLine i t q s).2) s := by
  cases i with
  | none =>
    simpa only [fieldLine,coordD,one_mul,mul_one,Function.comp_def] using
      (fullTime_hasDerivAt hF (t+s) q).comp s ((hasDerivAt_id s).const_add t)
  | some j => exact translation_hasDerivAt (smooth_slice_differentiable hF t) q j s

theorem field_words {F : Input → ScalarField} (hF : FieldCertificate F)
    (hbase : Effective (fun p : ValidInput × RationalPoint => fieldValue (F p.1.1) p.2)) :
    Effective (fun p : ValidInput × List (Option (Fin 3)) × RationalPoint => fieldValue (fieldWord p.2.1 (F p.1.1)) p.2.2) := by
  apply effective_words (A := ValidInput) (shift := fieldShift)
    (V := fun w (d : ValidInput) p => fieldValue (fieldWord w (F d.1)) p)
    fieldShift_recursive hbase (fun dn : ValidInput × ℕ => hF.budget (dn.1.1,dn.2+1,0))
  · apply Primrec.to_comp
    have ha : Primrec (fun dn : ValidInput × ℕ => (dn.1.1,dn.2+1,0)) :=
      (validData_recursive.comp Primrec.fst).pair ((Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).pair (Primrec.const 0))
    exact (hF.recursive.comp ha).of_eq (fun _ => rfl)
  intro d i w L hw p n
  have hs := fieldWord_contDiff (hF.smooth d.1) w
  have he := quotient_error (error_pos n)
    (fieldLine_deriv hs i (time p.1) (torusMk (rationalVector p.2)))
    (fieldLine_deriv (coordD_contDiff hs i) i (time p.1) (torusMk (rationalVector p.2)))
    (K := (hF.budget (d.1,L+1,0):ℝ)) (fun s hs => by
      have hb := hF.estimate d.1 d.2 (i::i::w) (L+1) 0
        (by simpa only [List.length_cons] using Nat.succ_le_succ hw)
        (fieldLine i (time p.1) (torusMk (rationalVector p.2)) s).1
        (fieldLine_nonneg i (time_nonneg p.1) hs.1 _)
        (fieldLine i (time p.1) (torusMk (rationalVector p.2)) s).2
      simpa only [pow_zero,one_mul,fieldWord_cons,Real.norm_eq_abs] using hb)
  rw [fieldShift_value]
  dsimp only [fieldValue,fieldWord_cons]
  simp only [fieldLine_zero] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (error_pos n).le)

theorem field_diff {F : Input → ScalarField} (hF : FieldCertificate F)
    (hf : Effective (fun p : ValidInput × RationalPoint => fieldValue (F p.1.1) p.2)) (i : Option (Fin 3)) :
    Effective (fun p : ValidInput × RationalPoint => fieldValue (coordD i (F p.1.1)) p.2) :=
  (field_words hF hf).comp (Primrec.fst.pair ((Primrec.const [i]).pair Primrec.snd)).to_comp

def ComponentsEffective (F : Input → VectorField) : Prop :=
  ∀ i : Fin 3, Effective (fun p : ValidInput × RationalPoint => F p.1.1 (time p.2.1) (torusMk (rationalVector p.2.2)) i)

theorem ComponentsEffective.diff {F : Input → VectorField} (hf : ComponentsEffective F)
    (hF : FieldCertificate F) (j : Option (Fin 3)) : ComponentsEffective (fun d => coordD j (F d)) := by
  intro i
  exact (field_diff (hF.component i) (hf i) j).congr (fun p => by
    dsimp only [fieldValue]
    rw [coordD_component (hF.smooth p.1.1)])

theorem ComponentsEffective.add {F G : Input → VectorField} (hf : ComponentsEffective F)
    (hg : ComponentsEffective G) : ComponentsEffective (fun d => F d + G d) := fun i => (hf i).add (hg i)

theorem ComponentsEffective.sub {F G : Input → VectorField} (hf : ComponentsEffective F)
    (hg : ComponentsEffective G) : ComponentsEffective (fun d => F d - G d) := fun i => (hf i).sub (hg i)

theorem ComponentsEffective.scale {F : Input → VectorField} (hf : ComponentsEffective F)
    (c : ℝ) (hc : Effective (fun _ : Unit => c)) : ComponentsEffective (fun d => c • F d) :=
  fun i => (hc.comp (Computable.const ())).mul (hf i)

end EffectiveFields

end
end PeriodicLattice

end OAI
