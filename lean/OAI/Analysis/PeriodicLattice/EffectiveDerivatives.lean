import OAI.Analysis.PeriodicLattice.Trigonometry

namespace OAI

/-! Certified finite differences and uniform field evaluation. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEffectiveDerivatives {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace CertifiedReal
open Encodable Filter Topology
local instance effectiveDerivativesLocal1 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section StencilBounds
variable {A B I : Type*} [Primcodable A] [Primcodable B] [Primcodable I]
variable (shift : I → B → ℕ → B) (q : (A × B) × ℕ → ℚ)

omit [Primcodable A] [Primcodable B] [Primcodable I] in
theorem difference_bound (V : List I → A → B → ℝ) (a : A) (L : ℕ) (K : ℝ)
    (hK : 1 ≤ K)
    (hbase : ∀ b n, |V [] a b - (q ((a,b),n) : ℝ)| ≤ error n)
    (htaylor : ∀ i w, (i::w).length ≤ L → ∀ b n,
      |V (i::w) a b - (V w a (shift i b n) - V w a b) / error n| ≤ K * error n)
    (w : List I) (hw : w.length ≤ L) (b : B) (n : ℕ) :
    |V w a b - (difference shift q w a b n : ℝ)| ≤ K * 3^w.length * error n := by
  induction w generalizing b n with
  | nil =>
    simpa only [List.length_nil, pow_zero, mul_one, difference] using
      (hbase b n).trans (le_mul_of_one_le_left (error_pos n).le hK)
  | cons i w ih =>
    have ht := htaylor i w hw b n
    have ha := ih (by simpa using Nat.le_of_succ_le hw) (shift i b n) (refinePrecision n)
    have hb := ih (by simpa using Nat.le_of_succ_le hw) b (refinePrecision n)
    rw [error_refine] at ha hb
    have hp : (1 : ℝ) ≤ 3^w.length := one_le_pow₀ (by norm_num)
    have hcoeff : 0 ≤ K * 3^w.length := mul_nonneg (by linarith) (by positivity)
    have hdiff : |(V w a (shift i b n) - V w a b) / error n -
        (difference shift q (i::w) a b n : ℝ)| ≤ 2*(K*3^w.length)*error n ^ 2 := by
      simp only [difference, Rat.cast_div, Rat.cast_sub, cast_qerror]
      have heq : (V w a (shift i b n) - V w a b) / error n -
          ((difference shift q w a (shift i b n) (refinePrecision n) : ℝ) -
            (difference shift q w a b (refinePrecision n) : ℝ)) / error n =
          ((V w a (shift i b n) - (difference shift q w a (shift i b n) (refinePrecision n) : ℝ)) -
            (V w a b - (difference shift q w a b (refinePrecision n) : ℝ))) / error n := by ring
      rw [heq, abs_div, abs_of_pos (error_pos n)]
      apply (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add ha hb)) (error_pos n).le).trans_eq
      field_simp [(error_pos n).ne']
      ring
    calc
      _ ≤ |V (i::w) a b - (V w a (shift i b n) - V w a b) / error n| +
          |(V w a (shift i b n) - V w a b) / error n - (difference shift q (i::w) a b n : ℝ)| := abs_sub_le _ _ _
      _ ≤ K * error n + 2*(K*3^w.length)*error n ^ 2 := add_le_add ht hdiff
      _ ≤ (K*3^w.length)*error n + 2*(K*3^w.length)*error n := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hp) (error_pos n).le
        · exact mul_le_mul_of_nonneg_left (by nlinarith [error_le_one n, error_pos n] : error n ^ 2 ≤ error n) (by positivity)
      _ = K*3^(i::w).length*error n := by simp only [List.length_cons, pow_succ]; ring

theorem effective_words (V : List I → A → B → ℝ)
    (hs : Primrec (fun p : I × B × ℕ => shift p.1 p.2.1 p.2.2))
    (hbase : Effective (fun p : A × B => V [] p.1 p.2))
    (K : A × ℕ → ℕ) (hK : Computable K)
    (htaylor : ∀ a i w L, (i::w).length ≤ L → ∀ b n,
      |V (i::w) a b - (V w a (shift i b n) - V w a b) / error n| ≤
        ((K (a,L) : ℝ)+1) * error n) :
    Effective (fun p : A × List I × B => V p.2.1 p.1 p.2.2) := by
  obtain ⟨q,hq,bq⟩ := hbase
  apply of_enclosures (q := fun p => difference shift q p.1.2.1 p.1.1 p.1.2.2 p.2)
    (e := fun p => ((K (p.1.1,p.1.2.1.length) : ℚ)+1)*3^p.1.2.1.length*qerror p.2)
  · exact difference_computable shift q hs hq
  · have hb : Computable (fun p : (A × List I × B) × ℕ => K (p.1.1,p.1.2.1.length)) :=
      hK.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))))
    fun_prop
  · intro p n
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat, cast_qerror] using
      difference_bound shift q V p.1 p.2.1.length ((K (p.1,p.2.1.length) : ℝ)+1)
        (by exact le_add_of_nonneg_left (Nat.cast_nonneg _)) (fun b n => bq (p.1,b) n)
        (fun i w hw => htaylor p.1 i w p.2.1.length hw) p.2.1 le_rfl p.2.2 n
  · intro p
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat, cast_qerror, mul_zero] using
      (tendsto_const_nhds.mul error_tendsto :
        Tendsto (fun n => (((K (p.1,p.2.1.length) : ℝ)+1)*3^p.2.1.length)*error n) atTop (𝓝 _))
end StencilBounds

theorem quotient_error {f f' f'' : ℝ → ℝ} {h K : ℝ} (hh : 0 < h)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ∀ s, HasDerivAt f' (f'' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 h, |f'' s| ≤ K) :
    |f' 0 - (f h - f 0)/h| ≤ K*h := by
  have hp (s : ℝ) (hs : s ∈ Set.Icc 0 h) : |f' s - f' 0| ≤ K*h := by
    have hv := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := h)
      (fun x _ => (hf' x).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x ⟨hx.1, hx.2.le⟩) s hs
    have hK : 0 ≤ K := (abs_nonneg (f'' 0)).trans (hbound 0 ⟨le_rfl,hh.le⟩)
    have hvs : |f' s - f' 0| ≤ K*s := by simpa only [Real.norm_eq_abs, sub_zero] using hv
    exact hvs.trans (mul_le_mul_of_nonneg_left hs.2 hK)
  have hd (s : ℝ) : HasDerivAt (fun x => f x - x * f' 0) (f' s - f' 0) s := by
    convert! (hf s).fun_sub ((hasDerivAt_id s).mul_const (f' 0)) using 1
    simp
  have hr := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := h)
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hp x ⟨hx.1, hx.2.le⟩) h ⟨hh.le,le_rfl⟩
  have heq : f' 0 - (f h - f 0)/h = -(f h - h * f' 0 - (f 0 - 0 * f' 0))/h := by field_simp [hh.ne']; ring
  rw [heq, abs_div, abs_neg, abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr (by simpa only [Real.norm_eq_abs, sub_zero] using hr)
end CertifiedReal
namespace RecursiveArithmetic
local instance effectiveDerivativesLocal2 : Primcodable ℚ := ratPrimcodable
@[fun_prop] theorem ratMax : Primrec (fun p : ℚ × ℚ => max p.1 p.2) := by
  exact (Primrec.ite ratLE Primrec.snd Primrec.fst).of_eq (fun p => by
    split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (le_of_not_ge h)).symm)
end RecursiveArithmetic

namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus
open scoped ContDiff
local instance effectiveDerivativesLocal3 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
local instance effectiveDerivativesLocal4 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectiveDerivativesLocal5 : Primcodable ValidInput := Primcodable.subtype RecursiveArithmetic.inputWellFormed

@[fun_prop] theorem validData_recursive : Primrec (fun d : ValidInput => d.1) := Primrec.subtype_val

def time (t : ℚ) : ℝ := (max t 0 : ℚ)
@[simp] theorem time_eq (t : ℚ) : time t = max (t : ℝ) 0 := by simp [time]
theorem time_nonneg (t : ℚ) : 0 ≤ time t := by simp

abbrev BiPoint := ℚ × ℚ
def biValue (F : ℝ → ℝ → ℝ) (p : BiPoint) : ℝ := F (time p.1) p.2

def biShift (i : Bool) (p : BiPoint) (n : ℕ) : BiPoint :=
  bif i then (max p.1 0 + qerror n, p.2) else (p.1,p.2+qerror n)

@[fun_prop] theorem biShift_recursive : Primrec (fun p : Bool × BiPoint × ℕ => biShift p.1 p.2.1 p.2.2) := by
  unfold biShift
  apply Primrec.cond Primrec.fst <;> fun_prop

def biLine (i : Bool) (t y s : ℝ) : ℝ × ℝ := bif i then (t+s,y) else (t,y+s)

@[simp] theorem biLine_zero (i : Bool) (t y : ℝ) : biLine i t y 0 = (t,y) := by cases i <;> simp [biLine]

theorem biLine_nonneg (i : Bool) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (y : ℝ) :
    0 ≤ (biLine i t y s).1 := by cases i <;> simp [biLine] <;> positivity

theorem biShift_value (i : Bool) (p : BiPoint) (n : ℕ) (F : ℝ → ℝ → ℝ) :
    biValue F (biShift i p n) =
      F (biLine i (time p.1) p.2 (error n)).1 (biLine i (time p.1) p.2 (error n)).2 := by
  cases i
  · simp [biShift, biValue, biLine]
  · have h : 0 ≤ max (p.1 : ℝ) 0 + error n := add_nonneg (le_max_right _ _) (error_pos n).le
    simp [biShift, biValue, biLine, max_eq_left h]

theorem biLine_deriv {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Bool) (t y s : ℝ) :
    HasDerivAt (fun z => F (biLine i t y z).1 (biLine i t y z).2)
      (biD i F (biLine i t y s).1 (biLine i t y s).2) s := by
  cases i
  · have hh : Differentiable ℝ (F t) := (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    convert! (hh (y+s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y) using 1
    simp [biLine,biD]
  · have hh : Differentiable ℝ (fun t => F t y) := (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    convert! (hh (t+s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add t) using 1
    simp [biLine,biD]

theorem bi_words {F : Input → ℝ → ℝ → ℝ} (hF : BiCertificate F)
    (hbase : Effective (fun p : ValidInput × BiPoint => biValue (F p.1.1) p.2)) :
    Effective (fun p : ValidInput × List Bool × BiPoint => biValue (wordD p.2.1 (F p.1.1)) p.2.2) := by
  apply effective_words (A := ValidInput) (shift := biShift) (V := fun w (d : ValidInput) p => biValue (wordD w (F d.1)) p) biShift_recursive hbase
    (fun dn : ValidInput × ℕ => hF.budget (dn.1.1,dn.2+1,0))
  · apply Primrec.to_comp
    exact hF.recursive.comp (g := fun dn : ValidInput × ℕ => (dn.1.1,dn.2+1,0)) (by fun_prop)
  intro d i w L hw p n
  have hs := wordD_contDiff (hF.smooth d.1) w
  have he := quotient_error (error_pos n)
    (biLine_deriv hs i (time p.1) p.2)
    (biLine_deriv (partial_contDiff hs i) i (time p.1) p.2)
    (K := (hF.budget (d.1,L+1,0) : ℝ)) (fun s hs => by
      have hb := hF.estimate d.1 d.2 (i::i::w) (L+1) 0
        (by simpa only [List.length_cons] using Nat.succ_le_succ hw)
        (biLine i (time p.1) p.2 s).1
        (biLine_nonneg i (time_nonneg p.1) hs.1 _) (biLine i (time p.1) p.2 s).2
      simpa only [pow_zero,one_mul,wordD_cons,Real.norm_eq_abs] using hb)
  rw [biShift_value]
  dsimp only [biValue, wordD_cons]
  simp only [biLine_zero] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (error_pos n).le)
end EffectiveFields
namespace CertifiedReal
open Filter Topology RecursiveArithmetic
local instance effectiveDerivativesLocal6 : Primcodable ℚ := ratPrimcodable
variable {A : Type*} [Primcodable A]

theorem quadrature_bound {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ)
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |f x-f y| ≤ K*|x-y|) (N : ℕ) (hN : 0 < N) :
    |(∫ s in (0:ℝ)..1, f s) - (∑ i ∈ Finset.range N, f ((i:ℝ)/N))/N| ≤ K/N := by
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  let a : ℕ → ℝ := fun i => (i:ℝ)/N
  have hadj (i : ℕ) : a (i+1)-a i = 1/(N:ℝ) := by dsimp [a]; push_cast; ring
  have hal (i : ℕ) : a i ≤ a (i+1) := by dsimp [a]; gcongr; exact Nat.le_succ i
  have hmem (i : ℕ) (hi : i ≤ N) : a i ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by dsimp [a]; positivity, (div_le_one hN').mpr (Nat.cast_le.mpr hi)⟩
  have he (i : ℕ) (hi : i ∈ Finset.range N) :
      |(∫ s in a i..a (i+1), f s)-f (a i)/N| ≤ K/N*(1/N) := by
    have hinc : Set.uIcc (a i) (a (i+1)) ⊆ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (hal i)]
      exact Set.Icc_subset_Icc (hmem i (Nat.le_of_lt (Finset.mem_range.mp hi))).1
        (hmem (i+1) (Finset.mem_range.mp hi)).2
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a i) (b := a (i+1)) (f := fun s => f s-f (a i)) (C := K/N)
      (fun s hs => by
        have hs' : s ∈ Set.uIcc (a i) (a (i+1)) := Set.uIoc_subset_uIcc hs
        have hd : |s-a i| ≤ 1/(N:ℝ) := by
          rw [Set.uIcc_of_le (hal i)] at hs'
          rw [abs_of_nonneg (sub_nonneg.mpr hs'.1)]
          linarith [hs'.2, hadj i]
        have hK : 0 ≤ K := by
          have H := hlip 0 (by norm_num) 1 (by norm_num)
          norm_num at H
          exact le_trans (abs_nonneg _) H
        exact (hlip s (hinc hs') (a i) (hmem i (Nat.le_of_lt (Finset.mem_range.mp hi)))).trans
          (by simpa only [← mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hd hK))
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, hadj i] at hh
    simpa only [Real.norm_eq_abs, one_div, abs_of_pos (inv_pos.mpr hN'), inv_mul_eq_div] using hh
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := N) (f := f) (μ := MeasureTheory.volume) (fun k _ => hf.intervalIntegrable (a k) (a (k+1)))
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a N = 1 := by simp [a,hN'.ne']
  rw [ha0,haN] at hsum
  change |(∫ s in (0:ℝ)..1, f s) - (∑ i ∈ Finset.range N, f (a i))/N| ≤ K/N
  rw [← hsum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |(∫ s in a i..a (i+1), f s)-f (a i)/N| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, K/N*(1/N) := Finset.sum_le_sum he
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; field_simp

theorem integral {f : A → ℝ → ℝ} (hv : Effective (fun p : A × ℚ => f p.1 p.2))
    (hc : ∀ a, Continuous (f a)) (K : A → ℕ) (hK : Computable K)
    (hlip : ∀ a x, x ∈ Set.Icc (0:ℝ) 1 → ∀ y, y ∈ Set.Icc (0:ℝ) 1 →
      |f a x-f a y| ≤ (K a:ℝ)*|x-y|) :
    Effective (fun a => ∫ s in (0:ℝ)..1, f a s) := by
  obtain ⟨v,hv,herr⟩ := hv
  let q : A × ℕ → ℚ := fun p => (∑ i ∈ Finset.range (p.2+1),
    v ((p.1,(i:ℚ)/(p.2+1)),p.2))/(p.2+1)
  let e : A × ℕ → ℚ := fun p => ((K p.1:ℚ)+1)*qerror p.2
  have hq : Computable q := by
    have hden := rat_add.to_comp.comp ((ratNat.to_comp.comp (Computable.snd.comp
      (Computable.fst : Computable (Prod.fst : (A×ℕ)×ℕ → A×ℕ)))).pair (Computable.const 1))
    have hrat := rat_div.to_comp.comp ((ratNat.to_comp.comp Computable.snd).pair hden)
    have ha : Computable (fun p : (A×ℕ)×ℕ => ((p.1.1,(p.2:ℚ)/(p.1.2+1)),p.1.2)) :=
      (((Computable.fst.comp Computable.fst).pair hrat).pair (Computable.snd.comp Computable.fst)).of_eq (fun _ => rfl)
    have hsum := computable_sum (Computable.succ.comp (Computable.snd : Computable (Prod.snd : A × ℕ → ℕ))) (hv.comp ha).to₂
    have hn : Computable (fun p : A × ℕ => (p.2:ℚ)+1) :=
      (rat_add.to_comp.comp ((ratNat.to_comp.comp (Computable.snd : Computable (Prod.snd : A × ℕ → ℕ))).pair (Computable.const (1 : ℚ)))).of_eq (fun p => rfl)
    exact (rat_div.to_comp.comp (hsum.pair hn)).of_eq (fun p => by rfl)
  have he : Computable e := by
    unfold e
    have hb := rat_add.to_comp.comp ((ratNat.to_comp.comp (hK.comp (Computable.fst : Computable (Prod.fst : A × ℕ → A)))).pair (Computable.const 1))
    exact (rat_mul.to_comp.comp (hb.pair (qerror_primrec.to_comp.comp Computable.snd))).of_eq (fun p => rfl)
  apply of_enclosures hq he
  · intro a n
    let S : ℝ := (∑ i ∈ Finset.range (n+1), f a ((i:ℝ)/(n+1)))/(n+1)
    have h1 := quadrature_bound (hc a) (K a) (hlip a) (n+1) (Nat.succ_pos _)
    have h2 : |S-(q (a,n):ℝ)| ≤ error n := by
      dsimp [S,q]
      push_cast
      rw [← sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<n+1), ← Finset.sum_sub_distrib]
      apply (div_le_iff₀ (by positivity)).mpr
      calc
        _ ≤ ∑ i ∈ Finset.range (n+1), |f a ((i:ℝ)/(n+1)) - (v ((a,(i:ℚ)/(n+1)),n):ℝ)| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (n+1), error n := Finset.sum_le_sum (fun i _ => by simpa using herr (a,(i:ℚ)/(n+1)) n)
        _ = _ := by simp; ring
    calc
      _ ≤ |(∫ s in (0:ℝ)..1, f a s)-S| + |S-(q (a,n):ℝ)| := abs_sub_le _ _ _
      _ ≤ (K a:ℝ)/(n+1) + error n := add_le_add (by simpa only [Nat.cast_add,Nat.cast_one] using h1) h2
      _ = (e (a,n):ℝ) := by simp [e,error]; ring
  · intro a
    simpa only [e,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,cast_qerror,mul_zero] using
      error_tendsto.const_mul ((K a:ℝ)+1)
end CertifiedReal

end
end PeriodicLattice

end OAI
