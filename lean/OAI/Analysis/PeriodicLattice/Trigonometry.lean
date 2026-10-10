import OAI.Analysis.PeriodicLattice.ElementaryFunctions

namespace OAI

/-! Effective trigonometric values and derivative stencils. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingTrigonometry {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace CertifiedReal
open Encodable Filter Topology Finset
local instance trigonometryLocal1 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

def phaseCoeff (sinFlag : Bool) (i : ℕ) : ℤ :=
  if sinFlag then (if i % 4 = 1 then 1 else if i % 4 = 3 then -1 else 0)
  else (if i % 4 = 0 then 1 else if i % 4 = 2 then -1 else 0)

@[fun_prop] theorem phaseCoeff_recursive : Primrec (fun p : Bool × ℕ => phaseCoeff p.1 p.2) := by
  unfold phaseCoeff
  apply RecursiveArithmetic.bool_cond Primrec.fst
  · apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) (Primrec.const 1)
    exact Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 3)) (Primrec.const (-1)) (Primrec.const 0)
  · apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0)) (Primrec.const 1)
    exact Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 2)) (Primrec.const (-1)) (Primrec.const 0)

def complexPart (b : Bool) (z : ℂ) : ℝ := if b then z.im else z.re

def trig (b : Bool) (x : ℝ) : ℝ := if b then Real.sin x else Real.cos x

theorem phaseCoeff_spec (b : Bool) (n : ℕ) :
    (phaseCoeff b n : ℝ) = complexPart b (Complex.I ^ n) := by
  have hm := Nat.mod_lt n (by decide : 0 < 4)
  dsimp [complexPart]
  rw [Complex.I_pow_eq_pow_mod]
  cases b <;> interval_cases h : n % 4 <;> norm_num [phaseCoeff, h]

theorem complexPart_linear (b : Bool) (x : ℝ) (n : ℕ) (k : ℕ) :
    complexPart b (((x : ℂ) * Complex.I) ^ n / k) = (phaseCoeff b n : ℝ) * x ^ n / k := by
  rw [phaseCoeff_spec, mul_pow, ← Complex.ofReal_pow]
  cases b <;> simp [complexPart, mul_comm] <;>
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem trig_taylor (b : Bool) (x : ℝ) (M N : ℕ) (hx : |x| ≤ M)
    (hN : 2 * M + 1 ≤ N) :
    |trig b x - ∑ i ∈ range N, (phaseCoeff b i : ℝ) * x ^ i / i.factorial| ≤
      2 * (M : ℝ) ^ N / N.factorial := by
  have htail := Complex.exp_bound' (x := (x : ℂ) * Complex.I) (n := N) (by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_div_of_nonneg_right hx (by positivity)).trans
    apply (div_le_iff₀ (by positivity)).mpr
    have hnR : 2 * (M : ℝ) + 1 ≤ N := by exact_mod_cast hN
    push_cast; linarith)
  have partBound (z : ℂ) : |complexPart b z| ≤ ‖z‖ := by
    cases b
    · exact Complex.abs_re_le_norm z
    · exact Complex.abs_im_le_norm z
  have h := (partBound (Complex.exp ((x : ℂ) * Complex.I) -
    ∑ i ∈ range N, ((x : ℂ) * Complex.I)^i / i.factorial)).trans htail
  have heq : complexPart b (Complex.exp ((x : ℂ) * Complex.I) -
      ∑ i ∈ range N, ((x : ℂ) * Complex.I)^i / i.factorial) =
      trig b x - ∑ i ∈ range N, (phaseCoeff b i : ℝ) * x ^ i / i.factorial := by
    have hsum : complexPart b (∑ i ∈ range N, ((x : ℂ) * Complex.I)^i / i.factorial) =
        ∑ i ∈ range N, (phaseCoeff b i : ℝ) * x ^ i / i.factorial := by
      simp_rw [← complexPart_linear b x]
      cases b <;> simp [complexPart]
    cases b <;> simp only [complexPart, Bool.false_eq_true, ↓reduceIte, Complex.sub_re, Complex.sub_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, trig] at hsum ⊢ <;> rw [hsum]
  rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  apply h.trans
  rw [div_mul_eq_mul_div, mul_comm _ (2 : ℝ)]
  gcongr

section
variable {A : Type*} [Primcodable A]

theorem Effective.trig {f : A → ℝ} (hf : Effective f) (flag : Bool) :
    Effective (fun a => trig flag (f a)) := by
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
  let N (a : A) (n : ℕ) := 2 * M a + 1 + n
  refine of_enclosures
    (q := fun an => ∑ i ∈ range (N an.1 an.2), (phaseCoeff flag i : ℚ) * q an ^ i / (i.factorial : ℚ))
    (e := fun an => qerror an.2 +
      2 * (M an.1 : ℚ) ^ N an.1 an.2 / (N an.1 an.2).factorial)
    (by
      apply computable_sum
      · unfold N; fun_prop
      · change Computable (fun p : (A × ℕ) × ℕ => (phaseCoeff flag p.2 : ℚ) * q p.1 ^ p.2 / (p.2.factorial : ℚ))
        fun_prop)
    (by unfold N; fun_prop) ?_ ?_
  · intro a n
    have hd : |CertifiedReal.trig flag (f a) - CertifiedReal.trig flag (q (a,n))| ≤ error n := by
      cases flag
      · exact (Real.abs_cos_sub_cos_le _ _).trans (bq a n)
      · exact (Real.abs_sin_sub_sin_le _ _).trans (bq a n)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_intCast, Rat.cast_sum, cast_qerror]
    exact (abs_sub_le _ _ _).trans (add_le_add hd (trig_taylor flag (q (a,n)) (M a) (N a n)
      (b a n) (by dsimp [N]; omega)))
  · intro a
    have hn : Tendsto (fun n => N a n) atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => show n ≤ N a n by dsimp [N]; omega) tendsto_id
    have ht := (Real.summable_pow_div_factorial (M a : ℝ)).tendsto_atTop_zero.comp hn
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast,
      cast_qerror, Rat.cast_div, Function.comp_apply, mul_div_assoc, mul_zero, add_zero] using
      error_tendsto.add (ht.const_mul 2)

theorem Effective.sin {f : A → ℝ} (hf : Effective f) : Effective (fun a => Real.sin (f a)) := hf.trig true

theorem Effective.cos {f : A → ℝ} (hf : Effective f) : Effective (fun a => Real.cos (f a)) := hf.trig false

end
end CertifiedReal
namespace CertifiedReal
open Encodable Filter Topology
local instance trigonometryLocal2 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A : Type*} [Primcodable A]

theorem Effective.cond {f g : A → ℝ} (hf : Effective f) (hg : Effective g)
    {b : A → Bool} (hb : Computable b) : Effective (fun a => if b a then f a else g a) := by
  obtain ⟨q,hq,bq⟩ := hf
  obtain ⟨v,hv,bv⟩ := hg
  refine ⟨fun an => if b an.1 then q an else v an,
    (by simpa only [Bool.cond_eq_ite] using Computable.cond (hb.comp Computable.fst) hq hv), ?_⟩
  intro a n
  cases h : b a
  · simpa [h] using bv a n
  · simpa [h] using bq a n

theorem Effective.ite {f g : A → ℝ} (hf : Effective f) (hg : Effective g)
    {p : A → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Effective (fun a => if p a then f a else g a) := by
  simpa only [decide_eq_true_eq] using hf.cond hg hp.decide.to_comp

end

def refinePrecision (n : ℕ) : ℕ := (n+1)^3-1

@[fun_prop] theorem refinePrecision_recursive : Primrec refinePrecision := by
  unfold refinePrecision; fun_prop

theorem error_refine (n : ℕ) : error (refinePrecision n) = error n ^ 3 := by
  have h : 1 ≤ (n+1)^3 := by exact Nat.one_le_pow _ _ (by omega)
  simp only [error, refinePrecision, Nat.cast_sub h, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [sub_add_cancel, one_div_pow]

section Stencils
variable {A B I : Type*} [Primcodable A] [Primcodable B] [Primcodable I]
variable (shift : I → B → ℕ → B)
abbrev Task (B : Type*) := B × ℕ × ℚ

def spawn (i : I) (v : Task B) : List (Task B) :=
  [(shift i v.1 v.2.1, refinePrecision v.2.1, v.2.2 / qerror v.2.1),
   (v.1, refinePrecision v.2.1, -v.2.2 / qerror v.2.1)]

def stencil (w : List I) (vs : List (Task B)) : List (Task B) :=
  w.foldl (fun vs i => vs.flatMap (spawn shift i)) vs

omit [Primcodable B] [Primcodable I] in
@[simp] theorem stencil_nil (vs : List (Task B)) : stencil shift [] vs = vs := rfl
omit [Primcodable B] [Primcodable I] in
@[simp] theorem stencil_cons (i : I) (w : List I) (vs : List (Task B)) :
    stencil shift (i::w) vs = stencil shift w (vs.flatMap (spawn shift i)) := rfl

theorem spawn_recursive (hs : Primrec (fun p : I × B × ℕ => shift p.1 p.2.1 p.2.2)) :
    Primrec (fun p : I × Task B => spawn shift p.1 p.2) := by
  unfold spawn
  have h₁ : Primrec (fun p : I × Task B =>
      (shift p.1 p.2.1 p.2.2.1, refinePrecision p.2.2.1, p.2.2.2 / qerror p.2.2.1)) := by
    apply (hs.comp (g := fun p : I × Task B => (p.1,p.2.1,p.2.2.1)) (by fun_prop)).pair
    fun_prop
  have h₂ : Primrec (fun p : I × Task B =>
      (p.2.1, refinePrecision p.2.2.1, -p.2.2.2 / qerror p.2.2.1)) := by fun_prop
  exact Primrec.list_cons.comp h₁ (Primrec.list_cons.comp h₂ (Primrec.const []))

theorem stencil_recursive (hs : Primrec (fun p : I × B × ℕ => shift p.1 p.2.1 p.2.2)) :
    Primrec (fun p : List I × List (Task B) => stencil shift p.1 p.2) := by
  have hstep : Primrec (fun p : List (Task B) × I => p.1.flatMap (spawn shift p.2)) :=
    Primrec.list_flatMap Primrec.fst
      ((spawn_recursive shift hs).comp (g := fun p : (List (Task B) × I) × Task B => (p.1.2,p.2)) (by fun_prop)).to₂
  exact Primrec.list_foldl Primrec.fst Primrec.snd (hstep.comp Primrec.snd).to₂

variable (q : (A × B) × ℕ → ℚ)
def difference : List I → A → B → ℕ → ℚ
  | [], a, b, n => q ((a,b),n)
  | i::w, a, b, n => (difference w a (shift i b n) (refinePrecision n) -
      difference w a b (refinePrecision n)) / qerror n

omit [Primcodable A] [Primcodable B] [Primcodable I] in
theorem stencil_correct (w : List I) (vs : List (Task B)) (a : A) :
    ((stencil shift w vs).map (fun v => v.2.2 * q ((a,v.1),v.2.1))).sum =
      (vs.map (fun v => v.2.2 * difference shift q w a v.1 v.2.1)).sum := by
  induction w generalizing vs with
  | nil => rfl
  | cons i w ih =>
    rw [stencil_cons, ih]
    induction vs with
    | nil => simp
    | cons v vs hiv =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons] at *
      rw [hiv]
      congr 1
      simp only [spawn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, difference]
      ring

theorem computable_list_sum {f : A → List ℚ} (hf : Computable f) :
    Computable (fun a => (f a).sum) := RecursiveArithmetic.listSumRat.to_comp.comp hf

theorem computable_list_map {l : A → List B} {f : A → B → ℚ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => ((l a).map (f a)).sum) := by
  have hi : Computable (fun p : A × ℕ => (l p.1)[p.2]?) :=
    Computable.list_getElem?.comp (hl.comp Computable.fst) Computable.snd
  have ht : Computable (fun p : A × ℕ => ((l p.1)[p.2]?.map (f p.1)).getD 0) := by
    apply Computable.option_getD
    · exact Computable.option_map hi (hf.comp
        (g := fun p : (A × ℕ) × B => p.1.1) (h := fun p => p.2)
        (Computable.fst.comp Computable.fst) Computable.snd).to₂
    · exact Computable.const 0
  apply (computable_sum (Computable.list_length.comp hl) ht.to₂).of_eq
  intro a
  dsimp only
  generalize l a = v
  induction v with
  | nil => simp
  | cons b v ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some, List.map_cons, List.sum_cons]
    rw [ih, add_comm]

theorem difference_computable
    (hs : Primrec (fun p : I × B × ℕ => shift p.1 p.2.1 p.2.2)) (hq : Computable q) :
    Computable (fun p : (A × List I × B) × ℕ => difference shift q p.1.2.1 p.1.1 p.1.2.2 p.2) := by
  have ha : Primrec (fun p : (A × List I × B) × ℕ =>
      (p.1.2.1, [(p.1.2.2,p.2,(1 : ℚ))])) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.list_cons.comp ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.const 1))) (Primrec.const []))
  have hl : Computable (fun p : (A × List I × B) × ℕ =>
      stencil shift p.1.2.1 [(p.1.2.2,p.2,(1 : ℚ))]) :=
    (stencil_recursive shift hs).to_comp.comp ha.to_comp
  have harg : Computable (fun p : ((A × List I × B) × ℕ) × Task B =>
      ((p.1.1.1,p.2.1),p.2.2.1)) :=
    ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      (Computable.fst.comp Computable.snd)).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hf : Computable (fun p : ((A × List I × B) × ℕ) × Task B =>
      p.2.2.2 * q ((p.1.1.1,p.2.1),p.2.2.1)) :=
    RecursiveArithmetic.rat_mul.to_comp.comp (g := fun p : ((A × List I × B) × ℕ) × Task B =>
      (p.2.2.2, q ((p.1.1.1,p.2.1),p.2.2.1)))
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair (hq.comp harg))
  apply (computable_list_map hl hf.to₂).of_eq
  intro p
  simpa using stencil_correct shift q p.1.2.1 [(p.1.2.2,p.2,1)] p.1.1

end Stencils
end CertifiedReal

end
end PeriodicLattice

end OAI
