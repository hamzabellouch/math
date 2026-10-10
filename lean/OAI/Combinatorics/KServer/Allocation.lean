import Mathlib
import OAI.Combinatorics.KServer.Minimization
import OAI.Combinatorics.KServer.Simplex

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Finset Set Filter MeasureTheory

/-! The exact source primitives installed in the actual affine minimizer
recursion. The coefficients use raw core flags; fine caps are deliberately
absent. The zero-potential cases do not evaluate the marked denominator. -/
namespace KServer.SimplexFamilies
open scoped BigOperators
open Finset Set MeasureTheory
open KServer.SimplexAnalytic KServer.AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

structure Data (J R : Type*) [Fintype J] where
  active : Finset J
  flags : J → R → Bool
  F : J → ℝ → ℝ
  eta : J → ℝ
  base : J → ℝ
  zeroPotential : Bool
  measurable : ∀ i, Measurable (F i)
  positive : ∀ i y, 0 ≤ y → 0 < F i y
  integrable : ∀ i, IntervalIntegrable (singularKernel (F i)) volume 0 1
  base_mem : ∀ i, base i ∈ Set.Icc 0 1

omit [DecidableEq J] [Fintype R] in
def K (d : Data J R) (a : J → ℝ) (i : J) : ℝ := ∫ s in d.base i..a i, kernel (d.F i) s
omit [DecidableEq J] [Fintype R] in
def Z (d : Data J R) (a : J → ℝ) (i : J) : ℝ := ∫ s in d.base i..a i, singularKernel (d.F i) s

def core (d : Data J R) (p : J × R → ℝ) (i : J) : ℝ := ∑ r, if d.flags i r then p (i,r) else 0

def potential (C ell : ℝ) (d : Data J R) (B a : J → ℝ) : ℝ :=
  if d.zeroPotential then 0 else ∑ i, primitive (d.F i) C ell (d.eta i) (∑ j, B j) (B i) (d.base i) (a i)

def coefficient (C ell : ℝ) (d : Data J R) (a : J → ℝ) (ir : J × R) : ℝ :=
  if d.zeroPotential then 0 else if d.flags ir.1 ir.2 then
    C*ell*((∑ i, K d a i)-(1+d.eta ir.1)*Z d a ir.1) else 0

omit [DecidableEq J] [Fintype R] in
lemma K_continuous (d : Data J R) (i : J) :
    ContinuousOn (fun a => K d a i) (ChangingDomains.simplex d.active) := by
  have hi := kernel_intervalIntegrable (d.measurable i) (d.positive i) (d.integrable i)
  have he : Set.uIcc (0:ℝ) 1=Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (he.symm ▸ d.base_mem i)
  rw [he] at hc
  exact hc.comp (continuous_apply i).continuousOn (fun a ha => ChangingDomains.simplex_coordinate ha i)

omit [DecidableEq J] [Fintype R] in
lemma Z_continuous (d : Data J R) (i : J) :
    ContinuousOn (fun a => Z d a i) (ChangingDomains.simplex d.active) := by
  have he : Set.uIcc (0:ℝ) 1=Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' (d.integrable i) (he.symm ▸ d.base_mem i)
  rw [he] at hc
  exact hc.comp (continuous_apply i).continuousOn (fun a ha => ChangingDomains.simplex_coordinate ha i)

omit [DecidableEq J] [Fintype R] in
lemma coefficient_continuous (C ell : ℝ) (d : Data J R) (ir : J × R) :
    ContinuousOn (fun a => coefficient C ell d a ir) (ChangingDomains.simplex d.active) := by
  unfold coefficient
  split_ifs
  · exact continuousOn_const
  · exact ((continuousOn_finsetSum _ fun i _ => K_continuous d i).sub
      ((Z_continuous d ir.1).const_mul _)).const_mul _
  · exact continuousOn_const

def family (C ell : ℝ) : Family (Data J R) (J × R) J where
  domain d := ChangingDomains.simplex d.active
  compact d := ChangingDomains.simplex_compact d.active
  seed d := ⟨ChangingDomains.canonical d.active,ChangingDomains.canonical_mem d.active⟩
  offset _ _ := 0
  coefficient := coefficient C ell
  offset_continuous _ := continuousOn_const
  coefficient_continuous := coefficient_continuous C ell

/-- Algebraic equality with the literal sum of the source's improper
integrals. In particular the family does not substitute another potential. -/
lemma value_eq (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (ha : a ∈ ChangingDomains.simplex d.active) :
    (family C ell).value d p a=potential C ell d (core d p) a := by
  by_cases hz : d.zeroPotential=true
  · simp [Family.value,family,coefficient,potential,hz]
  · have hi : ∀ i, primitive (d.F i) C ell (d.eta i) (∑ j, core d p j) (core d p i) (d.base i) (a i)=
        C*ell*((∑ j, core d p j)*K d a i-(1+d.eta i)*core d p i*Z d a i) := by
      intro i
      exact primitive_affine (d.measurable i) (d.positive i) (d.integrable i) C ell _ _ _
        (d.base_mem i) (ChangingDomains.simplex_coordinate ha i)
    simp only [Family.value,family,coefficient,potential,hz,Bool.false_eq_true,ite_false,zero_add]
    rw [Fintype.sum_prod_type]
    have hr (i : J) : (∑ r, (if d.flags i r=true then C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i) else 0)*p (i,r))=
        C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i)*core d p i := by
      rw [core,mul_sum]
      exact sum_congr rfl fun r _ => by split_ifs <;> simp_all
    simp_rw [hr,hi]
    have heL (i : J) : C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i)*core d p i =
        (C*ell*(∑ j, K d a j))*core d p i-C*ell*((1+d.eta i)*core d p i*Z d a i) := by ring
    have heR (i : J) : C*ell*((∑ j, core d p j)*K d a i-(1+d.eta i)*core d p i*Z d a i) =
        (C*ell*(∑ j, core d p j))*K d a i-C*ell*((1+d.eta i)*core d p i*Z d a i) := by ring
    simp_rw [heL,heR]
    simp only [sum_sub_distrib,←mul_sum]
    ring

/-- Uniform endpoint bound from the same dimension-free rank slopes; the
finite number of coordinates may occur only in this additive endpoint. -/
lemma value_bound (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ) {L : ℝ}
    (hc : ∀ ir, |coefficient C ell d a ir| ≤ L) (hp : ∀ ir, p ir ∈ Set.Icc 0 1) :
    |(family C ell).value d p a| ≤ L*Fintype.card (J × R) := by
  change |0+∑ ir, coefficient C ell d a ir*p ir| ≤ _
  rw [zero_add]
  calc _ ≤ ∑ ir, |coefficient C ell d a ir*p ir| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _ir : J × R, L := sum_le_sum fun ir _ => by
        rw [abs_mul,abs_of_nonneg (hp ir).1]
        exact (mul_le_mul_of_nonneg_left (hp ir).2 (abs_nonneg _)).trans (by simpa using hc ir)
       _ = _ := by simp [mul_comm]

def regular (A : Finset J) (flags : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1 ≤ h i) : Data J R where
  active := A
  flags := flags
  F i := regularF (h i)
  eta := eta
  base _ := 0
  zeroPotential := false
  measurable i := by unfold regularF; fun_prop
  positive i y hy := (show 0 < h i by linarith [hh i]).trans_le (regularF_lower (by linarith [hh i]) hy)
  integrable i := regular_singular_intervalIntegrable (by linarith [hh i])
  base_mem _ := ⟨le_rfl,by norm_num⟩

omit [DecidableEq J] [Fintype R] in
lemma regular_coefficient_bound (A : Finset J) (flags : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1 ≤ h i) (heta : ∀ i, eta i ∈ Set.Icc 0 1)
    {C ell : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ ell) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ir : J × R) :
    |coefficient C ell (regular A flags h eta hh) a ir| ≤ 3*C*ell := by
  have hai i := ChangingDomains.simplex_coordinate ha i
  have hb i := regular_coefficients (hh i) (hai i)
  have hs : (∑ i, K (regular A flags h eta hh) a i) ∈ Set.Icc 0 1 := by
    constructor
    · exact sum_nonneg fun i _ => (hb i).1.1
    · have hm := sum_le_sum fun i (_ : i∈Finset.univ) => (hb i).1.2
      change (∑ i, K (regular A flags h eta hh) a i) ≤ ∑ i, a i at hm
      rw [ha.2.1] at hm
      split_ifs at hm <;> linarith
  change |if flags ir.1 ir.2=true then C*ell*((∑ i, K (regular A flags h eta hh) a i)-(1+eta ir.1)*Z (regular A flags h eta hh) a ir.1) else 0| ≤ _
  split_ifs with hf
  · rw [abs_mul,abs_of_nonneg (mul_nonneg hC hell)]
    have hj : Z (regular A flags h eta hh) a ir.1 ∈ Set.Icc 0 1 := (hb ir.1).2
    have hprod := mul_le_mul (show 1+eta ir.1 ≤ 2 by linarith [(heta ir.1).2]) hj.2 hj.1 (by norm_num : (0:ℝ)≤2)
    have hprodn := mul_nonneg (show 0 ≤ 1+eta ir.1 by linarith [(heta ir.1).1]) hj.1
    have hab : |(∑ i, K (regular A flags h eta hh) a i)-(1+eta ir.1)*Z (regular A flags h eta hh) a ir.1| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hs.1,hs.2]
    nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg hC hell)]
  · simp only [abs_zero]; positivity


/-- The marked base point is exactly one; no value with `u=0` is accepted. -/
def marked (A : Finset J) (flags : J → R → Bool) (o : J) (h eta : J → ℝ)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (hh : ∀ i ≠ o, 1 ≤ h i) : Data J R where
  active := A
  flags := flags
  F i := if i=o then markedF u (1+Real.log (1/u)) else regularF (h i)
  eta := eta
  base i := if i=o then 1 else 0
  zeroPotential := false
  measurable i := by
    by_cases hi : i=o
    · simpa only [ite_eq_left hi] using (show Measurable (markedF u (1+Real.log (1/u))) by unfold markedF; fun_prop)
    · simpa only [ite_eq_right hi] using (show Measurable (regularF (h i)) by unfold regularF; fun_prop)
  positive i y hy := by
    split_ifs with hi
    · apply marked_positive hu _ y hy
      have := log_inverse_nonneg ⟨hu,hu1⟩
      linarith
    · exact (show 0 < h i by linarith [hh i hi]).trans_le
        (regularF_lower (by linarith [hh i hi]) hy)
  integrable i := by
    split_ifs with hi
    · apply marked_singular_intervalIntegrable hu
      have := log_inverse_nonneg ⟨hu,hu1⟩
      linarith
    · exact regular_singular_intervalIntegrable (by linarith [hh i hi])
  base_mem i := by split_ifs <;> constructor <;> norm_num

omit [Fintype R] in
lemma marked_coefficient_bound (A : Finset J) (flags : J → R → Bool) (o : J) (h eta : J → ℝ)
    {u C ell : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hh : ∀ i ≠ o, 1 ≤ h i)
    (heta : ∀ i, eta i ∈ Set.Icc 0 1) (hC : 0 ≤ C) (hell : 0 ≤ ell) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ir : J × R) :
    |coefficient C ell (marked A flags o h eta u hu hu1 hh) a ir| ≤ 13*C*ell := by
  let d := marked A flags o h eta u hu hu1 hh
  have hai i := ChangingDomains.simplex_coordinate ha i
  have hK (i : J) : |K d a i| ≤ a i+if i=o then 4 else 0 := by
    by_cases hi : i=o
    · subst i
      simp only [K,d,marked,ite_true]
      rw [intervalIntegral.integral_symm,abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 rfl (hai o)).1.1]
      linarith [(marked_coefficients hu hu1 rfl (hai o)).1.2,ha.1 o]
    · simp only [K,d,marked,ite_eq_right hi,add_zero]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (hai i)).1.1]
      exact (regular_coefficients (hh i hi) (hai i)).1.2
  have hs : |∑ i, K d a i| ≤ 5 := by
    apply (abs_sum_le_sum_abs _ _).trans
    have ht := sum_le_sum fun i (_ : i∈Finset.univ) => hK i
    classical
    have he : (∑ i : J, if i=o then (4:ℝ) else 0)=4 := by simp
    rw [sum_add_distrib,he,ha.2.1] at ht
    split_ifs at ht <;> linarith
  have hZ (i : J) : |Z d a i| ≤ 4 := by
    by_cases hi : i=o
    · subst i
      simp only [Z,d,marked,ite_true]
      rw [intervalIntegral.integral_symm,abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 rfl (hai o)).2.1]
      exact (marked_coefficients hu hu1 rfl (hai o)).2.2
    · simp only [Z,d,marked,ite_eq_right hi]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (hai i)).2.1]
      linarith [(regular_coefficients (hh i hi) (hai i)).2.2]
  change |if flags ir.1 ir.2=true then C*ell*((∑ i, K d a i)-(1+eta ir.1)*Z d a ir.1) else 0| ≤ _
  split_ifs
  · rw [abs_mul,abs_of_nonneg (mul_nonneg hC hell)]
    have hprod : |(1+eta ir.1)*Z d a ir.1| ≤ 8 := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ 1+eta ir.1 by linarith [(heta ir.1).1])]
      have := mul_le_mul (show 1+eta ir.1 ≤ 2 by linarith [(heta ir.1).2])
        (hZ ir.1) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      linarith
    have hab : |(∑ i, K d a i)-(1+eta ir.1)*Z d a ir.1| ≤ 13 :=
      (abs_sub _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg hC hell)]
  · simp only [abs_zero]; positivity

/-- The automatic empty/singleton rule is a genuine zero potential, not a
singular marked potential evaluated at a zero side parameter. -/
def automatic (A : Finset J) (flags : J → R → Bool) : Data J R :=
  {regular A flags (fun _ => 1) (fun _ => 0) (fun _ => le_rfl) with zeroPotential := true}

lemma automatic_value (C ell : ℝ) (A : Finset J) (flags : J → R → Bool)
    (p : J × R → ℝ) (a : J → ℝ) : (family C ell).value (automatic A flags) p a=0 := by
  simp [Family.value,family,coefficient,automatic]

end KServer.SimplexFamilies


noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace KServer.SimplexTracker

variable {ι : Type*} [Fintype ι]

def simplex : Set (ι → ℝ) := {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1}

def potential (f : ι → ℝ → ℝ) (a : ι → ℝ) : ℝ := ∑ i, f i (a i)

def movement (a b : ι → ℝ) : ℝ := ∑ i, |a i - b i|

def objective (f : ι → ℝ → ℝ) (S : ℝ) (a₀ a : ι → ℝ) : ℝ :=
  potential f a + S * movement a a₀

lemma max_coordinate {a : ι → ℝ} (ha : a ∈ simplex) (i : ι) : a i ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)
  rwa [ha.2] at h

/-- Quantitative deficit from replacing alpha_i by alpha_i/(1+eta_i). -/
lemma weighted_deficit {a h η : ι → ℝ} {ct ell ηmax : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax) :
    ∑ i, a i / (1 + η i) ≤
      1 - ct / (ell * (1 + ηmax)) * ∑ i, a i * h i := by
  by_cases he : IsEmpty ι
  · let := he
    have : (0 : ℝ) = 1 := by simpa using ha.2
    norm_num at this
  have : Nonempty ι := not_isEmpty_iff.mp he
  have hη0 : ∀ i, 0 ≤ η i := fun i => by rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hmax0 : 0 ≤ ηmax := (hη0 (Classical.arbitrary ι)).trans (hmax _)
  have hi : ∀ i, a i / (1 + η i) ≤
      a i - ct / (ell * (1 + ηmax)) * (a i * h i) := by
    intro i
    have hden : 0 < 1 + η i := by linarith [hη0 i]
    have hdm : 0 < 1 + ηmax := by linarith
    have hle := mul_le_mul_of_nonneg_left (hmax i) (ha.1 i)
    have hhi : ell * η i = ct * h i := by rw [hη i]; field_simp
    apply (div_le_iff₀ hden).mpr
    apply (mul_le_mul_iff_right₀ (mul_pos hl hdm)).mp
    field_simp
    rw [← hhi]
    nlinarith [mul_nonneg (mul_nonneg (ha.1 i) hl.le)
      (mul_nonneg (hη0 i) (sub_nonneg.mpr (hmax i)))]
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, ha.2] using hs

/-- The derivative contradiction in eq:alpha-derivative-contradiction,
with coefficients general enough to include the marked denominator. -/
lemma exists_negative_derivative {a h η F B γ : ι → ℝ}
    {ct ell ηmax Cα CF S : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax)
    (hCa : 0 < Cα) (_hCF : 0 ≤ CF) (hS : 0 < S)
    (hB : ∑ i, B i = S) (hF : ∀ i, 0 ≤ F i)
    (hT : 0 < ∑ i, a i * h i)
    (hden : ∑ i, a i * F i ≤ CF * ∑ i, a i * h i)
    (hgap : 2 * CF * (1 + ηmax) < Cα * ct)
    (hidentity : ∀ i, a i * F i / (1 + η i) * γ i =
      Cα * ell * (S * (a i / (1 + η i)) - B i)) :
    ∃ i, γ i < -2 * S := by
  have hη0 : ∀ i, 0 ≤ η i := fun i => by rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hdef := weighted_deficit ha hh hc hl hη hmax
  by_contra hall
  push Not at hall
  have hlow : -2 * S * (CF * ∑ i, a i * h i) ≤
      ∑ i, a i * F i / (1 + η i) * γ i := by
    calc
      _ ≤ -2 * S * ∑ i, a i * F i :=
        mul_le_mul_of_nonpos_left hden (by linarith)
      _ ≤ ∑ i, a i * F i / (1 + η i) * γ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hp : 0 ≤ a i * F i := mul_nonneg (ha.1 i) (hF i)
        have hd : 0 < 1 + η i := by linarith [hη0 i]
        have hdiv : a i * F i / (1 + η i) ≤ a i * F i := by
          apply (div_le_iff₀ hd).mpr
          nlinarith [mul_nonneg hp (hη0 i)]
        have hmul := mul_le_mul_of_nonneg_left (hall i) (div_nonneg hp hd.le)
        nlinarith
  have heq : (∑ i, a i * F i / (1 + η i) * γ i) =
      Cα * ell * (S * ∑ i, a i / (1 + η i) - S) := by
    simp_rw [hidentity]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hB]
  rw [heq] at hlow
  have hnon : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hT
  let := hnon
  have hmax0 : 0 ≤ ηmax := (hη0 (Classical.arbitrary ι)).trans (hmax _)
  have hdm : 0 < ell * (1 + ηmax) := by positivity
  have hup := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Cα * ell * S by positivity)
  have hstrict := mul_pos (sub_pos.mpr hgap) (mul_pos hS hT)
  have hid : ell * (1 + ηmax) * (ct / (ell * (1 + ηmax))) = ct := by
    field_simp
  have hlow' := mul_le_mul_of_nonneg_right hlow (show 0 ≤ 1 + ηmax by linarith)
  have hup' := mul_le_mul_of_nonneg_right hup (show 0 ≤ 1 + ηmax by linarith)
  have hr : Cα * ell * S * (1 - ct / (ell * (1 + ηmax)) * ∑ i, a i * h i) *
      (1 + ηmax) = Cα * ell * S * (1 + ηmax) - Cα * ct * S * ∑ i, a i * h i := by
    field_simp
  rw [hr] at hup'
  nlinarith

lemma simplex_isCompact : IsCompact (simplex (ι := ι)) := by
  have hc : IsClosed (simplex (ι := ι)) := by
    change IsClosed ({a : ι → ℝ | ∀ i, 0 ≤ a i} ∩ {a : ι → ℝ | ∑ i, a i = 1})
    apply IsClosed.inter
    · simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  apply (isCompact_pi_infinite fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hc
  intro a ha i
  exact ⟨ha.1 i, max_coordinate ha i⟩

lemma objective_continuousOn {f : ι → ℝ → ℝ} (hf : ∀ i, ContinuousOn (f i) (Icc 0 1))
    (S : ℝ) (a₀ : ι → ℝ) : ContinuousOn (objective f S a₀) simplex := by
  apply ContinuousOn.add
  · apply continuousOn_finsetSum _
    intro i _
    exact (hf i).comp (continuous_apply i).continuousOn
      (fun a ha => ⟨ha.1 i, max_coordinate ha i⟩)
  · apply ContinuousOn.const_mul
    apply continuousOn_finsetSum _
    intro i _
    exact ((continuous_apply i).sub continuous_const).abs.continuousOn

lemma exists_minimizer {f : ι → ℝ → ℝ} {S : ℝ} {a₀ : ι → ℝ}
    (hf : ∀ i, ContinuousOn (f i) (Icc 0 1)) (ha₀ : a₀ ∈ simplex) :
    ∃ a ∈ simplex, IsMinOn (objective f S a₀) simplex a :=
  simplex_isCompact.exists_isMinOn ⟨a₀, ha₀⟩ (objective_continuousOn hf S a₀)

lemma minimizer_payment {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (ha₀ : a₀ ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a) :
    S * movement a a₀ ≤ potential f a₀ - potential f a := by
  have h := hm ha₀
  change potential f a + S * movement a a₀ ≤ potential f a₀ + S * movement a₀ a₀ at h
  have hz : movement a₀ a₀ = 0 := by simp [movement]
  rw [hz, mul_zero, add_zero] at h
  linarith

lemma sum_replace [DecidableEq ι] (f : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (y : ℝ) :
    (∑ j, f j (Function.update w i y j)) = (∑ j, f j (w j)) - f i (w i) + f i y := by
  have he : (∑ j ∈ Finset.univ.erase i, f j (Function.update w i y j)) =
      ∑ j ∈ Finset.univ.erase i, f j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => f j (Function.update w i y j))
    (Finset.mem_univ i)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => f j (w j)) (Finset.mem_univ i)
  simp only [Function.update_self, he] at h₁
  linarith

/-- Transfer epsilon from donor i to receiver j, exactly as in §04. -/
def transfer [DecidableEq ι] (a : ι → ℝ) (i j : ι) (ε : ℝ) : ι → ℝ :=
  Function.update (Function.update a i (a i - ε)) j (a j + ε)

lemma sum_transfer [DecidableEq ι] (f : ι → ℝ → ℝ) (a : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (ε : ℝ) :
    (∑ l, f l (transfer a i j ε l)) =
      (∑ l, f l (a l)) - f i (a i) + f i (a i - ε) - f j (a j) + f j (a j + ε) := by
  simp only [transfer, sum_replace, Function.update_of_ne hij.symm]

lemma transfer_mem_simplex [DecidableEq ι] {a : ι → ℝ} (ha : a ∈ simplex) {i j : ι}
    (hij : i ≠ j) {ε : ℝ} (hε : ε ∈ Set.Icc 0 (a i)) : transfer a i j ε ∈ simplex := by
  constructor
  · intro l
    by_cases hlj : l = j
    · subst l; simp only [transfer, Function.update_self]; linarith [ha.1 j, hε.1]
    by_cases hli : l = i
    · subst l; simp [transfer, Function.update_of_ne hij, sub_nonneg.mpr hε.2]
    · simpa [transfer, Function.update_of_ne hlj, Function.update_of_ne hli] using ha.1 l
  · rw [sum_transfer (fun _ x => x) a hij ε, ha.2]
    ring

lemma transfer_min_comparison [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    {i j : ι} (hij : i ≠ j) {ε : ℝ} (hε : ε ∈ Set.Icc 0 (a i)) :
    f i (a i) + f j (a j) ≤ f i (a i - ε) + f j (a j + ε) + 2 * S * ε := by
  have h := hm (transfer_mem_simplex ha hij hε)
  change potential f a + S * movement a a₀ ≤ potential f (transfer a i j ε) +
    S * movement (transfer a i j ε) a₀ at h
  dsimp [potential, movement] at h
  rw [sum_transfer f a hij ε, sum_transfer (fun l x => |x - a₀ l|) a hij ε] at h
  have hi := abs_sub_le (a i - ε) (a i) (a₀ i)
  have hj := abs_sub_le (a j + ε) (a j) (a₀ j)
  have hei : |a i - ε - a i| = ε := by rw [show a i - ε - a i = -ε by ring, abs_neg, abs_of_nonneg hε.1]
  have hej : |a j + ε - a j| = ε := by rw [show a j + ε - a j = ε by ring, abs_of_nonneg hε.1]
  rw [hei] at hi
  rw [hej] at hj
  have hi' := mul_le_mul_of_nonneg_left hi hS
  have hj' := mul_le_mul_of_nonneg_left hj hS
  linarith

lemma minimizer_derivative_gap [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) {di dj : ℝ}
    (hdi : HasDerivAt (f i) di (a i)) (hdj : HasDerivAt (f j) dj (a j)) :
    di ≤ dj + 2 * S := by
  have hc : IsLocalMinOn (fun ε => f i (a i - ε) + f j (a j + ε) + 2 * S * ε)
      (Icc 0 (a i)) 0 := by
    apply IsMinOn.isLocalMinOn
    intro ε hε
    simpa using transfer_min_comparison hS ha hm hij hε
  have hd : HasDerivAt (fun ε => f i (a i - ε) + f j (a j + ε) + 2 * S * ε)
      (-di + dj + 2 * S) 0 := by
    have hi' : HasDerivAt (fun ε => f i (a i - ε)) (-di) 0 := by
      convert (hdi.comp_of_eq 0 ((hasDerivAt_id 0).const_sub (a i)) (by simp)) using 1 <;> first | rfl | simp
    have hj' : HasDerivAt (fun ε => f j (a j + ε)) dj 0 := by
      convert (hdj.comp_of_eq 0 ((hasDerivAt_id 0).const_add (a j)) (by simp)) using 1 <;> first | rfl | simp
    convert (hi'.add hj').add ((hasDerivAt_id 0).const_mul (2 * S)) using 1 <;> first | rfl | simp
  have ht : a i - 0 ∈ posTangentConeAt (Icc 0 (a i)) 0 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 (a i)).segment_subset ⟨le_rfl, hi.le⟩ ⟨hi.le, le_rfl⟩)
  have h := hc.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, sub_zero] at h
  nlinarith

/-- A singular inward slope cannot occur at a constrained global minimum:
there is always a positive donor in the unit simplex. -/
lemma minimizer_not_inward_atBot [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    (hderiv : ∀ i, 0 < a i → DifferentiableAt ℝ (f i) (a i))
    {j : ι} (hj : a j = 0) :
    ¬ Tendsto (fun ε : ℝ => (f j ε - f j 0) / ε) (𝓝[>] 0) atBot := by
  intro hsing
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have hsum : (∑ i, a i) ≤ 0 := Finset.sum_nonpos fun i _ => hn i
    linarith [ha.2]
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ j := by intro he; subst i; linarith
  have hdi := (hderiv i hi).hasDerivAt
  have hd : HasDerivAt (fun ε : ℝ => f i (a i - ε)) (-deriv (f i) (a i)) 0 := by
    convert hdi.comp_of_eq 0 ((hasDerivAt_id 0).const_sub (a i)) (by simp) using 1
    all_goals first | rfl | simp
  have hdl : Tendsto (fun ε : ℝ => (f i (a i - ε) - f i (a i)) / ε)
      (𝓝[>] 0) (𝓝 (-deriv (f i) (a i))) := by
    convert hd.tendsto_slope_zero_right using 1
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbot := tendsto_atBot_add_const_right (𝓝[>] (0 : ℝ)) (2 * S) (hdl.add_atBot hsing)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε ≤ a i ∧
      (f i (a i - ε) - f i (a i)) / ε + (f j ε - f j 0) / ε + 2 * S < 0 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_le_nhds hi).filter_mono nhdsWithin_le_nhds,
      hbot.eventually (eventually_lt_atBot 0)] with ε hε hεi hneg
    exact ⟨hε, hεi, hneg⟩
  obtain ⟨ε, hε, hεi, hneg⟩ := hev.exists
  have h := transfer_min_comparison hS ha hm hij ⟨hε.le, hεi⟩
  rw [hj, zero_add] at h
  have hmul := mul_neg_of_neg_of_pos hneg hε
  have hid : ((f i (a i - ε) - f i (a i)) / ε + (f j ε - f j 0) / ε + 2 * S) * ε =
      f i (a i - ε) - f i (a i) + (f j ε - f j 0) + 2 * S * ε := by
    field_simp
  rw [hid] at hmul
  linarith

/-- Complete minimizer feasibility reduction, using the genuine derivative and
singular endpoint properties of the source primitives. -/
lemma minimizer_feasible [DecidableEq ι]
    {f : ι → ℝ → ℝ} {a₀ a h η F B : ι → ℝ} {ct ell ηmax Cα CF S : ℝ}
    (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax)
    (hCa : 0 < Cα) (hCF : 0 ≤ CF) (hS : 0 < S)
    (hB0 : ∀ i, 0 ≤ B i) (hB : ∑ i, B i = S)
    (hF : ∀ i, 0 ≤ F i) (hFp : ∀ i, 0 < a i → 0 < F i)
    (hT : 0 < ∑ i, a i * h i)
    (hden : ∑ i, a i * F i ≤ CF * ∑ i, a i * h i)
    (hgap : 2 * CF * (1 + ηmax) < Cα * ct)
    (hderiv : ∀ i, 0 < a i → HasDerivAt (f i)
      (Cα * ell * ((S - (1 + η i) * B i / a i) / F i)) (a i))
    (hsing : ∀ i, a i = 0 → 0 < B i →
      Tendsto (fun ε : ℝ => (f i ε - f i 0) / ε) (𝓝[>] 0) atBot) :
    ∀ i, S * a i ≤ (1 + η i) * B i := by
  have hη0 : ∀ i, 0 ≤ η i := fun i => by
    rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hz : ∀ i, a i = 0 → B i = 0 := by
    intro i hi
    by_contra hBi
    have hp : 0 < B i := lt_of_le_of_ne (hB0 i) (Ne.symm hBi)
    exact minimizer_not_inward_atBot hS.le ha hm
      (fun j hj => (hderiv j hj).differentiableAt) hi (hsing i hi hp)
  let γ : ι → ℝ := fun i => if 0 < a i then
    Cα * ell * ((S - (1 + η i) * B i / a i) / F i) else 0
  have hid : ∀ i, a i * F i / (1 + η i) * γ i =
      Cα * ell * (S * (a i / (1 + η i)) - B i) := by
    intro i
    by_cases hi : 0 < a i
    · have hηi : 1 + η i ≠ 0 := by linarith [hη0 i]
      dsimp [γ]; rw [ite_eq_left hi]
      field_simp [hi.ne', (hFp i hi).ne', hηi]
    · have hzero : a i = 0 := le_antisymm (le_of_not_gt hi) (ha.1 i)
      simp only [γ, ite_eq_right hi, hzero, hz i hzero, zero_mul, zero_div, mul_zero, sub_self]
  obtain ⟨j, hj⟩ := exists_negative_derivative ha hh hc hl hη hmax hCa hCF hS hB hF hT hden hgap hid
  have hjp : 0 < a j := by
    by_contra hjp
    simp only [γ, ite_eq_right hjp] at hj
    linarith
  intro i
  by_contra hbad
  have hbad' : (1 + η i) * B i < S * a i := lt_of_not_ge hbad
  have hi : 0 < a i := by
    have hp : 0 ≤ (1 + η i) * B i := mul_nonneg (by linarith [hη0 i]) (hB0 i)
    nlinarith
  have hγi : 0 < γ i := by
    dsimp [γ]; rw [ite_eq_left hi]
    apply mul_pos (mul_pos hCa hl)
    apply div_pos _ (hFp i hi)
    exact sub_pos.mpr ((div_lt_iff₀ hi).mpr hbad')
  have hij : i ≠ j := by intro he; subst i; linarith
  have h := minimizer_derivative_gap hS.le ha hm hij hi (hderiv i hi) (hderiv j hjp)
  have hei : γ i = Cα * ell * ((S - (1 + η i) * B i / a i) / F i) := ite_eq_left hi
  have hej : γ j = Cα * ell * ((S - (1 + η j) * B j / a j) / F j) := ite_eq_left hjp
  rw [← hei, ← hej] at h
  linarith

end KServer.SimplexTracker


namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic

variable {ι : Type*} [Fintype ι]

lemma simplex_weight_pos {a h : ι → ℝ} (ha : a ∈ simplex) (hh : ∀ i, 0 < h i) :
    0 < ∑ i, a i * h i := by
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have : (∑ i, a i) ≤ 0 := Finset.sum_nonpos fun i _ => hn i
    linarith [ha.2]
  obtain ⟨i, hi⟩ := hex
  exact lt_of_lt_of_le (mul_pos hi (hh i))
    (Finset.single_le_sum (fun j _ => mul_nonneg (ha.1 j) (hh j).le) (Finset.mem_univ i))

lemma log_inverse_nonneg_closed {a : ℝ} (ha : a ∈ Set.Icc 0 1) : 0 ≤ Real.log (1 / a) := by
  rcases eq_or_lt_of_le ha.1 with hz | hp
  · subst a; simp
  · exact log_inverse_nonneg ⟨hp, ha.2⟩

/-- The exact integral update, including compact existence, singular endpoint
exclusion, feasibility and payment. Its analytic premises are proved above for
both displayed denominator types; no convexity is presumed. -/
lemma exists_simplex_update [DecidableEq ι]
    {F : ι → ℝ → ℝ} {a₀ h c B base : ι → ℝ} {ct ell ηmax Cα CF : ℝ}
    (ha₀ : a₀ ∈ simplex) (hh : ∀ i, 0 < h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct * h i / ell ≤ ηmax)
    (hCa : 0 < Cα) (hCF : 0 ≤ CF)
    (hB0 : ∀ i, 0 ≤ B i) (hb : ∀ i, base i ∈ Set.Icc 0 1)
    (hFc : ∀ i, Continuous (F i)) (hci : ∀ i, 0 < c i)
    (hF : ∀ i y, 0 ≤ y → c i * (1 + y)^2 ≤ F i y)
    (hdecay : ∀ i, Tendsto (fun s : ℝ => s * F i (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
    (hden : ∀ a ∈ simplex, ∑ i, a i * F i (Real.log (1 / a i)) ≤ CF * ∑ i, a i * h i)
    (hgap : 2 * CF * (1 + ηmax) < Cα * ct) :
    let S := ∑ i, B i
    let f := fun i => primitive (F i) Cα ell (ct * h i / ell) S (B i) (base i)
    ∃ a ∈ simplex, (∀ i, S * a i ≤ (1 + ct * h i / ell) * B i) ∧
      S * movement a a₀ ≤ potential f a₀ - potential f a ∧
      IsMinOn (objective f S a₀) simplex a := by
  dsimp only
  let S := ∑ i, B i
  let η := fun i => ct * h i / ell
  let f := fun i => primitive (F i) Cα ell (η i) S (B i) (base i)
  have hη : ∀ i, 0 ≤ η i := fun i => div_nonneg (mul_nonneg hc.le (hh i).le) hl.le
  have hp : ∀ i y, 0 ≤ y → 0 < F i y := fun i y hy =>
    (show 0 < c i * (1 + y)^2 by have := hci i; positivity).trans_le (hF i y hy)
  have hint := fun i => singular_intervalIntegrable_of_quadratic (hFc i).measurable (hci i) (hF i)
  have hfc : ∀ i, ContinuousOn (f i) (Icc 0 1) := fun i =>
    primitive_continuousOn (hFc i).measurable (hp i) (hint i) Cα ell (η i) S (B i) (hb i)
  obtain ⟨a, ha, hm⟩ := exists_minimizer hfc ha₀ (S := S)
  refine ⟨a, ha, ?_, minimizer_payment ha₀ hm, hm⟩
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hB0 i
  rcases eq_or_lt_of_le hS0 with hS | hS
  · intro i
    change S * a i ≤ (1 + η i) * B i
    rw [← hS, zero_mul]
    exact mul_nonneg (by linarith [hη i]) (hB0 i)
  have hF0 : ∀ i, 0 ≤ F i (Real.log (1 / a i)) := fun i =>
    (hp i _ (log_inverse_nonneg_closed ⟨ha.1 i, max_coordinate ha i⟩)).le
  apply minimizer_feasible ha hm (fun i => (hh i).le) hc hl (fun _ => rfl) hmax
    hCa hCF hS hB0 rfl hF0
    (fun i hi => hp i _ (log_inverse_nonneg ⟨hi, max_coordinate ha i⟩))
    (simplex_weight_pos ha hh) (hden a ha) hgap
  · intro i hi
    exact primitive_derivative (hFc i) (hp i) (hint i) Cα ell (η i) S (B i)
      (hb i) ⟨hi, max_coordinate ha i⟩
  · intro i _ hBi
    exact primitive_inward_atBot (hFc i) (hci i) (hF i) (hdecay i)
      hCa hl (hη i) hBi S (hb i)

/-- Instantiation on a domain without a dominant child, with the manuscript's
regular denominators and base point zero, at all simplex points including zero. -/
lemma regular_simplex_update [DecidableEq ι]
    {a₀ h B : ι → ℝ} {ct ell ηmax Cα Cexp : ℝ}
    (ha₀ : a₀ ∈ simplex) (hh : ∀ i, 1 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct * h i / ell ≤ ηmax) (hCa : 0 < Cα)
    (hB0 : ∀ i, 0 ≤ B i) (hCexp : 0 ≤ Cexp)
    (htail : ∑ i, Real.exp (-h i) ≤ Cexp)
    (hgap : 2 * (25 + 32 * Cexp) * (1 + ηmax) < Cα * ct) :
    let S := ∑ i, B i
    let f := fun i => primitive (regularF (h i)) Cα ell (ct * h i / ell) S (B i) 0
    ∃ a ∈ simplex, (∀ i, S * a i ≤ (1 + ct * h i / ell) * B i) ∧
      S * movement a a₀ ≤ potential f a₀ - potential f a ∧
      IsMinOn (objective f S a₀) simplex a := by
  apply exists_simplex_update (c := fun i => 1 / h i) (CF := 25 + 32 * Cexp)
    ha₀ (fun i => by linarith [hh i]) hc hl hmax hCa (by positivity) hB0
    (fun _ => ⟨le_rfl, by norm_num⟩)
    (fun i => by unfold regularF; fun_prop)
    (fun i => by have := hh i; positivity)
    (fun i _ hy => regular_quadratic_lower (hh i) hy)
    (fun i => regular_decay (h i))
  · intro a ha
    exact regular_denominator_sum ha.1 ha.2 hh htail
  · exact hgap

/-- Marked-domain instantiation; the base point is one exactly on the marked
coordinate, preserving the source's cancellation under parameter changes. -/
lemma marked_simplex_update [DecidableEq ι]
    {a₀ h B : ι → ℝ} {ct ell ηmax Cα Cexp c u H : ℝ} (o : ι)
    (ha₀ : a₀ ∈ simplex) (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) (ho : h o = u)
    (hh : ∀ i ≠ o, 1 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct * h i / ell ≤ ηmax) (hCa : 0 < Cα)
    (hB0 : ∀ i, 0 ≤ B i) (hCexp : 0 ≤ Cexp)
    (hsideC : 0 < c) (hsideC1 : c ≤ 1) (hside : ∀ i ≠ o, c * H ≤ h i)
    (htail : ∑ i ∈ Finset.univ.erase o, Real.exp (-h i) ≤ Cexp * u)
    (hgap : 2 * ((25 * c + 2 + 32 * Cexp) / c) * (1 + ηmax) < Cα * ct) :
    let S := ∑ i, B i
    let f := fun i => primitive (if i = o then markedF u H else regularF (h i))
      Cα ell (ct * h i / ell) S (B i) (if i = o then 1 else 0)
    ∃ a ∈ simplex, (∀ i, S * a i ≤ (1 + ct * h i / ell) * B i) ∧
      S * movement a a₀ ≤ potential f a₀ - potential f a ∧
      IsMinOn (objective f S a₀) simplex a := by
  have hH1 : 1 ≤ H := by
    rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hHp : 0 < H := by linarith
  have hhp : ∀ i, 0 < h i := by
    intro i
    by_cases hi : i = o
    · simpa [hi, ho] using hu
    · linarith [hh i hi]
  obtain ⟨cm, hcm, hFm⟩ := marked_lower_constant hu hHp
  apply exists_simplex_update (c := fun i => if i = o then cm else 1 / h i)
    (CF := (25 * c + 2 + 32 * Cexp) / c) ha₀ hhp hc hl hmax hCa
    (by positivity) hB0
  · intro i; split_ifs <;> norm_num
  · intro i
    split_ifs
    · unfold markedF; fun_prop
    · unfold regularF; fun_prop
  · intro i
    split_ifs
    · exact hcm
    · exact one_div_pos.mpr (hhp i)
  · intro i y hy
    by_cases hi : i = o
    · simpa [hi] using hFm y hy
    · simpa [hi] using regular_quadratic_lower (hh i hi) hy
  · intro i
    by_cases hi : i = o
    · simpa [hi] using marked_decay u H
    · simpa [hi] using regular_decay (h i)
  · intro a ha
    have hd := marked_denominator_sum o ha.1 ha.2 hu.le (hu1.trans hH1)
      hsideC hsideC1 hh hside hCexp htail
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    simp only [ite_true]
    have hs : (∑ i ∈ Finset.univ.erase o,
        a i * (if i = o then markedF u H else regularF (h i)) (Real.log (1 / a i))) =
        ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [hs]
    have ht : (∑ i, a i * h i) = a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), ho]
    rw [ht]
    exact hd
  · exact hgap

end KServer.Allocation


namespace KServer.SupportedAllocation
open scoped BigOperators
open Finset
variable {J : Type*} [Fintype J] [DecidableEq J]

def restrict (A : Finset J) (a : J → ℝ) : A → ℝ := fun i => a i

def extend (A : Finset J) (a : A → ℝ) : J → ℝ := fun i => if hi : i∈A then a ⟨i,hi⟩ else 0

omit [Fintype J] in
lemma extend_apply_mem (A : Finset J) (a : A → ℝ) (i : A) : extend A a i=a i := by
  simp [extend,i.property]

omit [Fintype J] in
lemma extend_apply_not_mem (A : Finset J) (a : A → ℝ) {i : J} (hi : i∉A) : extend A a i=0 := by
  simp [extend,hi]

omit [Fintype J] in
lemma restrict_extend (A : Finset J) (a : A → ℝ) : restrict A (extend A a)=a := by
  funext i; exact extend_apply_mem A a i

omit [Fintype J] in
lemma extend_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    extend A (restrict A a)=a := by
  funext i
  by_cases hi : i∈A
  · simp [extend,restrict,hi]
  · simp [extend,hi,ha i hi]

omit [DecidableEq J] in
lemma sum_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    (∑ i : A, a i)=∑ i, a i := by
  rw [←Finset.sum_subtype A (fun _ => Iff.rfl)]
  exact Finset.sum_subset (subset_univ A) fun i _ hi => ha i hi

lemma sum_extend (A : Finset J) (a : A → ℝ) : (∑ i, extend A a i)=∑ i, a i := by
  have he := sum_restrict A (extend A a) (fun i hi => extend_apply_not_mem A a hi)
  simpa only [extend_apply_mem] using he.symm

omit [DecidableEq J] in
lemma restrict_simplex {A : Finset J} (hA : A.Nonempty) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) : restrict A a ∈ SimplexTracker.simplex := by
  refine ⟨fun i => ha.1 i,?_⟩
  change (∑ i : A, a i)=1
  rw [sum_restrict A a ha.2.2,ha.2.1,ite_eq_left hA]

lemma extend_simplex {A : Finset J} (hA : A.Nonempty) {a : A → ℝ}
    (ha : a ∈ SimplexTracker.simplex) : extend A a ∈ ChangingDomains.simplex A := by
  refine ⟨?_,?_,fun i hi => extend_apply_not_mem A a hi⟩
  · intro i
    unfold extend
    split_ifs with hi
    · exact ha.1 ⟨i,hi⟩
    · exact le_rfl
  · rw [sum_extend,ite_eq_left hA]; exact ha.2

omit [DecidableEq J] in
lemma movement_restrict {A : Finset J} {a b : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hb : ∀ i∉A, b i=0) :
    SimplexTracker.movement (restrict A a) (restrict A b)=ChangingDomains.variation a b := by
  apply sum_restrict A (fun i => |a i-b i|)
  intro i hi; simp [ha i hi,hb i hi]

lemma movement_extend {A : Finset J} (a b : A → ℝ) :
    ChangingDomains.variation (extend A a) (extend A b)=SimplexTracker.movement a b := by
  have h := movement_restrict (fun i hi => extend_apply_not_mem A a hi)
    (fun i hi => extend_apply_not_mem A b hi)
  simpa only [restrict_extend] using h.symm

omit [DecidableEq J] in
lemma potential_restrict {A : Finset J} {f : J → ℝ → ℝ} {a : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hf : ∀ i∉A, f i 0=0) :
    SimplexTracker.potential (fun i : A => f i) (restrict A a)=∑ i, f i (a i) := by
  apply sum_restrict A (fun i => f i (a i))
  intro i hi; rw [ha i hi,hf i hi]

/-- Restriction is exact, including both the movement penalty and the literal
source potentials. No dummy inactive coordinate enters the denominator bound. -/
lemma restrict_isMin {A : Finset J} (hA : A.Nonempty) {f : J → ℝ → ℝ}
    {S : ℝ} {a a₀ : J → ℝ} (ha : a ∈ ChangingDomains.simplex A)
    (ha₀ : a₀ ∈ ChangingDomains.simplex A) (hf : ∀ i∉A, f i 0=0)
    (hm : IsMinOn (fun b => (∑ i, f i (b i))+S*ChangingDomains.variation b a₀)
      (ChangingDomains.simplex A) a) :
    IsMinOn (SimplexTracker.objective (fun i : A => f i) S (restrict A a₀))
      SimplexTracker.simplex (restrict A a) := by
  intro b hb
  have he := extend_simplex hA hb
  have hh := hm he
  change SimplexTracker.potential (fun i : A => f i) (restrict A a)+
      S*SimplexTracker.movement (restrict A a) (restrict A a₀) ≤
    SimplexTracker.potential (fun i : A => f i) b+S*SimplexTracker.movement b (restrict A a₀)
  rw [potential_restrict ha.2.2 hf,movement_restrict ha.2.2 ha₀.2.2]
  have hp := potential_restrict he.2.2 hf
  have hmove := movement_restrict he.2.2 ha₀.2.2
  rw [restrict_extend] at hp hmove
  rw [hp,hmove]
  exact hh

end KServer.SupportedAllocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The feasibility argument holds for every attained minimizer, in particular
for the fixed noncomputable choice in the causal recurrence. -/
lemma every_simplex_minimizer_feasible
    {F : ι → ℝ → ℝ} {a₀ a h c B base : ι → ℝ} {ct ell ηmax Cα CF : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 < h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct*h i/ell ≤ ηmax) (hCa : 0 < Cα) (hCF : 0 ≤ CF)
    (hB0 : ∀ i, 0 ≤ B i) (hb : ∀ i, base i ∈ Set.Icc 0 1)
    (hFc : ∀ i, Continuous (F i)) (hci : ∀ i, 0 < c i)
    (hF : ∀ i y, 0 ≤ y → c i*(1+y)^2 ≤ F i y)
    (hdecay : ∀ i, Tendsto (fun s : ℝ => s*F i (Real.log (1/s))) (𝓝[>] 0) (𝓝 0))
    (hden : ∀ b ∈ simplex, ∑ i, b i*F i (Real.log (1/b i)) ≤ CF*∑ i, b i*h i)
    (hgap : 2*CF*(1+ηmax) < Cα*ct)
    (hm : IsMinOn (objective (fun i => primitive (F i) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) (base i)) (∑ i, B i) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  let S := ∑ i, B i
  let η := fun i => ct*h i/ell
  have hη : ∀ i, 0 ≤ η i := fun i => div_nonneg (mul_nonneg hc.le (hh i).le) hl.le
  have hp : ∀ i y, 0 ≤ y → 0 < F i y := fun i y hy =>
    (show 0 < c i*(1+y)^2 by have := hci i; positivity).trans_le (hF i y hy)
  have hint := fun i => singular_intervalIntegrable_of_quadratic (hFc i).measurable (hci i) (hF i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hB0 i
  rcases eq_or_lt_of_le hS0 with hS | hS
  · intro i
    change S*a i ≤ (1+η i)*B i
    rw [←hS,zero_mul]
    exact mul_nonneg (by linarith [hη i]) (hB0 i)
  have hF0 : ∀ i, 0 ≤ F i (Real.log (1/a i)) := fun i =>
    (hp i _ (log_inverse_nonneg_closed ⟨ha.1 i,max_coordinate ha i⟩)).le
  apply minimizer_feasible ha hm (fun i => (hh i).le) hc hl (fun _ => rfl) hmax
    hCa hCF hS hB0 rfl hF0
    (fun i hi => hp i _ (log_inverse_nonneg ⟨hi,max_coordinate ha i⟩))
    (simplex_weight_pos ha hh) (hden a ha) hgap
  · intro i hi
    exact primitive_derivative (hFc i) (hp i) (hint i) Cα ell (η i) S (B i)
      (hb i) ⟨hi,max_coordinate ha i⟩
  · intro i _ hBi
    exact primitive_inward_atBot (hFc i) (hci i) (hF i) (hdecay i)
      hCa hl (hη i) hBi S (hb i)

end KServer.Allocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma every_regular_minimizer_feasible
    {a₀ a h B : ι → ℝ} {ct ell ηmax Cα Cexp : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 1≤h i) (hc : 0<ct) (hl : 0<ell)
    (hmax : ∀ i, ct*h i/ell≤ηmax) (hCa : 0<Cα) (hB0 : ∀ i, 0≤B i)
    (hCexp : 0≤Cexp) (htail : ∑ i, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (objective (fun i => primitive (regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) 0) (∑ i, B i) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
  apply every_simplex_minimizer_feasible (c := fun i => 1/h i) (CF := 25+32*Cexp)
    ha (fun i => by linarith [hh i]) hc hl hmax hCa (by positivity) hB0
    (fun _ => ⟨le_rfl,by norm_num⟩)
    (fun i => by unfold regularF; fun_prop)
    (fun i => by have := hh i; positivity)
    (fun i _ hy => regular_quadratic_lower (hh i) hy)
    (fun i => regular_decay (h i))
  · intro b hb; exact regular_denominator_sum hb.1 hb.2 hh htail
  · exact hgap
  · exact hm

end KServer.Allocation

namespace KServer.SupportedAllocation
open scoped BigOperators
open SimplexTracker SimplexAnalytic
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Uniform feasibility on the changing active domain. Its exp-tail hypothesis
is a sum over active children only, exactly as in the source. -/
lemma regular_supported_minimizer_feasible {A : Finset J} (hA : A.Nonempty)
    {a₀ a h B : J → ℝ} {ct ell ηmax Cα Cexp : ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ha₀ : a₀ ∈ ChangingDomains.simplex A)
    (hh : ∀ i∈A, 1≤h i) (hc : 0<ct) (hl : 0<ell)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCa : 0<Cα) (hB0 : ∀ i, 0≤B i)
    (hBout : ∀ i∉A, B i=0) (hCexp : 0≤Cexp) (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (fun b => (∑ i, primitive (regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) 0 (b i))+(∑ i, B i)*ChangingDomains.variation b a₀)
       (ChangingDomains.simplex A) a) :
    ∀ i, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
  have hsum : (∑ j : A, B j)=∑ j, B j := sum_restrict A B hBout
  have htail' : (∑ i : A, Real.exp (-h i))≤Cexp := by
    rw [←Finset.sum_subtype A (fun _ => Iff.rfl) (fun i => Real.exp (-h i))]
    exact htail
  have hm' := restrict_isMin hA ha ha₀ (fun i _ => by simp [primitive]) hm
  have he := Allocation.every_regular_minimizer_feasible
    (a₀ := restrict A a₀) (a := restrict A a) (h := fun i : A => h i) (B := fun i : A => B i)
    (restrict_simplex hA ha) (fun i => hh i i.property) hc hl (fun i => hmax i i.property)
    hCa (fun i => hB0 i) hCexp htail' hgap
  have hh' : ∀ i : A, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
    have hm'' : IsMinOn (objective (fun i : A => primitive (regularF (h i)) Cα ell (ct*h i/ell)
        (∑ j : A, B j) (B i) 0) (∑ i : A, B i) (restrict A a₀))
        simplex (restrict A a) := by simpa only [hsum] using hm'
    simpa only [hsum,restrict] using he hm''
  intro i
  by_cases hi : i∈A
  · exact hh' ⟨i,hi⟩
  · simp [ha.2.2 i hi,hBout i hi]

end KServer.SupportedAllocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma every_marked_minimizer_feasible
    {a₀ a h B : ι → ℝ} {ct ell ηmax Cα Cexp c u H : ℝ} (o : ι)
    (ha : a ∈ simplex) (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) (ho : h o = u)
    (hh : ∀ i ≠ o, 1 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct * h i / ell ≤ ηmax) (hCa : 0 < Cα)
    (hB0 : ∀ i, 0 ≤ B i) (hCexp : 0 ≤ Cexp)
    (hsideC : 0 < c) (hsideC1 : c ≤ 1) (hside : ∀ i ≠ o, c * H ≤ h i)
    (htail : ∑ i ∈ Finset.univ.erase o, Real.exp (-h i) ≤ Cexp * u)
    (hgap : 2 * ((25 * c + 2 + 32 * Cexp) / c) * (1 + ηmax) < Cα * ct)
    (hm : IsMinOn (objective (fun i => primitive (if i = o then markedF u H else regularF (h i))
      Cα ell (ct*h i/ell) (∑ j, B j) (B i) (if i=o then 1 else 0))
      (∑ j, B j) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  have hH1 : 1 ≤ H := by
    rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hHp : 0 < H := by linarith
  have hhp : ∀ i, 0 < h i := by
    intro i
    by_cases hi : i = o
    · simpa [hi, ho] using hu
    · linarith [hh i hi]
  obtain ⟨cm, hcm, hFm⟩ := marked_lower_constant hu hHp
  apply every_simplex_minimizer_feasible
    (F := fun i => if i=o then markedF u H else regularF (h i))
    (base := fun i => if i=o then 1 else 0)
    (c := fun i => if i = o then cm else 1 / h i)
    (CF := (25 * c + 2 + 32 * Cexp) / c) ha hhp hc hl hmax hCa
    (by positivity) hB0
  · intro i; split_ifs <;> norm_num
  · intro i
    split_ifs
    · unfold markedF; fun_prop
    · unfold regularF; fun_prop
  · intro i
    split_ifs
    · exact hcm
    · exact one_div_pos.mpr (hhp i)
  · intro i y hy
    by_cases hi : i = o
    · simpa [hi] using hFm y hy
    · simpa [hi] using regular_quadratic_lower (hh i hi) hy
  · intro i
    by_cases hi : i = o
    · simpa [hi] using marked_decay u H
    · simpa [hi] using regular_decay (h i)
  · intro a ha
    have hd := marked_denominator_sum o ha.1 ha.2 hu.le (hu1.trans hH1)
      hsideC hsideC1 hh hside hCexp htail
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    simp only [ite_true]
    have hs : (∑ i ∈ Finset.univ.erase o,
        a i * (if i = o then markedF u H else regularF (h i)) (Real.log (1 / a i))) =
        ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [hs]
    have ht : (∑ i, a i * h i) = a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), ho]
    rw [ht]
    exact hd
  · exact hgap

  · exact hm

end KServer.Allocation

namespace KServer.SupportedAllocation
open SimplexTracker SimplexAnalytic
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Feasibility for the actual changing marked domain; inactive coordinates
are zero instead of being assigned a spurious positive denominator weight. -/
lemma marked_supported_minimizer_feasible {A : Finset J} {o : J} (hoA : o ∈ A)
    {a₀ a h B : J → ℝ} {ct ell ηmax Cα Cexp c u H : ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ha₀ : a₀ ∈ ChangingDomains.simplex A)
    (hu : 0 < u) (hu1 : u ≤ 1) (hH : H = 1 + Real.log (1 / u)) (ho : h o = u)
    (hh : ∀ i∈A, i ≠ o → 1 ≤ h i) (hc : 0<ct) (hl : 0<ell)
    (hmax : ∀ i∈A, ct*h i/ell ≤ ηmax) (hCa : 0<Cα)
    (hB0 : ∀ i, 0≤B i) (hBout : ∀ i∉A, B i=0) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1) (hside : ∀ i∈A, i≠o → c*H≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i) ≤ Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (fun b => (∑ i, primitive (if i=o then markedF u H else regularF (h i))
      Cα ell (ct*h i/ell) (∑ j, B j) (B i) (if i=o then 1 else 0) (b i))+
      (∑ i, B i)*ChangingDomains.variation b a₀) (ChangingDomains.simplex A) a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  have hA : A.Nonempty := ⟨o,hoA⟩
  let o' : A := ⟨o,hoA⟩
  have hsum : (∑ j : A, B j)=∑ j, B j := sum_restrict A B hBout
  have hcon (i : A) : (i=o') ↔ ((i : J)=o) := Subtype.ext_iff
  have hm' := restrict_isMin hA ha ha₀
    (fun i hi => by simp [ite_eq_right (show i≠o by intro he; exact hi (he ▸ hoA)), primitive]) hm
  have htail' : (∑ i∈Finset.univ.erase o', Real.exp (-h (i : J))) ≤ Cexp*u := by
    have he : (∑ i∈Finset.univ.erase o', Real.exp (-h (i : J))) =
        ∑ i∈A.erase o, Real.exp (-h i) := by
      apply Finset.sum_bij (fun (i : A) (_ : i∈Finset.univ.erase o') => (i : J))
      · intro i hi
        exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hi).1
          (Subtype.ext he), i.property⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        refine ⟨⟨i,(Finset.mem_erase.mp hi).2⟩, ?_,rfl⟩
        exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hi).1
          (congrArg Subtype.val he),Finset.mem_univ _⟩
      · intro i _; rfl
    rw [he]; exact htail
  have hm'' : IsMinOn (objective (fun i : A => primitive
      (if i=o' then markedF u H else regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j : A, B j) (B i) (if i=o' then 1 else 0))
      (∑ i : A, B i) (restrict A a₀)) simplex (restrict A a) := by
    simpa only [hcon,hsum] using hm'
  have he := Allocation.every_marked_minimizer_feasible o'
    (restrict_simplex hA ha) hu hu1 hH ho
    (fun i hi => hh i i.property (fun he => hi (Subtype.ext he))) hc hl
    (fun i => hmax i i.property) hCa (fun i => hB0 i) hCexp hsideC hsideC1
    (fun i hi => hside i i.property (fun he => hi (Subtype.ext he))) htail' hgap hm''
  intro i
  by_cases hi : i∈A
  · simpa only [hsum,restrict] using he ⟨i,hi⟩
  · simp [ha.2.2 i hi,hBout i hi]
end KServer.SupportedAllocation

/-! The literal two-stage update of §04: prepare with the new core flags on
common coordinates, minimize on the old simplex, transpose at exactly zero
cost, then minimize on the new simplex. The bounds below calculate its edit
charge from the actual flags and held parameters, not from an assumed drift
or policy bound. -/
namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma update_isMin (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (c : ℝ) (a : J → ℝ) :
    IsMinOn (fun b => potential C ell d (core d p) b+c*ChangingDomains.variation b a)
      (ChangingDomains.simplex d.active) ((family C ell).update d p c a) := by
  have hm := ((family C ell).exists_update d p c a).choose_spec
  intro b hb
  have hm' := hm.2 hb
  change (family C ell).value d p ((family C ell).update d p c a)+c*movement ((family C ell).update d p c a) a ≤
    (family C ell).value d p b+c*movement b a at hm'
  rw [value_eq C ell d p ((family C ell).update d p c a)
      ((family C ell).update_mem d p c a), value_eq C ell d p b hb] at hm'
  exact hm'

lemma regular_update_feasible {A : Finset J} (hA : A.Nonempty)
    (f : J → R → Bool) (h : J → ℝ) (hh : ∀ i, 1≤h i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (hf : ∀ i∉A, ∀ r, f i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d := regular A f h (fun i => ct*h i/ell) hh
    let B := core d p
    let a' := (family C ell).update d p (∑ i, B i) a
    ∀ i, (∑ j, B j)*a' i≤(1+ct*h i/ell)*B i := by
  intro d B a'
  have hB : ∀ i, 0≤B i := by
    intro i
    exact ChangingDomains.core_nonneg (fun i r => hp (i,r)) i
  have hBz : ∀ i∉A, B i=0 := by
    intro i hi
    simp [B,core,d,regular,hf i hi]
  apply SupportedAllocation.regular_supported_minimizer_feasible hA
    ((family C ell).update_mem d p (∑ i, B i) a) ha
    (fun i _ => hh i) hc hl hmax hC hB hBz hCexp htail hgap
  exact update_isMin C ell d p (∑ i, B i) a

omit [DecidableEq J] in
lemma core_eq (A : Finset J) (f : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1≤h i) (p : J × R → ℝ) :
    core (regular A f h eta hh) p = ChangingDomains.core f (fun i r => p (i,r)) := rfl

/-- The prepared input is concrete and uses only new flags on the common
old/new active domain, as in §04 (not intersection of old and new flags). -/
def preparedFlags (A B : Finset J) (g : J → R → Bool) : J → R → Bool :=
  ChangingDomains.syntheticFlags A B g

def preparedInput (A B : Finset J) (g : J → R → Bool) (p : J × R → ℝ) : J → ℝ :=
  ChangingDomains.core (preparedFlags A B g) (fun i r => p (i,r))

omit [Fintype J] [Fintype R] in
lemma prepared_flags_outside (A B : Finset J) (g : J → R → Bool) :
    ∀ i∉A, ∀ r, preparedFlags A B g i r=false := by
  intro i hi r
  simp [preparedFlags,ChangingDomains.syntheticFlags,hi]

omit [Fintype J] in
lemma prepared_input_outside (A B : Finset J) (g : J → R → Bool) (p : J × R → ℝ) :
    ∀ i∉B, preparedInput A B g p i=0 := by
  intro i hi
  simp [preparedInput,preparedFlags,ChangingDomains.core,ChangingDomains.syntheticFlags,hi]

omit [DecidableEq J] [Fintype R] in
lemma regular_potential_zero (A : Finset J) (f : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1≤h i) (C ell : ℝ) (a : J → ℝ) :
    potential C ell (regular A f h eta hh) (fun _ => 0) a=0 := by
  simp [potential,regular,primitive]

omit [DecidableEq J] in
lemma nonneg_total_zero {B : J → ℝ} (hB : ∀ i, 0≤B i) (hS : (∑ i, B i)=0) :
    B=(fun _ => 0) := by
  funext i
  exact le_antisymm (by simpa [hS] using (single_le_sum (fun j _ => hB j) (mem_univ i))) (hB i)

omit [Fintype R] in
lemma regular_transpose_value (A B : Finset J) (f : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1≤h i) (C ell : ℝ) (v a : J → ℝ) (hv : ∀ i, 0≤v i) :
    potential C ell (regular A f h eta hh) v
      (ChangingDomains.transposeSimplex B (∑ i, v i) a)=
    potential C ell (regular A f h eta hh) v a := by
  by_cases hS : (∑ i, v i)=0
  · rw [nonneg_total_zero hv hS]
    simp only [regular_potential_zero]
  · simp [ChangingDomains.transposeSimplex,hS]

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] [Fintype R] in
lemma regular_input_bound (A : Finset J) (hA : A.Nonempty) (f : J → R → Bool)
    (h eta : J → ℝ) (hh : ∀ i, 1≤h i) (he : ∀ i, eta i∈Set.Icc 0 1)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B B' a : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) :
    |potential C ell (regular A f h eta hh) B a-
      potential C ell (regular A f h eta hh) B' a| ≤
      3*C*ell*ChangingDomains.variation B B' := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  exact regular_input_slopes ha.1 hs hh (fun i => (he i).1) (fun i => (he i).2) hC hl

omit [DecidableEq J] [Fintype R] in
lemma regular_parameter_jump (A A' : Finset J) (f g : J → R → Bool)
    (h h' eta eta' : J → ℝ) (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (he : ∀ i, eta i∈Set.Icc 0 1) (he' : ∀ i, eta' i∈Set.Icc 0 1)
    (heq : ∀ i, h i=h' i → eta i=eta' i)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B a : J → ℝ}
    (hB : ∀ i, 0≤B i) (ha : ∀ i, a i∈Set.Icc 0 1)
    (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) :
    |potential C ell (regular A' g h' eta' hh') B a-
      potential C ell (regular A f h eta hh) B a| ≤
      8*C*ell*(∑ i, if h i=h' i then 0 else B i) := by
  have hS : 0≤∑ i, B i := sum_nonneg fun i _ => hB i
  have hi (i : J) :
      |primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i)-
        primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i)| ≤
        8*C*ell*(if h i=h' i then 0 else B i) := by
    by_cases hhx : h i=h' i
    · simp [hhx,heq i hhx]
    · rw [ite_eq_right hhx]
      have ho := regular_component_bound (hh i) (ha i) hC hl (he i).1 hS (hB i)
      have hn := regular_component_bound (hh' i) (ha i) hC hl (he' i).1 hS (hB i)
      have hep := mul_le_mul_of_nonneg_right (he i).2 (hB i)
      have he'p := mul_le_mul_of_nonneg_right (he' i).2 (hB i)
      have hc' := hcap i
      have hlo : (∑ j, B j)*a i+(1+eta i)*B i≤4*B i := by nlinarith
      have hln : (∑ j, B j)*a i+(1+eta' i)*B i≤4*B i := by nlinarith
      have hco := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC hl)
      have hcn := mul_le_mul_of_nonneg_left hln (mul_nonneg hC hl)
      have hab := abs_sub
        (primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))
        (primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i))
      nlinarith
  change |(∑ i, primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))-
    ∑ i, primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i)| ≤ _
  rw [←sum_sub_distrib,mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hi i)

omit [DecidableEq J] in
lemma total_variation_bound (B B' : J → ℝ) :
    |(∑ i, B i)-(∑ i, B' i)|≤ChangingDomains.variation B B' := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [Fintype J] in
lemma transpose_cap {B : Finset J} {S : ℝ} {a v gamma : J → ℝ}
    (hv : ∀ i, 0≤v i) (hg : ∀ i, 0≤gamma i)
    (hcap : ∀ i, S*a i≤gamma i*v i) :
    ∀ i, S*(ChangingDomains.transposeSimplex B S a) i≤gamma i*v i := by
  intro i
  by_cases hs : S=0
  · simp only [hs,zero_mul]
    exact mul_nonneg (hg i) (hv i)
  · simpa [ChangingDomains.transposeSimplex,hs] using hcap i

/-- This is the prepared minimizer from the manuscript; no drift inequality
is an input to its definition. -/
def regularPrepare (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h : J → ℝ) (hh : ∀ i, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (regular A (preparedFlags A B g) h (fun i => ct*h i/ell) hh)
    p (∑ i, preparedInput A B g p i) a

/-- Delete and insert zero coordinates following the prepared minimizing
update, with a canonical simplex state only when its weight is exactly zero. -/
def regularTransport (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h : J → ℝ) (hh : ∀ i, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex B (∑ i, preparedInput A B g p i)
    (regularPrepare C ell ct A B g h hh p a)

lemma regular_transport_mem {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (g : J → R → Bool) (h : J → ℝ) (hh : ∀ i, 1≤h i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) :
    regularTransport C ell ct A B g h hh p a∈ChangingDomains.simplex B := by
  have hp' : ∀ i r, 0≤p (i,r) := fun i r => hp (i,r)
  have hcap := regular_update_feasible hA (preparedFlags A B g) h hh hC hl hc hmax
    hCexp htail hgap p hp (prepared_flags_outside A B g) a ha
  exact ChangingDomains.transposeSimplex_mem (v := preparedInput A B g p)
    hA hB ((family C ell).update_mem _ _ _ _)
    (sum_nonneg fun i _ => ChangingDomains.core_nonneg hp' i) hcap
    (prepared_input_outside A B g p)

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma literal_update_payment (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (c : ℝ)
    {a : J → ℝ} (ha : a∈ChangingDomains.simplex d.active) :
    c*ChangingDomains.variation ((family C ell).update d p c a) a ≤
      potential C ell d (core d p) a-
      potential C ell d (core d p) ((family C ell).update d p c a) := by
  have hm := update_isMin C ell d p c a ha
  change potential C ell d (core d p) ((family C ell).update d p c a)+
    c*ChangingDomains.variation ((family C ell).update d p c a) a ≤
    potential C ell d (core d p) a+c*ChangingDomains.variation a a at hm
  rw [ChangingDomains.variation_self,mul_zero,add_zero] at hm
  linarith

/-- The final update after genuine preparation and transport. -/
def regularStep (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h h' : J → ℝ) (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (regular B g h' (fun i => ct*h' i/ell) hh') p
    (∑ i, ChangingDomains.core g (fun i r => p (i,r)) i)
    (regularTransport C ell ct A B g h hh p a)

lemma regular_step_payment {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (he : ∀ i, ct*h i/ell∈Set.Icc 0 1) (he' : ∀ i, ct*h' i/ell∈Set.Icc 0 1)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, p ir∈Set.Icc 0 1)
    (hf : ∀ i∉A, ∀ r, f i r=false) (hg : ∀ i∉B, ∀ r, g i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d₀ := regular A f h (fun i => ct*h i/ell) hh
    let d₃ := regular B g h' (fun i => ct*h' i/ell) hh'
    let B₀ := core d₀ p
    let B₃ := core d₃ p
    let B₁ := preparedInput A B g p
    let a₃ := regularStep C ell ct A B g h h' hh hh' p a
    (∑ i, B₃ i)*ChangingDomains.variation a₃ a ≤
      potential C ell d₀ B₀ a-potential C ell d₃ B₃ a₃+
      (6*C*ell+4)*ChangingDomains.changedFlags f g+
      8*C*ell*(∑ i, if h i=h' i then 0 else B₁ i) := by
  intro d₀ d₃ B₀ B₃ B₁ a₃
  let d₁ := regular A (preparedFlags A B g) h (fun i => ct*h i/ell) hh
  let a₁ := regularPrepare C ell ct A B g h hh p a
  let a₂ := regularTransport C ell ct A B g h hh p a
  have hp₀ : ∀ ir, 0≤p ir := fun ir => (hp ir).1
  have hp₀' : ∀ i r, 0≤p (i,r) := fun i r => (hp (i,r)).1
  have hB₁ : ∀ i, 0≤B₁ i := fun i => ChangingDomains.core_nonneg hp₀' i
  have hS₁ : 0≤∑ i, B₁ i := sum_nonneg fun i _ => hB₁ i
  have ha₁ : a₁∈ChangingDomains.simplex A := (family C ell).update_mem _ _ _ _
  have ha₂ : a₂∈ChangingDomains.simplex B :=
    regular_transport_mem hA hB g h hh hC hl hc hmax hCexp htail hgap p hp₀ a ha
  have hcap₁ : ∀ i, (∑ j, B₁ j)*a₁ i≤(1+ct*h i/ell)*B₁ i :=
    regular_update_feasible hA (preparedFlags A B g) h hh hC hl hc hmax hCexp htail hgap
      p hp₀ (prepared_flags_outside A B g) a ha
  have hcap₂ : ∀ i, (∑ j, B₁ j)*a₂ i≤(1+ct*h i/ell)*B₁ i :=
    transpose_cap hB₁ (fun i => by linarith [(he i).1]) hcap₁
  have hin := ChangingDomains.synthetic_errors (fun i r => hp (i,r)) hf hg
  have herr₀ : ChangingDomains.variation B₀ B₁≤ChangingDomains.changedFlags f g := hin.1
  have herr₃ : ChangingDomains.variation B₃ B₁≤ChangingDomains.changedFlags f g := hin.2
  have hST : (∑ i, B₁ i)≤∑ i, B₃ i :=
    sub_nonneg.mp (ChangingDomains.synthetic_total (A := A) (B := B) (g := g) hp₀')
  have hδ : (∑ i, B₃ i)-(∑ i, B₁ i)≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound B₃ B₁).trans herr₃)
  have him₀ := regular_input_bound A hA f h (fun i => ct*h i/ell) hh he hC.le hl.le
    (B := B₀) (B' := B₁) ha
  have him₃ := regular_input_bound B hB g h' (fun i => ct*h' i/ell) hh' he' hC.le hl.le
    (B := B₃) (B' := B₁) ha₂
  have ht := regular_parameter_jump A B f g h h' (fun i => ct*h i/ell)
    (fun i => ct*h' i/ell) hh hh' he he' (fun i hi => by rw [hi]) hC.le hl.le
    hB₁ (fun i => ChangingDomains.simplex_coordinate ha₂ i) hcap₂
  have hpm₁ : (∑ i, B₁ i)*ChangingDomains.variation a₁ a ≤
      potential C ell d₀ B₁ a-potential C ell d₀ B₁ a₁ :=
    literal_update_payment C ell d₁ p (∑ i, B₁ i) ha
  have hpm₃ : (∑ i, B₃ i)*ChangingDomains.variation a₃ a₂ ≤
      potential C ell d₃ B₃ a₂-potential C ell d₃ B₃ a₃ :=
    literal_update_payment C ell d₃ p (∑ i, B₃ i) ha₂
  have htrans : potential C ell d₀ B₁ a₂=potential C ell d₀ B₁ a₁ :=
    regular_transpose_value A B f h (fun i => ct*h i/ell) hh C ell B₁ a₁ hB₁
  have hweight := ChangingDomains.prepared_weight_comparison ha ha₁ ha₂ hS₁ hST
    (ChangingDomains.transposeSimplex_payment B (∑ i, B₁ i) a₁) (a₃ := a₃)
  have hinput₀ := mul_le_mul_of_nonneg_left herr₀ (by positivity : 0≤3*C*ell)
  have hinput₃ := mul_le_mul_of_nonneg_left herr₃ (by positivity : 0≤3*C*ell)
  have he₀ := (neg_le_of_abs_le him₀)
  have he₃ := (le_of_abs_le him₃)
  have hep := le_of_abs_le ht
  change _ ≤ 8*C*ell*(∑ i, if h i=h' i then 0 else B₁ i) at hep
  change -(3*C*ell*ChangingDomains.variation B₀ B₁) ≤
    potential C ell d₀ B₀ a-potential C ell d₀ B₁ a at he₀
  change potential C ell d₃ B₃ a₂-potential C ell d₃ B₁ a₂ ≤
    3*C*ell*ChangingDomains.variation B₃ B₁ at he₃
  change potential C ell d₃ B₁ a₂-potential C ell d₀ B₁ a₂ ≤ _ at hep
  nlinarith

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma marked_update_feasible {A : Finset J} {o : J} (hoA : o∈A)
    (f : J → R → Bool) (h : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (hf : ∀ i∉A, ∀ r, f i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d := marked A f o h (fun i => ct*h i/ell) u hu hu1 hh
    let B := core d p
    let a' := (family C ell).update d p (∑ i, B i) a
    ∀ i, (∑ j, B j)*a' i≤(1+ct*h i/ell)*B i := by
  intro d B a'
  have hB : ∀ i, 0≤B i := fun i => ChangingDomains.core_nonneg (fun i r => hp (i,r)) i
  have hBz : ∀ i∉A, B i=0 := by
    intro i hi
    simp [B,core,d,marked,hf i hi]
  apply SupportedAllocation.marked_supported_minimizer_feasible hoA
    ((family C ell).update_mem d p (∑ i, B i) a) ha hu hu1 rfl ho
    (fun i _ hi => hh i hi) hc hl hmax hC hB hBz hCexp hsideC hsideC1 hside htail hgap
  exact update_isMin C ell d p (∑ i, B i) a

omit [Fintype R] in
lemma marked_input_bound (A : Finset J) (hA : A.Nonempty) (f : J → R → Bool)
    (o : J) (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (he : ∀ i, eta i∈Set.Icc 0 1)
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B B' a : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) :
    |potential C ell (marked A f o h eta u hu hu1 hh) B a-
      potential C ell (marked A f o h eta u hu hu1 hh) B' a| ≤
      13*C*ell*ChangingDomains.variation B B' := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  exact marked_input_slopes o ha.1 hs hh hu hu1 rfl (fun i => (he i).1)
    (fun i => (he i).2) hC hl

omit [Fintype R] in
lemma marked_potential_zero (A : Finset J) (f : J → R → Bool) (o : J)
    (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1) (hh : ∀ i≠o, 1≤h i)
    (C ell : ℝ) (a : J → ℝ) :
    potential C ell (marked A f o h eta u hu hu1 hh) (fun _ => 0) a=0 := by
  simp [potential,marked,primitive]

omit [Fintype R] in
lemma marked_transpose_value (A B : Finset J) (f : J → R → Bool) (o : J)
    (h eta : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1) (hh : ∀ i≠o, 1≤h i)
    (C ell : ℝ) (v a : J → ℝ) (hv : ∀ i, 0≤v i) :
    potential C ell (marked A f o h eta u hu hu1 hh) v
      (ChangingDomains.transposeSimplex B (∑ i, v i) a)=
    potential C ell (marked A f o h eta u hu hu1 hh) v a := by
  by_cases hS : (∑ i, v i)=0
  · rw [nonneg_total_zero hv hS]
    simp only [marked_potential_zero]
  · simp [ChangingDomains.transposeSimplex,hS]

lemma simplex_side_weight {A : Finset J} (hA : A.Nonempty) {a B eta : J → ℝ}
    (ha : a∈ChangingDomains.simplex A) (hB : ∀ i, 0≤B i)
    (he : ∀ i, eta i≤1) (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) (o : J) :
    (∑ j, B j)*(1-a o)≤2*(∑ i∈Finset.univ.erase o, B i) := by
  have hs : (∑ i, a i)=1 := by simpa only [ite_eq_left hA] using ha.2.1
  have hx : 1-a o=∑ i∈Finset.univ.erase o, a i := by
    have ht := Finset.add_sum_erase Finset.univ (fun i => a i) (Finset.mem_univ o)
    rw [hs] at ht
    linarith
  rw [hx,mul_sum,mul_sum]
  exact sum_le_sum fun i _ => (hcap i).trans
    (mul_le_mul_of_nonneg_right (by linarith [he i]) (hB i))

omit [Fintype R] in
/-- Marked parameter edits charge the dominant component only when `u`
changes, and charge it to the side total, not the dominant mass. -/
lemma marked_parameter_jump (A A' : Finset J) (hA' : A'.Nonempty)
    (f g : J → R → Bool) (o : J) (h h' eta eta' : J → ℝ)
    {u u' : ℝ} (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (he : ∀ i, eta i∈Set.Icc 0 1) (he' : ∀ i, eta' i∈Set.Icc 0 1)
    (heq : ∀ i, h i=h' i → eta i=eta' i)
    (heqo : u=u' → eta o=eta' o) (heo : eta o≤u) (heo' : eta' o≤u')
    {C ell : ℝ} (hC : 0≤C) (hl : 0≤ell) {B a : J → ℝ}
    (hB : ∀ i, 0≤B i) (ha : a∈ChangingDomains.simplex A')
    (hcap : ∀ i, (∑ j, B j)*a i≤(1+eta i)*B i) :
    |potential C ell (marked A' g o h' eta' u' hu' hu1' hh') B a-
      potential C ell (marked A f o h eta u hu hu1 hh) B a| ≤
      8*C*ell*(∑ i∈Finset.univ.erase o, if h i=h' i then 0 else B i)+
      24*C*ell*(if u=u' then 0 else
        (∑ i∈Finset.univ.erase o, B i)+(u+u')*(∑ i, B i)) := by
  let d₀ := marked A f o h eta u hu hu1 hh
  let d₁ := marked A' g o h' eta' u' hu' hu1' hh'
  let term := fun i => primitive (d₁.F i) C ell (eta' i) (∑ j, B j) (B i) (d₁.base i) (a i)-
    primitive (d₀.F i) C ell (eta i) (∑ j, B j) (B i) (d₀.base i) (a i)
  have hS : 0≤∑ i, B i := sum_nonneg fun i _ => hB i
  have hBs : 0≤∑ i∈Finset.univ.erase o, B i := sum_nonneg fun i _ => hB i
  have hai := fun i => ChangingDomains.simplex_coordinate ha i
  have hside := simplex_side_weight hA' ha hB (fun i => (he i).2) hcap o
  have hSpr : (∑ j, B j)=B o+∑ i∈Finset.univ.erase o, B i :=
    (Finset.add_sum_erase Finset.univ B (Finset.mem_univ o)).symm
  have hregular (i : J) (hi : i∈Finset.univ.erase o) :
      |term i|≤8*C*ell*(if h i=h' i then 0 else B i) := by
    have hio : i≠o := (Finset.mem_erase.mp hi).1
    change |primitive (if i=o then markedF u' (1+Real.log (1/u')) else regularF (h' i))
       C ell (eta' i) (∑ j, B j) (B i) (if i=o then 1 else 0) (a i)-
      primitive (if i=o then markedF u (1+Real.log (1/u)) else regularF (h i))
       C ell (eta i) (∑ j, B j) (B i) (if i=o then 1 else 0) (a i)|≤_
    simp only [ite_eq_right hio]
    by_cases hx : h i=h' i
    · simp [hx,heq i hx]
    · rw [ite_eq_right hx]
      have ho := regular_component_bound (hh i hio) (hai i) hC hl (he i).1 hS (hB i)
      have hn := regular_component_bound (hh' i hio) (hai i) hC hl (he' i).1 hS (hB i)
      have hep := mul_le_mul_of_nonneg_right (he i).2 (hB i)
      have he'p := mul_le_mul_of_nonneg_right (he' i).2 (hB i)
      have hlo : (∑ j, B j)*a i+(1+eta i)*B i≤4*B i := by nlinarith [hcap i]
      have hln : (∑ j, B j)*a i+(1+eta' i)*B i≤4*B i := by nlinarith [hcap i]
      have hco := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC hl)
      have hcn := mul_le_mul_of_nonneg_left hln (mul_nonneg hC hl)
      have hab := abs_sub
        (primitive (regularF (h' i)) C ell (eta' i) (∑ j, B j) (B i) 0 (a i))
        (primitive (regularF (h i)) C ell (eta i) (∑ j, B j) (B i) 0 (a i))
      nlinarith
  have hmarked : |term o|≤24*C*ell*(if u=u' then 0 else
      (∑ i∈Finset.univ.erase o, B i)+(u+u')*(∑ i, B i)) := by
    change |primitive (if o=o then markedF u' (1+Real.log (1/u')) else regularF (h' o))
       C ell (eta' o) (∑ j, B j) (B o) (if o=o then 1 else 0) (a o)-
      primitive (if o=o then markedF u (1+Real.log (1/u)) else regularF (h o))
       C ell (eta o) (∑ j, B j) (B o) (if o=o then 1 else 0) (a o)|≤_
    simp only [ite_true]
    by_cases hx : u=u'
    · simp [hx,heqo hx]
    · rw [ite_eq_right hx]
      have ho := marked_component_bound hu hu1 rfl (hai o) hC hl (he o).1 heo (hB o) hBs hSpr
      have hn := marked_component_bound hu' hu1' rfl (hai o) hC hl (he' o).1 heo' (hB o) hBs hSpr
      have hab := abs_sub
        (primitive (markedF u' (1+Real.log (1/u'))) C ell (eta' o) (∑ j, B j) (B o) 1 (a o))
        (primitive (markedF u (1+Real.log (1/u))) C ell (eta o) (∑ j, B j) (B o) 1 (a o))
      have hs := mul_le_mul_of_nonneg_left hside (by positivity : 0≤8*C*ell)
      have hpos : 0≤C*ell*(u+u')*(∑ j, B j) := by positivity
      nlinarith
  change |(∑ i, primitive (d₁.F i) C ell (eta' i) (∑ j, B j) (B i) (d₁.base i) (a i))-
    ∑ i, primitive (d₀.F i) C ell (eta i) (∑ j, B j) (B i) (d₀.base i) (a i)|≤_
  rw [←sum_sub_distrib]
  change |∑ i, term i|≤_
  have ht := (abs_sum_le_sum_abs term Finset.univ)
  rw [←Finset.add_sum_erase Finset.univ (fun i => |term i|) (Finset.mem_univ o)] at ht
  have hr := sum_le_sum hregular
  rw [←mul_sum] at hr
  linarith

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

def markedPrepare (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h : J → ℝ) (u : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update
    (marked A (preparedFlags A B g) o h (fun i => ct*h i/ell) u hu hu1 hh)
    p (∑ i, preparedInput A B g p i) a

def markedTransport (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h : J → ℝ) (u : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex B (∑ i, preparedInput A B g p i)
    (markedPrepare C ell ct A B g o h u hu hu1 hh p a)

lemma marked_transport_mem {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (g : J → R → Bool) (h : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) :
    markedTransport C ell ct A B g o h u hu hu1 hh p a∈ChangingDomains.simplex B := by
  have hp' : ∀ i r, 0≤p (i,r) := fun i r => hp (i,r)
  have hcap := marked_update_feasible hoA (preparedFlags A B g) h hu hu1 ho hh
    hC hl hc hmax hCexp hsideC hsideC1 hside htail hgap p hp
    (prepared_flags_outside A B g) a ha
  exact ChangingDomains.transposeSimplex_mem (v := preparedInput A B g p)
    ⟨o,hoA⟩ hB ((family C ell).update_mem _ _ _ _)
    (sum_nonneg fun i _ => ChangingDomains.core_nonneg hp' i) hcap
    (prepared_input_outside A B g p)

def markedStep (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h h' : J → ℝ) (u u' : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hu' : 0<u') (hu1' : u'≤1) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh') p
    (∑ i, ChangingDomains.core g (fun i r => p (i,r)) i)
    (markedTransport C ell ct A B g o h u hu hu1 hh p a)

lemma marked_step_payment {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (ho' : h' o=u') (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (he : ∀ i, ct*h i/ell∈Set.Icc 0 1) (he' : ∀ i, ct*h' i/ell∈Set.Icc 0 1)
    (hoeta : ct*u/ell≤u) (hoeta' : ct*u'/ell≤u')
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, p ir∈Set.Icc 0 1)
    (hf : ∀ i∉A, ∀ r, f i r=false) (hg : ∀ i∉B, ∀ r, g i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d₀ := marked A f o h (fun i => ct*h i/ell) u hu hu1 hh
    let d₃ := marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh'
    let B₀ := core d₀ p
    let B₃ := core d₃ p
    let B₁ := preparedInput A B g p
    let a₃ := markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh' p a
    (∑ i, B₃ i)*ChangingDomains.variation a₃ a ≤
      potential C ell d₀ B₀ a-potential C ell d₃ B₃ a₃+
      (26*C*ell+4)*ChangingDomains.changedFlags f g+
      8*C*ell*(∑ i∈Finset.univ.erase o, if h i=h' i then 0 else B₁ i)+
      24*C*ell*(if u=u' then 0 else
        (∑ i∈Finset.univ.erase o, B₁ i)+(u+u')*(∑ i, B₁ i)) := by
  intro d₀ d₃ B₀ B₃ B₁ a₃
  let d₁ := marked A (preparedFlags A B g) o h (fun i => ct*h i/ell) u hu hu1 hh
  let a₁ := markedPrepare C ell ct A B g o h u hu hu1 hh p a
  let a₂ := markedTransport C ell ct A B g o h u hu hu1 hh p a
  have hA : A.Nonempty := ⟨o,hoA⟩
  have hp₀ : ∀ ir, 0≤p ir := fun ir => (hp ir).1
  have hp₀' : ∀ i r, 0≤p (i,r) := fun i r => (hp (i,r)).1
  have hB₁ : ∀ i, 0≤B₁ i := fun i => ChangingDomains.core_nonneg hp₀' i
  have hS₁ : 0≤∑ i, B₁ i := sum_nonneg fun i _ => hB₁ i
  have ha₁ : a₁∈ChangingDomains.simplex A := (family C ell).update_mem _ _ _ _
  have ha₂ : a₂∈ChangingDomains.simplex B :=
    marked_transport_mem hoA hB g h hu hu1 ho hh hC hl hc hmax hCexp
      hsideC hsideC1 hside htail hgap p hp₀ a ha
  have hcap₁ : ∀ i, (∑ j, B₁ j)*a₁ i≤(1+ct*h i/ell)*B₁ i :=
    marked_update_feasible hoA (preparedFlags A B g) h hu hu1 ho hh hC hl hc hmax hCexp
      hsideC hsideC1 hside htail hgap p hp₀ (prepared_flags_outside A B g) a ha
  have hcap₂ : ∀ i, (∑ j, B₁ j)*a₂ i≤(1+ct*h i/ell)*B₁ i :=
    transpose_cap hB₁ (fun i => by linarith [(he i).1]) hcap₁
  have hin := ChangingDomains.synthetic_errors (fun i r => hp (i,r)) hf hg
  have herr₀ : ChangingDomains.variation B₀ B₁≤ChangingDomains.changedFlags f g := hin.1
  have herr₃ : ChangingDomains.variation B₃ B₁≤ChangingDomains.changedFlags f g := hin.2
  have hST : (∑ i, B₁ i)≤∑ i, B₃ i :=
    sub_nonneg.mp (ChangingDomains.synthetic_total (A := A) (B := B) (g := g) hp₀')
  have hδ : (∑ i, B₃ i)-(∑ i, B₁ i)≤ChangingDomains.changedFlags f g :=
    (le_abs_self _).trans ((total_variation_bound B₃ B₁).trans herr₃)
  have him₀ := marked_input_bound A hA f o h (fun i => ct*h i/ell) hu hu1 hh he
    hC.le hl.le (B := B₀) (B' := B₁) ha
  have him₃ := marked_input_bound B hB g o h' (fun i => ct*h' i/ell) hu' hu1' hh' he'
    hC.le hl.le (B := B₃) (B' := B₁) ha₂
  have ht := marked_parameter_jump A B hB f g o h h' (fun i => ct*h i/ell)
    (fun i => ct*h' i/ell) hu hu1 hu' hu1' hh hh' he he'
    (fun i hi => by rw [hi]) (fun hi => by rw [ho,ho',hi])
    (by simpa [ho] using hoeta) (by simpa [ho'] using hoeta') hC.le hl.le hB₁ ha₂ hcap₂
  have hpm₁ : (∑ i, B₁ i)*ChangingDomains.variation a₁ a ≤
      potential C ell d₀ B₁ a-potential C ell d₀ B₁ a₁ :=
    literal_update_payment C ell d₁ p (∑ i, B₁ i) ha
  have hpm₃ : (∑ i, B₃ i)*ChangingDomains.variation a₃ a₂ ≤
      potential C ell d₃ B₃ a₂-potential C ell d₃ B₃ a₃ :=
    literal_update_payment C ell d₃ p (∑ i, B₃ i) ha₂
  have htrans : potential C ell d₀ B₁ a₂=potential C ell d₀ B₁ a₁ :=
    marked_transpose_value A B f o h (fun i => ct*h i/ell) hu hu1 hh C ell B₁ a₁ hB₁
  have hweight := ChangingDomains.prepared_weight_comparison ha ha₁ ha₂ hS₁ hST
    (ChangingDomains.transposeSimplex_payment B (∑ i, B₁ i) a₁) (a₃ := a₃)
  have hinput₀ := mul_le_mul_of_nonneg_left herr₀ (by positivity : 0≤13*C*ell)
  have hinput₃ := mul_le_mul_of_nonneg_left herr₃ (by positivity : 0≤13*C*ell)
  have he₀ := neg_le_of_abs_le him₀
  have he₃ := le_of_abs_le him₃
  have hep := le_of_abs_le ht
  change -(13*C*ell*ChangingDomains.variation B₀ B₁) ≤
    potential C ell d₀ B₀ a-potential C ell d₀ B₁ a at he₀
  change potential C ell d₃ B₃ a₂-potential C ell d₃ B₁ a₂ ≤
    13*C*ell*ChangingDomains.variation B₃ B₁ at he₃
  change potential C ell d₃ B₁ a₂-potential C ell d₀ B₁ a₂ ≤ _ at hep
  nlinarith

end KServer.AdaptiveAllocation

/-! Exact side primitive and compact minimizing update of §04,
    eq:side-primitive-explicit and lem:side-tracker. This is an allocation
    dependency of the absent main, not a separately counted main theorem. -/
noncomputable section
open scoped BigOperators
open Set Filter
namespace KServer.SideTracker

/-- The explicit integral in eq:side-primitive-explicit. -/
def primitive (c b θ z B D w : ℝ) : ℝ :=
  c * (D / θ * (w - z * Real.log (1 + w / z)) +
    D * z * Real.log (1 + w / z) / 2 -
    (b + θ / 2) * B * Real.log (1 + w / z) / θ)

lemma primitive_derivative {c b θ z B D w : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hw : 0 ≤ w) :
    HasDerivAt (primitive c b θ z B D)
      (c * (D * w - (b + θ / 2) * B + D * θ * z / 2) /
        (θ * (w + z))) w := by
  have hl : 0 < 1 + w / z := by positivity
  have hd := (((hasDerivAt_id w).div_const z).const_add 1).log hl.ne'
  have he : 1 / z / (1 + w / z) = 1 / (w + z) := by
    field_simp
    ring
  simp only [id_eq] at hd
  rw [he] at hd
  have H := ((((hasDerivAt_id w).sub (hd.const_mul z)).const_mul (D / θ)).add
    ((hd.const_mul (D * z)).div_const 2)).sub
      ((hd.const_mul ((b + θ / 2) * B)).div_const θ)
  have hwz : w + z ≠ 0 := by positivity
  have he' : c * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) =
      c * (D / θ * (1 - z * (1 / (w + z))) + D * z * (1 / (w + z)) / 2 -
        (b + θ / 2) * B * (1 / (w + z)) / θ) := by
    field_simp [hθ.ne', hwz]
    ring
  rw [he']
  exact H.const_mul c

/-- One-sided necessary optimality, allowing a nondifferentiable movement cost. -/
lemma derivative_le_of_left_comparison {f : ℝ → ℝ} {f' D x : ℝ}
    (hx : 0 < x) (hd : HasDerivAt f f' x)
    (hc : ∀ y ∈ Set.Icc 0 x, f x ≤ f y + D * (x - y)) : f' ≤ D := by
  have hm : IsLocalMinOn (fun y => f y - D * y) (Set.Icc 0 x) x := by
    apply IsMinOn.isLocalMinOn
    intro y hy
    have h := hc y hy
    change f x - D * x ≤ f y - D * y
    linarith
  have ht : 0 - x ∈ posTangentConeAt (Set.Icc 0 x) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 x).segment_subset ⟨hx.le, le_rfl⟩ ⟨le_rfl, hx.le⟩)
  have h := hm.hasFDerivWithinAt_nonneg
    ((hd.sub ((hasDerivAt_id x).const_mul D)).hasFDerivAt.hasFDerivWithinAt) ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  nlinarith

lemma neg_derivative_le_of_right_comparison {f : ℝ → ℝ} {f' D x ε : ℝ}
    (hε : 0 < ε) (hd : HasDerivAt f f' x)
    (hc : ∀ y ∈ Set.Icc x (x + ε), f x ≤ f y + D * (y - x)) : -D ≤ f' := by
  have hm : IsLocalMinOn (fun y => f y + D * y) (Set.Icc x (x + ε)) x := by
    apply IsMinOn.isLocalMinOn
    intro y hy
    have h := hc y hy
    change f x + D * x ≤ f y + D * y
    linarith
  have ht : (x + ε) - x ∈ posTangentConeAt (Set.Icc x (x + ε)) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc x (x + ε)).segment_subset ⟨le_rfl, by linarith⟩
        ⟨by linarith, le_rfl⟩)
  have h := hm.hasFDerivWithinAt_nonneg
    ((hd.add ((hasDerivAt_id x).const_mul D)).hasFDerivAt.hasFDerivWithinAt) ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  nlinarith

variable {ι : Type*} [Fintype ι]

def domain (Cw : ℝ) : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ Cw}

def potential (c b : ℝ) (θ z B : ι → ℝ) (D : ℝ) (w : ι → ℝ) : ℝ :=
  ∑ i, primitive c b (θ i) (z i) (B i) D (w i)

def movement (w v : ι → ℝ) : ℝ := ∑ i, |w i - v i|

def objective (c b : ℝ) (θ z B : ι → ℝ) (D : ℝ) (w₀ w : ι → ℝ) : ℝ :=
  potential c b θ z B D w + D * movement w w₀

lemma movement_self (w : ι → ℝ) : movement w w = 0 := by simp [movement]

lemma domain_isCompact (Cw : ℝ) : IsCompact (domain (ι := ι) Cw) := by
  have hc : IsClosed (domain (ι := ι) Cw) := by
    change IsClosed ({w : ι → ℝ | ∀ i, 0 ≤ w i} ∩ {w : ι → ℝ | ∑ i, w i ≤ Cw})
    apply IsClosed.inter
    · simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  apply (isCompact_pi_infinite fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := Cw)).of_isClosed_subset hc
  intro w hw i
  exact ⟨hw.1 i, (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans hw.2⟩

lemma primitive_continuousOn {c b θ z B D : ℝ} (hθ : 0 < θ) (hz : 0 < z) :
    ContinuousOn (primitive c b θ z B D) (Ici 0) := by
  intro w hw
  exact (primitive_derivative hθ hz hw).continuousAt.continuousWithinAt

lemma objective_continuousOn (c b D Cw : ℝ) (θ z B w₀ : ι → ℝ)
    (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i) :
    ContinuousOn (objective c b θ z B D w₀) (domain Cw) := by
  apply ContinuousOn.add
  · apply continuousOn_finsetSum _
    intro i _
    exact (primitive_continuousOn (hθ i) (hz i)).comp
      (continuous_apply i).continuousOn (fun _ hw => hw.1 i)
  · apply ContinuousOn.const_mul
    apply continuousOn_finsetSum _
    intro i _
    exact ((continuous_apply i).sub continuous_const).abs.continuousOn

lemma exists_minimizer {c b D Cw : ℝ} {θ z B w₀ : ι → ℝ}
    (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i) (hw : w₀ ∈ domain Cw) :
    ∃ w ∈ domain Cw, IsMinOn (objective c b θ z B D w₀) (domain Cw) w :=
  (domain_isCompact Cw).exists_isMinOn ⟨w₀, hw⟩
    (objective_continuousOn c b D Cw θ z B w₀ hθ hz)

lemma minimizer_payment {c b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hw₀ : w₀ ∈ domain Cw)
    (hm : IsMinOn (objective c b θ z B D w₀) (domain Cw) w) :
    D * movement w w₀ ≤ potential c b θ z B D w₀ - potential c b θ z B D w := by
  have h := hm hw₀
  change potential c b θ z B D w + D * movement w w₀ ≤
    potential c b θ z B D w₀ + D * movement w₀ w₀ at h
  rw [movement_self, mul_zero, add_zero] at h
  linarith

lemma sum_replace [DecidableEq ι] (f : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (y : ℝ) :
    (∑ j, f j (Function.update w i y j)) = (∑ j, f j (w j)) - f i (w i) + f i y := by
  have he : (∑ j ∈ Finset.univ.erase i, f j (Function.update w i y j)) =
      ∑ j ∈ Finset.univ.erase i, f j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => f j (Function.update w i y j))
    (Finset.mem_univ i)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => f j (w j)) (Finset.mem_univ i)
  simp only [Function.update_self, he] at h₁
  linarith

lemma replace_mem_domain [DecidableEq ι] {Cw : ℝ} {w : ι → ℝ}
    (hw : w ∈ domain Cw) (i : ι) {y : ℝ} (hy : 0 ≤ y)
    (hs : y ≤ w i + (Cw - ∑ j, w j)) : Function.update w i y ∈ domain Cw := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hy
    · simpa [Function.update, h] using hw.1 j
  · rw [sum_replace (fun _ x => x)]
    linarith

lemma coordinate_min_comparison [DecidableEq ι] {c b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hD : 0 ≤ D)
    (hm : IsMinOn (objective c b θ z B D w₀) (domain Cw) w)
    (i : ι) {y : ℝ} (hy : Function.update w i y ∈ domain Cw) :
    primitive c b (θ i) (z i) (B i) D (w i) ≤
      primitive c b (θ i) (z i) (B i) D y + D * |y - w i| := by
  have h := hm hy
  change potential c b θ z B D w + D * movement w w₀ ≤
    potential c b θ z B D (Function.update w i y) +
      D * movement (Function.update w i y) w₀ at h
  dsimp [potential, movement] at h
  rw [sum_replace (fun j x => primitive c b (θ j) (z j) (B j) D x),
    sum_replace (fun j x => |x - w₀ j|)] at h
  have ht := mul_le_mul_of_nonneg_left (abs_sub_le y (w i) (w₀ i)) hD
  linarith

lemma derivative_upper_violation {M b θ z B D w : ℝ}
    (hb : 1 ≤ b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B)
    (hD : 0 < D) (hw : 0 ≤ w) (hM : b + θ ≤ M)
    (hv : (b + θ) * B < D * w) :
    D < 8 * M * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) := by
  let N := D * w - (b + θ / 2) * B + D * θ * z / 2
  have hN : 0 < N := by
    dsimp [N]
    nlinarith [mul_nonneg hθ.le hB, mul_pos (mul_pos hD hθ) hz]
  have h1 : D * θ * w + D * θ * (b + θ) * z < 2 * (b + θ) * N := by
    have hh : 0 < (2 * b + θ) * (D * w - (b + θ) * B) :=
      mul_pos (by linarith) (sub_pos.mpr hv)
    dsimp [N]
    nlinarith
  have h2 : D * θ * (w + z) ≤ D * θ * w + D * θ * (b + θ) * z := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ b + θ by linarith)
      (mul_nonneg (mul_nonneg hD.le hθ.le) hz.le)
    nlinarith
  have h3 : 2 * (b + θ) * N ≤ 8 * M * N := by
    have hh := mul_le_mul_of_nonneg_right hM hN.le
    nlinarith [mul_pos (show 0 < M by linarith) hN]
  apply (lt_div_iff₀ (mul_pos hθ (by linarith : 0 < w + z))).mpr
  dsimp [N] at h2 h1 h3
  nlinarith [h2.trans_lt (h1.trans_le h3)]

lemma derivative_lower_violation {M b θ z B D w : ℝ}
    (hb : 1 ≤ b) (hθ : 0 < θ) (hz : 0 < z)
    (hD : 0 < D) (hw : 0 ≤ w) (hM : b + θ ≤ M)
    (hv : D * w < b * B - θ * z * D) :
    8 * M * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) < -D := by
  let N := D * w - (b + θ / 2) * B + D * θ * z / 2
  have hB : 0 < B := by
    have : 0 < b * B := by nlinarith [mul_nonneg hD.le hw, mul_pos (mul_pos hθ hz) hD]
    exact (mul_pos_iff.mp this).resolve_right (by rintro ⟨h, _⟩; linarith) |>.2
  have hN : N < 0 := by
    dsimp [N]
    nlinarith [mul_pos hθ hB, mul_pos (mul_pos hD hθ) hz]
  have h1 : 2 * b * N < -(D * θ * w + D * θ * b * z) := by
    have hh : 0 < (2 * b + θ) * (b * B - D * w - θ * z * D) :=
      mul_pos (by linarith) (by linarith)
    dsimp [N]
    nlinarith [mul_pos (mul_pos (mul_pos hD hθ) hθ) hz]
  have h2 : -(D * θ * w + D * θ * b * z) ≤ -(D * θ * (w + z)) := by
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hD.le hθ.le) hz.le)
    nlinarith
  have h3 : 8 * M * N ≤ 2 * b * N := by
    have hh := mul_le_mul_of_nonpos_right (show b ≤ M by linarith) hN.le
    nlinarith [mul_neg_of_pos_of_neg (show 0 < M by linarith) hN]
  apply (div_lt_iff₀ (mul_pos hθ (by linarith : 0 < w + z))).mpr
  dsimp [N] at h1 h3
  nlinarith [h3.trans_lt (h1.trans_le h2)]

/-- Every minimizing update has the source's upper side feasibility. -/
lemma minimizer_upper {M b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hb : 1 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hB : ∀ i, 0 ≤ B i) (hD : 0 ≤ D) (hM : ∀ i, b + θ i ≤ M)
    (hw : w ∈ domain Cw)
    (hm : IsMinOn (objective (8 * M) b θ z B D w₀) (domain Cw) w) :
    ∀ i, D * w i ≤ (b + θ i) * B i := by
  classical
  intro i
  by_cases hD0 : D = 0
  · rw [hD0, zero_mul]
    exact mul_nonneg (by linarith [hθ i]) (hB i)
  have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
  by_contra h
  have hv := lt_of_not_ge h
  have hwi : 0 < w i := by
    nlinarith [mul_nonneg (show 0 ≤ b + θ i by linarith [hθ i]) (hB i)]
  have hc : ∀ y ∈ Set.Icc 0 (w i),
      primitive (8 * M) b (θ i) (z i) (B i) D (w i) ≤
        primitive (8 * M) b (θ i) (z i) (B i) D y + D * (w i - y) := by
    intro y hy
    have hh := coordinate_min_comparison hD hm i
      (replace_mem_domain hw i hy.1 (by linarith [hw.2, hy.2]))
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)] at hh
    linarith
  have hder := derivative_le_of_left_comparison hwi
    (primitive_derivative (c := 8 * M) (b := b) (B := B i) (D := D)
      (hθ i) (hz i) (hw.1 i)) hc
  have hvder := derivative_upper_violation hb (hθ i) (hz i) (hB i) hDp
    (hw.1 i) (hM i) hv
  linarith

/-- The lower bound uses the slack proved from the upper bound, not a new
    assumption that the simplex constraint is inactive. -/
lemma minimizer_lower {M b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hb : 1 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hB : ∀ i, 0 ≤ B i) (hD : 0 ≤ D) (hM : ∀ i, b + θ i ≤ M)
    (hCw : 2 * M < Cw) (hS : ∑ i, B i ≤ 2 * D)
    (hw : w ∈ domain Cw)
    (hm : IsMinOn (objective (8 * M) b θ z B D w₀) (domain Cw) w) :
    ∀ i, b * B i - θ i * z i * D ≤ D * w i := by
  classical
  intro i
  by_cases hD0 : D = 0
  · have hBi : B i = 0 := by
      have hh := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
      rw [hD0, mul_zero] at hS
      linarith [hB i]
    simp [hD0, hBi]
  have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
  have hupper := minimizer_upper hb hθ hz hB hD hM hw hm
  have hs : ∑ j, w j ≤ 2 * M := by
    have hs₁ : D * ∑ j, w j ≤ M * ∑ j, B j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (hupper j).trans
        (mul_le_mul_of_nonneg_right (hM j) (hB j))
    have hMp : 0 ≤ M := by linarith [hM i, hθ i]
    have hh := mul_le_mul_of_nonneg_left hS hMp
    nlinarith
  have hgap : 0 < Cw - ∑ j, w j := by linarith
  have hc : ∀ y ∈ Set.Icc (w i) (w i + (Cw - ∑ j, w j)),
      primitive (8 * M) b (θ i) (z i) (B i) D (w i) ≤
        primitive (8 * M) b (θ i) (z i) (B i) D y + D * (y - w i) := by
    intro y hy
    have hh := coordinate_min_comparison hD hm i
      (replace_mem_domain hw i ((hw.1 i).trans hy.1) hy.2)
    rwa [abs_of_nonneg (sub_nonneg.mpr hy.1)] at hh
  have hder := neg_derivative_le_of_right_comparison hgap
    (primitive_derivative (c := 8 * M) (b := b) (B := B i) (D := D)
      (hθ i) (hz i) (hw.1 i)) hc
  by_contra h
  have hvder := derivative_lower_violation hb (hθ i) (hz i) hDp
    (hw.1 i) (hM i) (lt_of_not_ge h)
  linarith

/-- Section 04, Lemma side-tracker, with the explicit sufficient multiplier
    C'_w = 8M. No rank assumption or positivity assumption on D is added. -/
theorem side_update {M b D Cw : ℝ} {θ z B w₀ : ι → ℝ}
    (hb : 1 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hB : ∀ i, 0 ≤ B i) (hD : 0 ≤ D) (hM : ∀ i, b + θ i ≤ M)
    (hCw : 2 * M < Cw) (hw₀ : w₀ ∈ domain Cw) :
    ∃ w ∈ domain Cw,
      IsMinOn (objective (8 * M) b θ z B D w₀) (domain Cw) w ∧
      (∀ i, D * w i ≤ (b + θ i) * B i) ∧
      ((∑ i, B i) ≤ 2 * D → ∀ i, b * B i - θ i * z i * D ≤ D * w i) ∧
      D * movement w w₀ ≤ potential (8 * M) b θ z B D w₀ -
        potential (8 * M) b θ z B D w := by
  obtain ⟨w, hw, hm⟩ := exists_minimizer (c := 8 * M) (b := b) (B := B)
    (D := D) hθ hz hw₀
  exact ⟨w, hw, hm, minimizer_upper hb hθ hz hB hD hM hw hm,
    fun hS => minimizer_lower hb hθ hz hB hD hM hCw hS hw hm,
    minimizer_payment hw₀ hm⟩

/-- The logarithmic formula is exactly the source's interval integral. -/
lemma primitive_eq_integral {c b θ z B D w : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hw : 0 ≤ w) :
    primitive c b θ z B D w =
      c * ∫ s in (0 : ℝ)..w,
        (D * s - (b + θ / 2) * B + D * θ * z / 2) / (θ * (s + z)) := by
  have hc : ContinuousOn (fun s : ℝ =>
      (D * s - (b + θ / 2) * B + D * θ * z / 2) / (θ * (s + z))) (Set.Icc 0 w) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      exact mul_ne_zero hθ.ne' (ne_of_gt (by linarith [hs.1]))
  have hd : ∀ s ∈ uIcc (0 : ℝ) w,
      HasDerivAt (primitive 1 b θ z B D)
        ((D * s - (b + θ / 2) * B + D * θ * z / 2) / (θ * (s + z))) s := by
    intro s hs
    rw [uIcc_of_le hw] at hs
    simpa only [one_mul] using primitive_derivative (c := (1 : ℝ))
      (b := b) (B := B) (D := D) hθ hz hs.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.mono (by rw [uIcc_of_le hw])).intervalIntegrable)
  simp [primitive] at h
  rw [h]
  rfl

/-- Affinity in (B,D), used before every update decision in the all-step
    filtering telescope. In particular the held-D part is constant. -/
lemma primitive_affine_inputs (c b θ z B₁ B₂ D₁ D₂ t w : ℝ) :
    primitive c b θ z ((1 - t) * B₁ + t * B₂) ((1 - t) * D₁ + t * D₂) w =
      (1 - t) * primitive c b θ z B₁ D₁ w + t * primitive c b θ z B₂ D₂ w := by
  unfold primitive
  ring

end KServer.SideTracker

namespace KServer.SideTracker
open scoped BigOperators

lemma log_factors {z w : ℝ} (hz : 0 < z) (hw : 0 ≤ w) :
    0 ≤ Real.log (1 + w / z) ∧
    0 ≤ z * Real.log (1 + w / z) ∧
    z * Real.log (1 + w / z) ≤ w := by
  have hq : 0 ≤ w / z := div_nonneg hw hz.le
  have hl : 0 ≤ Real.log (1 + w / z) := Real.log_nonneg (by linarith)
  refine ⟨hl, mul_nonneg hz.le hl, ?_⟩
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + w / z by positivity)
  have hh' : Real.log (1 + w / z) ≤ w / z := by linarith
  have := mul_le_mul_of_nonneg_left hh' hz.le
  simpa [mul_div_cancel₀ _ hz.ne'] using this

lemma side_log_bound {h W w : ℝ} (hh : 1 ≤ h) (hW : 0 ≤ W)
    (hw : w ∈ Set.Icc 0 W) :
    Real.log (1 + w / (Real.exp (1 - h) / h)) ≤
      (Real.log (1 + W) + 2) * h := by
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hw0 : 0 ≤ w := hw.1
  have he : 1 ≤ Real.exp (h - 1) := Real.one_le_exp (by linarith)
  have hh' : h ≤ Real.exp (h - 1) := by
    have := Real.add_one_le_exp (h - 1)
    linarith
  have hE := Real.exp_pos (h - 1)
  have heq : 1 + w / (Real.exp (1 - h) / h) =
      1 + w * h * Real.exp (h - 1) := by
    have hn : 1 - h = -(h - 1) := by ring
    rw [hn, Real.exp_neg]
    field_simp
  rw [heq]
  have hmul : w * h * Real.exp (h - 1) ≤ W * Real.exp (h - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hw.2 hp.le,
      mul_le_mul_of_nonneg_left hh' hW,
      mul_le_mul_of_nonneg_right
        (mul_le_mul hw.2 hh' hp.le hW) hE.le]
  have hs : 1 ≤ Real.exp (h - 1) ^ 2 := by nlinarith
  have hbound : 1 + w * h * Real.exp (h - 1) ≤
      (1 + W) * Real.exp (2 * (h - 1)) := by
    rw [show 2 * (h - 1) = (h - 1) + (h - 1) by ring, Real.exp_add]
    nlinarith
  have hlog := Real.log_le_log (show 0 < 1 + w * h * Real.exp (h - 1) by positivity) hbound
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hLW : 0 ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  nlinarith

/-- Coefficients of the actual primitive; all are nonnegative on the side
    domain. Their estimates use size-derived logarithmic cancellation. -/
def Dcoef (c θ z w : ℝ) : ℝ :=
  c * ((w - z * Real.log (1 + w / z)) / θ + z * Real.log (1 + w / z) / 2)
def Bcoef (c b θ z w : ℝ) : ℝ :=
  c * (b + θ / 2) * Real.log (1 + w / z) / θ

lemma primitive_coefficients (c b θ z B D w : ℝ) :
    primitive c b θ z B D w = Dcoef c θ z w * D - Bcoef c b θ z w * B := by
  unfold primitive Dcoef Bcoef
  ring

lemma coefficients_nonneg {c b θ z w : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hθ : 0 < θ) (hz : 0 < z) (hw : 0 ≤ w) :
    0 ≤ Dcoef c θ z w ∧ 0 ≤ Bcoef c b θ z w := by
  obtain ⟨hL, hzL, hLw⟩ := log_factors hz hw
  constructor
  · exact mul_nonneg hc (add_nonneg (div_nonneg (sub_nonneg.mpr hLw) hθ.le)
      (by positivity))
  · exact div_nonneg (mul_nonneg (mul_nonneg hc (by positivity)) hL) hθ.le

lemma Dcoef_bound {c θ z w cw ell h : ℝ} (hc : 0 ≤ c)
    (hz : 0 < z) (hw : 0 ≤ w) (hcw : 0 < cw) (hell : 1 ≤ ell)
    (hh : 1 ≤ h) (hθ : θ = cw * h / ell) :
    Dcoef c θ z w ≤ c * (1 / cw + 1) * ell * w := by
  have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hθp : 0 < θ := by rw [hθ]; positivity
  obtain ⟨hL, hzL, hLw⟩ := log_factors hz hw
  have hi : 1 / θ ≤ ell / cw := by
    rw [div_le_div_iff₀ hθp hcw]
    rw [hθ]
    have he : ell * (cw * h / ell) = cw * h := by field_simp
    rw [he]
    nlinarith
  have ht : (w - z * Real.log (1 + w / z)) / θ ≤ w * (ell / cw) := by
    calc
      _ ≤ w / θ := div_le_div_of_nonneg_right (by linarith) hθp.le
      _ = w * (1 / θ) := by ring
      _ ≤ w * (ell / cw) := mul_le_mul_of_nonneg_left hi hw
  have hq : z * Real.log (1 + w / z) / 2 ≤ ell * w := by nlinarith
  unfold Dcoef
  calc
    _ ≤ c * (w * (ell / cw) + ell * w) :=
      mul_le_mul_of_nonneg_left (add_le_add ht hq) hc
    _ = c * (1 / cw + 1) * ell * w := by ring

lemma Bcoef_bound {c b θ z w cw ell h K M : ℝ} (hc : 0 ≤ c)
    (hb : 0 ≤ b) (hz : 0 < z) (hw : 0 ≤ w) (hcw : 0 < cw)
    (hell : 0 < ell) (hh : 0 < h) (hθ : θ = cw * h / ell)
    (hBM : b + θ / 2 ≤ M)
    (hLK : Real.log (1 + w / z) ≤ K * h) :
    Bcoef c b θ z w ≤ c * M * K / cw * ell := by
  have hθp : 0 < θ := by rw [hθ]; positivity
  obtain ⟨hL, _, _⟩ := log_factors hz hw
  have hM : 0 ≤ M := (by positivity : 0 ≤ b + θ / 2).trans hBM
  unfold Bcoef
  calc
    _ ≤ c * M * (K * h) / θ := div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hBM hc) hLK hL (mul_nonneg hc hM)) hθp.le
    _ = c * M * K / cw * ell := by rw [hθ]; field_simp

lemma primitive_component_bound {c b θ z w cw ell h K M B D : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hz : 0 < z) (hw : 0 ≤ w)
    (hcw : 0 < cw) (hell : 1 ≤ ell) (hh : 1 ≤ h)
    (hθ : θ = cw * h / ell) (hBM : b + θ / 2 ≤ M)
    (hLK : Real.log (1 + w / z) ≤ K * h) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |primitive c b θ z B D w| ≤
      c * (1 / cw + 1) * ell * (D * w) + c * M * K / cw * ell * B := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hθp : 0 < θ := by rw [hθ]; positivity
  have hn := coefficients_nonneg hc hb hθp hz hw
  rw [primitive_coefficients]
  calc
    _ ≤ |Dcoef c θ z w * D| + |Bcoef c b θ z w * B| := abs_sub _ _
    _ = Dcoef c θ z w * D + Bcoef c b θ z w * B := by
      rw [abs_of_nonneg (mul_nonneg hn.1 hD), abs_of_nonneg (mul_nonneg hn.2 hB)]
    _ ≤ (c * (1 / cw + 1) * ell * w) * D + (c * M * K / cw * ell) * B :=
      add_le_add (mul_le_mul_of_nonneg_right (Dcoef_bound hc hz hw hcw hell hh hθ) hD)
        (mul_le_mul_of_nonneg_right (Bcoef_bound hc hb hz hw hcw he hp hθ hBM hLK) hB)
    _ = _ := by ring

lemma side_z_identity {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    a / (A * (1 + Real.log (A / a))) =
      Real.exp (1 - (1 + Real.log (A / a))) / (1 + Real.log (A / a)) := by
  rw [show 1 - (1 + Real.log (A / a)) = -Real.log (A / a) by ring,
    Real.exp_neg, Real.exp_log (div_pos hA ha)]
  field_simp

lemma potential_input_bound {ι : Type*} [Fintype ι]
    {c b cw ell K M Cw : ℝ} {θ z h w : ι → ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hcw : 0 < cw) (hell : 1 ≤ ell)
    (hz : ∀ i, 0 < z i) (hh : ∀ i, 1 ≤ h i)
    (hθ : ∀ i, θ i = cw * h i / ell)
    (hBM : ∀ i, b + θ i / 2 ≤ M)
    (hLK : ∀ i, Real.log (1 + w i / z i) ≤ K * h i)
    (hw : w ∈ domain Cw) (B B' : ι → ℝ) (D D' : ℝ) :
    |potential c b θ z B D w - potential c b θ z B' D' w| ≤
      c * (1 / cw + 1) * ell * Cw * |D - D'| +
        c * M * K / cw * ell * (∑ i, |B i - B' i|) := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hdc (i) := Dcoef_bound hc (hz i) (hw.1 i) hcw hell (hh i) (hθ i)
  have hbc (i) := Bcoef_bound hc hb (hz i) (hw.1 i) hcw he
    (lt_of_lt_of_le zero_lt_one (hh i)) (hθ i) (hBM i) (hLK i)
  have hnn (i) : 0 ≤ Dcoef c (θ i) (z i) (w i) ∧
      0 ≤ Bcoef c b (θ i) (z i) (w i) :=
    coefficients_nonneg hc hb (by rw [hθ i]; exact div_pos (mul_pos hcw (lt_of_lt_of_le zero_lt_one (hh i))) he) (hz i) (hw.1 i)
  have hdiff (i) : primitive c b (θ i) (z i) (B i) D (w i) -
      primitive c b (θ i) (z i) (B' i) D' (w i) =
      Dcoef c (θ i) (z i) (w i) * (D - D') -
      Bcoef c b (θ i) (z i) (w i) * (B i - B' i) := by
    rw [primitive_coefficients, primitive_coefficients]
    ring
  have hpoint (i) : |primitive c b (θ i) (z i) (B i) D (w i) -
      primitive c b (θ i) (z i) (B' i) D' (w i)| ≤
      c * (1 / cw + 1) * ell * w i * |D - D'| +
        c * M * K / cw * ell * |B i - B' i| := by
    rw [hdiff]
    calc
      _ ≤ |Dcoef c (θ i) (z i) (w i) * (D - D')| +
          |Bcoef c b (θ i) (z i) (w i) * (B i - B' i)| := abs_sub _ _
      _ = Dcoef c (θ i) (z i) (w i) * |D - D'| +
          Bcoef c b (θ i) (z i) (w i) * |B i - B' i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hnn i).1, abs_of_nonneg (hnn i).2]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hdc i) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hbc i) (abs_nonneg _))
  unfold potential
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |primitive c b (θ i) (z i) (B i) D (w i) -
        primitive c b (θ i) (z i) (B' i) D' (w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (c * (1 / cw + 1) * ell * w i * |D - D'| +
        c * M * K / cw * ell * |B i - B' i|) := Finset.sum_le_sum fun i _ => hpoint i
    _ = c * (1 / cw + 1) * ell * (∑ i, w i) * |D - D'| +
        c * M * K / cw * ell * (∑ i, |B i - B' i|) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw.2 (by positivity)) (abs_nonneg _)) le_rfl

end KServer.SideTracker

namespace KServer.SideSupported
open Finset
variable {J : Type*} [Fintype J] [DecidableEq J]
def restrict (A : Finset J) (a : J → ℝ) : A → ℝ := fun i => a i

def extend (A : Finset J) (a : A → ℝ) : J → ℝ := fun i => if hi : i∈A then a ⟨i,hi⟩ else 0

omit [Fintype J] in
lemma extend_apply_mem (A : Finset J) (a : A → ℝ) (i : A) : extend A a i=a i := by
  simp [extend,i.property]

omit [Fintype J] in
lemma extend_apply_not_mem (A : Finset J) (a : A → ℝ) {i : J} (hi : i∉A) : extend A a i=0 := by
  simp [extend,hi]

omit [Fintype J] in
lemma restrict_extend (A : Finset J) (a : A → ℝ) : restrict A (extend A a)=a := by
  funext i; exact extend_apply_mem A a i

omit [Fintype J] in
lemma extend_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    extend A (restrict A a)=a := by
  funext i
  by_cases hi : i∈A
  · simp [extend,restrict,hi]
  · simp [extend,hi,ha i hi]

omit [DecidableEq J] in
lemma sum_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    (∑ i : A, a i)=∑ i, a i := by
  rw [←Finset.sum_subtype A (fun _ => Iff.rfl)]
  exact Finset.sum_subset (subset_univ A) fun i _ hi => ha i hi

lemma sum_extend (A : Finset J) (a : A → ℝ) : (∑ i, extend A a i)=∑ i, a i := by
  have he := sum_restrict A (extend A a) (fun i hi => extend_apply_not_mem A a hi)
  simpa only [extend_apply_mem] using he.symm


end KServer.SideSupported

namespace KServer.SideSupported
open Finset SideTracker
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma restrict_mem {A : Finset J} {W : ℝ} {a : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) : restrict A a∈domain W := by
  refine ⟨fun i => ha.1 i, ?_⟩
  simpa only [restrict,sum_restrict A a ha.2.2] using ha.2.1

lemma extend_mem {A : Finset J} {W : ℝ} {a : A → ℝ}
    (ha : a∈domain W) : extend A a∈ChangingDomains.sideDomain A W := by
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [extend]
    split_ifs with hi
    · exact ha.1 ⟨i,hi⟩
    · exact le_rfl
  · simpa only [sum_extend] using ha.2
  · exact fun i hi => extend_apply_not_mem A a hi

omit [DecidableEq J] in
lemma sideDomain_compact (A : Finset J) (W : ℝ) :
    IsCompact (ChangingDomains.sideDomain A W) := by
  have he : ChangingDomains.sideDomain A W=
      (domain W)∩{a : J → ℝ | ∀ i∉A, a i=0} := by
    ext a
    simp only [ChangingDomains.sideDomain,domain,Set.mem_ofPred_eq,Set.mem_inter_iff]
    tauto
  rw [he]
  apply IsCompact.inter_right (domain_isCompact W)
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const

omit [DecidableEq J] in
lemma movement_restrict {A : Finset J} {a b : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hb : ∀ i∉A, b i=0) :
    movement (restrict A a) (restrict A b)=ChangingDomains.variation a b := by
  exact sum_restrict A (fun i => |a i-b i|) (fun i hi => by simp [ha i hi,hb i hi])

omit [DecidableEq J] in
lemma potential_restrict {A : Finset J} {c b D : ℝ} {θ z B a : J → ℝ}
    (ha : ∀ i∉A, a i=0) :
    potential c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a)=
      potential c b θ z B D a := by
  unfold potential restrict
  exact sum_restrict A (fun i => primitive c b (θ i) (z i) (B i) D (a i))
    (fun i hi => by simp [ha i hi,primitive])

lemma restrict_isMin {A : Finset J} {c b D W : ℝ} {θ z B a a₀ : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) (ha₀ : a₀∈ChangingDomains.sideDomain A W)
    (hm : IsMinOn (fun v => potential c b θ z B D v+D*ChangingDomains.variation v a₀)
      (ChangingDomains.sideDomain A W) a) :
    IsMinOn (objective c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a₀))
      (domain W) (restrict A a) := by
  intro v hv
  have he := extend_mem hv
  have hh := hm he
  change potential c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a)+
    D*movement (restrict A a) (restrict A a₀) ≤
    potential c b (restrict A θ) (restrict A z) (restrict A B) D v+
    D*movement v (restrict A a₀)
  rw [potential_restrict ha.2.2,movement_restrict ha.2.2 ha₀.2.2]
  have hp := potential_restrict (c := c) (b := b) (D := D) (θ := θ) (z := z) (B := B) he.2.2
  have hmove := movement_restrict he.2.2 ha₀.2.2
  rw [restrict_extend] at hp hmove
  rw [hp,hmove]
  exact hh

lemma supported_feasible {A : Finset J} {M b D W : ℝ} {θ z B a a₀ : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) (ha₀ : a₀∈ChangingDomains.sideDomain A W)
    (hb : 1≤b) (hθ : ∀ i, 0<θ i) (hz : ∀ i, 0<z i)
    (hB : ∀ i, 0≤B i) (hBz : ∀ i∉A, B i=0) (hD : 0≤D)
    (hM : ∀ i∈A, b+θ i≤M) (hW : 2*M<W)
    (hm : IsMinOn (fun v => potential (8*M) b θ z B D v+D*ChangingDomains.variation v a₀)
      (ChangingDomains.sideDomain A W) a) :
    (∀ i, D*a i≤(b+θ i)*B i) ∧
      ((∑ i, B i)≤2*D → ∀ i, b*B i-θ i*z i*D≤D*a i) := by
  have hm' := restrict_isMin ha ha₀ hm
  have hupper := minimizer_upper hb (fun i : A => hθ i) (fun i : A => hz i)
    (fun i : A => hB i) hD (fun i : A => hM i i.property) (restrict_mem ha) hm'
  constructor
  · intro i
    by_cases hi : i∈A
    · exact hupper ⟨i,hi⟩
    · simp [ha.2.2 i hi,hBz i hi]
  · intro hS
    have hS' : (∑ i : A, B i)≤2*D := by simpa only [sum_restrict A B hBz] using hS
    have hlower := minimizer_lower hb (fun i : A => hθ i) (fun i : A => hz i)
      (fun i : A => hB i) hD (fun i : A => hM i i.property) hW hS' (restrict_mem ha) hm'
    intro i
    by_cases hi : i∈A
    · exact hlower ⟨i,hi⟩
    · simp only [ha.2.2 i hi,hBz i hi,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (hθ i).le (hz i).le) hD)

end KServer.SideSupported

namespace KServer.SideFamilies
open Finset SideTracker AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

structure Data (J R : Type*) where
  active : Finset J
  flags : J → R → Bool
  W : ℝ
  b : ℝ
  D : ℝ
  θ : J → ℝ
  z : J → ℝ
  W_nonneg : 0≤W
  θ_pos : ∀ i, 0<θ i
  z_pos : ∀ i, 0<z i

def core (d : Data J R) (p : J × R → ℝ) (i : J) : ℝ :=
  ∑ r, if d.flags i r then p (i,r) else 0

def coefficient (c : ℝ) (d : Data J R) (a : J → ℝ) (ir : J × R) : ℝ :=
  if d.flags ir.1 ir.2 then -Bcoef c d.b (d.θ ir.1) (d.z ir.1) (a ir.1) else 0

def offset (c : ℝ) (d : Data J R) (a : J → ℝ) : ℝ :=
  d.D * ∑ i, Dcoef c (d.θ i) (d.z i) (a i)

lemma Dcoef_continuousOn {c θ z : ℝ} (hθ : 0<θ) (hz : 0<z) :
    ContinuousOn (Dcoef c θ z) (Set.Ici 0) := by
  have he : Dcoef c θ z=primitive c 0 θ z 0 1 := by
    funext w
    unfold Dcoef primitive
    ring
  rw [he]
  exact primitive_continuousOn hθ hz

lemma Bcoef_continuousOn {c b θ z : ℝ} (hθ : 0<θ) (hz : 0<z) :
    ContinuousOn (Bcoef c b θ z) (Set.Ici 0) := by
  have he : Bcoef c b θ z=fun w => -primitive c b θ z 1 0 w := by
    funext w
    unfold Bcoef primitive
    ring
  rw [he]
  exact (primitive_continuousOn hθ hz).neg

omit [DecidableEq J] [Fintype R] in
lemma coefficient_continuous (c : ℝ) (d : Data J R) (ir : J × R) :
    ContinuousOn (fun a => coefficient c d a ir) (ChangingDomains.sideDomain d.active d.W) := by
  unfold coefficient
  split_ifs
  · exact ((Bcoef_continuousOn (d.θ_pos ir.1) (d.z_pos ir.1)).comp
      (continuous_apply ir.1).continuousOn (fun a ha => ha.1 ir.1)).neg
  · exact continuousOn_const

omit [DecidableEq J] [Fintype R] in
lemma offset_continuous (c : ℝ) (d : Data J R) :
    ContinuousOn (offset c d) (ChangingDomains.sideDomain d.active d.W) := by
  unfold offset
  apply ContinuousOn.const_mul
  exact continuousOn_finsetSum _ fun i _ =>
    (Dcoef_continuousOn (d.θ_pos i) (d.z_pos i)).comp
      (continuous_apply i).continuousOn (fun a ha => ha.1 i)

def family (c : ℝ) : Family (Data J R) (J × R) J where
  domain d := ChangingDomains.sideDomain d.active d.W
  compact d := SideSupported.sideDomain_compact d.active d.W
  seed d := ⟨fun _ => 0,by
    refine ⟨fun _ => le_rfl,?_,fun _ _ => rfl⟩
    simpa using d.W_nonneg⟩
  offset := offset c
  coefficient := coefficient c
  offset_continuous := offset_continuous c
  coefficient_continuous := coefficient_continuous c

omit [DecidableEq J] in
lemma value_eq (c : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ) :
    (family c).value d p a=potential c d.b d.θ d.z (core d p) d.D a := by
  simp only [Family.value,family,offset,coefficient,potential]
  rw [Fintype.sum_prod_type]
  have hi (i : J) : (∑ r, (if d.flags i r then -Bcoef c d.b (d.θ i) (d.z i) (a i) else 0)*p (i,r))=
      -Bcoef c d.b (d.θ i) (d.z i) (a i)*core d p i := by
    rw [core,mul_sum]
    exact sum_congr rfl fun r _ => by split_ifs <;> simp_all
  simp_rw [hi,primitive_coefficients]
  rw [mul_sum,←sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

lemma update_feasible (d : Data J R) {M : ℝ} (hb : 1≤d.b) (hD : 0≤d.D)
    (hM : ∀ i∈d.active, d.b+d.θ i≤M) (hW : 2*M<d.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (hf : ∀ i∉d.active, ∀ r, d.flags i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain d.active d.W) :
    let a' := (family (8*M)).update d p d.D a
    (∀ i, d.D*a' i≤(d.b+d.θ i)*core d p i) ∧
      ((∑ i, core d p i)≤2*d.D → ∀ i,
        d.b*core d p i-d.θ i*d.z i*d.D≤d.D*a' i) := by
  intro a'
  have hB : ∀ i, 0≤core d p i := by
    intro i
    unfold core
    apply sum_nonneg
    intro r _
    split_ifs
    · exact hp (i,r)
    · exact le_rfl
  have hBz : ∀ i∉d.active, core d p i=0 := by
    intro i hi
    simp [core,hf i hi]
  apply SideSupported.supported_feasible ((family (8*M)).update_mem _ _ _ _) ha hb
    d.θ_pos d.z_pos hB hBz hD hM hW
  intro v hv
  have hm := ((family (8*M)).exists_update d p d.D a).choose_spec.2 hv
  change (family (8*M)).value d p a'+d.D*AdaptiveMinimization.movement a' a ≤
    (family (8*M)).value d p v+d.D*AdaptiveMinimization.movement v a at hm
  simpa only [value_eq,AdaptiveMinimization.movement,ChangingDomains.variation, a', Set.mem_ofPred_eq] using hm

omit [DecidableEq J] in
lemma update_payment (c : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (ha : a∈ChangingDomains.sideDomain d.active d.W) :
    let a' := (family c).update d p d.D a
    d.D*ChangingDomains.variation a' a≤
      potential c d.b d.θ d.z (core d p) d.D a-
      potential c d.b d.θ d.z (core d p) d.D a' := by
  have hp := (family c).update_payment d p d.D ha
  simpa only [value_eq,AdaptiveMinimization.movement,ChangingDomains.variation] using hp

end KServer.SideFamilies

namespace KServer.SideFamilies
open Finset SideTracker AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

omit [DecidableEq J] [Fintype R] in
lemma domain_coordinate {d : Data J R} {a : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain d.active d.W) (i : J) :
    a i∈Set.Icc 0 d.W :=
  ⟨ha.1 i,(single_le_sum (fun j _ => ha.1 j) (mem_univ i)).trans ha.2.1⟩

/-- The exact side regularizers obtained from the stored log size. -/
def fromLog (A : Finset J) (f : J → R → Bool) (W b D cw ell : ℝ)
    (h : J → ℝ) (hW : 0≤W) (hcw : 0<cw) (hell : 0<ell) (hh : ∀ i, 1≤h i) : Data J R where
  active := A
  flags := f
  W := W
  b := b
  D := D
  θ i := cw*h i/ell
  z i := Real.exp (1-h i)/h i
  W_nonneg := hW
  θ_pos i := div_pos (mul_pos hcw (lt_of_lt_of_le zero_lt_one (hh i))) hell
  z_pos i := div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))

omit [DecidableEq J] [Fintype R] in
lemma fromLog_input_bound {A : Finset J} (_flags : J → R → Bool)
    {W b cw ell c M D D' : ℝ} (h : J → ℝ)
    (hW : 0≤W) (hcw : 0<cw) (hell : 1≤ell) (hh : ∀ i, 1≤h i)
    (hc : 0≤c) (hb : 0≤b) (hM : ∀ i, b+cw*h i/ell≤M)
    {a B B' : J → ℝ} (ha : a∈ChangingDomains.sideDomain A W) :
    |potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B D a-
      potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B' D' a|≤
      c*(1/cw+1)*ell*W*|D-D'|+
        c*M*(Real.log (1+W)+2)/cw*ell*ChangingDomains.variation B B' := by
  have hp : 0<ell := lt_of_lt_of_le zero_lt_one hell
  apply potential_input_bound hc hb hcw hell
    (fun i => div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))) hh
    (fun _ => rfl)
  · intro i
    have ht : 0≤cw*h i/ell := div_nonneg (mul_nonneg hcw.le (le_trans zero_le_one (hh i))) hp.le
    linarith [hM i]
  · intro i
    apply side_log_bound (hh i) hW
    exact ⟨ha.1 i,(single_le_sum (fun j _ => ha.1 j) (mem_univ i)).trans ha.2.1⟩
  · exact ⟨ha.1,ha.2.1⟩

omit [DecidableEq J] in
lemma parameter_jump {W b cw ell c M D : ℝ} {h h' B a : J → ℝ}
    (hW : 0≤W) (hcw : 0<cw) (hell : 1≤ell)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (hc : 0≤c) (hb : 0≤b) (hD : 0≤D) (hB : ∀ i, 0≤B i)
    (hM : ∀ i, b+cw*h i/ell≤M) (hM' : ∀ i, b+cw*h' i/ell≤M)
    (ha : a∈domain W) (hcap : ∀ i, D*a i≤M*B i) :
    |potential c b (fun i => cw*h' i/ell) (fun i => Real.exp (1-h' i)/h' i) B D a-
      potential c b (fun i => cw*h i/ell) (fun i => Real.exp (1-h i)/h i) B D a|≤
      2*(c*(1/cw+1)*M+c*M*(Real.log (1+W)+2)/cw)*ell*
        (∑ i, if h i=h' i then 0 else B i) := by
  have hp : 0<ell := lt_of_lt_of_le zero_lt_one hell
  have hw (i : J) : a i∈Set.Icc 0 W :=
    ⟨ha.1 i,(single_le_sum (fun j _ => ha.1 j) (mem_univ i)).trans ha.2⟩
  have hbound (q : J → ℝ) (hq : ∀ i, 1≤q i) (hMq : ∀ i, b+cw*q i/ell≤M) (i : J) :
      |primitive c b (cw*q i/ell) (Real.exp (1-q i)/q i) (B i) D (a i)|≤
        (c*(1/cw+1)*M+c*M*(Real.log (1+W)+2)/cw)*ell*B i := by
    have ht : 0≤cw*q i/ell := div_nonneg (mul_nonneg hcw.le (le_trans zero_le_one (hq i))) hp.le
    have he := primitive_component_bound hc hb
      (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hq i))) (ha.1 i)
      hcw hell (hq i) rfl (show b+(cw*q i/ell)/2≤M by linarith [hMq i])
      (side_log_bound (hq i) hW (hw i)) (hB i) hD
    have hcap' := mul_le_mul_of_nonneg_left (hcap i)
      (show 0≤c*(1/cw+1)*ell by positivity)
    calc
      _ ≤ c*(1/cw+1)*ell*(D*a i)+
        c*M*(Real.log (1+W)+2)/cw*ell*B i := he
      _ ≤ c*(1/cw+1)*ell*(M*B i)+
        c*M*(Real.log (1+W)+2)/cw*ell*B i := add_le_add hcap' le_rfl
      _ = _ := by ring
  unfold potential
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : h i=h' i
  · simp [hi]
  · rw [ite_eq_right hi]
    have ho := hbound h hh hM i
    have hn := hbound h' hh' hM' i
    exact (abs_sub _ _).trans (by linarith)

/-- Synthetic ranks use the new flags on the intersection of active sets. -/
def prepareData (old new : Data J R) : Data J R :=
  {old with flags := ChangingDomains.syntheticFlags old.active new.active new.flags, D := new.D}

def prepare (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family c).update (prepareData old new) p new.D a

def transport (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSide new.active (prepare c old new p a)

def step (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family c).update new p new.D (transport c old new p a)

lemma prepare_mem (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) :
    prepare c old new p a∈ChangingDomains.sideDomain old.active old.W :=
  (family c).update_mem _ _ _ _

lemma transport_mem (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (hW : old.W=new.W) :
    transport c old new p a∈ChangingDomains.sideDomain new.active new.W := by
  rw [←hW]
  exact ChangingDomains.transposeSide_mem (prepare_mem c old new p a)

lemma step_mem (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) :
    step c old new p a∈ChangingDomains.sideDomain new.active new.W :=
  (family c).update_mem _ _ _ _

omit [Fintype J] in
lemma prepared_core_zero (old new : Data J R) (p : J × R → ℝ)
    {i : J} (hi : i∉old.active∩new.active) : core (prepareData old new) p i=0 := by
  simp [core,prepareData,ChangingDomains.syntheticFlags,hi]

lemma transport_payment (old new : Data J R) {M : ℝ}
    (hb : 1≤old.b) (hD : 0≤new.D)
    (hM : ∀ i∈old.active, old.b+old.θ i≤M) (hW : 2*M<old.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain old.active old.W) :
    new.D*ChangingDomains.variation (transport (8*M) old new p a)
      (prepare (8*M) old new p a)=0 := by
  have hfeas := update_feasible (prepareData old new) hb hD hM hW p hp
    (fun i hi r => by
      change i∉old.active at hi
      simp [prepareData,ChangingDomains.syntheticFlags,hi]) a ha
  exact ChangingDomains.transposeSide_payment (prepare_mem (8*M) old new p a).1 hD
    hfeas.1 (fun i hi => prepared_core_zero old new p (by simp [hi]))

lemma transport_value (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (hzero : new.D*ChangingDomains.variation (transport c old new p a)
      (prepare c old new p a)=0) :
    (family c).value (prepareData old new) p (transport c old new p a)=
      (family c).value (prepareData old new) p (prepare c old new p a) := by
  rw [value_eq,value_eq]
  unfold potential
  apply sum_congr rfl
  intro i _
  by_cases hi : i∈new.active
  · simp [transport,ChangingDomains.transposeSide,hi]
  · have hB : core (prepareData old new) p i=0 :=
      prepared_core_zero old new p (by simp [hi])
    by_cases hD : new.D=0
    · rw [hB]
      change primitive c old.b (old.θ i) (old.z i) 0 new.D _ =
        primitive c old.b (old.θ i) (old.z i) 0 new.D _
      simp [hD,primitive]
    · have hvar : ChangingDomains.variation (transport c old new p a)
          (prepare c old new p a)=0 := (mul_eq_zero.mp hzero).resolve_left hD
      have hd := single_le_sum (s := univ)
        (f := fun j => |transport c old new p a j-prepare c old new p a j|)
        (fun j _ => abs_nonneg _) (mem_univ i)
      change |transport c old new p a i-prepare c old new p a i|≤
        ChangingDomains.variation (transport c old new p a) (prepare c old new p a) at hd
      rw [hvar] at hd
      have he := sub_eq_zero.mp (abs_nonpos_iff.mp hd)
      rw [he]

/-- Local side edit payment for the actual two minimizers and deletion.  The
potential discrepancy terms will be bounded with the literal log parameters. -/
lemma step_payment (old new : Data J R) {M : ℝ}
    (hb : 1≤old.b) (hD : 0≤new.D)
    (hM : ∀ i∈old.active, old.b+old.θ i≤M) (hW : 2*M<old.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain old.active old.W)
    (hWW : old.W=new.W) :
    new.D*ChangingDomains.variation (step (8*M) old new p a) a ≤
      (family (8*M)).value old p a-(family (8*M)).value new p (step (8*M) old new p a)+
      |(family (8*M)).value (prepareData old new) p a-(family (8*M)).value old p a|+
      |(family (8*M)).value new p (transport (8*M) old new p a)-
        (family (8*M)).value (prepareData old new) p (transport (8*M) old new p a)| := by
  have hz := transport_payment old new hb hD hM hW p hp a ha
  have he := transport_value (8*M) old new p a hz
  have h₁ := (family (8*M)).update_payment (prepareData old new) p new.D ha
  have h₂ := (family (8*M)).update_payment new p new.D (transport_mem (8*M) old new p a hWW)
  have hm₁ := ChangingDomains.variation_triangle (step (8*M) old new p a)
    (transport (8*M) old new p a) a
  have hm₂ := ChangingDomains.variation_triangle (transport (8*M) old new p a)
    (prepare (8*M) old new p a) a
  have hp₁ := mul_le_mul_of_nonneg_left hm₁ hD
  have hp₂ := mul_le_mul_of_nonneg_left hm₂ hD
  change new.D*ChangingDomains.variation (prepare (8*M) old new p a) a ≤
    (family (8*M)).value (prepareData old new) p a-
      (family (8*M)).value (prepareData old new) p (prepare (8*M) old new p a) at h₁
  change new.D*ChangingDomains.variation (step (8*M) old new p a)
    (transport (8*M) old new p a) ≤
    (family (8*M)).value new p (transport (8*M) old new p a)-
      (family (8*M)).value new p (step (8*M) old new p a) at h₂
  have hab₁ := le_abs_self ((family (8*M)).value (prepareData old new) p a-(family (8*M)).value old p a)
  have hab₂ := le_abs_self ((family (8*M)).value new p (transport (8*M) old new p a)-
    (family (8*M)).value (prepareData old new) p (transport (8*M) old new p a))
  nlinarith

end KServer.SideFamilies

end
end
end

end OAI
