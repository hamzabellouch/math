import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Avg
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DivisorPrimeFactor
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedMatrixBilinear
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPowLeGramTrace
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumFinFunSucc

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.Localization
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h ℓ L D₀ : ℕ}

def Adj (D : S.DivisorFamily B τ C₀) (h : ℕ) (x y : ℤ) : Prop :=
  ∃ d ∈ D.members, y = x+(h:ℤ)*d ∨ x = y+(h:ℤ)*d

lemma adj_ne (D : S.DivisorFamily B τ C₀) (hh : 0<h) {x y : ℤ}
    (he : Adj D h x y) : x ≠ y := by
  obtain ⟨d,hd,he⟩ := he
  have hp : (0:ℤ)<h := by exact_mod_cast hh
  have hd' : (0:ℤ)<d := by exact_mod_cast (lt_trans Nat.zero_lt_one (D.greater_one d hd))
  rintro rfl
  rcases he with he | he <;> nlinarith [mul_pos hp hd']

def WindowWalk (D : S.DivisorFamily B τ C₀) (h ℓ D₀ : ℕ) :=
  {v : Fin (ℓ+1) → Fin D₀ // v (Fin.last ℓ) = v 0 ∧
    ∀ i : Fin ℓ, Adj D h ((v i.castSucc).val:ℤ) ((v i.succ).val:ℤ)}

instance (D : S.DivisorFamily B τ C₀) (h ℓ D₀ : ℕ) : Fintype (WindowWalk D h ℓ D₀) :=
  inferInstanceAs (Fintype {_walk : Fin (ℓ+1) → Fin D₀ // _})

namespace WindowWalk
variable {D : S.DivisorFamily B τ C₀}

def label (w : WindowWalk D h ℓ D₀) (i : Fin ℓ) : ℕ :=
  (w.property.2 i).choose
lemma label_mem (w : WindowWalk D h ℓ D₀) (i : Fin ℓ) : w.label i ∈ D.members :=
  (w.property.2 i).choose_spec.1
lemma label_step (w : WindowWalk D h ℓ D₀) (i : Fin ℓ) :
    ((w.val i.succ).val:ℤ) = (w.val i.castSucc).val+(h:ℤ)*w.label i ∨
      ((w.val i.castSucc).val:ℤ)=(w.val i.succ).val+(h:ℤ)*w.label i :=
  (w.property.2 i).choose_spec.2

def sign (w : WindowWalk D h ℓ D₀) (i : Fin ℓ) : ℤ :=
  if (w.val i.castSucc).val < (w.val i.succ).val then 1 else -1

def line (w : WindowWalk D h ℓ D₀) (hh : 0<h) : NumericalLine D h ℓ where
  line := {
    offset := fun i => (w.val i).val-(w.val 0).val
    label := w.label
    sign := w.sign
    label_pos := fun i => Nat.zero_lt_one.trans (D.greater_one _ (w.label_mem i))
    sign_mem := fun i => by unfold sign; split_ifs <;> simp
    start_zero := sub_self _
    end_zero := by rw [w.property.1]; exact sub_self _
    step := by
      intro i
      have hp : (0:ℤ)<h := by exact_mod_cast hh
      have hd : (0:ℤ)<w.label i := by
        exact_mod_cast Nat.zero_lt_one.trans (D.greater_one _ (w.label_mem i))
      have hi := w.label_step i
      unfold sign
      split_ifs with he
      · have he' : ((w.val i.castSucc).val:ℤ)<(w.val i.succ).val := by exact_mod_cast he
        rcases hi with hi | hi <;> nlinarith [mul_pos hp hd]
      · have he' : ((w.val i.succ).val:ℤ)≤(w.val i.castSucc).val := by exact_mod_cast (le_of_not_gt he)
        rcases hi with hi | hi <;> nlinarith [mul_pos hp hd]
  }
  labels := w.label_mem

lemma encode_injective (hh : 0<h) : Function.Injective
    (fun w : WindowWalk D h ℓ D₀ => (w.val 0, w.line hh)) := by
  intro w v he
  have he0 := congrArg Prod.fst he
  have hel := congrArg (fun z => z.2.line.offset) he
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrFun hel i
  change (w.val i).val-(w.val 0).val = ((v.val i).val:ℤ)-(v.val 0).val at hi
  have he00 := congrArg (fun x : Fin D₀ => (x.val:ℤ)) he0
  have hi' : ((w.val i).val:ℤ)=(v.val i).val := by linarith
  exact_mod_cast hi'

end WindowWalk

lemma integer_vertex_shift (n s b : ℤ) :
    S.vertexWeight (S.integerResidues n) b =
      S.vertexWeight (S.integerResidues (n+s)) (b-s) := by
  simp only [vertexWeight, integerResidues, Int.cast_add, Int.cast_sub]
  congr 1
  funext p
  congr 2
  ring_nf

lemma integer_edge_shift (cut : S.Cutoffs T) (n s : ℤ) (d : ℕ) (b c : ℤ) :
    S.divisorEdgeWeight cut (S.integerResidues n) d b c =
      S.divisorEdgeWeight cut (S.integerResidues (n+s)) d (b-s) (c-s) := by
  have hc (b : ℤ) : S.shiftCore (S.restrictCore (S.integerResidues n)) b =
      S.shiftCore (S.restrictCore (S.integerResidues (n+s))) (b-s) := by
    funext p
    simp only [shiftCore, restrictCore, integerResidues, Int.cast_add, Int.cast_sub]
    ring
  have hp (b : ℤ) (p : S.Index) : S.divisorPrimeFactor (S.integerResidues n) b p =
      S.divisorPrimeFactor (S.integerResidues (n+s)) (b-s) p := by
    simp only [divisorPrimeFactor, activity, integerResidues, Int.cast_add, Int.cast_sub,
      show ((n:ZMod (p:ℕ))+s)+((b:ZMod (p:ℕ))-s)=(n:ZMod (p:ℕ))+b by ring]
    rfl
  simp only [divisorEdgeWeight, hc, hp]

def edgeCoeff (D : S.DivisorFamily B τ C₀) (h : ℕ) (a : ℕ→ℂ) (x y : ℤ) : ℂ :=
  ∑ d ∈ D.members,
    if y=x+(h:ℤ)*d then a d else if x=y+(h:ℤ)*d then star (a d) else 0

lemma edgeCoeff_zero (D : S.DivisorFamily B τ C₀) (h : ℕ) (a : ℕ→ℂ) (x y : ℤ)
    (he : ¬Adj D h x y) : edgeCoeff D h a x y=0 := by
  apply sum_eq_zero
  intro d hd
  have h1 : y≠x+(h:ℤ)*d := fun h => he ⟨d,hd,Or.inl h⟩
  have h2 : x≠y+(h:ℤ)*d := fun h => he ⟨d,hd,Or.inr h⟩
  simp only [h1,h2,ite_false]

lemma label_unique (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    {x y : ℤ} {d e : ℕ} (hd : d∈D.members) (he : e∈D.members)
    (hdxy : y=x+(h:ℤ)*d ∨ x=y+(h:ℤ)*d)
    (hexy : y=x+(h:ℤ)*e ∨ x=y+(h:ℤ)*e) : d=e := by
  have hp : (0:ℤ)<h := by exact_mod_cast hh
  have hdp : (0:ℤ)<d := by exact_mod_cast (Nat.zero_lt_one.trans (D.greater_one d hd))
  have hep : (0:ℤ)<e := by exact_mod_cast (Nat.zero_lt_one.trans (D.greater_one e he))
  have eq : (d:ℤ)=e := by
    rcases hdxy with hdxy | hdxy <;> rcases hexy with hexy | hexy
    all_goals nlinarith [mul_pos hp hdp,mul_pos hp hep]
  exact_mod_cast eq

lemma edgeCoeff_eq (D : S.DivisorFamily B τ C₀) (hh : 0<h) (a : ℕ→ℂ)
    {x y : ℤ} {d : ℕ} (hd : d∈D.members)
    (hdxy : y=x+(h:ℤ)*d ∨ x=y+(h:ℤ)*d) :
    edgeCoeff D h a x y = if x<y then a d else star (a d) := by
  have hp : (0:ℤ)<h := by exact_mod_cast hh
  have hdp : (0:ℤ)<d := by exact_mod_cast (Nat.zero_lt_one.trans (D.greater_one d hd))
  unfold edgeCoeff
  rw [sum_eq_single d]
  · rcases hdxy with hdxy | hdxy
    · have hlt : x<y := by nlinarith [mul_pos hp hdp]
      rw [ite_eq_left hdxy, ite_eq_left hlt]
    · have hlt : y<x := by nlinarith [mul_pos hp hdp]
      have hn : y≠x+(h:ℤ)*d := by nlinarith [mul_pos hp hdp]
      rw [ite_eq_right hn, ite_eq_left hdxy, ite_eq_right (not_lt.mpr hlt.le)]
  · intro e he hed
    have hn : ¬ (y=x+(h:ℤ)*e ∨ x=y+(h:ℤ)*e) := by
      intro hexy
      exact hed (label_unique D hh he hd hexy hdxy)
    simp only [not_or] at hn
    simp only [hn.1,hn.2,ite_false]
  · exact fun hn => (hn hd).elim

def symMatrix (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (a : ℕ → ℂ) (D₀ : ℕ) (n : ℤ) : Matrix (Fin D₀) (Fin D₀) ℂ := fun x y =>
  if VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val) then
    ∑ d∈D.members,
      (if (y.val:ℤ)=x.val+(h:ℤ)*d ∨ (x.val:ℤ)=y.val+(h:ℤ)*d then
        if x.val<y.val then a d else star (a d) else 0) *
      ((S.divisorEdgeWeight cut (S.integerResidues n) d x.val y.val /
        Real.sqrt (S.vertexWeight (S.integerResidues n) x.val *
          S.vertexWeight (S.integerResidues n) y.val)):ℝ)
  else 0

lemma symMatrix_zero (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (a : ℕ → ℂ) (n : ℤ) (x y : Fin D₀)
    (he : ¬Adj D h (x.val:ℤ) y.val) : symMatrix D h L cut a D₀ n x y=0 := by
  unfold symMatrix
  split
  · apply sum_eq_zero
    intro d hd
    have hn : ¬((y.val:ℤ)=x.val+(h:ℤ)*d ∨ (x.val:ℤ)=y.val+(h:ℤ)*d) :=
      fun hexy => he ⟨d,hd,hexy⟩
    simp only [hn,ite_false,zero_mul]
  · rfl

lemma symMatrix_entry (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (n : ℤ) (x y : Fin D₀)
    (d : ℕ) (hd : d∈D.members)
    (he : (y.val:ℤ)=x.val+(h:ℤ)*d ∨ (x.val:ℤ)=y.val+(h:ℤ)*d) :
    symMatrix D h L cut a D₀ n x y=
      if VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val) then
        (if x.val<y.val then a d else star (a d)) *
        ((S.divisorEdgeWeight cut (S.integerResidues n) d x.val y.val /
          Real.sqrt (S.vertexWeight (S.integerResidues n) x.val *
            S.vertexWeight (S.integerResidues n) y.val)):ℝ)
      else 0 := by
  unfold symMatrix
  split
  · rw [sum_eq_single d,ite_eq_left he]
    · intro e he' hed
      have hn : ¬((y.val:ℤ)=x.val+(h:ℤ)*e ∨ (x.val:ℤ)=y.val+(h:ℤ)*e) := by
        intro hex
        exact hed (label_unique D hh he' hd hex he)
      simp only [hn,ite_false,zero_mul]
    · exact fun hn => (hn hd).elim
  · rfl

lemma symMatrix_hermitian (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (n : ℤ) :
    (symMatrix D h L cut a D₀ n).IsHermitian := by
  ext x y
  change star (symMatrix D h L cut a D₀ n y x) = symMatrix D h L cut a D₀ n x y
  by_cases he : Adj D h (x.val:ℤ) y.val
  · obtain ⟨d,hd,he⟩ := he
    rw [symMatrix_entry D hh L cut a n x y d hd he,
      symMatrix_entry D hh L cut a n y x d hd he.symm]
    have hne : x.val ≠ y.val := by
      intro hxy
      exact adj_ne D hh ⟨d,hd,he⟩ (by exact_mod_cast hxy)
    have hdiv : (d:ℤ)∣(y.val:ℤ)-x.val := by
      rcases he with he | he
      · refine ⟨h,?_⟩; rw [he]; ring
      · refine ⟨-(h:ℤ),?_⟩; rw [he]; ring
    have hsym := divisorEdgeWeight_symm cut (S.integerResidues n) d x.val y.val hdiv
    by_cases hy : VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val)
    · rw [ite_eq_left hy,ite_eq_left hy.symm,Complex.star_def,map_mul,Complex.conj_ofReal,
        ←hsym,mul_comm (S.vertexWeight (S.integerResidues n) (y.val:ℤ))]
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · simp only [hxy,not_lt.mpr hxy.le,ite_true,ite_false,Complex.conj_conj]
      · simp only [hyx,not_lt.mpr hyx.le,ite_true,ite_false]
    · have hy' : ¬(VertexAllowed D h L (n+y.val) ∧ VertexAllowed D h L (n+x.val)) :=
        fun hx => hy hx.symm
      simp only [hy,hy',ite_false,star_zero]
  · have he' : ¬Adj D h (y.val:ℤ) x.val := by
      rintro ⟨d,hd,he'⟩
      exact he ⟨d,hd,he'.symm⟩
    rw [symMatrix_zero D h L cut a n x y he, symMatrix_zero D h L cut a n y x he',star_zero]

lemma walk_allowed_iff {D : S.DivisorFamily B τ C₀}
    (w : WindowWalk D h ℓ D₀) (hℓ : 0<ℓ) (P : Fin D₀ → Prop) :
    (∀ i : Fin ℓ,P (w.val i.castSucc) ∧ P (w.val i.succ)) ↔
      ∀ i : Fin (ℓ+1), P (w.val i) := by
  constructor
  · intro he i
    refine Fin.lastCases ?_ (fun i => (he i).1) i
    rw [w.property.1]
    exact (he ⟨0,hℓ⟩).1
  · exact fun he i => ⟨he _,he _⟩

namespace WindowWalk
variable {D : S.DivisorFamily B τ C₀}

def coefficient (w : WindowWalk D h ℓ D₀) (a : ℕ→ℂ) : ℂ :=
  ∏ i : Fin ℓ,if (w.val i.castSucc).val < (w.val i.succ).val then a (w.label i)
    else star (a (w.label i))

lemma coefficient_norm (w : WindowWalk D h ℓ D₀) (a : ℕ→ℂ)
    (ha : ∀ d∈D.members,‖a d‖≤1) : ‖w.coefficient a‖≤1 := by
  rw [coefficient,norm_prod]
  apply prod_le_one₀ (fun i hi => norm_nonneg _)
  intro i hi
  split_ifs <;> simpa only [norm_star] using ha _ (w.label_mem i)

lemma matrix_product (w : WindowWalk D h ℓ D₀) (hh : 0<h) (hℓ : 0<ℓ)
    (L : ℕ) (cut : S.Cutoffs T) (a : ℕ→ℂ) (n : ℤ) :
    matrixWalkProduct (symMatrix D h L cut a D₀ n) ℓ w.val =
      w.coefficient a * ((S.chronologicalKernel (w.line hh).line cut
        (S.integerResidues (n+(w.val 0).val)) * allowedIndicator (w.line hh).line D L
        (S.integerResidues (n+(w.val 0).val))):ℝ) := by
  have he (i : Fin ℓ) := symMatrix_entry D hh L cut a n (w.val i.castSucc)
    (w.val i.succ) (w.label i) (w.label_mem i) (w.label_step i)
  have hp : (∏ i : Fin ℓ,S.divisorEdgeWeight cut (S.integerResidues n) (w.label i)
      (w.val i.castSucc).val (w.val i.succ).val /
        Real.sqrt (S.vertexWeight (S.integerResidues n) (w.val i.castSucc).val *
          S.vertexWeight (S.integerResidues n) (w.val i.succ).val)) =
      S.chronologicalKernel (w.line hh).line cut (S.integerResidues (n+(w.val 0).val)) := by
    rw [←normalized_closedLine_product]
    apply prod_congr rfl
    intro i hi
    rw [integer_edge_shift cut n (w.val 0).val,
      integer_vertex_shift n (w.val 0).val (w.val i.castSucc).val,
      integer_vertex_shift n (w.val 0).val (w.val i.succ).val]
    rfl
  have hY : allowedIndicator (w.line hh).line D L
      (S.integerResidues (n+(w.val 0).val)) =
      if ∀ i : Fin (ℓ+1),VertexAllowed D h L (n+(w.val i).val) then 1 else 0 := by
    rw [allowedIndicator_integer]
    have heq (i : Fin (ℓ+1)) : n+(w.val 0).val+(w.line hh).line.offset i =
        n+(w.val i).val := by change n+(w.val 0).val+((w.val i).val-(w.val 0).val)=_; ring
    simp_rw [heq]
    simp only [Fintype.prod_ite_zero,Finset.prod_const_one]
  simp only [matrixWalkProduct,he,Fintype.prod_ite_zero,
    walk_allowed_iff w hℓ (fun x => VertexAllowed D h L (n+x.val)),hY]
  split_ifs
  · rw [prod_mul_distrib,←Complex.ofReal_prod,hp]
    simp only [coefficient,mul_one]
  · simp only [mul_zero,Complex.ofReal_zero]

end WindowWalk

lemma matrix_trace (D : S.DivisorFamily B τ C₀) (h L ℓ D₀ : ℕ) (cut : S.Cutoffs T)
    (a : ℕ → ℂ) (n : ℤ) :
    ((symMatrix D h L cut a D₀ n)^ℓ).trace =
      ∑ w : WindowWalk D h ℓ D₀,matrixWalkProduct (symMatrix D h L cut a D₀ n) ℓ w.val := by
  rw [matrix_trace_walks]
  have heq := Finset.sum_subtype
    (p := fun v : Fin (ℓ+1) → Fin D₀ => v (Fin.last ℓ)=v 0 ∧
      ∀ i : Fin ℓ,Adj D h (v i.castSucc).val (v i.succ).val)
    (F := inferInstance)
    (univ.filter (fun v : Fin (ℓ+1) → Fin D₀ => v (Fin.last ℓ)=v 0 ∧
      ∀ i : Fin ℓ,Adj D h (v i.castSucc).val (v i.succ).val)) (by simp)
    (fun v => matrixWalkProduct (symMatrix D h L cut a D₀ n) ℓ v)
  change _ = ∑ w : {v : Fin (ℓ+1) → Fin D₀ // v (Fin.last ℓ)=v 0 ∧
      ∀ i : Fin ℓ,Adj D h (v i.castSucc).val (v i.succ).val},_
  rw [←heq,Finset.sum_filter]
  apply sum_congr rfl
  intro v hv
  by_cases hc : v (Fin.last ℓ)=v 0
  · rw [ite_eq_left hc]
    by_cases he : ∀ i : Fin ℓ,Adj D h (v i.castSucc).val (v i.succ).val
    · simp [hc,he]
    · simp only [hc,he,true_and,ite_false]
      push Not at he
      obtain ⟨i,hi⟩ := he
      exact prod_eq_zero (mem_univ i) (symMatrix_zero D h L cut a n _ _ hi)
  · simp only [hc,false_and,ite_false]

open scoped Matrix.Norms.L2Operator
lemma matrix_norm_moment (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (n : ℤ) (hD : 0<D₀) (m : ℕ) :
    ‖symMatrix D h L cut a D₀ n‖^(2*m) ≤ ((symMatrix D h L cut a D₀ n)^(2*m)).trace.re := by
  let : Nonempty (Fin D₀) := ⟨⟨0,hD⟩⟩
  have hb := norm_pow_le_gram_trace (symMatrix D h L cut a D₀ n) m
  rw [symMatrix_hermitian D hh L cut a n,←pow_two,←pow_mul] at hb
  exact hb

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
