import Mathlib
import OAI.Probability.UnimodularPercolation.Criticality.Sharpness

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedExploration

 
theorem centered_bernoulli_mgf_le (p : unitInterval) (lam : ℝ) :
    (1-(p:ℝ))*Real.exp (-lam*p) + p*Real.exp (lam*(1-p)) ≤ Real.exp (lam^2/8) := by
  let X : Bool → ℝ := fun b => if b then 1-(p:ℝ) else -(p:ℝ)
  have hb : ∀ᵐ b ∂bernoulliMeasure true false p, X b ∈ Set.Icc (-(p:ℝ)) (1-p) := by
    filter_upwards with b
    cases b <;> simp [X]
  have hc : ∫ b, X b ∂bernoulliMeasure true false p = 0 := by
    rw [integral_bernoulliMeasure]
    simp [X]
    ring
  have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := bernoulliMeasure true false p) (X := X)
    (Measurable.of_discrete.aemeasurable) hb hc
  have hh := hg.mgf_le lam
  simp only [mgf,integral_bernoulliMeasure] at hh
  norm_num [X,sub_neg_eq_add,sub_add_cancel,smul_eq_mul] at hh
  rw [show (1/4:ℝ)*lam^2/2 = lam^2/8 by ring] at hh
  simpa only [neg_mul,add_comm] using hh

 
inductive ProbeTree where
  | done (success : Bool)
  | edge (closed open_ : ProbeTree)
  | mark (unmarked marked : ProbeTree)

namespace ProbeTree

@[reducible] def Leaf : ProbeTree → Type
  | .done _ => Unit
  | .edge t₀ t₁ => Leaf t₀ ⊕ Leaf t₁
  | .mark t₀ t₁ => Leaf t₀ ⊕ Leaf t₁

instance leafFintype : (t : ProbeTree) → Fintype t.Leaf
  | .done _ => inferInstanceAs (Fintype Unit)
  | .edge t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)
  | .mark t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)

noncomputable def weight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 1
  | .edge t₀ _, .inl l => (1-p)*weight p h t₀ l
  | .edge _ t₁, .inr l => p*weight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*weight p h t₀ l
  | .mark _ t₁, .inr l => h*weight p h t₁ l

noncomputable def score (p : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => score p t₀ l-p
  | .edge _ t₁, .inr l => score p t₁ l+(1-p)
  | .mark t₀ _, .inl l => score p t₀ l
  | .mark _ t₁, .inr l => score p t₁ l

def queries : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => queries t₀ l+1
  | .edge _ t₁, .inr l => queries t₁ l+1
  | .mark t₀ _, .inl l => queries t₀ l
  | .mark _ t₁, .inr l => queries t₁ l

@[reducible] def outcome : (t : ProbeTree) → t.Leaf → Bool
  | .done b, _ => b
  | .edge t₀ _, .inl l => outcome t₀ l
  | .edge _ t₁, .inr l => outcome t₁ l
  | .mark t₀ _, .inl l => outcome t₀ l
  | .mark _ t₁, .inr l => outcome t₁ l

lemma weight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ weight p h t l := by
  induction t with
  | done b => exact zero_le_one
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr p.2.2) (ih₀ l)
    | inr l => exact mul_nonneg p.2.1 (ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_nonneg (sub_nonneg.mpr h.2.2) (ih₀ l)
    | inr l => exact mul_nonneg h.2.1 (ih₁ l)

lemma sum_weight (p h : ℝ) (t : ProbeTree) : ∑ l, weight p h t l = 1 := by
  induction t with
  | done b => change (∑ _ : Unit, (1:ℝ)) = 1; simp
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) = 1
    simp only [Fintype.sum_sum_type,weight,← Finset.mul_sum,ih₀,ih₁]
    ring

 
theorem score_mgf (p h : unitInterval) (lam : ℝ) (t : ProbeTree) :
    ∑ l, weight p h t l * Real.exp (lam*score p t l-lam^2*(queries t l : ℝ)/8) ≤ 1 := by
  induction t with
  | done b => change (∑ l : Unit, _) ≤ (1:ℝ); simp [weight,score,queries]
  | edge t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) ≤ (1:ℝ)
    rw [Fintype.sum_sum_type]
    have h₀ (l : t₀.Leaf) :
        weight p h (.edge t₀ t₁) (.inl l) *
          Real.exp (lam*score p (.edge t₀ t₁) (.inl l)-lam^2*(queries (.edge t₀ t₁) (.inl l):ℝ)/8) =
        ((1-(p:ℝ))*Real.exp (-lam*p-lam^2/8)) *
          (weight p h t₀ l * Real.exp (lam*score p t₀ l-lam^2*(queries t₀ l:ℝ)/8)) := by
      simp only [weight,score,queries,Nat.cast_add,Nat.cast_one]
      rw [show lam*(score p t₀ l-p)-lam^2*((queries t₀ l:ℝ)+1)/8 =
        (-lam*p-lam^2/8)+(lam*score p t₀ l-lam^2*(queries t₀ l:ℝ)/8) by ring,Real.exp_add]
      ring
    have h₁ (l : t₁.Leaf) :
        weight p h (.edge t₀ t₁) (.inr l) *
          Real.exp (lam*score p (.edge t₀ t₁) (.inr l)-lam^2*(queries (.edge t₀ t₁) (.inr l):ℝ)/8) =
        ((p:ℝ)*Real.exp (lam*(1-p)-lam^2/8)) *
          (weight p h t₁ l * Real.exp (lam*score p t₁ l-lam^2*(queries t₁ l:ℝ)/8)) := by
      simp only [weight,score,queries,Nat.cast_add,Nat.cast_one]
      rw [show lam*(score p t₁ l+(1-p))-lam^2*((queries t₁ l:ℝ)+1)/8 =
        (lam*(1-p)-lam^2/8)+(lam*score p t₁ l-lam^2*(queries t₁ l:ℝ)/8) by ring,Real.exp_add]
      ring
    simp only [h₀,h₁,← Finset.mul_sum]
    have hc₀ : 0 ≤ (1-(p:ℝ))*Real.exp (-lam*p-lam^2/8) :=
      mul_nonneg (sub_nonneg.mpr p.2.2) (Real.exp_pos _).le
    have hc₁ : 0 ≤ (p:ℝ)*Real.exp (lam*(1-p)-lam^2/8) :=
      mul_nonneg p.2.1 (Real.exp_pos _).le
    calc
      _ ≤ (1-(p:ℝ))*Real.exp (-lam*p-lam^2/8) + p*Real.exp (lam*(1-p)-lam^2/8) := by
        simpa using add_le_add (mul_le_mul_of_nonneg_left ih₀ hc₀) (mul_le_mul_of_nonneg_left ih₁ hc₁)
      _ = ((1-(p:ℝ))*Real.exp (-lam*p)+p*Real.exp (lam*(1-p))) / Real.exp (lam^2/8) := by
        simp only [Real.exp_sub]; ring
      _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (centered_bernoulli_mgf_le p lam)
  | mark t₀ t₁ ih₀ ih₁ =>
    change (∑ l : t₀.Leaf ⊕ t₁.Leaf, _) ≤ (1:ℝ)
    simp only [Fintype.sum_sum_type,weight,score,queries,mul_assoc,← Finset.mul_sum]
    calc
      _ ≤ (1-(h:ℝ))*1+(h:ℝ)*1 :=
        add_le_add (mul_le_mul_of_nonneg_left ih₀ (sub_nonneg.mpr h.2.2))
          (mul_le_mul_of_nonneg_left ih₁ h.2.1)
      _ = 1 := by ring

noncomputable def successWeight (p h : ℝ) (t : ProbeTree) (l : t.Leaf) : ℝ :=
  if outcome t l then weight p h t l else 0

noncomputable def successMass (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l

noncomputable def successScore (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * score p t l

noncomputable def successQueries (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * queries t l

lemma successWeight_nonneg (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    0 ≤ successWeight p h t l := by
  unfold successWeight
  split <;> simp_all [weight_nonneg]

lemma successWeight_le (p h : unitInterval) (t : ProbeTree) (l : t.Leaf) :
    successWeight p h t l ≤ weight p h t l := by
  unfold successWeight
  split
  · exact le_rfl
  · exact weight_nonneg p h t l

lemma successMass_nonneg (p h : unitInterval) (t : ProbeTree) : 0 ≤ successMass p h t :=
  Finset.sum_nonneg fun _ _ => successWeight_nonneg p h t _

lemma successMass_le_one (p h : unitInterval) (t : ProbeTree) : successMass p h t ≤ 1 := by
  rw [← sum_weight p h t]
  exact Finset.sum_le_sum fun _ _ => successWeight_le p h t _

lemma successQueries_nonneg (p h : unitInterval) (t : ProbeTree) : 0 ≤ successQueries p h t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (successWeight_nonneg p h t _) (Nat.cast_nonneg _)

 
theorem conditional_score_bound (p h : unitInterval) (t : ProbeTree)
    (hH : 0 < successMass p h t) (lam : ℝ) :
    lam*(successScore p h t / successMass p h t) ≤
      Real.log (1/successMass p h t) + lam^2/8*(successQueries p h t / successMass p h t) := by
  let H := successMass p h t
  let w : t.Leaf → ℝ := fun l => successWeight p h t l / H
  let X : t.Leaf → ℝ := fun l => lam*score p t l-lam^2*(queries t l : ℝ)/8
  have hw : ∀ l ∈ (Finset.univ : Finset t.Leaf), 0 ≤ w l :=
    fun l _ => div_nonneg (successWeight_nonneg p h t l) hH.le
  have hw1 : ∑ l, w l = 1 := by
    simp only [w,← Finset.sum_div]
    exact div_self hH.ne'
  have hJ := convexOn_exp.map_sum_le hw hw1 (fun _ _ => Set.mem_univ _ : ∀ l ∈
    (Finset.univ : Finset t.Leaf), X l ∈ Set.univ)
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ l, w l * X l = lam*(successScore p h t/H)-
      lam^2/8*(successQueries p h t/H) := by
    simp only [w,X,successScore,successQueries,Finset.sum_div,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have he : ∑ l, w l * Real.exp (X l) ≤ 1/H := by
    calc
      _ = (∑ l, successWeight p h t l * Real.exp (X l))/H := by
        simp only [Finset.sum_div,w]; apply Finset.sum_congr rfl; intro l _; ring
      _ ≤ (∑ l, weight p h t l * Real.exp (X l))/H := by
        apply div_le_div_of_nonneg_right _ hH.le
        exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (successWeight_le p h t l)
          (Real.exp_pos _).le
      _ ≤ 1/H := div_le_div_of_nonneg_right (score_mgf p h lam t) hH.le
  rw [hsum] at hJ
  have hb := (Real.le_log_iff_exp_le (one_div_pos.mpr hH)).mpr (hJ.trans he)
  linarith

noncomputable def dweight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => -weight p h t₀ l+(1-p)*dweight p h t₀ l
  | .edge _ t₁, .inr l => weight p h t₁ l+p*dweight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*dweight p h t₀ l
  | .mark _ t₁, .inr l => h*dweight p h t₁ l

lemma hasDerivAt_weight (p h : ℝ) (t : ProbeTree) (l : t.Leaf) :
    HasDerivAt (fun q => weight q h t l) (dweight p h t l) p := by
  induction t with
  | done b => exact hasDerivAt_const p 1
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => convert ((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih₀ l) using 1 <;> try rfl
               simp [dweight]
    | inr l => convert (hasDerivAt_id p).mul (ih₁ l) using 1 <;> try rfl
               simp [dweight]
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact (ih₀ l).const_mul (1-h)
    | inr l => exact (ih₁ l).const_mul h

lemma score_eq_derivative (p h : ℝ) (t : ProbeTree) (l : t.Leaf) :
    p*(1-p)*dweight p h t l = weight p h t l * score p t l := by
  induction t with
  | done b => simp [dweight,weight,score]
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => dsimp [dweight,weight,score]; linear_combination (1-p)*(ih₀ l)
    | inr l => dsimp [dweight,weight,score]; linear_combination p*(ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => dsimp [dweight,weight,score]; linear_combination (1-h)*(ih₀ l)
    | inr l => dsimp [dweight,weight,score]; linear_combination h*(ih₁ l)

 
theorem successScore_eq_deriv (p h : ℝ) (t : ProbeTree) :
    successScore p h t = p*(1-p)*deriv (fun q => successMass q h t) p := by
  have hd : HasDerivAt (fun q => successMass q h t)
      (∑ l, if outcome t l then dweight p h t l else 0) p := by
    have hh (l : t.Leaf) (_ : l ∈ (Finset.univ : Finset t.Leaf)) :
        HasDerivAt (fun q => successWeight q h t l) (if outcome t l then dweight p h t l else 0) p := by
      by_cases hl : outcome t l
      · simpa [successWeight,hl] using hasDerivAt_weight p h t l
      · simpa [successWeight,hl] using hasDerivAt_const p (0:ℝ)
    simpa only [successMass,Finset.sum_apply] using HasDerivAt.fun_sum hh
  rw [hd.deriv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : outcome t l
  · simpa [successWeight,hl] using (score_eq_derivative p h t l).symm
  · simp [successWeight,hl]

 
inductive IsMarkSearch : ProbeTree → Prop
  | fail : IsMarkSearch (.done false)
  | edge {t₀ t₁} : IsMarkSearch t₀ → IsMarkSearch t₁ → IsMarkSearch (.edge t₀ t₁)
  | mark {t₀} : IsMarkSearch t₀ → IsMarkSearch (.mark t₀ (.done true))

def marks : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => marks t₀ l
  | .edge _ t₁, .inr l => marks t₁ l
  | .mark t₀ _, .inl l => marks t₀ l+1
  | .mark _ t₁, .inr l => marks t₁ l+1

noncomputable def successMarks (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * marks t l

lemma successMass_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.edge t₀ t₁) = (1-p)*successMass p h t₀+p*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

lemma successMass_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMass p h (.mark t₀ t₁) = (1-h)*successMass p h t₀+h*successMass p h t₁ := by
  simp only [successMass,Fintype.sum_sum_type,successWeight,outcome,weight,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp

@[simp] lemma successMass_done (p h : ℝ) (b : Bool) :
    successMass p h (.done b) = if b then 1 else 0 := by
  cases b <;> simp [successMass,successWeight,outcome,weight]

lemma successMarks_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMarks p h (.edge t₀ t₁) = (1-p)*successMarks p h t₀+p*successMarks p h t₁ := by
  simp only [successMarks,Fintype.sum_sum_type,successWeight,outcome,weight,marks,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split <;> simp [mul_assoc]

lemma successMarks_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    successMarks p h (.mark t₀ t₁) =
      (1-h)*(successMarks p h t₀+successMass p h t₀) +
        h*(successMarks p h t₁+successMass p h t₁) := by
  simp only [successMarks,successMass,Fintype.sum_sum_type,successWeight,outcome,weight,marks,
    Nat.cast_add,Nat.cast_one,← Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> split_ifs <;> ring

@[simp] lemma successMarks_done (p h : ℝ) (b : Bool) : successMarks p h (.done b) = 0 := by
  simp [successMarks,marks]

 
theorem marks_times_parameter_le (p h : unitInterval) {t : ProbeTree} (ht : IsMarkSearch t) :
    (h:ℝ)*successMarks p h t ≤ successMass p h t := by
  induction ht with
  | fail => simp
  | @edge t₀ t₁ _ _ ih₀ ih₁ =>
    rw [successMarks_edge,successMass_edge]
    nlinarith [mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr ih₀),
      mul_nonneg p.2.1 (sub_nonneg.mpr ih₁)]
  | @mark t₀ _ ih =>
    rw [successMarks_mark,successMass_mark]
    simp only [successMarks_done,successMass_done,ite_true,zero_add,mul_one]
    have hn := mul_nonneg (mul_nonneg h.2.1 (sub_nonneg.mpr h.2.2))
      (sub_nonneg.mpr (successMass_le_one p h t₀))
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2.2) (sub_nonneg.mpr ih)]

theorem successQueries_times_parameter_le (p h : unitInterval) {t : ProbeTree}
    (ht : IsMarkSearch t) (d : ℕ) (hcost : ∀ l, queries t l ≤ d*marks t l) :
    (h:ℝ)*successQueries p h t ≤ d*successMass p h t := by
  have hs : successQueries p h t ≤ d*successMarks p h t := by
    simp only [successQueries,successMarks,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    calc
      _ ≤ successWeight p h t l * ((d:ℝ)*marks t l) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcost l) (successWeight_nonneg p h t l)
      _ = _ := by ring
  calc
    _ ≤ (h:ℝ)*(d*successMarks p h t) := mul_le_mul_of_nonneg_left hs h.2.1
    _ = d*((h:ℝ)*successMarks p h t) := by ring
    _ ≤ d*successMass p h t := mul_le_mul_of_nonneg_left (marks_times_parameter_le p h ht)
      (Nat.cast_nonneg _)

 
theorem marked_score_bound (p h : unitInterval) (hh : 0 < (h:ℝ))
    {t : ProbeTree} (ht : IsMarkSearch t) (d : ℕ)
    (hcost : ∀ l, queries t l ≤ d*marks t l) (hroot : (h:ℝ) ≤ successMass p h t)
    (lam : ℝ) :
    lam*(successScore p h t / successMass p h t) ≤
      Real.log (1/(h:ℝ)) + lam^2*(d:ℝ)/(8*h) := by
  have hH := hh.trans_le hroot
  have hlog : Real.log (1/successMass p h t) ≤ Real.log (1/(h:ℝ)) :=
    Real.log_le_log (one_div_pos.mpr hH) (one_div_le_one_div_of_le hh hroot)
  have hQ : successQueries p h t / successMass p h t ≤ (d:ℝ)/h := by
    apply (div_le_div_iff₀ hH hh).mpr
    simpa [mul_comm] using successQueries_times_parameter_le p h ht d hcost
  calc
    _ ≤ Real.log (1/successMass p h t)+lam^2/8*(successQueries p h t/successMass p h t) :=
      conditional_score_bound p h t hH lam
    _ ≤ Real.log (1/(h:ℝ))+lam^2/8*((d:ℝ)/h) :=
      add_le_add hlog (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = _ := by ring

end ProbeTree
end MarkedExploration

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

inductive LabelledTree (V E : Type*) where
  | done (success : Bool)
  | edge (e : E) (closed opened : LabelledTree V E)
  | mark (v : V) (unmarked marked : LabelledTree V E)

namespace LabelledTree

def forget : LabelledTree V E → ProbeTree
  | .done b => .done b
  | .edge _ t₀ t₁ => .edge t₀.forget t₁.forget
  | .mark _ t₀ t₁ => .mark t₀.forget t₁.forget

@[reducible] noncomputable def eval (ω : Finset E) (m : Finset V) : LabelledTree V E → Bool
  | .done b => b
  | .edge e t₀ t₁ => if e ∈ ω then eval ω m t₁ else eval ω m t₀
  | .mark v t₀ t₁ => if v ∈ m then eval ω m t₁ else eval ω m t₀

def Valid (Q : Finset E) (F : Finset V) : LabelledTree V E → Prop
  | .done _ => True
  | .edge e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) F t₀ ∧ Valid (Q.erase e) F t₁
  | .mark v t₀ t₁ => v ∈ F ∧ Valid Q (F.erase v) t₀ ∧ Valid Q (F.erase v) t₁

theorem eval_congr (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {ω ω' : Finset E} {m m' : Finset V}
    (hω : ∀ e ∈ Q, e ∈ ω ↔ e ∈ ω') (hm : ∀ v ∈ F, v ∈ m ↔ v ∈ m') :
    t.eval ω m = t.eval ω' m' := by
  induction t generalizing Q F with
  | done b => rfl
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    simp only [eval,hω e he]
    split
    · exact ih₁ h₁ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
    · exact ih₀ h₀ (fun a ha => hω a (Finset.mem_of_mem_erase ha)) hm
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    simp only [eval,hm v hv]
    split
    · exact ih₁ h₁ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))
    · exact ih₀ h₀ hω (fun a ha => hm a (Finset.mem_of_mem_erase ha))

lemma eval_insert_edge (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {e : E} (he : e ∉ Q) (ω : Finset E) (m : Finset V) :
    t.eval (insert e ω) m = t.eval ω m := by
  apply eval_congr t ht
  · intro a ha
    simp [show a ≠ e from fun hh => he (hh ▸ ha)]
  · simp

lemma eval_insert_mark (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) {v : V} (hv : v ∉ F) (ω : Finset E) (m : Finset V) :
    t.eval ω (insert v m) = t.eval ω m := by
  apply eval_congr t ht
  · simp
  · intro a ha
    simp [show a ≠ v from fun hh => hv (hh ▸ ha)]

end LabelledTree

theorem bernoulliPolynomial_affine (s : Finset E) (f g : Finset E → ℝ) (a b p : ℝ) :
    bernoulliPolynomial s (fun t => a*f t+b*g t) p =
      a*bernoulliPolynomial s f p+b*bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring

namespace LabelledTree

 
theorem expectation_eq (t : LabelledTree V E) {Q : Finset E} {F : Finset V}
    (ht : Valid Q F t) (p h : ℝ) :
    bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
      (fun m => if t.eval ω m then 1 else 0) h) p =
      ProbeTree.successMass p h t.forget := by
  induction t generalizing Q F with
  | done b =>
    cases b <;> simp [eval,forget,ProbeTree.successMass_done,bernoulliPolynomial_const]
  | edge e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    conv_lhs => rw [← Finset.insert_erase he]
    rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
    have hc : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval ω m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₀.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω hω
      have heω : e ∉ ω := fun hh => Finset.notMem_erase e Q (hω hh)
      simp only [eval,heω,ite_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if (edge e t₀ t₁).eval (insert e ω) m then 1 else 0) h) p =
        bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
        (fun m => if t₁.eval ω m then 1 else 0) h) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [eval,Finset.mem_insert_self,ite_true]
      apply bernoulliPolynomial_congr
      intro m _
      rw [eval_insert_edge t₁ h₁ (Finset.notMem_erase e Q)]
    rw [hc,ho,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_edge]
  | mark v t₀ t₁ ih₀ ih₁ =>
    obtain ⟨hv,h₀,h₁⟩ := ht
    have hh : ∀ ω, bernoulliPolynomial F
        (fun m => if (mark v t₀ t₁).eval ω m then 1 else 0) h =
      (1-h)*bernoulliPolynomial (F.erase v) (fun m => if t₀.eval ω m then 1 else 0) h +
        h*bernoulliPolynomial (F.erase v) (fun m => if t₁.eval ω m then 1 else 0) h := by
      intro ω
      conv_lhs => rw [← Finset.insert_erase hv]
      rw [bernoulliPolynomial_insert _ v (Finset.notMem_erase v F)]
      congr 1
      · congr 1
        apply bernoulliPolynomial_congr
        intro m hm
        have hvm : v ∉ m := fun hh => Finset.notMem_erase v F (hm hh)
        simp only [eval,hvm,ite_false]
      · congr 1
        apply bernoulliPolynomial_congr
        intro m _
        simp only [eval,Finset.mem_insert_self,ite_true]
        rw [eval_insert_mark t₁ h₁ (Finset.notMem_erase v F)]
    simp_rw [hh]
    rw [bernoulliPolynomial_affine,ih₀ h₀,ih₁ h₁,forget,ProbeTree.successMass_mark]

end LabelledTree
end LabelledExploration

section GraphMarkedSearch
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
def SearchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ t.2.2 ∉ R ∧ G t.1 = s(t.2.1,t.2.2)

noncomputable def searchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) : E × V × V := Classical.choose h

theorem searchCrossing_spec (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) :
    (searchCrossing G Q R h).1 ∈ Q ∧ (searchCrossing G Q R h).2.1 ∈ R ∧
      (searchCrossing G Q R h).2.2 ∉ R ∧
      G (searchCrossing G Q R h).1 = s((searchCrossing G Q R h).2.1,(searchCrossing G Q R h).2.2) :=
  Classical.choose_spec h

 
def SearchAvailable (G : BondGraph V E) (Q : Finset E) (R F : Finset V) : Prop :=
  ∀ e ∈ Q, ∀ v ∈ G e, v ∈ R ∨ v ∈ F

noncomputable def clusterSearch (G : BondGraph V E) : ℕ → Finset E → Finset V → LabelledTree V E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .edge t.1 (clusterSearch G n (Q.erase t.1) R)
        (.mark t.2.2 (clusterSearch G n (Q.erase t.1) (insert t.2.2 R)) (.done true))
    else .done false

lemma searchAvailable_erase (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) : SearchAvailable G (Q.erase e) R F :=
  fun _ ha _ hv => h _ (Finset.mem_of_mem_erase ha) _ hv

lemma searchAvailable_discover (G : BondGraph V E) {Q : Finset E} {R F : Finset V}
    (h : SearchAvailable G Q R F) (e : E) (v : V) :
    SearchAvailable G (Q.erase e) (insert v R) (F.erase v) := by
  intro a ha b hb
  rcases h a (Finset.mem_of_mem_erase ha) b hb with hb | hb
  · exact Or.inl (Finset.mem_insert_of_mem hb)
  · by_cases hbe : b = v
    · exact Or.inl (by simp [hbe])
    · exact Or.inr (Finset.mem_erase.mpr ⟨hbe,hb⟩)

theorem clusterSearch_valid (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F : Finset V)
    (ha : SearchAvailable G Q R F) : LabelledTree.Valid Q F (clusterSearch G n Q R) := by
  induction n generalizing Q R F with
  | zero => trivial
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      refine ⟨he,ih _ _ _ (searchAvailable_erase G ha _),?_,?_,trivial⟩
      · exact (ha _ he _ (by rw [hends]; simp)).resolve_left hw
      · exact ih _ _ _ (searchAvailable_discover G ha _ _)
    · trivial

theorem clusterSearch_markSearch (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V) :
    ProbeTree.IsMarkSearch (clusterSearch G n Q R).forget := by
  induction n generalizing Q R with
  | zero => exact .fail
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs
    · exact .edge (ih _ _) (.mark (ih _ _))
    · exact .fail

 
def SeedMarked (G : BondGraph V E) (ω : Set E) (R m : Finset V) : Prop :=
  ∃ a ∈ R, ∃ b ∈ m, Conn G ω a b

theorem seedMarked_insert_edge (G : BondGraph V E) (ω : Set E) (R m : Finset V)
    (e : E) (a b : V) (ha : a ∈ R) (he : G e = s(a,b)) :
    SeedMarked G (insert e ω) R m ↔ SeedMarked G ω (insert b R) m := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hx,y,hy,h⟩
    · exact ⟨b,by simp,y,hy,h⟩
    · exact ⟨a,Finset.mem_insert_of_mem ha,y,hy,h⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine ⟨a,ha,y,hy,?_⟩
      exact (Relation.ReflTransGen.single ⟨e,Set.mem_insert e ω,he⟩).trans
        (conn_mono G (Set.subset_insert e ω) hxy)
    · exact ⟨x,hx,y,hy,conn_mono G (Set.subset_insert e ω) hxy⟩

theorem seedMarked_false_of_no_crossing (G : BondGraph V E) (Q : Finset E) (R m : Finset V)
    (hc : ¬ SearchCrossing G Q R) (hm : Disjoint R m) (ω : Finset E) (hω : ω ⊆ Q) :
    ¬ SeedMarked G (ω : Set E) R m := by
  rintro ⟨a,ha,b,hb,hab⟩
  have hclosed : ∀ x ∈ R, ∀ y, Conn G (ω : Set E) x y → y ∈ R := by
    intro x hx y hxy
    induction hxy with
    | refl => exact hx
    | @tail v w hv hw ih =>
      by_contra hn
      obtain ⟨e,he,hevw⟩ := hw
      exact hc ⟨(e,v,w),hω he,ih,hn,hevw⟩
  exact Finset.disjoint_left.mp hm (hclosed a ha b hab) hb

 
theorem clusterSearch_correct (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R F m : Finset V)
    (hn : Q.card ≤ n) (ha : SearchAvailable G Q R F) (hm : Disjoint R m)
    (ω : Finset E) (hω : ω ⊆ Q) :
    (clusterSearch G n Q R).eval ω m = true ↔ SeedMarked G (ω : Set E) R m := by
  induction n generalizing Q R F ω with
  | zero =>
    have hQ : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    have hωe : ω = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by simp_all)
    simp only [clusterSearch,LabelledTree.eval,Bool.false_eq_true,false_iff]
    exact seedMarked_false_of_no_crossing G Q R m (by simp [SearchCrossing,hQ]) hm ω hω
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hcard : (Q.erase (searchCrossing G Q R hc).1).card ≤ n := by
        rw [Finset.card_erase_of_mem he]; omega
      simp only [LabelledTree.eval]
      by_cases heω : (searchCrossing G Q R hc).1 ∈ ω
      · simp only [heω,ite_true]
        rw [← Finset.insert_erase heω,Finset.coe_insert,
          seedMarked_insert_edge G _ R m _ _ _ hv hends]
        by_cases hwm : (searchCrossing G Q R hc).2.2 ∈ m
        · simp only [hwm,ite_true,true_iff]
          exact ⟨_,by simp,_,hwm,conn_refl G _ _⟩
        · simp only [hwm,ite_false]
          rw [LabelledTree.eval_insert_edge _
            (clusterSearch_valid G n _ _ (F.erase (searchCrossing G Q R hc).2.2)
              (searchAvailable_discover G ha _ _)) (Finset.notMem_erase _ _)]
          exact ih _ _ _ hcard (searchAvailable_discover G ha _ _)
            (Finset.disjoint_insert_left.mpr ⟨hwm,hm⟩) (ω.erase (searchCrossing G Q R hc).1)
            (Finset.erase_subset_erase _ hω)
      · simp only [heω,ite_false]
        exact ih _ _ _ hcard (searchAvailable_erase G ha _ ) hm ω
          (fun e he => Finset.mem_erase.mpr ⟨fun heq => heω (heq ▸ he),hω he⟩)
    · simp only [false_iff]
      exact seedMarked_false_of_no_crossing G Q R m hc hm ω hω

end GraphMarkedSearch

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace ProbeTree

def Budget (t : ProbeTree) (K d : ℕ) : Prop := ∀ l, queries t l ≤ K+d*marks t l

lemma budget_done (b : Bool) (K d : ℕ) : Budget (.done b) K d := by
  intro l
  simp [queries,marks]

lemma budget_mono {t : ProbeTree} {K L d : ℕ} (h : Budget t K d) (hKL : K ≤ L) :
    Budget t L d := fun l => (h l).trans (Nat.add_le_add_right hKL _)

lemma budget_edge {t₀ t₁ : ProbeTree} {K d : ℕ} (h₀ : Budget t₀ K d) (h₁ : Budget t₁ K d) :
    Budget (.edge t₀ t₁) (K+1) d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₀ l) 1
  | inr l => simpa [queries,marks,Nat.add_right_comm] using Nat.add_le_add_right (h₁ l) 1

lemma budget_mark {t₀ t₁ : ProbeTree} {K d : ℕ}
    (h₀ : Budget t₀ (K+d) d) (h₁ : Budget t₁ (K+d) d) :
    Budget (.mark t₀ t₁) K d := by
  intro l
  cases l with
  | inl l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₀ l
  | inr l => simpa [queries,marks,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₁ l

end ProbeTree

 
noncomputable def queryPotential (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Finset E :=
  Q.filter (fun e => ∃ v ∈ R, v ∈ G e)

lemma queryPotential_erase (G : BondGraph V E) (Q : Finset E) (R : Finset V) (e : E) :
    queryPotential G (Q.erase e) R = (queryPotential G Q R).erase e := by
  ext a
  simp [queryPotential,and_assoc]

lemma queryPotential_insert (G : BondGraph V E) (Q : Finset E) (R : Finset V) (v : V) :
    queryPotential G Q (insert v R) = queryPotential G Q R ∪ Q.filter (fun e => v ∈ G e) := by
  ext a
  simp [queryPotential,and_or_left,or_comm]

lemma filtered_degree_erase (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) (a : E) :
    ∀ v, ((Q.erase a).filter (fun e => v ∈ G e)).card ≤ d := by
  intro v
  apply (Finset.card_le_card ?_).trans (hd v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1,
    (Finset.mem_filter.mp he).2⟩

lemma queryPotential_discover_card (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (e : E) (v : V) (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    (queryPotential G (Q.erase e) (insert v R)).card ≤
      ((queryPotential G Q R).erase e).card+d := by
  rw [queryPotential_insert,queryPotential_erase]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (filtered_degree_erase G Q d hd e v) _)

 
theorem clusterSearch_budget (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (clusterSearch G n Q R).forget (queryPotential G Q R).card d := by
  induction n generalizing Q R with
  | zero => exact ProbeTree.budget_done _ _ _
  | succ n ih =>
    simp only [clusterSearch]
    split_ifs with hc
    · obtain ⟨he,hv,hw,hends⟩ := searchCrossing_spec G Q R hc
      have hpot : (searchCrossing G Q R hc).1 ∈ queryPotential G Q R := by
        exact Finset.mem_filter.mpr ⟨he,_,hv,by rw [hends]; simp⟩
      have hpos : 0 < (queryPotential G Q R).card := Finset.card_pos.mpr ⟨_,hpot⟩
      have hclosed := ih (Q.erase (searchCrossing G Q R hc).1) R
        (filtered_degree_erase G Q d hd _)
      have hopen := ih (Q.erase (searchCrossing G Q R hc).1)
        (insert (searchCrossing G Q R hc).2.2 R) (filtered_degree_erase G Q d hd _)
      rw [queryPotential_erase,Finset.card_erase_of_mem hpot] at hclosed
      have hnew := queryPotential_discover_card G Q R (searchCrossing G Q R hc).1
        (searchCrossing G Q R hc).2.2 d hd
      rw [Finset.card_erase_of_mem hpot] at hnew
      have hh := ProbeTree.budget_edge hclosed
        (ProbeTree.budget_mark (ProbeTree.budget_mono hopen hnew) (ProbeTree.budget_done true _ _))
      have hcadd : (queryPotential G Q R).card-1+1 = (queryPotential G Q R).card := by omega
      simpa only [LabelledTree.forget,hcadd] using hh
    · exact ProbeTree.budget_done _ _ _

noncomputable def searchVertices (G : BondGraph V E) (Q : Finset E) : Finset V :=
  Q.biUnion fun e => (G e).toFinset

lemma mem_searchVertices (G : BondGraph V E) {Q : Finset E} {e : E} (he : e ∈ Q)
    {v : V} (hv : v ∈ G e) : v ∈ searchVertices G Q :=
  Finset.mem_biUnion.mpr ⟨e,he,Sym2.mem_toFinset.mpr hv⟩

noncomputable def markedClusterTree (G : BondGraph V E) (Q : Finset E) (x : V) : LabelledTree V E :=
  .mark x (clusterSearch G Q.card Q {x}) (.done true)

lemma markedClusterTree_available (G : BondGraph V E) (Q : Finset E) (x : V) :
    SearchAvailable G Q {x} ((insert x (searchVertices G Q)).erase x) := by
  intro e he v hv
  by_cases hx : v = x
  · exact Or.inl (by simpa using hx)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hx,Finset.mem_insert_of_mem (mem_searchVertices G he hv)⟩)

theorem markedClusterTree_valid (G : BondGraph V E) (Q : Finset E) (x : V) :
    LabelledTree.Valid Q (insert x (searchVertices G Q)) (markedClusterTree G Q x) :=
  ⟨by simp,clusterSearch_valid G _ _ _ _ (markedClusterTree_available G Q x),trivial⟩

theorem markedClusterTree_budget (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ProbeTree.Budget (markedClusterTree G Q x).forget 0 d := by
  have hh := clusterSearch_budget G Q.card Q {x} d hd
  have hcost : (queryPotential G Q {x}).card ≤ 0+d := by simpa [queryPotential] using hd x
  exact ProbeTree.budget_mark (ProbeTree.budget_mono hh hcost) (ProbeTree.budget_done true _ _)

theorem markedClusterTree_correct (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    (markedClusterTree G Q x).eval ω m = true ↔ ∃ y ∈ m, Conn G (ω : Set E) x y := by
  simp only [markedClusterTree,LabelledTree.eval]
  by_cases hxm : x ∈ m
  · simp only [hxm,ite_true,true_iff]
    exact ⟨x,hxm,conn_refl G _ x⟩
  · simp only [hxm,ite_false]
    rw [clusterSearch_correct G Q.card Q {x} ((insert x (searchVertices G Q)).erase x) m
      le_rfl (markedClusterTree_available G Q x) (by simpa) ω hω]
    simp only [SeedMarked,Finset.mem_singleton,exists_eq_left]

end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem quadratic_test_bound {z L B : ℝ} (hL : 0 ≤ L) (hB : 0 < B)
    (h : ∀ lam : ℝ, lam*z ≤ L+lam^2*B) : z ≤ Real.sqrt (4*B*L) := by
  have hh := h (z/(2*B))
  have hid : z/(2*B)*z-(z/(2*B))^2*B = z^2/(4*B) := by
    field_simp
    ring
  have hs : z^2/(4*B) ≤ L := by rw [← hid]; linarith
  have hs' := (div_le_iff₀ (by positivity : 0 < 4*B)).mp hs
  have hn : 0 ≤ 4*B*L := by positivity
  have hsq := Real.sq_sqrt hn
  have hpos := Real.sqrt_nonneg (4*B*L)
  nlinarith

 
noncomputable def markedConnectionPolynomial (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => if ∃ y ∈ m, Conn G (ω : Set E) x y then 1 else 0) h) p

theorem markedConnectionPolynomial_eq_tree (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) :
    markedConnectionPolynomial G Q x h p =
      ProbeTree.successMass p h (markedClusterTree G Q x).forget := by
  rw [← LabelledTree.expectation_eq _ (markedClusterTree_valid G Q x) p h]
  apply bernoulliPolynomial_congr
  intro ω hω
  apply bernoulliPolynomial_congr
  intro m _
  simp only [markedClusterTree_correct G Q x ω hω m]

theorem markedConnectionPolynomial_ge_mark (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) : (h:ℝ) ≤ markedConnectionPolynomial G Q x h p := by
  rw [markedConnectionPolynomial_eq_tree,markedClusterTree,LabelledTree.forget,
    ProbeTree.successMass_mark]
  simp only [LabelledTree.forget,ProbeTree.successMass_done,ite_true,mul_one]
  exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr h.2.2)
    (ProbeTree.successMass_nonneg p h _))

 
theorem markedConnection_derivative_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ))
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    (p:ℝ)*deriv (markedConnectionPolynomial G Q x h) p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        markedConnectionPolynomial G Q x h p := by
  let t := (markedClusterTree G Q x).forget
  have ht : ProbeTree.IsMarkSearch t := .mark (clusterSearch_markSearch G _ _ _)
  have hcost : ∀ l, ProbeTree.queries t l ≤ d*ProbeTree.marks t l := by
    simpa only [ProbeTree.Budget,zero_add] using markedClusterTree_budget G Q x d hdeg
  have hroot : (h:ℝ) ≤ ProbeTree.successMass p h t := by
    simpa only [markedConnectionPolynomial_eq_tree] using markedConnectionPolynomial_ge_mark G Q x p h
  have hB : 0 < (d:ℝ)/(8*h) := div_pos (by exact_mod_cast hd) (by positivity)
  have hL : 0 ≤ Real.log (1/(h:ℝ)) := Real.log_nonneg ((one_le_div hh).mpr h.2.2)
  have htest (lam : ℝ) : lam*(ProbeTree.successScore p h t/ProbeTree.successMass p h t) ≤
      Real.log (1/(h:ℝ))+lam^2*((d:ℝ)/(8*h)) := by
    simpa only [mul_div_assoc] using ProbeTree.marked_score_bound p h hh ht d hcost hroot lam
  have hz := quadratic_test_bound hL hB htest
  have hsqrt : Real.sqrt (4*((d:ℝ)/(8*h))*Real.log (1/(h:ℝ))) =
      Real.sqrt ((d:ℝ)/2)*Real.sqrt (Real.log (1/(h:ℝ))/h) := by
    rw [show 4*((d:ℝ)/(8*h))*Real.log (1/(h:ℝ)) =
      ((d:ℝ)/2)*(Real.log (1/(h:ℝ))/h) by ring,Real.sqrt_mul (by positivity)]
  rw [hsqrt] at hz
  have hH : 0 < ProbeTree.successMass p h t := hh.trans_le hroot
  have hscore := (div_le_iff₀ hH).mp hz
  rw [ProbeTree.successScore_eq_deriv] at hscore
  have heq : markedConnectionPolynomial G Q x h = fun q => ProbeTree.successMass q h t :=
    funext fun q => markedConnectionPolynomial_eq_tree G Q x h q
  rw [heq]
  have hq : 0 < 1-(p:ℝ) := sub_pos.mpr hp
  calc
    _ = ((p:ℝ)*(1-p)*deriv (fun q => ProbeTree.successMass q h t) p)/(1-p) := by
      field_simp
    _ ≤ (Real.sqrt ((d:ℝ)/2)*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        ProbeTree.successMass p h t)/(1-p) := div_le_div_of_nonneg_right hscore hq.le
    _ = _ := by ring

theorem bernoulliPolynomial_open_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then f t-f (t.erase e) else 0) p =
      p*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e s)]
  have hclosed : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then f t-f (t.erase e) else 0) p = 0 := by
    rw [← bernoulliPolynomial_zero (s.erase e) p]
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun hh => Finset.notMem_erase e s (ht hh)]
  rw [hclosed,mul_zero,zero_add]
  congr 1
  apply bernoulliPolynomial_congr
  intro t ht
  have het : e ∉ t := fun hh => Finset.notMem_erase e s (ht hh)
  simp [het]

 
noncomputable def markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ (∃ y ∈ m, Conn G (ω : Set E) x y) ∧
      ¬ ∃ y ∈ m, Conn G (ω.erase e : Set E) x y

 
noncomputable def markedPivotalMomentOne (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => ((markedOpenPivotals G Q x ω m).card:ℝ)) h) p

theorem marked_pivotal_russo (G : BondGraph V E) (Q : Finset E) (x : V) (h p : ℝ) :
    markedPivotalMomentOne G Q x h p = p*deriv (markedConnectionPolynomial G Q x h) p := by
  let F := insert x (searchVertices G Q)
  let f : Finset E → Finset V → ℝ := fun ω m =>
    if ∃ y ∈ m, Conn G (ω : Set E) x y then 1 else 0
  have hcard (ω : Finset E) (m : Finset V) : ((markedOpenPivotals G Q x ω m).card:ℝ) =
      ∑ e ∈ Q, if e ∈ ω then f ω m-f (ω.erase e) m else 0 := by
    rw [markedOpenPivotals,Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hmono : (∃ y ∈ m, Conn G (ω.erase e : Set E) x y) →
        ∃ y ∈ m, Conn G (ω : Set E) x y := by
      rintro ⟨y,hy,hxy⟩
      exact ⟨y,hy,conn_mono G (by exact_mod_cast Finset.erase_subset e ω) hxy⟩
    by_cases he : e ∈ ω <;> by_cases h₁ : ∃ y ∈ m, Conn G (ω : Set E) x y <;>
      by_cases h₀ : ∃ y ∈ m, Conn G (ω.erase e : Set E) x y <;>
      simp only [f,he,h₁,h₀,and_true,and_false,not_true_eq_false,
        not_false_eq_true,ite_true,ite_false,Nat.cast_one,Nat.cast_zero,sub_self,sub_zero]
    exact False.elim (h₁ (hmono h₀))
  have heq : markedConnectionPolynomial G Q x h =
      bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (f ω) h) := rfl
  rw [heq,(hasDerivAt_bernoulliPolynomial Q _ p).deriv,Finset.mul_sum]
  simp only [markedPivotalMomentOne,hcard,bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← bernoulliPolynomial_open_difference Q e he (fun ω => bernoulliPolynomial F (f ω) h) p]
  apply bernoulliPolynomial_congr
  intro ω _
  by_cases heω : e ∈ ω
  · simp only [heω,ite_true,F]
    exact bernoulliPolynomial_sub _ _ _ _
  · simp only [heω,ite_false,bernoulliPolynomial_zero]

 
theorem marked_pivotal_first_moment (G : BondGraph V E) (Q : Finset E) (x : V)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    markedPivotalMomentOne G Q x h p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        markedConnectionPolynomial G Q x h p := by
  rw [marked_pivotal_russo]
  exact markedConnection_derivative_bound G Q x p h hp hh d hd hdeg

end MarkedFirstMoment

section PivotalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def MarkedEvent (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V) : Prop :=
  ∃ y ∈ m, Conn G ω x y

 
def OpenMarkedPivotal (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    (e : E) : Prop :=
  e ∈ ω ∧ MarkedEvent G ω m x ∧ ¬MarkedEvent G (ω \ {e}) m x

theorem markedEvent_mono (G : BondGraph V E) {ω η : Set E} (h : ω ⊆ η)
    {m : Set V} {x : V} (hx : MarkedEvent G ω m x) : MarkedEvent G η m x := by
  obtain ⟨y,hy,hxy⟩ := hx
  exact ⟨y,hy,conn_mono G h hxy⟩

theorem edge_cluster_sides (G : BondGraph V E) (ω : Set E) (x : V)
    {e : E} {a b : V} (he : e ∈ ω) (hab : G e = s(a,b)) :
    a ∈ cluster G ω x ↔ b ∈ cluster G ω x := by
  have hc : Conn G ω a b := .single ⟨e,he,hab⟩
  exact ⟨fun h => h.trans hc,fun h => h.trans (conn_symm G ω hc)⟩

 
theorem conn_restrict_cluster_compl (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω hau))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x he heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

theorem conn_restrict_cluster (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans hau
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x he heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 
theorem openMarkedPivotal_oriented (G : BondGraph V E) (ω : Set E) (m : Set V)
    (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e) :
    ∃ a b, G e = s(a,b) ∧ Conn G (ω \ {e}) x a ∧
      ¬Conn G (ω \ {e}) x b ∧ MarkedEvent G (ω \ {e}) m b := by
  obtain ⟨y,hy,hxy⟩ := he.2.1
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  have heq : insert e (ω \ {e}) = ω := by
    have heω : e ∈ ω := he.1
    ext d
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases h : d = e <;> simp_all
  rw [← heq,conn_insert_iff G _ e a b x y hab] at hxy
  rcases hxy with hxy | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
  · exact (he.2.2 ⟨y,hy,hxy⟩).elim
  · exact ⟨a,b,hab,hxa,fun hxb => he.2.2 ⟨y,hy,hxb.trans hby⟩,y,hy,hby⟩
  · exact ⟨b,a,hab.trans (Sym2.eq_swap ..),hxb,
      fun hxa => he.2.2 ⟨y,hy,hxa.trans hay⟩,y,hy,hay⟩

 
theorem pivotal_rootSide_disjoint_marks (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e) :
    Disjoint (cluster G (ω \ {e}) x) m := by
  rw [Set.disjoint_left]
  exact fun y hy hm => he.2.2 ⟨y,hm,hy⟩

 
theorem conn_delete_internal_of_outside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x))
    (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster_compl G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨u,v,heq⟩ : ∃ u v, G f = s(u,v) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  exact ((mem_internalEdges_of_ends G _ f u v heq).mp he.2).1
    ((mem_internalEdges_of_ends G _ f u v heq).mp hf).1

 
theorem pivotal_other_sides (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (_he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : f ≠ e) :
    f ∈ internalEdges G (cluster G (ω \ {e}) x) ∨
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G f = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  have hop : f ∈ ω \ {e} := ⟨hf.1,hne⟩
  have hiff := edge_cluster_sides G (ω \ {e}) x hop hab
  by_cases ha : a ∈ cluster G (ω \ {e}) x
  · exact Or.inl ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,hiff.mp ha⟩)
  · exact Or.inr ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,fun hb => ha (hiff.mpr hb)⟩)

 
theorem conn_delete_exterior_of_inside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x)ᶜ)
    (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨⟨u,v⟩,heq⟩ := Quot.exists_rep (G f)
  exact ((mem_internalEdges_of_ends G _ f u v heq.symm).mp hf).1
    ((mem_internalEdges_of_ends G _ f u v heq.symm).mp he.2).1

 
theorem pivotal_rootSide_ssubset (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e) (hne : e ≠ f)
    (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x := by
  have hsub : cluster G (ω \ {e}) x ⊆ cluster G (ω \ {f}) x := by
    intro y hy
    exact conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hf (conn_refl G _ x) hy)
  refine ⟨hsub,?_⟩
  obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G ω m x he
  intro hback
  apply hxb
  apply hback
  exact (hsub hxa).tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem pivotal_rootSides_nested (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : e ≠ f) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x ∨
      cluster G (ω \ {f}) x ⊂ cluster G (ω \ {e}) x := by
  rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | houtside
  · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
    obtain ⟨y,hy,hby⟩ := hbm
    have hby' : Conn G (ω \ {f}) b y := conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
    have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
    have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
      hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
    exact Or.inr (pivotal_rootSide_ssubset G ω m x hf hne.symm
      ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩))
  · exact Or.inl (pivotal_rootSide_ssubset G ω m x he hne houtside)

 
theorem conn_restrict_cluster_compl_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∉ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω (conn_mono G hη hau)))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x (hη he) heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 

theorem markedEvent_after_pivotal (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e) (hne : e ≠ f)
    {a b : V} (hab : G e = s(a,b)) (hxa : Conn G (ω \ {e}) x a)
    (hxb : ¬Conn G (ω \ {e}) x b)
    (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) :
    MarkedEvent G (ω \ {f}) m x ↔
      MarkedEvent G ((ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) \ {f}) m b := by
  let W := cluster G (ω \ {e}) x
  have heq : insert e ((ω \ {e}) \ {f}) = ω \ {f} := by
    ext d
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨⟨hd,hde⟩,hdf⟩)
      · exact ⟨he.1,hne⟩
      · exact ⟨hd,hdf⟩
    · rintro ⟨hd,hdf⟩
      by_cases hde : d = e
      · exact Or.inl hde
      · exact Or.inr ⟨⟨hd,hde⟩,hdf⟩
  constructor
  · rintro ⟨y,hy,hxy⟩
    rw [← heq,conn_insert_iff G _ e a b x y hab] at hxy
    rcases hxy with hxy | ⟨_,hby⟩ | ⟨hxb',_⟩
    · exact (he.2.2 ⟨y,hy,conn_mono G Set.sdiff_subset hxy⟩).elim
    · refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl_of_subset G (ω \ {e}) x
        Set.sdiff_subset hxb hby)⟩
      intro d hd
      exact ⟨⟨hd.1.1.1,hd.2⟩,hd.1.2⟩
    · exact (hxb (conn_mono G Set.sdiff_subset hxb')).elim
  · rintro ⟨y,hy,hby⟩
    have hxa' : Conn G (ω \ {f}) x a := conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hf (conn_refl G _ x) hxa)
    refine ⟨y,hy,(hxa'.tail ⟨e,⟨he.1,hne⟩,hab⟩).trans (conn_mono G ?_ hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩

 
theorem openMarkedPivotal_exterior_iff (G : BondGraph V E) (ω : Set E) (m : Set V)
    (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e)
    {a b : V} (hab : G e = s(a,b)) (hxa : Conn G (ω \ {e}) x a)
    (hxb : ¬Conn G (ω \ {e}) x b) (hbm : MarkedEvent G (ω \ {e}) m b)
    (f : E) :
    OpenMarkedPivotal G (ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) m b f ↔
      OpenMarkedPivotal G ω m x f ∧ f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hbase : MarkedEvent G (ω ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ) m b := by
    obtain ⟨y,hy,hby⟩ := hbm
    refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl G (ω \ {e}) x hxb hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩
  have hexterior (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hf).1 hxa
  constructor
  · intro hf
    have hiff := markedEvent_after_pivotal G ω m x he (hexterior hf.1.2) hab hxa hxb hf.1.2
    exact ⟨⟨hf.1.1,he.2.1,fun h => hf.2.2 (hiff.mp h)⟩,hf.1.2⟩
  · rintro ⟨hf,hout⟩
    have hiff := markedEvent_after_pivotal G ω m x he (hexterior hout) hab hxa hxb hout
    exact ⟨⟨hf.1,hout⟩,hbase,fun h => hf.2.2 (hiff.mpr h)⟩

 
theorem cluster_finite_of_finite_edges (G : BondGraph V E) {ω : Set E}
    (hω : ω.Finite) (x : V) : (cluster G ω x).Finite := by
  let F : Finset V := insert x (hω.toFinset.biUnion fun e => (G e).toFinset)
  apply F.finite_toSet.subset
  intro y hxy
  induction hxy with
  | refl => exact Finset.mem_insert_self x _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨e,hω.mem_toFinset.mpr he,by simp [heq]⟩

 
noncomputable def pivotalRank (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : ℕ :=
  (cluster G (ω \ {e}) x).ncard

theorem pivotalRank_injective (G : BondGraph V E) {ω : Set E} (hω : ω.Finite)
    (m : Set V) (x : V) : Set.InjOn (pivotalRank G ω x) {e | OpenMarkedPivotal G ω m x e} := by
  intro e he f hf hsame
  by_contra hne
  rcases pivotal_rootSides_nested G ω m x he hf hne with h | h
  · have hh := Set.ncard_lt_ncard h (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
    exact (Nat.ne_of_lt hh) hsame
  · have hh := Set.ncard_lt_ncard h (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
    exact (Nat.ne_of_lt hh) hsame.symm

 
theorem pivotalRank_lt_iff (G : BondGraph V E) {ω : Set E} (hω : ω.Finite)
    (m : Set V) (x : V) {e f : E} (he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) :
    pivotalRank G ω x e < pivotalRank G ω x f ↔
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hexterior (hout : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    obtain ⟨a,b,hab,hxa,_,_⟩ := openMarkedPivotal_oriented G ω m x he
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hout).1 hxa
  constructor
  · intro hlt
    have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
    rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | hout
    · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
      obtain ⟨y,hy,hby⟩ := hbm
      have hby' : Conn G (ω \ {f}) b y := conn_mono G
        (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
        (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
      have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
      have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
        hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
      have hs := pivotal_rootSide_ssubset G ω m x hf hne.symm
        ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩)
      have hrev := Set.ncard_lt_ncard hs
        (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hrev) hlt).elim
    · exact hout
  · intro hout
    exact Set.ncard_lt_ncard (pivotal_rootSide_ssubset G ω m x he (hexterior hout) hout)
      (cluster_finite_of_finite_edges G (hω.subset Set.sdiff_subset) x)

end PivotalGeometry

end Percolation

end OAI
