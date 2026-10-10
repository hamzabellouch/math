import Mathlib
import OAI.Probability.CriticalPercolation.Modular.PushMass

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z I M : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma pushMass_comp (f : X → Y) (g : Y → Z) (P : X → ℝ) :
    pushMass g (pushMass f P) = pushMass (g ∘ f) P := by
  funext z
  have hh := sum_pushMass_mul f P (fun y => if g y = z then (1:ℝ) else 0)
  change (∑ y, if g y = z then pushMass f P y else 0) =
    ∑ x, if g (f x) = z then P x else 0
  simpa only [mul_ite,mul_one,mul_zero] using hh

omit [Fintype Y] in
lemma sum_pushMass_pair (P : X → ℝ) (u : X → Y) (v : X → Z) (y : Y) :
    ∑ z, pushMass (fun x => (u x,v x)) P (y,z) = pushMass u P y := by
  unfold pushMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : u x = y
  · simp [h]
  · simp [h]

noncomputable def conditionalMass (P : X → ℝ) (u : X → Y) (v : X → Z)
    (y : Y) (z : Z) : ℝ :=
  pushMass (fun x => (u x,v x)) P (y,z) / pushMass u P y

omit [Fintype Y] [Fintype Z] in
lemma conditionalMass_nonneg (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (y : Y) (z : Z) : 0 ≤ conditionalMass P u v y z :=
  div_nonneg (pushMass_nonneg _ _ hP _) (pushMass_nonneg _ _ hP _)

omit [Fintype Y] in
lemma sum_conditionalMass_le_one (P : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (y : Y) : ∑ z, conditionalMass P u v y z ≤ 1 := by
  unfold conditionalMass
  rw [← Finset.sum_div, sum_pushMass_pair]
  by_cases h : pushMass u P y = 0
  · simp [h]
  · rw [div_self h]

omit [Fintype Y] [Fintype Z] in
lemma conditionalMass_pos (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (x : X) (hx : 0 < P x) :
    0 < conditionalMass P u v (u x) (v x) :=
  div_pos (hx.trans_le (le_pushMass _ _ hP x)) (hx.trans_le (le_pushMass _ _ hP x))

lemma divergence_as_log (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence P R = ∑ x, P x * Real.log (P x) - ∑ x, P x * Real.log (R x) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    rw [Real.log_div hx (hs x hp).ne']
    ring

variable [Fintype I] [Fintype M]

omit [Fintype Y] in

theorem conditional_marks_log {Y' : I → Type*} (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (t : (i : I) → X → Y' i) :
    (∑ i, ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i))) ≤
      (∑ x, P x * Real.log (P x)) -
        ∑ x, P x * Real.log (pushMass Prod.fst P x.1) := by
  let K (i : I) (ω : X) (m : M) :=
    conditionalMass P (fun x => t i x.1) (fun x => x.2 i) (t i ω) m
  let R (x : X × (I → M)) := pushMass Prod.fst P x.1 * ∏ i, K i x.1 (x.2 i)
  have hR : ∀ x, 0 ≤ R x := fun x => mul_nonneg (pushMass_nonneg _ _ hP _)
    (Finset.prod_nonneg fun i _ => conditionalMass_nonneg _ hP _ _ _ _)
  have hmass : ∑ x, R x ≤ 1 := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ ω, pushMass Prod.fst P ω * (∏ i, ∑ m, K i ω m) := by
        apply Finset.sum_congr rfl
        intro ω _
        simp only [R,← Finset.mul_sum,← Fintype.prod_sum]
      _ ≤ ∑ ω, pushMass Prod.fst P ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_of_le_one_right (pushMass_nonneg _ _ hP _)
        exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun m _ =>
          conditionalMass_nonneg _ hP _ _ _ _) (fun i _ => sum_conditionalMass_le_one _ hP _ _ _)
      _ = 1 := (pushMass_sum _ _).trans hm
  have hs (x : X × (I → M)) (hx : 0 < P x) : 0 < R x :=
    mul_pos (hx.trans_le (le_pushMass _ _ hP x)) (Finset.prod_pos fun i _ =>
      conditionalMass_pos _ hP _ _ x hx)
  have hd : 0 ≤ divergence P R := by
    have hh := mass_sub_le_divergence P R hP hR hs
    rw [hm] at hh
    linarith
  rw [divergence_as_log P R hP hs] at hd
  have heq : ∑ x, P x * Real.log (R x) =
      (∑ x, P x * Real.log (pushMass Prod.fst P x.1)) +
        ∑ i, ∑ x, P x * Real.log (K i x.1 (x.2 i)) := by
    rw [Finset.sum_comm,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      have hs0 : 0 < pushMass Prod.fst P x.1 := hp.trans_le (le_pushMass _ _ hP x)
      have hK (i : I) : 0 < K i x.1 (x.2 i) := conditionalMass_pos _ hP _ _ x hp
      dsimp only [R]
      rw [Real.log_mul hs0.ne' (Finset.prod_pos (fun i _ => hK i)).ne',
        Real.log_prod (fun i _ => (hK i).ne'),mul_add,Finset.mul_sum]
  rw [heq] at hd
  dsimp only [K] at hd
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma divergence_pushMass_eq (f : X → Y) (P : X → ℝ) (R : Y → ℝ) :
    divergence (pushMass f P) R =
      ∑ x, P x * Real.log (pushMass f P (f x) / R (f x)) :=
  sum_pushMass_mul f P (fun y => Real.log (pushMass f P y / R y))

lemma divergence_mark_chain (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (μ : Y → ℝ) (a : Y → Z → ℝ)
    (hμ : ∀ x, 0 < P x → 0 < μ (u x))
    (ha : ∀ x, 0 < P x → 0 < a (u x) (v x)) :
    divergence (pushMass (fun x => (u x,v x)) P) (fun yz => μ yz.1 * a yz.1 yz.2) =
      divergence (pushMass u P) μ +
        ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x)) := by
  rw [divergence_pushMass_eq,divergence_pushMass_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    have hu : 0 < pushMass u P (u x) := hp.trans_le (le_pushMass _ _ hP x)
    have huv : 0 < pushMass (fun x => (u x,v x)) P (u x,v x) :=
      hp.trans_le (le_pushMass _ _ hP x)
    have hm := hμ x hp
    have ham := ha x hp
    have hc := conditionalMass_pos P hP u v x hp
    rw [Real.log_div huv.ne' (mul_pos hm ham).ne',Real.log_mul hm.ne' ham.ne',
      Real.log_div hu.ne' hm.ne',Real.log_div hc.ne' ham.ne',conditionalMass,
      Real.log_div huv.ne' hu.ne']
    ring

lemma conditional_cost_ge (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (a : Y → Z → ℝ) (ha : ∀ y z, 0 ≤ a y z)
    (hs : ∀ x, 0 < P x → 0 < a (u x) (v x)) :
    -(∑ x, P x * Real.log (∑ z, a (u x) z)) ≤
      ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x)) := by
  let A (y : Y) := ∑ z, a y z
  let U := pushMass (fun x => (u x,v x)) P
  let R (yz : Y × Z) := pushMass u P yz.1 * (a yz.1 yz.2 / A yz.1)
  have hA (y : Y) : 0 ≤ A y := Finset.sum_nonneg (fun z _ => ha y z)
  have hAP (x : X) (hx : 0 < P x) : 0 < A (u x) :=
    (hs x hx).trans_le (Finset.single_le_sum (fun z _ => ha (u x) z) (Finset.mem_univ (v x)))
  have hR : ∀ yz, 0 ≤ R yz := fun yz => mul_nonneg (pushMass_nonneg _ _ hP _)
    (div_nonneg (ha _ _) (hA _))
  have hm : ∑ yz, R yz ≤ ∑ yz, U yz := by
    rw [Fintype.sum_prod_type,pushMass_sum]
    calc
      _ = ∑ y, pushMass u P y * (A y / A y) := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [R,← Finset.mul_sum,← Finset.sum_div,A]
      _ ≤ ∑ y, pushMass u P y := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_of_le_one_right (pushMass_nonneg _ _ hP _)
        by_cases hy : A y = 0
        · simp [hy]
        · rw [div_self hy]
      _ = ∑ x, P x := pushMass_sum _ _
  have hsR (yz : Y × Z) (hyz : 0 < U yz) : 0 < R yz := by
    obtain ⟨x,he,hx⟩ : ∃ x, (u x,v x) = yz ∧ 0 < P x := by
      by_contra! h
      have hh : U yz ≤ 0 := by
        apply Finset.sum_nonpos
        intro x _
        split_ifs with he
        · exact h x he
        · exact le_rfl
      linarith
    subst yz
    exact mul_pos (hx.trans_le (le_pushMass _ _ hP x))
      (div_pos (hs x hx) (hAP x hx))
  have hd : 0 ≤ divergence U R := by
    have hh := mass_sub_le_divergence U R (pushMass_nonneg _ _ hP) hR hsR
    linarith
  have hchain := divergence_mark_chain P hP u v (pushMass u P) (fun y z => a y z / A y)
    (fun x hx => hx.trans_le (le_pushMass _ _ hP x))
    (fun x hx => div_pos (hs x hx) (hAP x hx))
  change divergence U R = _ at hchain
  have hself : divergence (pushMass u P) (pushMass u P) = 0 := by
    unfold divergence
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : pushMass u P y = 0
    · simp [hy]
    · simp [hy]
  rw [hself,zero_add] at hchain
  rw [hchain] at hd
  have hlog : ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) /
      (a (u x) (v x) / A (u x))) =
      (∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x))) +
        ∑ x, P x * Real.log (A (u x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      have hc := conditionalMass_pos P hP u v x hp
      have ham := hs x hp
      have hA' := hAP x hp
      rw [Real.log_div hc.ne' (div_pos ham hA').ne',Real.log_div ham.ne' hA'.ne',
        Real.log_div hc.ne' ham.ne']
      ring
  rw [hlog] at hd
  dsimp only [A] at hd
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (Y i)] in

theorem conditional_mark_cost_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ) (L : ℝ)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i)) :
    (∑ i, ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))) ≤
      L - divergence (pushMass Prod.fst P) μ := by
  have hsub := conditional_marks_log P hP hm t
  have hden : (∑ x, P x * Real.log (P x)) -
      (∑ x, P x * Real.log (μ x.1)) -
        (∑ i, ∑ x, P x * Real.log (a i (t i x.1) (x.2 i))) ≤ L := by
    have hh (x : X × (I → M)) : P x * Real.log (P x) ≤
        P x * (L + Real.log (μ x.1) + ∑ i, Real.log (a i (t i x.1) (x.2 i))) := by
      by_cases hx : P x = 0
      · simp [hx]
      · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
        have hpr : 0 < ∏ i, a i (t i x.1) (x.2 i) := Finset.prod_pos (fun i _ => ha i x hp)
        have hlog := Real.log_le_log hp (hdensity x)
        rw [Real.log_mul (mul_pos (Real.exp_pos L) (hμ x.1)).ne' hpr.ne',
          Real.log_mul (Real.exp_ne_zero L) (hμ x.1).ne',Real.log_exp,
          Real.log_prod (fun i _ => (ha i x hp).ne')] at hlog
        exact mul_le_mul_of_nonneg_left hlog (hP x)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hh x)
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum] at hh
    rw [← Finset.sum_mul,hm,one_mul,Finset.sum_comm] at hh
    linarith
  have hdiv : divergence (pushMass Prod.fst P) μ =
      (∑ x, P x * Real.log (pushMass Prod.fst P x.1)) -
        ∑ x, P x * Real.log (μ x.1) := by
    rw [divergence_pushMass_eq,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      rw [Real.log_div (hp.trans_le (le_pushMass _ _ hP x)).ne' (hμ x.1).ne']
      ring
  have hcost (i : I) : (∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))) =
      (∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
        (fun x => x.2 i) (t i x.1) (x.2 i))) -
      ∑ x, P x * Real.log (a i (t i x.1) (x.2 i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      rw [Real.log_div (conditionalMass_pos _ hP _ _ x hp).ne' (ha i x hp).ne']
      ring
  simp_rw [hcost]
  rw [Finset.sum_sub_distrib,hdiv]
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

theorem active_contact_entropy_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ) (L : ℝ) (S : Finset I)
    (han : ∀ i y m, 0 ≤ a i y m)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i)) :
    (∑ i ∈ S, divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
      (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2)) ≤
      (∑ i ∈ S, divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ)) +
        L - divergence (pushMass Prod.fst P) μ +
      ∑ i ∈ Sᶜ, ∑ x, P x * Real.log (∑ m, a i (t i x.1) m) := by
  let C (i : I) := ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
    (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))
  have hall := conditional_mark_cost_le P hP hm μ hμ t a L ha hdensity
  change (∑ i, C i) ≤ L - divergence (pushMass Prod.fst P) μ at hall
  rw [← Finset.sum_add_sum_compl S] at hall
  have hinactive : -(∑ i ∈ Sᶜ, ∑ x, P x * Real.log (∑ m, a i (t i x.1) m)) ≤
      ∑ i ∈ Sᶜ, C i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => conditional_cost_ge P hP _ _ (a i) (han i) (ha i))
  have heq (i : I) : divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
      (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2) =
        divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ) + C i := by
    exact divergence_mark_chain P hP _ _ _ _
      (fun x _ => (hμ x.1).trans_le (le_pushMass _ _ (fun ω => (hμ ω).le) x.1)) (ha i)
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]

lemma pushMass_fst (P : X × M → ℝ) (x : X) :
    pushMass Prod.fst P x = ∑ m, P (x,m) := by
  simp only [pushMass,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

theorem marginal_density_le (P : (X × (I → M)) → ℝ) (μ : X → ℝ)
    (a : I → X → M → ℝ) (L : ℝ)
    (hd : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i x.1 (x.2 i)) (ω : X) :
    pushMass Prod.fst P ω ≤ Real.exp L * μ ω * ∏ i, ∑ m, a i ω m := by
  rw [pushMass_fst, Fintype.prod_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun m _ => hd (ω,m)

theorem entropy_exponential_domination (Q μ : X → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hm : ∑ x, Q x = 1) (hμ : ∀ x, 0 < μ x) (ξ : X → ℝ)
    (L B : ℝ) (hd : ∀ x, Q x ≤ Real.exp L * μ x * Real.exp (ξ x))
    (hmgf : ∑ x, μ x * Real.exp (2 * ξ x) ≤ Real.exp B) :
    divergence Q μ ≤ 2*L+B ∧ (∑ x, Q x*ξ x) ≤ L+B := by
  have hlog : divergence Q μ ≤ L + ∑ x, Q x * ξ x := by
    have hh (x : X) : Q x * Real.log (Q x / μ x) ≤ Q x * (L + ξ x) := by
      by_cases hx : Q x = 0
      · simp [hx]
      · have hp : 0 < Q x := lt_of_le_of_ne (hQ x) (Ne.symm hx)
        have hr : Q x / μ x ≤ Real.exp (L + ξ x) := by
          rw [div_le_iff₀ (hμ x), Real.exp_add]
          simpa only [mul_assoc,mul_left_comm,mul_comm] using hd x
        have hl := Real.log_le_log (div_pos hp (hμ x)) hr
        rw [Real.log_exp] at hl
        exact mul_le_mul_of_nonneg_left hl (hQ x)
    have hh := Finset.sum_le_sum (s := Finset.univ) fun x _ => hh x
    simpa only [divergence, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul] using hh
  have hent := entropy_inequality Q μ hQ (fun x => (hμ x).le) hm
    (fun x _ => hμ x) (fun x => 2 * ξ x)
  have hmgfpos := normalizer_pos Q μ hQ (fun x => (hμ x).le) hm
    (fun x _ => hμ x) (fun x => 2 * ξ x)
  have hb := Real.log_le_log hmgfpos hmgf
  rw [Real.log_exp] at hb
  have he : (∑ x, Q x * (2 * ξ x)) = 2 * ∑ x, Q x * ξ x := by
    simp only [Finset.mul_sum]
    congr 1
    ext x
    ring
  rw [he] at hent
  constructor <;> linarith

noncomputable def logContactMass (a : I → X → M → ℝ) (ω : X) : ℝ :=
  ∑ i, Real.log (max 1 (∑ m, a i ω m))

omit [Fintype X] in
lemma exp_logContactMass (a : I → X → M → ℝ) (ω : X) :
    Real.exp (logContactMass a ω) = ∏ i, max 1 (∑ m, a i ω m) := by
  rw [logContactMass,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

omit [Fintype X] in
lemma logContactMass_nonneg (a : I → X → M → ℝ) (ω : X) :
    0 ≤ logContactMass a ω :=
  Finset.sum_nonneg fun _i _ => Real.log_nonneg (le_max_left _ _)

theorem contact_configuration_entropy (P : (X × (I → M)) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (a : I → X → M → ℝ) (ha : ∀ i ω m, 0 ≤ a i ω m) (L B : ℝ)
    (hd : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i x.1 (x.2 i))
    (hmgf : ∑ ω, μ ω * Real.exp (2 * logContactMass a ω) ≤ Real.exp B) :
    divergence (pushMass Prod.fst P) μ ≤ 2*L+B ∧
      (∑ x, P x * logContactMass a x.1) ≤ L+B := by
  have hd' (ω : X) : pushMass Prod.fst P ω ≤
      Real.exp L * μ ω * Real.exp (logContactMass a ω) := by
    rw [exp_logContactMass]
    exact (marginal_density_le P μ a L hd ω).trans
      (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
        (fun i _ => Finset.sum_nonneg fun m _ => ha i ω m)
        (fun i _ => le_max_right _ _)) (mul_pos (Real.exp_pos L) (hμ ω)).le)
  have hh := entropy_exponential_domination (pushMass Prod.fst P) μ
    (pushMass_nonneg _ _ hP) (by rw [pushMass_sum,hm]) hμ (logContactMass a) L B hd' hmgf
  rw [sum_pushMass_mul] at hh
  exact hh

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (Y i)] in
lemma inactive_contact_log_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (a : I → X → M → ℝ) (ha : ∀ i ω m, 0 ≤ a i ω m)
    (hs : ∀ i x, 0 < P x → 0 < a i x.1 (x.2 i)) (S : Finset I) :
    (∑ i ∈ S, ∑ x, P x * Real.log (∑ m, a i x.1 m)) ≤
      ∑ x, P x * logContactMass a x.1 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    apply mul_le_mul_of_nonneg_left _ (hP x)
    calc
      _ ≤ ∑ i ∈ S, Real.log (max 1 (∑ m, a i x.1 m)) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.log_le_log ((hs i x hp).trans_le
          (Finset.single_le_sum (fun m _ => ha i x.1 m) (Finset.mem_univ _)))
          (le_max_right _ _)
      _ ≤ logContactMass a x.1 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => Real.log_nonneg (le_max_left _ _))

theorem active_inverse_cost_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ)
    (cost : (i : I) → Y i → M → ℝ) (L : ℝ) (S : Finset I)
    (han : ∀ i y m, 0 ≤ a i y m)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hc : ∀ i y m, 0 ≤ cost i y m)
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i))
    (hmoment : ∀ i ∈ S, ∑ ym : Y i × M, pushMass (t i) μ ym.1 *
      a i ym.1 ym.2 * (1 + cost i ym.1 ym.2) ≤ 4) :
    (∑ i ∈ S, ∑ x, P x * Real.log (1 + cost i (t i x.1) (x.2 i))) ≤
      (∑ i ∈ S, divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ)) +
        L - divergence (pushMass Prod.fst P) μ +
      (∑ x, P x * logContactMass (fun i ω => a i (t i ω)) x.1) +
        (S.card : ℝ) * Real.log 4 := by
  have hactive := active_contact_entropy_le P hP hm μ hμ t a L S han ha hdensity
  have hinactive := inactive_contact_log_le P hP (fun i ω => a i (t i ω))
    (fun i ω m => han i (t i ω) m) ha Sᶜ
  have hi (i : I) (hi : i ∈ S) :
      (∑ x, P x * Real.log (1 + cost i (t i x.1) (x.2 i))) ≤
        divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
          (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2) + Real.log 4 := by
    let f : X × (I → M) → Y i × M := fun x => (t i x.1,x.2 i)
    let R : Y i × M → ℝ := fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2
    have hR : ∀ ym, 0 ≤ R ym := fun ym => mul_nonneg
      (pushMass_nonneg _ _ (fun ω => (hμ ω).le) _) (han i _ _)
    have hs (ym : Y i × M) (h : 0 < pushMass f P ym) : 0 < R ym := by
      obtain ⟨x,hx,hfx⟩ : ∃ x, 0 < P x ∧ f x = ym := by
        by_contra! hn
        have hh : pushMass f P ym ≤ 0 := by
          unfold pushMass
          apply Finset.sum_nonpos
          intro x _
          split_ifs with he
          · exact le_of_not_gt (fun hx => hn x hx he)
          · rfl
        linarith
      subst ym
      exact mul_pos ((hμ x.1).trans_le (le_pushMass _ _ (fun ω => (hμ ω).le) x.1))
        (ha i x hx)
    have hpos (ym : Y i × M) : 0 < 1 + cost i ym.1 ym.2 := by linarith [hc i ym.1 ym.2]
    have hh := entropy_inequality (pushMass f P) R (pushMass_nonneg _ _ hP) hR
      (by rw [pushMass_sum,hm]) hs (fun ym => Real.log (1 + cost i ym.1 ym.2))
    have hm' : (∑ ym, R ym * Real.exp (Real.log (1 + cost i ym.1 ym.2))) ≤ 4 := by
      simp only [Real.exp_log (hpos _)]
      exact hmoment i hi
    have hz := normalizer_pos (pushMass f P) R (pushMass_nonneg _ _ hP) hR
      (by rw [pushMass_sum,hm]) hs (fun ym => Real.log (1 + cost i ym.1 ym.2))
    have hl := Real.log_le_log hz hm'
    rw [sum_pushMass_mul] at hh
    exact hh.trans (add_le_add_right hl _)
  have hsum := Finset.sum_le_sum (fun i hi' => hi i hi')
  simp only [Finset.sum_add_distrib,Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

end CriticalPercolation.FiniteEntropy
end
end

end OAI
