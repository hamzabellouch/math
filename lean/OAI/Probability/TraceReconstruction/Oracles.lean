import OAI.Probability.TraceReconstruction.InitialMoments

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem law_ext {P Q : FiniteLaw α} (h : ∀a,P.mass a=Q.mass a) : P=Q := by
  cases P; cases Q; congr; exact funext h

theorem tv_self (P : FiniteLaw α) : P.tv P=0 := by simp [tv]

theorem tv_le_one (P Q : FiniteLaw α) : P.tv Q≤1 := by
  unfold tv
  have h : (∑a,|P.mass a-Q.mass a|)≤2 := by
    calc
      _ ≤ ∑a, (P.mass a+Q.mass a) := Finset.sum_le_sum (fun a _ =>
        (abs_sub (P.mass a) (Q.mass a)).trans_eq (by rw [abs_of_nonneg (P.nonneg a),abs_of_nonneg (Q.nonneg a)]))
      _ = 2 := by rw [Finset.sum_add_distrib,P.total,Q.total]; norm_num
  linarith

theorem expect_bind (P : FiniteLaw α) (K : α → FiniteLaw β) (f : β → ℝ) :
    (P.bind K).expect f=P.expect (fun a => (K a).expect f) := by
  unfold expect bind
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bind_assoc (P : FiniteLaw α) (K : α → FiniteLaw β) (L : β → FiniteLaw γ) :
    (P.bind K).bind L=P.bind (fun a => (K a).bind L) := by
  apply law_ext
  intro c
  simp only [bind,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tv_bind_kernel_le (P : FiniteLaw α) (K L : α → FiniteLaw β) :
    (P.bind K).tv (P.bind L) ≤ P.expect (fun a => (K a).tv (L a)) := by
  unfold tv bind expect
  simp only
  calc
    _ = (1/2:ℝ)*∑b, |∑a,P.mass a*((K a).mass b-(L a).mass b)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (1/2:ℝ)*∑b,∑a,P.mass a*|(K a).mass b-(L a).mass b| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro b _
      simpa only [abs_mul,abs_of_nonneg (P.nonneg _)] using
        Finset.abs_sum_le_sum_abs (fun a => P.mass a*((K a).mass b-(L a).mass b)) Finset.univ
    _ = _ := by
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
      ring

/-- An invalid layout is charged only its unconditional probability. -/
theorem tv_bind_fit_le (P : FiniteLaw α) (K L : α → FiniteLaw β)
    (good : α → Prop) [DecidablePred good] (E : ℝ)
    (hfit : ∀a,good a → (K a).tv (L a)≤E) :
    (P.bind K).tv (P.bind L) ≤ P.expect (fun a => if good a then E else 1) := by
  apply (tv_bind_kernel_le P K L).trans
  apply expect_mono
  intro a
  split_ifs with h
  · exact hfit a h
  · exact tv_le_one _ _

theorem tv_prod_eq_left (P Q : FiniteLaw α) (R : FiniteLaw β) :
    (P.prod R).tv (Q.prod R)=P.tv Q := by
  unfold tv prod
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [← sub_mul,abs_mul,abs_of_nonneg (R.nonneg _),← Finset.mul_sum,R.total,mul_one]

theorem tv_prod_eq_right (P : FiniteLaw α) (Q R : FiniteLaw β) :
    (P.prod Q).tv (P.prod R)=Q.tv R := by
  unfold tv prod
  congr 1
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sub,abs_mul,abs_of_nonneg (P.nonneg _),← Finset.mul_sum]
  rw [← Finset.sum_mul,P.total,one_mul]

theorem tv_prod_le (P Q : FiniteLaw α) (R S : FiniteLaw β) :
    (P.prod R).tv (Q.prod S) ≤ P.tv Q+R.tv S := by
  have H := tv_triangle (P.prod R) (Q.prod R) (Q.prod S)
  rwa [tv_prod_eq_left,tv_prod_eq_right] at H

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem coordinateProduct_succ_tv {n : ℕ} (P Q : Fin (n+1) → FiniteLaw α) :
    (coordinateProduct P).tv (coordinateProduct Q) =
      ((P 0).prod (coordinateProduct (fun i => P i.succ))).tv
        ((Q 0).prod (coordinateProduct (fun i => Q i.succ))) := by
  change (1/2:ℝ)*(∑x : Fin (n+1) → α, |(∏i,(P i).mass (x i))-(∏i,(Q i).mass (x i))|)=
    (1/2:ℝ)*∑x : α × (Fin n → α), |(P 0).mass x.1*(∏i,(P i.succ).mass (x.2 i))-(Q 0).mass x.1*(∏i,(Q i.succ).mass (x.2 i))|
  congr 1
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem tv_coordinateProduct_le {n : ℕ} (P Q : Fin n → FiniteLaw α) :
    (coordinateProduct P).tv (coordinateProduct Q) ≤ ∑i, (P i).tv (Q i) := by
  induction n with
  | zero => simp [tv,coordinateProduct]
  | succ n ih =>
    rw [coordinateProduct_succ_tv,Fin.sum_univ_succ]
    exact (tv_prod_le _ _ _ _).trans (by linarith [ih (fun i => P i.succ) (fun i => Q i.succ)])

theorem expect_coordinateProduct_succ {n : ℕ} (P : Fin (n+1) → FiniteLaw α)
    (F : (Fin (n+1) → α) → ℝ) :
    (coordinateProduct P).expect F =
      (P 0).expect (fun a => (coordinateProduct (fun i => P i.succ)).expect
        (fun x => F (Fin.cons a x))) := by
  change (∑x : Fin (n+1) → α, (∏i,(P i).mass (x i))*F x)=
    ∑a : α, (P 0).mass a*(∑x : Fin n → α, (∏i,(P i.succ).mass (x i))*F (Fin.cons a x))
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp_rw [Finset.mul_sum,mul_assoc]

end TraceReconstruction.FiniteLaw


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem FiniteLaw.expect_sub {α : Type*} [Fintype α] (P : FiniteLaw α)
    (F G : α → ℝ) : P.expect (fun a => F a-G a)=P.expect F-P.expect G := by
  simp only [FiniteLaw.expect,mul_sub,Finset.sum_sub_distrib]

theorem FiniteLaw.abs_expect_le {α : Type*} [Fintype α] (P : FiniteLaw α) (F : α → ℝ) :
    |P.expect F|≤P.expect (fun a => |F a|) := by
  simpa only [FiniteLaw.expect,abs_mul,abs_of_nonneg (P.nonneg _)] using
    Finset.abs_sum_le_sum_abs (fun a => P.mass a*F a) Finset.univ

/-- A finite auxiliary observation, decoded by a fixed function, simulates the
usual deletion channel on a literal binary word. Test functions range over the
observable traces only, never latent boundaries. -/
def SimulatesTrace {α : Type*} [Fintype α] (q : ℝ) (P : FiniteLaw α)
    (decode : α → List Bool) (w : List Bool) : Prop :=
  ∀ F : List Bool → ℝ, P.expect (fun a => F (decode a))=listDeletionExpectation q w F

def ApproximatesTrace {α : Type*} [Fintype α] (q : ℝ) (P : FiniteLaw α)
    (decode : α → List Bool) (w : List Bool) (E : ℝ) : Prop :=
  ∀ F : List Bool → ℝ, (∀t,F t∈Set.Icc 0 1) →
    |P.expect (fun a => F (decode a))-listDeletionExpectation q w F|≤E

theorem listDeletionExpectation_const (q c : ℝ) (w : List Bool) :
    listDeletionExpectation q w (fun _ => c)=c := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [listDeletionExpectation,ih]; ring

theorem listDeletionExpectation_linear (q : ℝ) (w : List Bool)
    (a b : ℝ) (F G : List Bool → ℝ) :
    listDeletionExpectation q w (fun t => a*F t+b*G t)=
      a*listDeletionExpectation q w F+b*listDeletionExpectation q w G := by
  induction w generalizing F G with
  | nil => rfl
  | cons c w ih => simp only [listDeletionExpectation,ih]; ring

theorem listDeletionExpectation_mono {q : ℝ} (hq : q∈Set.Icc 0 1)
    (w : List Bool) {F G : List Bool → ℝ} (h : ∀t,F t≤G t) :
    listDeletionExpectation q w F≤listDeletionExpectation q w G := by
  induction w generalizing F G with
  | nil => exact h []
  | cons b w ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih h) hq.1)
      (mul_le_mul_of_nonneg_left (ih (fun t => h (b::t))) (sub_nonneg.mpr hq.2))

theorem listDeletionExpectation_range {q : ℝ} (hq : q∈Set.Icc 0 1)
    (w : List Bool) (F : List Bool → ℝ) (hF : ∀t,F t∈Set.Icc 0 1) :
    listDeletionExpectation q w F∈Set.Icc 0 1 := by
  constructor
  · simpa only [listDeletionExpectation_const] using
      listDeletionExpectation_mono hq w (fun t => (hF t).1)
  · simpa only [listDeletionExpectation_const] using
      listDeletionExpectation_mono hq w (fun t => (hF t).2)

theorem listDeletionExpectation_sum {α : Type*} [Fintype α] (q : ℝ)
    (w : List Bool) (F : α → List Bool → ℝ) :
    listDeletionExpectation q w (fun t => ∑a,F a t)=
      ∑a,listDeletionExpectation q w (F a) := by
  induction w generalizing F with
  | nil => rfl
  | cons b w ih =>
    simp only [listDeletionExpectation,ih,Finset.mul_sum,Finset.sum_add_distrib]

theorem FiniteLaw.expect_listDeletionExpectation {α : Type*} [Fintype α]
    (P : FiniteLaw α) (q : ℝ) (w : List Bool) (F : α → List Bool → ℝ) :
    P.expect (fun a => listDeletionExpectation q w (F a))=
      listDeletionExpectation q w (fun t => P.expect (fun a => F a t)) := by
  unfold FiniteLaw.expect
  rw [listDeletionExpectation_sum]
  apply Finset.sum_congr rfl
  intro a _
  have H := listDeletionExpectation_linear q w (P.mass a) 0 (F a) (fun _ => 0)
  simpa only [zero_mul,add_zero] using H.symm

theorem SimulatesTrace.append {α β : Type*} [Fintype α] [Fintype β]
    {q : ℝ} {P : FiniteLaw α} {Q : FiniteLaw β} {f : α → List Bool} {g : β → List Bool}
    {x y : List Bool} (hP : SimulatesTrace q P f x) (hQ : SimulatesTrace q Q g y) :
    SimulatesTrace q (P.prod Q) (fun a => f a.1++g a.2) (x++y) := by
  intro F
  rw [FiniteLaw.expect_prod,listDeletionExpectation_append]
  change P.expect (fun a => Q.expect (fun b => F (f a++g b)))=_
  unfold SimulatesTrace at hP hQ
  calc
    _ = P.expect (fun a => listDeletionExpectation q y (fun t => F (f a++t))) :=
      congrArg P.expect (funext fun a => hQ (fun t => F (f a++t)))
    _ = _ := hP (fun t => listDeletionExpectation q y (fun u => F (t++u)))

theorem SimulatesTrace.approximate {α : Type*} [Fintype α]
    {q : ℝ} {P : FiniteLaw α} {f : α → List Bool} {w : List Bool}
    (h : SimulatesTrace q P f w) : ApproximatesTrace q P f w 0 := by
  intro F _
  rw [h,sub_self,abs_zero]

theorem ApproximatesTrace.append {α β : Type*} [Fintype α] [Fintype β]
    {q : ℝ} (hq : q∈Set.Icc 0 1) {P : FiniteLaw α} {Q : FiniteLaw β}
    {f : α → List Bool} {g : β → List Bool} {x y : List Bool} {E D : ℝ}
    (hP : ApproximatesTrace q P f x E) (hQ : ApproximatesTrace q Q g y D) :
    ApproximatesTrace q (P.prod Q) (fun a => f a.1++g a.2) (x++y) (E+D) := by
  intro F hF
  rw [FiniteLaw.expect_prod,listDeletionExpectation_append]
  let H : List Bool → ℝ := fun t => listDeletionExpectation q y (fun u => F (t++u))
  have hH : ∀t,H t∈Set.Icc 0 1 := fun t => listDeletionExpectation_range hq y _ (fun u => hF (t++u))
  have h1 := hP H hH
  have h2 : |P.expect (fun a => Q.expect (fun b => F (f a++g b)))-P.expect (fun a => H (f a))|≤D := by
    rw [← FiniteLaw.expect_sub]
    calc
      _ ≤ P.expect (fun a => |Q.expect (fun b => F (f a++g b))-H (f a)|) := FiniteLaw.abs_expect_le _ _
      _ ≤ P.expect (fun _ => D) := FiniteLaw.expect_mono _ (fun a => hQ _ (fun t => hF (f a++t)))
      _ = D := FiniteLaw.expect_const _ _
  exact (abs_sub_le _ _ _).trans (by linarith only [h1,h2])

/-- Any randomized partition into exactly the same literal word gives exactly
its usual trace after boundaries are forgotten. No fit conditioning occurs. -/
theorem SimulatesTrace.random_partition {α Ω : Type*} [Fintype α] [Fintype Ω]
    {q : ℝ} (P : FiniteLaw Ω) (K : Ω → FiniteLaw α) (decode : α → List Bool)
    (w : List Bool) (h : ∀ω,SimulatesTrace q (K ω) decode w) :
    SimulatesTrace q (P.bind K) decode w := by
  intro F
  rw [FiniteLaw.expect_bind]
  unfold SimulatesTrace at h
  simp_rw [h]
  exact FiniteLaw.expect_const _ _

/-- A failed deterministic layout is charged its unconditional probability;
the conditional law on all metadata, not a fit-conditioned law, is used. -/
theorem ApproximatesTrace.random_partition {α Ω : Type*} [Fintype α] [Fintype Ω]
    {q : ℝ} (hq : q∈Set.Icc 0 1) (P : FiniteLaw Ω) (K : Ω → FiniteLaw α)
    (decode : α → List Bool) (w : List Bool) (good : Ω → Prop) [DecidablePred good]
    (E : ℝ) (h : ∀ω,good ω → ApproximatesTrace q (K ω) decode w E) :
    ApproximatesTrace q (P.bind K) decode w (P.expect (fun ω => if good ω then E else 1)) := by
  intro F hF
  rw [FiniteLaw.expect_bind,← FiniteLaw.expect_const P (listDeletionExpectation q w F),← FiniteLaw.expect_sub]
  apply (FiniteLaw.abs_expect_le _ _).trans
  apply FiniteLaw.expect_mono
  intro ω
  split_ifs with hgood
  · exact h ω hgood F hF
  · have hc := listDeletionExpectation_range hq w F hF
    have hn := FiniteLaw.expect_mono (K ω) (fun a => (hF (decode a)).1)
    have hu := FiniteLaw.expect_mono (K ω) (fun a => (hF (decode a)).2)
    rw [FiniteLaw.expect_const] at hn hu
    exact abs_le.mpr ⟨by linarith [hc.2],by linarith [hc.1]⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Admissible close child labels, without relaxing any plateau restrictions
on the anchor. An arbitrary finite label domain is retained. -/
def closeLabels (A : Finset ℤ) (L : ℕ) (a : ℤ) : Finset ℤ :=
  A.filter (fun c => |c-a| < (L:ℤ))

theorem closeLabels_card (A : Finset ℤ) (L : ℕ) (a : ℤ) :
    (closeLabels A L a).card ≤ 2*L := by
  have hsub : closeLabels A L a ⊆ Finset.Ioo (a-(L:ℤ)) (a+(L:ℤ)) := by
    intro c hc
    have h := abs_lt.mp ((Finset.mem_filter.mp hc).2)
    exact Finset.mem_Ioo.mpr ⟨by omega,by omega⟩
  have H := Finset.card_le_card hsub
  rw [Int.card_Ioo] at H
  omega

/-- Root anchor and close-child energy. This keeps the actual labels finite,
including any additional source plateau cutoff. -/
theorem root_anchor_energy (n L : ℕ) (A B : Finset ℤ) (c : ℤ) :
    (∑ a∈A, ∑ _d∈closeLabels B L a, windowKernel n L (a-c)^2) ≤
      2*L^3*binomialBound n := by
  calc
    _ ≤ ∑a∈A, (2*L:ℝ)*windowKernel n L (a-c)^2 := by
      apply Finset.sum_le_sum
      intro a _
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast closeLabels_card B L a) (sq_nonneg _)
    _ = (2*L:ℝ)*(∑a∈A,windowKernel n L (a-c)^2) := by rw [Finset.mul_sum]
    _ ≤ (2*L:ℝ)*(L^2*binomialBound n) :=
      mul_le_mul_of_nonneg_left (windowKernel_energy n L A c) (by positivity)
    _ = _ := by ring

/-- The shared global jitter stays in the joint kernel until after squaring.
The two close labels cost only (2L)^2, uniformly in parent labels. -/
theorem sibling_anchor_energy (g n₁ n₂ L : ℕ) (A B C D : Finset ℤ) (c₁ c₂ : ℤ) :
    (∑ a∈A, ∑ b∈B, ∑ _c∈closeLabels C L a, ∑ _d∈closeLabels D L b,
      jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2) ≤
      4*L^6*binomialBound g*binomialBound n₂ := by
  calc
    _ ≤ ∑a∈A, ∑b∈B, (2*L:ℝ)^2*jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((closeLabels C L a).card:ℝ)≤2*L := by exact_mod_cast closeLabels_card C L a
      have hd : ((closeLabels D L b).card:ℝ)≤2*L := by exact_mod_cast closeLabels_card D L b
      have hm := mul_le_mul hc hd (by positivity) (by positivity : (0:ℝ)≤2*L)
      rw [mul_assoc] at hm
      nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg (jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)))]
    _ = (2*L:ℝ)^2*(∑a∈A,∑b∈B,jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (2*L:ℝ)^2*(L^4*binomialBound g*binomialBound n₂) :=
      mul_le_mul_of_nonneg_left (jointWindowKernel_energy g n₁ n₂ L A B c₁ c₂) (by positivity)
    _ = _ := by ring

/-- Exact bottom-up summation of any finite binary anchor model. The state
contains its actual index path, so group-dependent kernels are allowed. -/
def binaryTreeSum {α : Type*} [Fintype α] (K : ℕ → α → α × α → ℝ) : ℕ → α → ℝ
  | 0, _ => 1
  | n+1, a => ∑b, K n a b*binaryTreeSum K n b.1*binaryTreeSum K n b.2

def binaryTreeBudget (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => C n*(binaryTreeBudget C n)^2

theorem binaryTreeBudget_nonneg (C : ℕ → ℝ) (hC : ∀n,0≤C n) (n : ℕ) :
    0≤binaryTreeBudget C n := by
  cases n with
  | zero => norm_num [binaryTreeBudget]
  | succ n => exact mul_nonneg (hC n) (sq_nonneg _)

theorem binaryTreeSum_nonneg {α : Type*} [Fintype α]
    (K : ℕ → α → α × α → ℝ) (hK : ∀n a b,0≤K n a b) (n : ℕ) (a : α) :
    0≤binaryTreeSum K n a := by
  induction n generalizing a with
  | zero => norm_num [binaryTreeSum]
  | succ n ih => exact Finset.sum_nonneg (fun b _ => mul_nonneg (mul_nonneg (hK n a b) (ih b.1)) (ih b.2))

/-- Uniform local anchor square sums multiply without decoupling the two
correlated offsets of a sibling group. Domain/plateau indicators can be
included in K and are never removed by conditioning. -/
theorem binaryTreeSum_le {α : Type*} [Fintype α]
    (K : ℕ → α → α × α → ℝ) (hK : ∀n a b,0≤K n a b)
    (C : ℕ → ℝ) (hC : ∀n,0≤C n) (hlocal : ∀n a, (∑b,K n a b)≤C n)
    (n : ℕ) (a : α) : binaryTreeSum K n a≤binaryTreeBudget C n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    calc
      _ ≤ ∑b, K n a b*(binaryTreeBudget C n)^2 := by
        apply Finset.sum_le_sum
        intro b _
        rw [mul_assoc,pow_two]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (ih b.1) (ih b.2)
          (binaryTreeSum_nonneg K hK n b.2) (binaryTreeBudget_nonneg C hC n)) (hK n a b)
      _ = (∑b,K n a b)*(binaryTreeBudget C n)^2 := by rw [Finset.sum_mul]
      _ ≤ C n*(binaryTreeBudget C n)^2 := mul_le_mul_of_nonneg_right (hlocal n a) (sq_nonneg _)
      _ = _ := rfl

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hypergeomMass_middle_sq (V M m v : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hm : m≤V+M) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    hypergeomMass V M m v^2≤4096/((M:ℝ)+1) := by
  have hp' : p∈Set.Ioo (0:ℝ) 1 := by constructor <;> linarith [hp.1,hp.2]
  have hpp : (1/8:ℝ)≤p*(1-p) := by nlinarith [sq_nonneg (p-1/2),mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hNr : (16:ℝ)≤(V:ℝ)+M := by exact_mod_cast hN
  have hVr : (M:ℝ)≤V := by exact_mod_cast hMV
  have hv : 1≤(V+M:ℕ)*p*(1-p) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) V,Nat.cast_nonneg (α:=ℝ) M]
  have H := hypergeomMass_sq_upper V M m v hp' hm hmean hv
  apply H.trans
  have hd : 0<((V:ℝ)+1)*((M:ℝ)+1)*p*(1-p) := by positivity [hp'.1,sub_pos.mpr hp'.2]
  apply (div_le_iff₀ hd).2
  have hM : 0<(M:ℝ)+1 := by positivity
  have he : 4096/((M:ℝ)+1)*(((V:ℝ)+1)*((M:ℝ)+1)*p*(1-p))=
      4096*((V:ℝ)+1)*(p*(1-p)) := by field_simp
  rw [he]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hpp (show 0≤(V:ℝ)+1 by positivity)]

theorem hypergeomMass_middle_le (V M m v : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hm : m≤V+M) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    hypergeomMass V M m v≤64/Real.sqrt ((M:ℝ)+1) := by
  have H := hypergeomMass_middle_sq V M m v hp hMV hN hm hmean
  have hs : 0<Real.sqrt ((M:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have he : (64/Real.sqrt ((M:ℝ)+1))^2=4096/((M:ℝ)+1) := by
    rw [div_pow,Real.sq_sqrt (by positivity)]; norm_num
  rw [←he] at H
  exact (sq_le_sq₀ (hypergeomMass_nonneg _ _ _ _) (by positivity)).1 H

theorem sum_range_extend_zero {f : ℕ→ℝ} {m n : ℕ} (hmn : m≤n)
    (hz : ∀k,m≤k→f k=0) : ∑k∈Finset.range n,f k=∑k∈Finset.range m,f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro k _ hk
  exact hz k (by simpa using hk)

theorem hypergeomMass_above_total (V M m v : ℕ) (h : m<v) :
    hypergeomMass V M m v=0 := by simp only [hypergeomMass,ite_eq_right (by omega : ¬v≤ m)]

def hypergeomLaw (V M m : ℕ) (hm : m≤V+M) : FiniteLaw (Fin (V+M+1)) where
  mass v := hypergeomMass V M m v
  nonneg _ := hypergeomMass_nonneg _ _ _ _
  total := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [sum_range_extend_zero (Nat.add_le_add_right hm 1) (fun k hk =>
      hypergeomMass_above_total V M m k (by omega))]
    exact sum_hypergeomMass V M m hm

theorem hypergeomMass_complement (V M m v : ℕ) (hv : v≤ m) :
    hypergeomMass V M m v=hypergeomMass M V m (m-v) := by
  simp only [hypergeomMass,ite_eq_left hv,ite_eq_left (Nat.sub_le _ _),Nat.sub_sub_self hv]
  rw [Nat.add_comm M V,mul_comm]

theorem hypergeomLaw_adjacent_tv (V M m : ℕ) (hM : M≤ m) (hV : m<V) :
    (hypergeomLaw V M (m+1) (by omega)).tv (hypergeomLaw V M m (by omega))=
      adjacentHypergeomTV V M m := by
  unfold FiniteLaw.tv
  simp only [hypergeomLaw]
  rw [Fin.sum_univ_eq_sum_range (fun v => |hypergeomMass V M (m+1) v-
    hypergeomMass V M m v|)]
  rw [sum_range_extend_zero (show m+2≤V+M+1 by omega) (fun k hk => by
    rw [hypergeomMass_above_total V M (m+1) k (by omega),
      hypergeomMass_above_total V M m k (by omega),sub_self,abs_zero])]
  rw [←Finset.sum_range_reflect (fun v => |hypergeomMass V M (m+1) v-
    hypergeomMass V M m v|) (m+2)]
  rw [show m+2=(m+1)+1 by omega,Finset.sum_range_succ']
  have hzero : |hypergeomMass V M (m+1) (m+1)-hypergeomMass V M m (m+1)|=
      hypergeomMass M V (m+1) 0 := by
    rw [hypergeomMass_above_total V M m (m+1) (by omega),sub_zero,
      hypergeomMass_complement V M (m+1) (m+1) le_rfl,Nat.sub_self,
      abs_of_nonneg (hypergeomMass_nonneg _ _ _ _)]
  have he (k : ℕ) (hk : k∈Finset.range (m+1)) :
      |hypergeomMass V M (m+1) ((m+1+1)-1-(k+1))-
       hypergeomMass V M m ((m+1+1)-1-(k+1))|=
      |hypergeomMass M V (m+1) (k+1)-hypergeomMass M V m k| := by
    have hk' : k≤ m := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
    rw [show (m+1+1)-1-(k+1)=m-k by omega,
      hypergeomMass_complement V M (m+1) (m-k) (by omega),
      hypergeomMass_complement V M m (m-k) (by omega)]
    rw [show m+1-(m-k)=k+1 by omega,show m-(m-k)=k by omega]
  rw [Finset.sum_congr rfl he]
  simp only [Nat.add_sub_cancel,Nat.sub_zero,hzero]
  rw [sum_range_extend_zero (Nat.add_le_add_right hM 1) (fun k hk => by
    rw [hypergeomMass_high M V (m+1) (k+1) (by omega),
      hypergeomMass_high M V m k (by omega),sub_self,abs_zero])]
  unfold adjacentHypergeomTV
  ring

theorem adjacentHypergeomTV_middle_le (V M m : ℕ) {p : ℝ}
    (hp : p∈Set.Icc (1/4:ℝ) (3/4:ℝ)) (hMV : M≤V)
    (hN : 16≤V+M) (hM : M≤ m) (hV : m<V) (hmean : (m:ℝ)=(V+M:ℕ)*p) :
    adjacentHypergeomTV V M m≤64/Real.sqrt ((M:ℝ)+1) := by
  apply (adjacentHypergeomTV_le_mass V M m hM hV).trans
  rw [hypergeomMass_complement M V m _ (by
    exact (hypergeomHiddenMode_le (V-1) M m (by omega)).trans hM)]
  exact hypergeomMass_middle_le V M m _ hp hMV hN (by omega) hmean

theorem hypergeomLaw_adjacent_middle (V M m : ℕ) (hN : 16≤V+M)
    (hM : M≤ m) (hV : m<V) (hlow : V+M≤4*m) (hhigh : 4*m≤3*(V+M)) :
    (hypergeomLaw V M m (by omega)).tv (hypergeomLaw V M (m+1) (by omega))≤
      64/Real.sqrt ((M:ℝ)+1) := by
  have hn : 0<(V+M:ℕ) := by omega
  have hnr : (0:ℝ)<(V+M:ℕ) := by exact_mod_cast hn
  have hL : ((V+M:ℕ):ℝ)≤4*(m:ℝ) := by exact_mod_cast hlow
  have hU : 4*(m:ℝ)≤3*((V+M:ℕ):ℝ) := by exact_mod_cast hhigh
  rw [FiniteLaw.tv_symm,hypergeomLaw_adjacent_tv V M m hM hV]
  have hp : (m:ℝ)/(V+M:ℕ)∈Set.Icc (1/4:ℝ) (3/4:ℝ) := by
    constructor
    · apply (le_div_iff₀ hnr).2; linarith
    · apply (div_le_iff₀ hnr).2; linarith
  exact adjacentHypergeomTV_middle_le V M m hp (by omega) hN hM hV
    (by field_simp)

theorem FiniteLaw.tv_chain {α : Type*} [Fintype α] (P : ℕ→FiniteLaw α) (n : ℕ) :
    (P 0).tv (P n)≤∑i∈Finset.range n,(P i).tv (P (i+1)) := by
  induction n with
  | zero => simp [FiniteLaw.tv_self]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [FiniteLaw.tv_triangle (P 0) (P n) (P (n+1))]

theorem hypergeomLaw_steps (V M m P : ℕ) (hN : 16≤V+M)
    (hM : M≤ m) (hV : m+P<V) (hlow : V+M≤4*m) (hhigh : 4*(m+P)≤3*(V+M)) :
    (hypergeomLaw V M m (by omega)).tv (hypergeomLaw V M (m+P) (by omega))≤
      (P:ℝ)*64/Real.sqrt ((M:ℝ)+1) := by
  let Q : ℕ→FiniteLaw (Fin (V+M+1)) := fun j =>
    hypergeomLaw V M (m+min j P) (by omega)
  have H := FiniteLaw.tv_chain Q P
  have hQ0 : Q 0=hypergeomLaw V M m (by omega) := by simp [Q]
  have hQP : Q P=hypergeomLaw V M (m+P) (by omega) := by simp [Q]
  rw [hQ0,hQP] at H
  apply H.trans
  calc
    _≤∑j∈Finset.range P,64/Real.sqrt ((M:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j<P := Finset.mem_range.mp hj
      simp only [Q,min_eq_left (by omega : j≤P),min_eq_left (by omega : j+1≤P)]
      exact hypergeomLaw_adjacent_middle V M (m+j) hN (by omega) (by omega)
        (by omega) (by omega)
    _=_ := by simp [mul_div_assoc]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]

def visibleFiberEquiv (m : ℕ) (S : Finset α) (hS : S.card≤ m) :
    {T : FixedSubset (α⊕β) m // T.val.toLeft=S} ≃ FixedSubset β (m-S.card) where
  toFun T := ⟨T.val.val.toRight,by
    have hc := Finset.card_toLeft_add_card_toRight (u:=T.val.val)
    rw [T.property,T.val.property] at hc
    omega⟩
  invFun R := ⟨⟨S.disjSum R.val,by simp only [Finset.card_disjSum,R.property]; omega⟩,by simp⟩
  left_inv T := by
    apply Subtype.ext; apply Subtype.ext
    simpa only [T.property] using (Finset.toLeft_disjSum_toRight (u:=T.val.val))
  right_inv R := by apply Subtype.ext; exact Finset.toRight_disjSum

def visibleScheduleLaw (m : ℕ) (hm : m≤Fintype.card α+Fintype.card β) : FiniteLaw (Finset α) :=
  (uniformSubsetLaw (α:=α⊕β) m (by simpa using hm)).map (fun T => T.val.toLeft)

theorem visibleScheduleLaw_mass (m : ℕ) (hm : m≤Fintype.card α+Fintype.card β) (S : Finset α) :
    (visibleScheduleLaw (α:=α) (β:=β) m hm).mass S=
      if S.card≤ m then ((Fintype.card β).choose (m-S.card):ℝ)/
        ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0 := by
  unfold visibleScheduleLaw
  rw [FiniteLaw.map_mass]
  by_cases hS : S.card≤ m
  · rw [ite_eq_left hS]
    simp only [uniformSubsetLaw,Fintype.card_sum]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have he : (Finset.univ.filter (fun T : FixedSubset (α⊕β) m => T.val.toLeft=S)).card=
        (Fintype.card β).choose (m-S.card) := by
      rw [←Fintype.card_subtype]
      exact (Fintype.card_congr (visibleFiberEquiv (β:=β) m S hS)).trans (card_fixedSubset _)
    rw [he]
    ring
  · rw [ite_eq_right hS]
    apply Finset.sum_eq_zero
    intro T _
    have hnot : T.val.toLeft≠S := by
      intro he
      apply hS
      simpa only [he,T.property] using (Finset.card_toLeft_le (u:=T.val))
    rw [ite_eq_right hnot]

theorem sum_finset_card (f : ℕ→ℝ) :
    (∑S : Finset α,f S.card)=∑v : Fin (Fintype.card α+1),
      ((Fintype.card α).choose v.val:ℝ)*f v.val := by
  let g : Finset α→Fin (Fintype.card α+1) := fun S =>
    ⟨S.card,by have H:=Finset.card_le_univ S; omega⟩
  rw [←Fintype.sum_fiberwise g (fun S => f S.card)]
  apply Finset.sum_congr rfl
  intro v _
  have hc : Fintype.card {S : Finset α // g S=v}=(Fintype.card α).choose v.val := by
    let e : {S : Finset α // g S=v} ≃ FixedSubset α v.val :=
      { toFun := fun S => ⟨S.val,by have H:=congrArg Fin.val S.property; exact H⟩
        invFun := fun S => ⟨S.val,by apply Fin.ext; exact S.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (card_fixedSubset _)
  calc
    _=∑_S : {S : Finset α // g S=v},f v.val := by
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      exact congrArg Fin.val S.property
    _=_ := by simp [hc]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem visibleScheduleLaw_tv (m m' : ℕ)
    (hm : m≤Fintype.card α+Fintype.card β) (hm' : m'≤Fintype.card α+Fintype.card β) :
    (visibleScheduleLaw (α:=α) (β:=β) m hm).tv (visibleScheduleLaw m' hm')=
      (hypergeomLaw (Fintype.card α) (Fintype.card β) m hm).tv
        (hypergeomLaw (Fintype.card α) (Fintype.card β) m' hm') := by
  unfold FiniteLaw.tv
  simp_rw [visibleScheduleLaw_mass]
  rw [sum_finset_card (α:=α) (fun v =>
    |(if v≤ m then ((Fintype.card β).choose (m-v):ℝ)/
      ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0)-
     (if v≤ m' then ((Fintype.card β).choose (m'-v):ℝ)/
      ((Fintype.card α+Fintype.card β).choose m':ℝ) else 0)|)]
  have he (v : ℕ) :
      ((Fintype.card α).choose v:ℝ)*
        |(if v≤ m then ((Fintype.card β).choose (m-v):ℝ)/
          ((Fintype.card α+Fintype.card β).choose m:ℝ) else 0)-
         (if v≤ m' then ((Fintype.card β).choose (m'-v):ℝ)/
          ((Fintype.card α+Fintype.card β).choose m':ℝ) else 0)|=
      |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v| := by
    rw [←abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) ((Fintype.card α).choose v)),←abs_mul,mul_sub]
    simp only [mul_ite,mul_zero,hypergeomMass,mul_div_assoc]
  simp_rw [he]
  simp only [hypergeomLaw]
  rw [Fin.sum_univ_eq_sum_range (fun v => |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v|)]
  rw [Fin.sum_univ_eq_sum_range (n:=Fintype.card α+Fintype.card β+1)
    (fun v => |hypergeomMass (Fintype.card α) (Fintype.card β) m v-
       hypergeomMass (Fintype.card α) (Fintype.card β) m' v|)]
  congr 1
  symm
  apply sum_range_extend_zero (by omega)
  intro k hk
  rw [hypergeomMass_high _ _ _ _ (by omega),hypergeomMass_high _ _ _ _ (by omega),sub_self,abs_zero]

theorem visibleScheduleLaw_steps (m P : ℕ)
    (hN : 16≤Fintype.card α+Fintype.card β) (hM : Fintype.card β≤ m)
    (hV : m+P<Fintype.card α) (hlow : Fintype.card α+Fintype.card β≤4*m)
    (hhigh : 4*(m+P)≤3*(Fintype.card α+Fintype.card β)) :
    (visibleScheduleLaw (α:=α) (β:=β) m (by omega)).tv
      (visibleScheduleLaw (β:=β) (m+P) (by omega))≤
      (P:ℝ)*64/Real.sqrt ((Fintype.card β:ℝ)+1) := by
  rw [visibleScheduleLaw_tv]
  exact hypergeomLaw_steps _ _ m P hN hM hV hlow hhigh

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem ext_expect {P Q : FiniteLaw α} (h : ∀f : α→ℝ,P.expect f=Q.expect f) : P=Q := by
  apply ext
  funext a
  have H:=h (fun b => if b=a then 1 else 0)
  simpa only [expect,mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq'] using H

theorem expect_map (P : FiniteLaw α) (f : α→β) (G : β→ℝ) :
    (P.map f).expect G=P.expect (G∘f) := expectation_map P f G

theorem map_map (P : FiniteLaw α) (f : α→β) (g : β→γ) :
    (P.map f).map g=P.map (g∘f) := by
  apply ext_expect
  intro G
  rw [expect_map,expect_map,expect_map]
  rfl

theorem map_id (P : FiniteLaw α) : P.map id=P := by
  apply ext_expect
  intro G
  rw [expect_map]
  rfl

theorem map_equiv_mass (P : FiniteLaw α) (e : α≃β) (b : β) :
    (P.map e).mass b=P.mass (e.symm b) := by
  rw [map_mass]
  simp only [←e.eq_symm_apply,Fintype.sum_ite_eq']

theorem tv_map_equiv (P Q : FiniteLaw α) (e : α≃β) :
    (P.map e).tv (Q.map e)=P.tv Q := by
  unfold tv
  simp_rw [map_equiv_mass]
  rw [e.symm.sum_comp (fun a => |P.mass a-Q.mass a|)]

end FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

def fixedSubsetEquiv (e : α≃β) (m : ℕ) : FixedSubset α m ≃ FixedSubset β m where
  toFun S := ⟨S.val.map e.toEmbedding,by simpa only [Finset.card_map] using S.property⟩
  invFun T := ⟨T.val.map e.symm.toEmbedding,by simpa only [Finset.card_map] using T.property⟩
  left_inv S := by apply Subtype.ext; exact e.finsetCongr.left_inv S.val
  right_inv T := by apply Subtype.ext; exact e.finsetCongr.right_inv T.val

theorem uniformSubsetLaw_map (e : α≃β) (m : ℕ) (hm : m≤Fintype.card α) :
    (uniformSubsetLaw m hm).map (fixedSubsetEquiv e m)=
      uniformSubsetLaw m (by simpa only [←Fintype.card_congr e] using hm) := by
  apply FiniteLaw.ext
  funext T
  rw [FiniteLaw.map_equiv_mass]
  simp only [uniformSubsetLaw,Fintype.card_congr e]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

abbrev HiddenIndex (H : Finset α) := {a : α // a∈H}
abbrev VisibleIndex (H : Finset α) := {a : α // a∉H}

def splitIndexEquiv (H : Finset α) : VisibleIndex H⊕HiddenIndex H ≃ α :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl (fun a => a∈H))

theorem card_splitIndex (H : Finset α) :
    Fintype.card (VisibleIndex H)+Fintype.card (HiddenIndex H)=Fintype.card α := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (splitIndexEquiv H)

omit [Fintype α] in
theorem card_hiddenIndex (H : Finset α) : Fintype.card (HiddenIndex H)=H.card := by
  exact Fintype.card_coe H

def eraseScheduleLaw (H : Finset α) (m : ℕ) (hm : m≤Fintype.card α) : FiniteLaw (Finset α) :=
  (uniformSubsetLaw m hm).map (fun S => S.val\H)

omit [Fintype α] in
theorem erase_splitIndex (H : Finset α) (S : Finset (VisibleIndex H⊕HiddenIndex H)) :
    (S.map (splitIndexEquiv H).toEmbedding)\H=
      S.toLeft.map ⟨Subtype.val,Subtype.val_injective⟩ := by
  ext a
  constructor
  · intro ha
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    cases b with
    | inl b =>
      apply Finset.mem_map.mpr
      exact ⟨b,by simpa using hb,rfl⟩
    | inr b => exact False.elim (hn b.property)
  · intro ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp ha
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_map.mpr ⟨Sum.inl b,by simpa using hb,rfl⟩
    · exact b.property

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eraseScheduleLaw_eq (H : Finset α) (m : ℕ) (hm : m≤Fintype.card α) :
    eraseScheduleLaw H m hm=
      (visibleScheduleLaw (α:=VisibleIndex H) (β:=HiddenIndex H) m
        (by simpa only [card_splitIndex] using hm)).map
        (fun S => S.map ⟨Subtype.val,Subtype.val_injective⟩) := by
  have h:=uniformSubsetLaw_map (splitIndexEquiv H) m
    (by simpa only [Fintype.card_sum,card_splitIndex] using hm)
  unfold eraseScheduleLaw visibleScheduleLaw
  rw [←h,FiniteLaw.map_map,FiniteLaw.map_map]
  congr 1
  funext S
  exact erase_splitIndex H S.val

theorem eraseScheduleLaw_steps (H : Finset α) (m P : ℕ)
    (hN : 16≤Fintype.card α) (hM : H.card≤ m)
    (hV : m+P+H.card<Fintype.card α) (hlow : Fintype.card α≤4*m)
    (hhigh : 4*(m+P)≤3*Fintype.card α) :
    (eraseScheduleLaw H m (by omega)).tv (eraseScheduleLaw H (m+P) (by omega))≤
    (P:ℝ)*64/Real.sqrt ((H.card:ℝ)+1) := by
  rw [eraseScheduleLaw_eq,eraseScheduleLaw_eq]
  refine (FiniteLaw.tv_map_le _ _ _).trans ?_
  have hc:=card_splitIndex H
  have hd:=card_hiddenIndex H
  have h:=visibleScheduleLaw_steps (α:=VisibleIndex H) (β:=HiddenIndex H) m P
    (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa only [hd] using h

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀i,Fintype (β i)]

def sigma (P : FiniteLaw ι) (K : ∀i, FiniteLaw (β i)) : FiniteLaw (Σi,β i) where
  mass a:=P.mass a.1*(K a.1).mass a.2
  nonneg a:=mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total:=by
    rw [Fintype.sum_sigma]
    simp_rw [←Finset.mul_sum,(K _).total,mul_one]
    exact P.total

theorem expect_sigma (P : FiniteLaw ι) (K : ∀i,FiniteLaw (β i)) (F : (Σi,β i)→ℝ) :
    (P.sigma K).expect F=P.expect (fun i => (K i).expect (fun b => F ⟨i,b⟩)) := by
  simp only [expect,sigma,Fintype.sum_sigma,Finset.mul_sum,mul_assoc]

theorem overlap_sigma_lower (P Q : FiniteLaw ι) (K L : ∀i,FiniteLaw (β i)) :
    (∑i,min (P.mass i) (Q.mass i)*overlap (K i) (L i))≤overlap (P.sigma K) (Q.sigma L) := by
  simp only [overlap,sigma,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro b _
  apply le_min
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (P.nonneg i)
  · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (Q.nonneg i)
end FiniteLaw

theorem sum_binomialMass_cutoff {n N : ℕ} (hn : n≤N) (p : ℝ) :
    ∑l : Fin (N+1),binomialMass n p l.val=1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => binomialMass n p k) (N+1)]
  rw [←sum_binomialMass n p]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have hn' : n<k := by simp only [Finset.mem_range] at hk; omega
  simp [binomialMass,Nat.choose_eq_zero_of_lt hn']

def boundedCountLaw {n N : ℕ} (hn : n≤N) (p : ℝ) (hp : p∈Set.Icc 0 1) : FiniteLaw (Fin (N+1)) where
  mass l:=binomialMass n p l.val
  nonneg l:=binomialMass_nonneg n l.val hp
  total:=sum_binomialMass_cutoff hn p

abbrev BoundedMarks (N : ℕ) := Σl : Fin (N+1),Fin l.val→PrimitiveMark

def boundedConditionalPrimitiveLaw {n N : ℕ} {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) (l : Fin (N+1)) : FiniteLaw (Fin l.val→PrimitiveMark) :=
  if h : l.val≤n then conditionalPrimitiveLaw h q hq θ else (primitiveMarkLaw q hq false).product l.val

theorem primitiveRetention_mem {q : ℝ} (hq : q∈Set.Ioo 0 1) :
    1-primitiveErasure q∈Set.Icc 0 1 := by
  constructor
  · exact (primitive_retain_pos hq).le
  · unfold primitiveErasure; nlinarith [sq_nonneg q]

def countedPrimitiveLaw {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) : FiniteLaw (BoundedMarks N) :=
  (boundedCountLaw hn (1-primitiveErasure q) (primitiveRetention_mem hq)).sigma
    (boundedConditionalPrimitiveLaw hq θ)

def decodeBoundedMarks {N : ℕ} (a : BoundedMarks N) : List Bool := joinPrimitiveMarks (List.ofFn a.2)

theorem countedPrimitiveLaw_expect {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) (F : List PrimitiveMark→ℝ) :
    (countedPrimitiveLaw hn hq θ).expect (fun a => F (List.ofFn a.2))=
      silentMarkExpectation q (List.ofFn θ) F := by
  rw [countedPrimitiveLaw,FiniteLaw.expect_sigma,silentMarkExpectation_count_mixture q hq θ F]
  change (∑l : Fin (N+1),binomialMass n (1-primitiveErasure q) l.val*
    (boundedConditionalPrimitiveLaw hq θ l).expect (fun x => F (List.ofFn x)))=_
  let f : ℕ→ℝ := fun l => if hl:l≤n then binomialMass n (1-primitiveErasure q) l*
    (conditionalPrimitiveLaw hl q hq θ).expect (fun x => F (List.ofFn x)) else 0
  have hleft : (∑l : Fin (N+1),binomialMass n (1-primitiveErasure q) l.val*
    (boundedConditionalPrimitiveLaw hq θ l).expect (fun x => F (List.ofFn x)))=
      ∑l : Fin (N+1),f l.val := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl:l.val≤n
    · simp only [boundedConditionalPrimitiveLaw,hl,dite_eq_left,f]
    · simp [boundedConditionalPrimitiveLaw,hl,f,binomialMass,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hl)]
  rw [hleft,Fin.sum_univ_eq_sum_range f (N+1)]
  have he : (∑l∈Finset.range (n+1),f l)=∑l∈Finset.range (N+1),f l := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l _ hl
    simp only [Finset.mem_range] at hl
    simp [f,show ¬l≤n by omega]
  rw [←he,←Fin.sum_univ_eq_sum_range f (n+1)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [f,dite_eq_left (Nat.le_of_lt_succ l.isLt)]

theorem countedPrimitiveLaw_simulates {n N : ℕ} (hn : n≤N) {q : ℝ} (hq : q∈Set.Ioo 0 1)
    (θ : Fin n→Bool) :
    SimulatesTrace q (countedPrimitiveLaw hn hq θ) decodeBoundedMarks
      (((List.ofFn θ).map primitiveBlock).flatten) := by
  intro F
  rw [primitive_run_simulation hq]
  exact countedPrimitiveLaw_expect hn hq θ (fun a => F (joinPrimitiveMarks a))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

theorem subsetLaw_expect_card (p : ℝ) (hp : p∈Set.Icc 0 1) (f : ℕ→ℝ) :
    (subsetLaw (α:=α) p hp).expect (fun S => f S.card)=
      ∑k∈Finset.range (Fintype.card α+1),binomialMass (Fintype.card α) p k*f k := by
  change (∑S : Finset α,p^S.card*(1-p)^(Fintype.card α-S.card)*f S.card)=_
  rw [sum_finset_card (α:=α) (fun k => p^k*(1-p)^(Fintype.card α-k)*f k),
    Fin.sum_univ_eq_sum_range (fun k => ((Fintype.card α).choose k:ℝ)*(p^k*(1-p)^(Fintype.card α-k)*f k))]
  apply Finset.sum_congr rfl
  intro k _
  unfold binomialMass
  ring

theorem subsetLaw_variance (p : ℝ) (hp : p∈Set.Icc 0 1) :
    (subsetLaw (α:=α) p hp).expect (fun S => ((S.card:ℝ)-Fintype.card α*p)^2)=
      (Fintype.card α:ℝ)*p*(1-p) := by
  rw [subsetLaw_expect_card p hp (fun k => ((k:ℝ)-Fintype.card α*p)^2)]
  exact binomialMass_variance _ p

def hiddenScheduleLaw (p : ℝ) (hp : p∈Set.Icc 0 1) (m : ℕ) (hm : m≤Fintype.card α) :
    FiniteLaw (Finset α×Finset α) :=
  (subsetLaw p hp).bind (fun H => (eraseScheduleLaw H m hm).map (fun S => (H,S)))

theorem hiddenScheduleLaw_tv (p : ℝ) (hp : p∈Set.Icc 0 1) (m m' : ℕ)
    (hm : m≤Fintype.card α) (hm' : m'≤Fintype.card α) :
    (hiddenScheduleLaw p hp m hm).tv (hiddenScheduleLaw p hp m' hm') ≤
      (subsetLaw (α:=α) p hp).expect (fun H =>
        (eraseScheduleLaw H m hm).tv (eraseScheduleLaw H m' hm')) := by
  unfold hiddenScheduleLaw
  refine (FiniteLaw.tv_bind_kernel_le _ _ _).trans ?_
  apply FiniteLaw.expect_mono
  intro H
  exact FiniteLaw.tv_map_le _ _ _

theorem good_hiddenSchedule_bound {G P : ℕ} {p : ℝ}
    (hG : 8≤G) (hP : 4*P≤G) (hp : p∈Set.Ioc 0 (1/8))
    (H : Finset (Fin (2*G)))
    (hlo : p*(2*G:ℝ)/2≤H.card) (hhi : (H.card:ℝ)≤2*p*(2*G:ℝ)) :
    (eraseScheduleLaw H G (by simp only [Fintype.card_fin]; omega)).tv
      (eraseScheduleLaw H (G+P) (by simp only [Fintype.card_fin]; omega))≤
      (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2) := by
  have hgr : (0:ℝ)<G := by exact_mod_cast (show 0<G by omega)
  have hhr : (H.card:ℝ)≤(G:ℝ)/2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 hgr.le]
  have hh : 2*H.card≤G := by exact_mod_cast (show 2*(H.card:ℝ)≤G by linarith)
  have h:=eraseScheduleLaw_steps H G P (by simp only [Fintype.card_fin]; omega)
    (by omega) (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  apply h.trans
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.sqrt_pos.2 (by positivity [hp.1]))
    (Real.sqrt_le_sqrt (by linarith))

theorem bad_hiddenSchedule_variance {μ x : ℝ} (hμ : 0<μ)
    (hbad : ¬(μ/2≤x ∧ x≤2*μ)) :
    1≤4*(x-μ)^2/μ^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hμ)]
  push Not at hbad
  by_cases h : μ/2≤x
  · have hx:=hbad h
    nlinarith [sq_nonneg (x-2*μ)]
  · have hx : x<μ/2 := lt_of_not_ge h
    nlinarith [sq_nonneg (x-μ/2)]

theorem hiddenScheduleLaw_steps {G P : ℕ} {p : ℝ}
    (hG : 8≤G) (hP : 4*P≤G) (hp : p∈Set.Ioc 0 (1/8)) :
    (hiddenScheduleLaw (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩ G
      (by simp only [Fintype.card_fin]; omega)).tv
      (hiddenScheduleLaw p ⟨hp.1.le,by linarith [hp.2]⟩ (G+P)
        (by simp only [Fintype.card_fin]; omega))≤
      (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ)) := by
  let μ : ℝ := p*(2*G:ℝ)
  have hgr : (0:ℝ)<G := by exact_mod_cast (show 0<G by omega)
  have hμ : 0<μ := by dsimp [μ]; positivity [hp.1]
  have hμ0 : μ≠0 := ne_of_gt hμ
  let E : ℝ := (P:ℝ)*64/Real.sqrt (μ/2)
  have hE : 0≤E := by dsimp [E]; positivity
  apply (hiddenScheduleLaw_tv p ⟨hp.1.le,by linarith [hp.2]⟩ G (G+P) _ _).trans
  have he := (subsetLaw (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩).expect_mono
    (g:=fun H => E+4*((H.card:ℝ)-μ)^2/μ^2) (fun H => by
      by_cases hg : μ/2≤(H.card:ℝ) ∧ (H.card:ℝ)≤2*μ
      · exact (good_hiddenSchedule_bound hG hP hp H hg.1 (by simpa only [μ,mul_assoc] using hg.2)).trans
          (le_add_of_nonneg_right (by positivity))
      · exact (FiniteLaw.tv_le_one _ _).trans
          ((bad_hiddenSchedule_variance hμ hg).trans (by linarith)))
  apply he.trans
  have hv:=subsetLaw_variance (α:=Fin (2*G)) p ⟨hp.1.le,by linarith [hp.2]⟩
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hv
  change (∑H,(subsetLaw p _).mass H*(E+4*((H.card:ℝ)-μ)^2/μ^2))≤E+4/μ
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul,FiniteLaw.total,one_mul]
  have heq : (∑H : Finset (Fin (2*G)),(subsetLaw p ⟨hp.1.le,by linarith [hp.2]⟩).mass H*(4*((H.card:ℝ)-μ)^2/μ^2))=
      4/μ^2*(2*(G:ℝ)*p*(1-p)) := by
    rw [←hv,FiniteLaw.expect,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H _
    dsimp [μ]
    ring
  rw [heq]
  have heq' : 4/μ^2*(2*(G:ℝ)*p*(1-p))=4/μ*(1-p) := by
    have h : 2*(G:ℝ)*p=μ := by dsimp [μ]; ring
    rw [h]
    field_simp
  rw [heq']
  have h:=mul_le_mul_of_nonneg_left (show 1-p≤1 by linarith [hp.1]) (show 0≤4/μ by positivity)
  linarith

end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_comm (P : FiniteLaw α) (Q : FiniteLaw β) (F : α→β→ℝ) :
    P.expect (fun a => Q.expect (F a))=Q.expect (fun b => P.expect (fun a => F a b)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bind_map (P : FiniteLaw α) (f : α→β) (K : β→FiniteLaw γ) :
    (P.map f).bind K=P.bind (K∘f) := by
  apply ext_expect
  intro F
  rw [expect_bind,expect_map,expect_bind]
  rfl

theorem map_bind (P : FiniteLaw α) (K : α→FiniteLaw β) (f : β→γ) :
    (P.bind K).map f=P.bind (fun a => (K a).map f) := by
  apply ext_expect
  intro F
  simp only [expect_bind,expect_map]

theorem bind_comm (P : FiniteLaw α) (Q : FiniteLaw β) (K : α→β→FiniteLaw γ) :
    P.bind (fun a => Q.bind (K a))=Q.bind (fun b => P.bind (fun a => K a b)) := by
  apply ext_expect
  intro F
  simp only [expect_bind]
  exact expect_comm P Q (fun a b => (K a b).expect F)

end FiniteLaw
variable {α : Type*} [Fintype α]

theorem subsetWeight_mask {n : ℕ} (p : ℝ) (a : Mask n) :
    subsetWeight p (maskSubset a)=maskWeight (1-p) a := by
  rw [maskWeight_card]
  simp only [subsetWeight,Fintype.card_fin,sub_sub_cancel]

theorem coordinateProduct_common_flags {n : ℕ} (p : ℝ) (hp : p∈Set.Icc 0 1)
    (U : FiniteLaw α) (R P : Fin n→FiniteLaw α)
    (hP : ∀ i x,(P i).mass x=p*U.mass x+(1-p)*(R i).mass x) :
    (subsetLaw p hp).bind (fun H : Finset (Fin n) =>
      FiniteLaw.coordinateProduct (fun i => if i∈H then U else R i))=
      FiniteLaw.coordinateProduct P := by
  apply FiniteLaw.ext
  funext x
  change (∑H : Finset (Fin n),subsetWeight p H*(∏i,(if i∈H then U else R i).mass (x i)))=
    ∏i,(P i).mass (x i)
  rw [←(maskSubsetEquiv n).sum_comp]
  change (∑a : Mask n,subsetWeight p (maskSubset a)*(∏i,(if i∈maskSubset a then U else R i).mass (x i)))=_
  simp_rw [subsetWeight_mask,maskWeight,←Finset.prod_mul_distrib]
  have he (a : Mask n) (i : Fin n) :
      (if a i then 1-(1-p) else 1-p)*(if i∈maskSubset a then U else R i).mass (x i)=
      if a i then p*U.mass (x i) else (1-p)*(R i).mass (x i) := by
    cases ha : a i <;> simp [maskSubset,ha]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p*U.mass (x i) else (1-p)*(R i).mass (x i))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false]
  rw [hP]

end TraceReconstruction

namespace TraceReconstruction
open scoped Classical
variable {α : Type*} [Fintype α]

def schedulePayload {n : ℕ} (U P Q : FiniteLaw α) (z : Finset (Fin n)×Finset (Fin n)) :
    FiniteLaw (Fin n→α) :=
  FiniteLaw.coordinateProduct (fun i => if i∈z.1 then U else if i∈z.2 then Q else P)

def uniformSchedulePayload {n : ℕ} (P Q : FiniteLaw α) (m : ℕ) (hm : m≤n) :
    FiniteLaw (Fin n→α) :=
  (uniformSubsetLaw (α:=Fin n) m (by simpa using hm)).bind
    (fun S => FiniteLaw.coordinateProduct (fun i => if i∈S.val then Q else P))

theorem hiddenSchedule_payload_exact {n : ℕ} (p : ℝ) (hp : p∈Set.Icc 0 1)
    (U P' Q' P Q : FiniteLaw α)
    (hP : ∀ x,P.mass x=p*U.mass x+(1-p)*P'.mass x)
    (hQ : ∀ x,Q.mass x=p*U.mass x+(1-p)*Q'.mass x)
    (m : ℕ) (hm : m≤n) :
    (hiddenScheduleLaw (α:=Fin n) p hp m (by simpa using hm)).bind (schedulePayload U P' Q')=
      uniformSchedulePayload P Q m hm := by
  unfold hiddenScheduleLaw eraseScheduleLaw
  rw [FiniteLaw.bind_assoc]
  simp_rw [FiniteLaw.bind_map]
  rw [FiniteLaw.bind_comm]
  unfold uniformSchedulePayload
  congr 1
  funext S
  trans (subsetLaw p hp).bind (fun H : Finset (Fin n) =>
    FiniteLaw.coordinateProduct (fun i => if i∈H then U else if i∈S.val then Q' else P'))
  · congr 1
    funext H
    dsimp only [Function.comp_def,schedulePayload]
    congr 1
    funext i
    by_cases h : i∈H <;> by_cases h' : i∈S.val <;> simp [h,h']
  apply coordinateProduct_common_flags
  intro i x
  by_cases h : i∈S.val
  · simpa [h] using hQ x
  · simpa [h] using hP x

theorem uniformSchedulePayload_steps {G R : ℕ} {p : ℝ}
    (hG : 8≤G) (hR : 4*R≤G) (hp : p∈Set.Ioc 0 (1/8))
    (P Q : FiniteLaw α) (hov : p≤FiniteLaw.overlap P Q) :
    (uniformSchedulePayload (n:=2*G) P Q G (by omega)).tv
      (uniformSchedulePayload P Q (G+R) (by omega))≤
      (R:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ)) := by
  have hp1 : p∈Set.Ioo 0 1 := ⟨hp.1,by linarith [hp.2]⟩
  obtain ⟨U,P',Q',hP,hQ⟩:=FiniteLaw.common_part_decomposition P Q hp1 hov
  rw [←hiddenSchedule_payload_exact p ⟨hp.1.le,hp1.2.le⟩ U P' Q' P Q hP hQ,
    ←hiddenSchedule_payload_exact p ⟨hp.1.le,hp1.2.le⟩ U P' Q' P Q hP hQ]
  exact (FiniteLaw.tv_bind_le _ _ _).trans (hiddenScheduleLaw_steps hG hR hp)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

def coordinateWord {n : ℕ} (w : Fin n→List Bool) : List Bool := (List.ofFn w).flatten

theorem coordinateWord_succ {n : ℕ} (w : Fin (n+1)→List Bool) :
    coordinateWord w=w 0++coordinateWord (fun i => w i.succ) := by
  simp only [coordinateWord,List.ofFn_succ,List.flatten_cons]

theorem coordinateWord_cons {n : ℕ} (w : List Bool) (v : Fin n→List Bool) :
    coordinateWord (Fin.cons w v)=w++coordinateWord v := by
  rw [coordinateWord_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

theorem coordinateProduct_simulates {α : Type*} [Fintype α]
    {n : ℕ} {q : ℝ} (P : Fin n→FiniteLaw α) (f : α→List Bool) (w : Fin n→List Bool)
    (h : ∀i,SimulatesTrace q (P i) f (w i)) :
    SimulatesTrace q (FiniteLaw.coordinateProduct P) (fun a => coordinateWord (fun i => f (a i)))
      (coordinateWord w) := by
  induction n with
  | zero =>
    intro F
    change (FiniteLaw.coordinateProduct P).expect (fun _ => F [])=F []
    exact FiniteLaw.expect_const _ _
  | succ n ih =>
    intro F
    rw [FiniteLaw.expect_coordinateProduct_succ,coordinateWord_succ,listDeletionExpectation_append]
    have hj (a : α) (x : Fin n→α) :
        coordinateWord (fun i => f ((Fin.cons a x : Fin (n+1)→α) i))=f a++coordinateWord (fun i => f (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [hj]
    have ht:=ih (fun i => P i.succ) (fun i => w i.succ) (fun i => h i.succ)
    calc
      _=(P 0).expect (fun a => listDeletionExpectation q (coordinateWord (fun i => w i.succ))
          (fun t => F (f a++t))) := by
        congr 1
        funext a
        exact ht (fun t => F (f a++t))
      _=_ := h 0 (fun t => listDeletionExpectation q (coordinateWord (fun i => w i.succ)) (fun u => F (t++u)))

theorem sum_subset_choices {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (∑i : Fin n,if i∈S then k+1 else k)=n*k+S.card := by
  have he (i : Fin n) : (if i∈S then k+1 else k)=k+(if i∈S then 1 else 0) := by
    split_ifs <;> omega
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_id]

theorem coordinateWord_pureAtomRun {n : ℕ} (w : List Bool) (k : Fin n→ℕ) :
    coordinateWord (fun i => pureAtomRun w (k i))=pureAtomRun w (∑i,k i) := by
  change (List.ofFn (pureAtomRun w ∘ k)).flatten=_
  rw [←List.map_ofFn,pureAtomRun_partition,List.sum_ofFn]

theorem uniform_schedule_word {n m : ℕ} (S : FixedSubset (Fin n) m) (w : List Bool) (k : ℕ) :
    coordinateWord (fun i => if i∈S.val then pureAtomRun w (k+1) else pureAtomRun w k)=
      pureAtomRun w (n*k+m) := by
  have he (i : Fin n) : (if i∈S.val then pureAtomRun w (k+1) else pureAtomRun w k)=
      pureAtomRun w (if i∈S.val then k+1 else k) := by split_ifs <;> rfl
  simp_rw [he]
  rw [coordinateWord_pureAtomRun,sum_subset_choices,S.property]

end TraceReconstruction
noncomputable section
namespace TraceReconstruction

theorem lifting_count_scale {F k P : ℕ} {C p : ℝ}
    (hk : 1≤k) (hP : 1≤P) (hp : p∈Set.Ioc 0 (1/8))
    (hC : 1073741824≤p*C) (hF : C*k*P≤F) :
    (1048576:ℝ)*(P:ℝ)^2≤p*((F*P/(2*k+1):ℕ):ℝ) := by
  let G := F*P/(2*k+1)
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hGr : (0:ℝ)≤G := Nat.cast_nonneg G
  have hnat:=Nat.lt_mul_div_succ (F*P) (show 0<2*k+1 by omega)
  have hupper : (F:ℝ)*P<(2*(k:ℝ)+1)*((G:ℝ)+1) := by exact_mod_cast hnat
  have hF' := mul_le_mul_of_nonneg_right hF (show (0:ℝ)≤P by positivity)
  have hupper' := mul_lt_mul_of_pos_left hupper hp.1
  have hlower:=mul_le_mul_of_nonneg_left hF' hp.1.le
  have hC' := mul_le_mul_of_nonneg_right hC (show (0:ℝ)≤(k:ℝ)*(P:ℝ)^2 by positivity)
  have hden : (2*(k:ℝ)+1)*(p*((G:ℝ)+1))≤3*(k:ℝ)*(p*((G:ℝ)+1)) := by
    apply mul_le_mul_of_nonneg_right (by linarith)
    positivity [hp.1.le]
  have hmain : (1073741824:ℝ)*(P:ℝ)^2<3*p*((G:ℝ)+1) := by
    have h : (k:ℝ)*(1073741824*(P:ℝ)^2)<(k:ℝ)*(3*p*((G:ℝ)+1)) := by
      nlinarith only [hlower,hupper',hC',hden]
    exact (mul_lt_mul_iff_of_pos_left (by linarith : (0:ℝ)<k)).mp h
  change (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)
  nlinarith [sq_nonneg ((P:ℝ)-1),hp.2]

theorem lifting_scale_valid {G P : ℕ} {p : ℝ}
    (hP : 1≤P) (hp : p∈Set.Ioc 0 (1/8))
    (hscale : (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)) : 8≤G ∧ 4*P≤G := by
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hmul:=mul_le_mul_of_nonneg_right hp.2 (Nat.cast_nonneg (α:=ℝ) G)
  have hG : (8:ℝ)≤G := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  have h4 : 4*(P:ℝ)≤G := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  constructor
  · exact_mod_cast hG
  · exact_mod_cast h4

theorem lifting_numeric_bound {G P : ℕ} {p : ℝ}
    (hP : 1≤P) (_hp : p∈Set.Ioc 0 (1/8))
    (hscale : (1048576:ℝ)*(P:ℝ)^2≤p*(G:ℝ)) :
    (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)+4/(p*(2*G:ℝ))≤1/3 := by
  have hPr : (1:ℝ)≤P := by exact_mod_cast hP
  have hs : 0<p*(G:ℝ) := by nlinarith [sq_nonneg ((P:ℝ)-1)]
  have hre : p*(2*G:ℝ)/2=p*G := by ring
  have hden : (0:ℝ)<p*(2*G:ℝ) := by nlinarith
  have hsq : 1024*(P:ℝ)≤Real.sqrt (p*(G:ℝ)) := by
    apply (Real.le_sqrt (by positivity) (le_of_lt hs)).2
    nlinarith only [hscale]
  have hspos:=Real.sqrt_pos.2 hs
  have hfirst : (P:ℝ)*64/Real.sqrt (p*(2*G:ℝ)/2)≤1/16 := by
    rw [hre,div_le_iff₀ hspos]
    nlinarith only [hsq]
  have hsecond : 4/(p*(2*G:ℝ))≤1/16 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg ((P:ℝ)-1)]
  linarith

end TraceReconstruction
universe u
namespace TraceReconstruction
open scoped Classical
variable {α : Type u} [Fintype α]

theorem maskLaw_simulates {q : ℝ} (hq : q∈Set.Icc 0 1) (w : List Bool) :
    SimulatesTrace q (maskLaw q hq) (traceOfMask w.get) w := by
  intro F
  have h:=listDeletionExpectation_ofFn q w.get F
  rw [List.ofFn_get] at h
  exact h.symm

theorem uniformSchedulePayload_simulates {n m k : ℕ} {q : ℝ} (hm : m≤n)
    (P Q : FiniteLaw α) (f : α→List Bool) (w : List Bool)
    (hP : SimulatesTrace q P f (pureAtomRun w k))
    (hQ : SimulatesTrace q Q f (pureAtomRun w (k+1))) :
    SimulatesTrace q (uniformSchedulePayload P Q m hm)
      (fun a => coordinateWord (fun i => f (a i))) (pureAtomRun w (n*k+m)) := by
  apply SimulatesTrace.random_partition
  intro S
  rw [←uniform_schedule_word S w k]
  apply coordinateProduct_simulates
  intro i
  by_cases h : i∈S.val
  · simpa only [h,ite_true] using hQ
  · simpa only [h,ite_false] using hP

/-- Explicit source common-part lifting, using finite auxiliary observations
that decode exactly to ordinary complete traces of the adjacent pure powers. -/
theorem adjacent_power_lift {F k R : ℕ} {C p q : ℝ}
    (hk : 1≤k) (hR : 1≤R) (hp : p∈Set.Ioc 0 (1/8)) (hq : q∈Set.Icc 0 1)
    (hC : 1073741824≤p*C) (hF : C*k*R≤F)
    (P Q : FiniteLaw α) (f : α→List Bool) (w : List Bool)
    (hP : SimulatesTrace q P f (pureAtomRun w k))
    (hQ : SimulatesTrace q Q f (pureAtomRun w (k+1)))
    (hov : p≤FiniteLaw.overlap P Q) :
    ∃ (β : Type u) (_ : Fintype β) (P' Q' : FiniteLaw β) (g : β→List Bool),
      SimulatesTrace q P' g (pureAtomRun w (F*R)) ∧
      SimulatesTrace q Q' g (pureAtomRun w (F*R+R)) ∧
      (2/3:ℝ)≤FiniteLaw.overlap P' Q' := by
  let G := F*R/(2*k+1)
  have hs : (1048576:ℝ)*(R:ℝ)^2≤p*(G:ℝ) := lifting_count_scale hk hR hp hC hF
  obtain ⟨hG,hr⟩:=lifting_scale_valid hR hp hs
  let A:=uniformSchedulePayload (n:=2*G) P Q G (by omega)
  let B:=uniformSchedulePayload (n:=2*G) P Q (G+R) (by omega)
  have htv : A.tv B≤1/3 :=
    (uniformSchedulePayload_steps hG hr hp P Q hov).trans (lifting_numeric_bound hR hp hs)
  let tail:=pureAtomRun w (F*R-G*(2*k+1))
  let S:=maskLaw (n:=tail.length) q hq
  let g : (Fin (2*G)→α)×Mask tail.length→List Bool :=
    fun a => coordinateWord (fun i => f (a.1 i))++traceOfMask tail.get a.2
  refine ⟨(Fin (2*G)→α)×Mask tail.length,inferInstance,A.prod S,B.prod S,g,?_,?_,?_⟩
  · have ha:=uniformSchedulePayload_simulates (n:=2*G) (by omega : G≤2*G) P Q f w hP hQ
    have ht:=(ha.append (maskLaw_simulates hq tail))
    have hh : G*(2*k+1)≤F*R := Nat.div_mul_le_self _ _
    have he : 2*G*k+G+(F*R-G*(2*k+1))=F*R := by
      have he0 : G*(2*k+1)=2*G*k+G := by ring
      omega
    simpa only [tail,←pureAtomRun_add,he] using ht
  · have hb:=uniformSchedulePayload_simulates (n:=2*G) (by omega : G+R≤2*G) P Q f w hP hQ
    have ht:=(hb.append (maskLaw_simulates hq tail))
    have hh : G*(2*k+1)≤F*R := Nat.div_mul_le_self _ _
    have he : 2*G*k+(G+R)+(F*R-G*(2*k+1))=F*R+R := by
      have he0 : G*(2*k+1)=2*G*k+G := by ring
      omega
    simpa only [tail,←pureAtomRun_add,he] using ht
  · rw [FiniteLaw.overlap_eq_one_sub_tv,FiniteLaw.tv_prod_eq_left]
    linarith

end TraceReconstruction



/-!
Concrete objects for the scale inequalities, Definition 3 (the level invariant).
The observable channel remains the complete deletion trace of a literal word.
-/
noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

/-- The maximizing test for total variation on a finite sample space. -/
theorem tv_eq_positive_test (P Q : FiniteLaw α) :
    P.tv Q = P.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0) -
      Q.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0) := by
  have hz : (∑ a, (P.mass a - Q.mass a)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]
  have he (a : α) :
      |P.mass a-Q.mass a|+(P.mass a-Q.mass a) =
        2*((P.mass a-Q.mass a)*(if Q.mass a ≤ P.mass a then 1 else 0)) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  have hs := congrArg (fun f : α → ℝ => ∑ a, f a) (funext he)
  simp only [Finset.sum_add_distrib, hz, add_zero, ← Finset.mul_sum] at hs
  simp only [tv, expect]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  linarith only [hs]

/-- Dual characterization, sufficient for simulators with different latent spaces. -/
theorem tv_le_of_tests (P Q : FiniteLaw α) {E : ℝ}
    (h : ∀ f : α → ℝ, (∀ a, f a ∈ Set.Icc 0 1) →
      P.expect f-Q.expect f ≤ E) : P.tv Q ≤ E := by
  rw [tv_eq_positive_test]
  exact h _ (fun a => by split_ifs <;> norm_num)

theorem abs_expect_sub_le_tv (P Q : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ a, f a ∈ Set.Icc 0 1) : |P.expect f-Q.expect f| ≤ P.tv Q := by
  apply abs_le.mpr
  constructor
  · have h := expectation_diff_le_tv Q P f hf
    rw [tv_symm Q P] at h
    change Q.expect f-P.expect f ≤ P.tv Q at h
    linarith
  · exact expectation_diff_le_tv P Q f hf
end FiniteLaw

/-- The genuine complete-trace law embedded in a specified finite trace space.
The extra elements have mass zero, not a cemetery mass. -/
def listTraceLaw (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) : FiniteLaw (BoundedTrace M) :=
  (maskLaw (n:=w.length) q hq).map (fun a =>
    ⟨traceOfMask w.get a, mem_traceSpace_of_length_le _
      ((traceOfMask_length_le w.get a).trans hw)⟩)

theorem listTraceLaw_expect (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) (F : List Bool → ℝ) :
    (listTraceLaw q hq w M hw).expect (fun a => F a.val) =
      listDeletionExpectation q w F := by
  rw [listTraceLaw, FiniteLaw.expect_map]
  have h := listDeletionExpectation_ofFn q w.get F
  rw [List.ofFn_get] at h
  exact h.symm

theorem listTraceLaw_simulates (q : ℝ) (hq : q ∈ Set.Icc 0 1) (w : List Bool)
    (M : ℕ) (hw : w.length ≤ M) :
    SimulatesTrace q (listTraceLaw q hq w M hw) Subtype.val w :=
  listTraceLaw_expect q hq w M hw

/-- Ordinary overlap of complete traces, including unequal input lengths. -/
def listTraceOverlap (q : ℝ) (hq : q ∈ Set.Icc 0 1) (x y : List Bool) : ℝ :=
  let M := max x.length y.length
  FiniteLaw.overlap (listTraceLaw q hq x M (le_max_left _ _))
    (listTraceLaw q hq y M (le_max_right _ _))

/-- Common approximate simulation transfers distinguishability to genuine
complete traces, without revealing the latent partition. -/
theorem approximations_trace_tv {α : Type*} [Fintype α]
    {q : ℝ} (hq : q ∈ Set.Icc 0 1) (P Q : FiniteLaw α) (decode : α → List Bool)
    (x y : List Bool) (Ex Ey : ℝ) (M : ℕ) (hx : x.length ≤ M) (hy : y.length ≤ M)
    (hP : ApproximatesTrace q P decode x Ex)
    (hQ : ApproximatesTrace q Q decode y Ey) :
    (listTraceLaw q hq x M hx).tv (listTraceLaw q hq y M hy) ≤ P.tv Q+Ex+Ey := by
  apply FiniteLaw.tv_le_of_tests
  intro f hf
  let F : List Bool → ℝ := fun t => if h : t ∈ traceSpace M then f ⟨t,h⟩ else 0
  have hF : ∀ t, F t ∈ Set.Icc 0 1 := by
    intro t
    dsimp [F]
    split_ifs with h
    · exact hf ⟨t,h⟩
    · norm_num
  have hFx : (listTraceLaw q hq x M hx).expect f = listDeletionExpectation q x F := by
    rw [← listTraceLaw_expect q hq x M hx F]
    congr 1
    funext t
    simp only [F, dite_eq_left t.property]
  have hFy : (listTraceLaw q hq y M hy).expect f = listDeletionExpectation q y F := by
    rw [← listTraceLaw_expect q hq y M hy F]
    congr 1
    funext t
    simp only [F, dite_eq_left t.property]
  rw [hFx,hFy]
  have hp := hP F hF
  have hq' := hQ F hF
  have ht := FiniteLaw.abs_expect_sub_le_tv P Q (fun a => F (decode a)) (fun a => hF _)
  linarith [le_abs_self (P.expect (fun a => F (decode a))-Q.expect (fun a => F (decode a))),
    (abs_le.mp hp).1, (abs_le.mp hp).2, (abs_le.mp hq').1, (abs_le.mp hq').2]

/-- A literal witness of the source level invariant. `halfOrder` is half its
positive even moment order. `countFactor` is the prescribed upper multiplier
`C^(2*B*i+O_B(1))`, to be instantiated uniformly in the actual construction.
Finite outcomes suffice for the source's finite latent experiments, and any
randomized common decoder can be included as an additional latent draw. -/
structure ConcreteLevelPair (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (N Δ d ω countFactor : ℝ) (i halfOrder : ℕ) where
  left : List Bool
  right : List Bool
  equalLength : left.length = right.length
  different : left ≠ right
  length_lower : N/2 ≤ (left.length : ℝ)
  length_upper : (left.length : ℝ) ≤ N
  Outcome : Type
  finiteOutcome : Fintype Outcome
  firstLaw : @FiniteLaw Outcome finiteOutcome
  secondLaw : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  error : ℝ
  error_nonneg : 0 ≤ error
  normalized_error : error/(left.length : ℝ) ≤ ((i:ℝ)+1)*Δ
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q firstLaw decode left error
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q secondLaw decode right error
  score : Outcome → ℝ
  density : ∀ a, secondLaw.mass a = firstLaw.mass a*(1+score a)
  score_bound : @FiniteLaw.evenMomentSq Outcome finiteOutcome firstLaw score halfOrder ≤ N ^ (-d)
  overlapCount : ℕ
  overlapCount_lower : left.length ≤ overlapCount
  overlapCount_upper : (overlapCount:ℝ) ≤ countFactor*(left.length:ℝ)
  power_overlap : ω ≤ listTraceOverlap q hq (pureAtomRun left overlapCount)
    (pureAtomRun left (overlapCount+1))

end TraceReconstruction



/-! The actual finite paired-flag experiment.  We separate its unconditional
orientation-first generation (used for trace simulation) from its exact
metadata-first Bayes factorization (used for the density estimates).
Neither construction conditions on successful window layout. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A joint law retaining both the latent variable and its conditional draw. -/
def joint (P : FiniteLaw α) (K : α → FiniteLaw β) : FiniteLaw (α × β) where
  mass z := P.mass z.1 * (K z.1).mass z.2
  nonneg z := mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

theorem expect_joint (P : FiniteLaw α) (K : α → FiniteLaw β) (F : α × β → ℝ) :
    (P.joint K).expect F = P.expect (fun a => (K a).expect (fun b => F (a,b))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_mixture (P : FiniteLaw α) (K : α → FiniteLaw β) (F : β → ℝ) :
    (P.mixture K).expect F = P.expect (fun a => (K a).expect F) := by
  simp only [expect, mixture, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem mixture_eq_bind (P : FiniteLaw α) (K : α → FiniteLaw β) :
    P.mixture K = P.bind K := rfl

/-- Independent maps commute with the literal finite product law. -/
theorem coordinateProduct_map {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → β) :
    (coordinateProduct P).map (fun a i => f i (a i)) =
      coordinateProduct (fun i => (P i).map (f i)) := by
  apply FiniteLaw.ext
  funext b
  rw [map_mass]
  change (∑ a : Fin n → α, if (fun i => f i (a i)) = b then ∏ i, (P i).mass (a i) else 0) =
    ∏ i, ((P i).map (f i)).mass (b i)
  simp_rw [map_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : (fun i => f i (a i)) = b
  · rw [ite_eq_left hab]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun hab i)]
  · rw [ite_eq_right hab]
    symm
    have hi : ∃ i, f i (a i) ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Forgetting the report recovers the two independent side emissions. -/
theorem pairedFlagLaw_map (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a)
    (b : Bool) :
    (pairedFlagLaw P Q H hω hP hQ b).map Prod.snd = orientedProd P Q b := by
  apply FiniteLaw.ext
  funext z
  rw [map_mass, Fintype.sum_prod_type]
  simp only [pairedFlagLaw]
  simp_rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact pairedFlag_simulation P Q H ω b z

end FiniteLaw

variable {Side Leaf : Type*} [Fintype Side] [Fintype Leaf] {m n : ℕ}

/-- Data of the paired mechanisms, with common submass proved for each side.
All words and their actual trace laws will be substituted in these fields. -/
structure PairedMechanisms (Side : Type*) [Fintype Side] (m : ℕ) where
  first : Fin m → FiniteLaw Side
  second : Fin m → FiniteLaw Side
  common : Fin m → FiniteLaw Side
  hiddenWeight : Fin m → ℝ
  weight_nonneg : ∀ i, 0 ≤ hiddenWeight i
  common_first : ∀ i a, hiddenWeight i*(common i).mass a ≤ (first i).mass a
  common_second : ∀ i a, hiddenWeight i*(common i).mass a ≤ (second i).mass a

abbrev Reports (Side : Type*) (m : ℕ) := Fin m → Option Bool × (Side × Side)

namespace PairedMechanisms
variable (M : PairedMechanisms Side m)

def reports : FiniteLaw (Reports Side m) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.pairedReport (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i))

def reportsGiven (b : Fin m → Bool) : FiniteLaw (Reports Side m) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.pairedFlagLaw (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i) (b i))

/-- Bit orientations, prior to generating any emissions. -/
def fairOrientations (m : ℕ) : FiniteLaw (Fin m → Bool) :=
  (FiniteLaw.flagPosterior none).product m

/-- Exact posterior, with zero-mass metadata treated by the same canonical
formula. In particular unseen orientations are independent fair bits. -/
def orientationsGiven (z : Reports Side m) : FiniteLaw (Fin m → Bool) :=
  FiniteLaw.coordinateProduct (fun i => FiniteLaw.flagPosterior (z i).1)

def selectedLeafLaw (P Q : FiniteLaw Leaf) (θ : Fin n → Bool) :
    FiniteLaw (Fin n → Leaf) :=
  FiniteLaw.coordinateProduct (fun i => if θ i then Q else P)

/-- Actual orientation-first, unconditioned augmented observation. -/
def orientationOracle (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    FiniteLaw (Reports Side m × (Fin n → Leaf)) :=
  (fairOrientations m).mixture (fun b => (M.reportsGiven b).prod (selectedLeafLaw P Q (θ b)))

/-- Metadata-first factorization of exactly the same law, not a new oracle. -/
def canonicalOracle (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    FiniteLaw (Reports Side m × (Fin n → Leaf)) :=
  M.reports.joint (fun z => (orientationsGiven z).mixture (fun b => selectedLeafLaw P Q (θ b)))

theorem oracle_factorization (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    M.orientationOracle P Q θ = M.canonicalOracle P Q θ := by
  apply FiniteLaw.ext
  funext zx
  rcases zx with ⟨z,x⟩
  change (∑ b, (∏ i : Fin m, (1/2:ℝ)) *
      ((∏ i, FiniteLaw.pairedFlagMass (M.first i) (M.second i) (M.common i)
        (M.hiddenWeight i) (b i) (z i)) * (selectedLeafLaw P Q (θ b)).mass x)) =
    (∏ i, FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (z i)) *
      (∑ b, (∏ i, (FiniteLaw.flagPosterior (z i).1).mass (b i)) * (selectedLeafLaw P Q (θ b)).mass x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, ← Finset.prod_mul_distrib,
    FiniteLaw.pairedFlags_product_bayes, mul_assoc]

/-- The reference is independent old-first-law emissions, even after reporting
all side traces. This equality is exact for every metadata value. -/
theorem canonicalOracle_density (P Q : FiniteLaw Leaf) (Z : Leaf → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a*(1+Z a))
    (θ : (Fin m → Bool) → Fin n → Bool) (z : Reports Side m) (x : Fin n → Leaf) :
    (M.canonicalOracle P Q θ).mass (z,x) =
      (M.reports.prod (P.product n)).mass (z,x) *
        averagedDensity (orientationsGiven z) θ Z x := by
  change M.reports.mass z *
    ((orientationsGiven z).mixture (fun b => FiniteLaw.coordinateProduct
      (fun i => if θ b i then Q else P))).mass x = _
  rw [leaf_oracle_density P Q Z hZ]
  exact (mul_assoc _ _ _).symm

/-- The full side metadata has a common law for both hypotheses. -/
theorem canonicalOracle_metadata (P Q : FiniteLaw Leaf)
    (θ : (Fin m → Bool) → Fin n → Bool) (F : Reports Side m → ℝ) :
    (M.canonicalOracle P Q θ).expect (fun z => F z.1) = M.reports.expect F := by
  rw [canonicalOracle, FiniteLaw.expect_joint]
  simp only [FiniteLaw.expect_const]

/-- Conditional on every orientation, forgetting flags gives independent side
emissions. This is the unconditional simulation side of the construction. -/
theorem reportsGiven_forget (b : Fin m → Bool) :
    (M.reportsGiven b).map (fun z i => (z i).2) =
      FiniteLaw.coordinateProduct (fun i => FiniteLaw.orientedProd (M.first i) (M.second i) (b i)) := by
  rw [reportsGiven, FiniteLaw.coordinateProduct_map]
  congr 1
  funext i
  exact FiniteLaw.pairedFlagLaw_map _ _ _ _ _ _ _

end PairedMechanisms
end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
