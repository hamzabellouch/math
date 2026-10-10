import OAI.Geometry.UnitDistances.Transfer

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

def dependent (μ : Law X) (ν : X → Law Y) : Law (X×Y) where
  val xy := μ.val xy.1*(ν xy.1).val xy.2
  nonneg xy := mul_nonneg (μ.nonneg _) ((ν _).nonneg _)
  total := by simp [Fintype.sum_prod_type,← mul_sum,Law.total]

def mix (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg _ := avg_nonneg _ (fun x => (ν x).nonneg _)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp [← mul_sum,Law.total]

def tensor (μ : I → Law X) : Law (I → X) where
  val x := ∏ i,(μ i).val (x i)
  nonneg x := prod_nonneg fun i _ => (μ i).nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [Law.total]

lemma dependent_avg (μ : Law X) (ν : X → Law Y) (f : X×Y → ℝ) :
    avg (dependent μ ν) f = avg μ (fun x => avg (ν x) (fun y => f (x,y))) := by
  simp [avg,dependent,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma mix_avg (μ : Law X) (ν : X → Law Y) (f : Y → ℝ) :
    avg (mix μ ν) f = avg μ (fun x => avg (ν x) f) := by
  simp only [avg,mix,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]
lemma tensor_event (μ : I → Law X) (P : I → X → Prop) :
    event (tensor μ) (fun x => ∀i,P i (x i)) = ∏ i,event (μ i) (P i) := by
  classical
  simp only [event_eq_sum,tensor]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : ∀i,P i (x i)
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [h,ite_false]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]
lemma tensor_coordinate (μ : I → Law X) (i : I) (P : X → Prop) :
    event (tensor μ) (fun x => P (x i)) = event (μ i) P := by
  classical
  calc
    _ = event (tensor μ) (fun x => ∀j, j=i → P (x j)) :=
      event_congr _ (fun x => by simp)
    _ = ∏ j,event (μ j) (fun x => j=i → P x) := tensor_event μ (fun j x => j=i → P x)
    _ = event (μ i) P := by
      rw [prod_eq_single i]
      · apply event_congr; simp
      · intro j _ hji
        simp only [hji,false_implies]
        exact event_true _
      · simp
lemma tensor_union_le (μ : I → Law X) (P : I → X → Prop) :
    event (tensor μ) (fun x => ∃i,P i (x i)) ≤ ∑ i,event (μ i) (P i) := by
  have h := event_exists_le (tensor μ) (fun i x => P i (x i))
  simpa only [tensor_coordinate] using h

lemma tensor_dependent (μ : Law X) (ν : X → Law Y) (f : (I → X) → (I → Y) → ℝ) :
    avg (independent (dependent μ ν) I) (fun xy => f (fun i => (xy i).1) (fun i => (xy i).2)) =
    avg (independent μ I) (fun x => avg (tensor (fun i => ν (x i))) (f x)) := by
  classical
  let e : (I → X×Y) ≃ (I → X)×(I → Y) := Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => Y)
  have he : ∀ xy, (independent (dependent μ ν) I).val xy =
      (dependent (independent μ I) (fun x => tensor (fun i => ν (x i)))).val (e xy) := by
    intro xy
    change (∏i,μ.val (xy i).1*(ν (xy i).1).val (xy i).2) =
      (∏i,μ.val (xy i).1)*(∏i,(ν (xy i).1).val (xy i).2)
    exact prod_mul_distrib
  have h := equiv_avg (independent (dependent μ ν) I)
    (dependent (independent μ I) (fun x => tensor (fun i => ν (x i)))) e he
    (fun xy => f xy.1 xy.2)
  rw [dependent_avg] at h
  exact h

lemma independent_push (μ : Law X) (φ : X → Y) (f : (I → Y) → ℝ) :
    avg (independent μ I) (fun x => f (φ ∘ x)) = avg (independent (push μ φ) I) f := by
  classical
  have hw : ∀y : I → Y,(push (independent μ I) (fun x => φ ∘ x)).val y =
      (independent (push μ φ) I).val y := by
    intro y
    change event (independent μ I) (fun x => φ ∘ x=y) = ∏i,event μ (fun x => φ x=y i)
    rw [event_congr _ (fun x => funext_iff)]
    exact independent_event μ (fun i x => φ x=y i)
  calc
    _ = avg (push (independent μ I) (fun x => φ ∘ x)) f :=
      (push_avg _ _ _).symm
    _ = _ := by unfold avg; simp_rw [hw]

lemma law_ext {μ ν : Law X} (h : ∀x,μ.val x=ν.val x) : μ=ν := by
  cases μ with | mk a ha sa =>
    cases ν with | mk b hb sb =>
      have : a=b := funext h
      subst b
      rfl

lemma push_dependent_fst (μ : Law X) (ν : X → Law Y) :
    push (dependent μ ν) Prod.fst=μ := by
  apply law_ext
  intro x
  change event (dependent μ ν) (fun xy => xy.1=x)=μ.val x
  simp only [event_eq_sum,dependent,Fintype.sum_prod_type]
  simp [← mul_sum,Law.total]

lemma push_dependent_snd (μ : Law X) (ν : X → Law Y) :
    push (dependent μ ν) Prod.snd=mix μ ν := by
  apply law_ext
  intro y
  change event (dependent μ ν) (fun xy => xy.2=y)=avg μ (fun x => (ν x).val y)
  simp only [event_eq_sum,dependent,Fintype.sum_prod_type,avg]
  simp

lemma tensor_mixture (μ : Law X) (ν : X → Law Y) (f : (I → Y) → ℝ) :
    avg (independent μ I) (fun x => avg (tensor (fun i => ν (x i))) f) =
      avg (independent (mix μ ν) I) f := by
  rw [← tensor_dependent]
  have h := independent_push (I := I) (dependent μ ν) Prod.snd f
  rw [push_dependent_snd] at h
  exact h
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WedgeLaw
open FiniteLaw FiniteStarCoupling WedgeProfiles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

def law (π : Law (P×Q)) : Law (Q×(P×P)) :=
  dependent (right π) (fun q => pair (col π q) (col π q))

lemma average (π : Law (P×Q)) (f : Q×(P×P) → ℝ) :
    avg (law π) f=avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp => f (q,pp))) :=
  dependent_avg _ _ _

lemma first (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (law π) (fun a => f a.2.1 a.1)=avg π (fun pq => f pq.1 pq.2) := by
  rw [average]
  calc
    _ = avg (right π) (fun q => avg (col π q) (fun p => f p q)) := by
      apply avg_congr
      intro q
      exact FiniteLaw.pair_fst (col π q) (col π q) (fun p => f p q)
    _ = _ := col_avg π f

lemma second (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (law π) (fun a => f a.2.2 a.1)=avg π (fun pq => f pq.1 pq.2) := by
  rw [average]
  calc
    _ = avg (right π) (fun q => avg (col π q) (fun p => f p q)) := by
      apply avg_congr
      intro q
      exact FiniteLaw.pair_snd (col π q) (col π q) (fun p => f p q)
    _ = _ := col_avg π f

lemma first_point (π : Law (P×Q)) (f : P → ℝ) :
    avg (law π) (fun a => f a.2.1)=avg (left π) f := by
  rw [first π (fun p _ => f p)]
  exact (push_avg π Prod.fst f).symm

lemma second_point (π : Law (P×Q)) (f : P → ℝ) :
    avg (law π) (fun a => f a.2.2)=avg (left π) f := by
  rw [second π (fun p _ => f p)]
  exact (push_avg π Prod.fst f).symm

lemma mismatch (π : Law (P×Q)) (b : P → Q → Bool) :
    avg (law π) (fun a => |value (b a.2.1 a.1)-value (b a.2.2 a.1)|)=VQ π b := by
  rw [average]
  apply avg_congr
  intro q
  rw [←StarScore.mismatch]
  apply avg_congr
  intro pp
  cases h₁ : b pp.1 q <;> cases h₂ : b pp.2 q <;> norm_num [value,h₁,h₂]
end
end PlanarUnitDistances.WedgeLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma row_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (left π).val p*(row π p).val q=π.val (p,q) := by
  simp only [row,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.2=q then fiberMass π Prod.fst p*(cond π Prod.fst p).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma row_val (π : Law (P×Q)) {p : P} (hp : 0<(left π).val p) (q : Q) :
    (row π p).val q=π.val (p,q)/(left π).val p := by
  apply (eq_div_iff hp.ne').mpr
  simpa only [mul_comm] using row_weight π p q
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.TemplateCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def joint (π : Law (P×Q)) (a : Q → Law Θ) : Law ((P×Q)×Θ) := dependent π (fun pq => a pq.2)
def templates (π : Law (P×Q)) (a : Q → Law Θ) : Law Θ := push (joint π a) Prod.snd
def slice (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) : Law (P×Q) :=
  push (cond (joint π a) Prod.snd θ) Prod.fst

lemma slice_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (pq : P×Q) :
    (templates π a).val θ*(slice π a θ).val pq=π.val pq*(a pq.2).val θ := by
  exact col_weight (joint π a) pq θ
lemma template_val (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) :
    (templates π a).val θ=avg (right π) (fun q => (a q).val θ) := by
  change (right (joint π a)).val θ=_
  rw [right_val]
  simp only [joint,dependent,Fintype.sum_prod_type,avg,right_val,sum_mul]
  rw [sum_comm]
lemma slice_avg (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → ℝ) :
    avg (templates π a) (fun θ => avg (slice π a θ) (f θ))=
      avg π (fun pq => avg (a pq.2) (fun θ => f θ pq)) := by
  simp only [slice,push_avg]
  change avg (push (joint π a) Prod.snd) _=_
  rw [cond_tower_dep]
  exact dependent_avg π _ _
lemma slice_event (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → Prop) :
    avg (templates π a) (fun θ => event (slice π a θ) (f θ))=
      avg π (fun pq => event (a pq.2) (fun θ => f θ pq)) := by
  unfold event
  exact slice_avg π a _
lemma slice_right_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q) :
    (templates π a).val θ*(right (slice π a θ)).val q = (right π).val q*(a q).val θ := by
  simp only [right_val,mul_sum,sum_mul,slice_weight]

lemma col_eq (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q)
    (ht : 0<(templates π a).val θ) (hq : 0<(right (slice π a θ)).val q) :
    col (slice π a θ) q=col π q := by
  have he := slice_right_weight π a θ q
  apply law_ext
  intro p
  apply (mul_right_inj' (mul_ne_zero ht.ne' hq.ne')).mp
  calc
    _ = (templates π a).val θ*(slice π a θ).val (p,q) := by rw [mul_assoc,col_weight]
    _ = π.val (p,q)*(a q).val θ := slice_weight π a θ (p,q)
    _ = ((templates π a).val θ*(right (slice π a θ)).val q)*(col π q).val p := by
      rw [he]
      calc
        _ = ((right π).val q*(col π q).val p)*(a q).val θ := by rw [col_weight]
        _ = _ := by ring

lemma center_statistic (π : Law (P×Q)) (a : Q → Law Θ) (F : Q → Law P → ℝ) :
    avg (templates π a) (fun θ => avg (right (slice π a θ)) (fun q => F q (col (slice π a θ) q)))=
      avg (right π) (fun q => F q (col π q)) := by
  have he (θ : Θ) (q : Q) :
      (templates π a).val θ*((right (slice π a θ)).val q*F q (col (slice π a θ) q))=
        (right π).val q*(a q).val θ*F q (col π q) := by
    rw [← mul_assoc]
    by_cases ht : 0<(templates π a).val θ
    · by_cases hq : 0<(right (slice π a θ)).val q
      · rw [col_eq π a θ q ht hq,slice_right_weight]
      · have hz := le_antisymm (le_of_not_gt hq) ((right (slice π a θ)).nonneg q)
        rw [← slice_right_weight,hz,mul_zero,zero_mul,zero_mul]
    · have hz := le_antisymm (le_of_not_gt ht) ((templates π a).nonneg θ)
      rw [← slice_right_weight,hz,zero_mul,zero_mul,zero_mul]
  simp only [avg,mul_sum,he]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← sum_mul,← mul_sum,(a q).total,mul_one]

lemma center_variation (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool) :
    avg (templates π a) (fun θ => VQ (slice π a θ) bit)=VQ π bit :=
  center_statistic π a (fun q ν => StarScore.variation ν (fun p => bit p q))
lemma center_score {A B : Type*} (π : Law (P×Q)) (a : Q → Law Θ)
    (bit : P → Q → Bool) (x : P → A×B) :
    avg (templates π a) (fun θ => DQ (slice π a θ) bit x)=DQ π bit x :=
  center_statistic π a (fun q ν => StarScore.score ν (fun p => bit p q) x)
end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.CrossSampling
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]

def crossMass (ν : Law (A×B)) (y : A×B) : ℝ := event ν (fun x => Adj x y)
def rowMass (ν : Law (A×B)) (a : A) : ℝ := event ν (fun x => x.1=a)
def colMass (ν : Law (A×B)) (b : B) : ℝ := event ν (fun x => x.2=b)

def Bad (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ y,crossMass ν y < 1-α ∧ ∀ i,Adj (xs i) y

def Corner (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) (i j : I) : Prop :=
  i≠j ∧ crossMass ν ((xs i).1,(xs j).2)<1-α ∧
    ∀ l,Adj (xs l) ((xs i).1,(xs j).2)
def LowRow (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ a,rowMass ν a ≤ 1-α/2 ∧ ∀ i,(xs i).1=a
def LowCol (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ b,colMass ν b ≤ 1-α/2 ∧ ∀ i,(xs i).2=b
def HeavyAvoid (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ y,α/2<ν.val y ∧ ∀ i,xs i≠y

lemma atom_eq (ν : Law (A×B)) (y : A×B) : event ν (fun x => x=y)=ν.val y := by
  classical
  rw [event_eq_sum]
  exact sum_eq_single y (fun x _ hx => ite_eq_right hx) (by simp) |>.trans (ite_eq_left rfl)
lemma row_le_cross_add_atom (ν : Law (A×B)) (y : A×B) :
    rowMass ν y.1 ≤ crossMass ν y+ν.val y := by
  have h := event_mono ν (P := fun x => x.1=y.1) (Q := fun x => Adj x y ∨ x=y) (by
    intro x hx
    by_cases hy : x.2=y.2
    · exact Or.inr (Prod.ext hx hy)
    · exact Or.inl (Or.inl ⟨hx,hy⟩))
  exact h.trans ((event_union_le ν _ _).trans_eq (by rw [atom_eq]; rfl))
lemma col_le_cross_add_atom (ν : Law (A×B)) (y : A×B) :
    colMass ν y.2 ≤ crossMass ν y+ν.val y := by
  have h := event_mono ν (P := fun x => x.2=y.2) (Q := fun x => Adj x y ∨ x=y) (by
    intro x hy
    by_cases hx : x.1=y.1
    · exact Or.inr (Prod.ext hx hy)
    · exact Or.inl (Or.inr ⟨hx,hy⟩))
  exact h.trans ((event_union_le ν _ _).trans_eq (by rw [atom_eq]; rfl))

omit [DecidableEq I] in
lemma bad_decomposition (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) (h : Bad ν α xs) :
    (∃ ij : I×I,Corner ν α xs ij.1 ij.2) ∨ LowRow ν α xs ∨ LowCol ν α xs ∨
      HeavyAvoid ν α xs := by
  obtain ⟨y,hy,hall⟩ := h
  have hne : ∀ i,xs i ≠ y := by
    intro i eq
    have hi := hall i
    rw [eq] at hi
    simp [Adj] at hi
  by_cases hr : ∃ i,(xs i).1=y.1 ∧ (xs i).2≠y.2
  · obtain ⟨i,hi⟩ := hr
    by_cases hc : ∃ j,(xs j).1≠y.1 ∧ (xs j).2=y.2
    · obtain ⟨j,hj⟩ := hc
      have hij : i≠j := by intro he; subst j; exact hj.1 hi.1
      left
      refine ⟨(i,j),hij,?_,?_⟩
      · simpa only [hi.1,hj.2,Prod.mk.eta] using hy
      · simpa only [hi.1,hj.2,Prod.mk.eta] using hall
    · have har : ∀ j,(xs j).1=y.1 := by
        intro j
        rcases hall j with h|h
        · exact h.1
        · exact False.elim (hc ⟨j,h⟩)
      by_cases hlo : rowMass ν y.1 ≤ 1-α/2
      · exact Or.inr (Or.inl ⟨y.1,hlo,har⟩)
      · right; right; right
        refine ⟨y,?_,hne⟩
        have := row_le_cross_add_atom ν y
        linarith
  · have hac : ∀ j,(xs j).2=y.2 := by
      intro j
      rcases hall j with h|h
      · exact False.elim (hr ⟨j,h⟩)
      · exact h.2
    by_cases hlo : colMass ν y.2 ≤ 1-α/2
    · exact Or.inr (Or.inr (Or.inl ⟨y.2,hlo,hac⟩))
    · right; right; right
      refine ⟨y,?_,hne⟩
      have := col_le_cross_add_atom ν y
      linarith

lemma low_fiber_bound {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (f : X → Y)
    {r : ℝ} (hr : 0≤r) (hI : 0<Fintype.card I) :
    event (independent ν I) (fun xs => ∃ y,event ν (fun x => f x=y) ≤ r ∧ ∀ i,f (xs i)=y) ≤
      r^(Fintype.card I-1) := by
  refine (event_exists_le _ _).trans ?_
  have hb : ∀ y,event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
      ∀ i,f (xs i)=y) ≤ event ν (fun x => f x=y)*r^(Fintype.card I-1) := by
    intro y
    by_cases hy : event ν (fun x => f x=y) ≤ r
    · have he : event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
          ∀ i,f (xs i)=y) = event (independent ν I) (fun xs => ∀ i,f (xs i)=y) := by
        apply event_congr
        intro xs
        simp only [hy,true_and]
      rw [he,independent_all (I := I) ν (fun x => f x=y)]
      conv_lhs => rw [show Fintype.card I=1+(Fintype.card I-1) by omega,pow_add,pow_one]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (event_nonneg _ _) hy _) (event_nonneg _ _)
    · have he : event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
          ∀ i,f (xs i)=y) = 0 := by
        calc
          _ = event (independent ν I) (fun _ => False) := event_congr _ (by intro xs; simp only [hy,false_and])
          _ = 0 := event_false _
      rw [he]
      exact mul_nonneg (event_nonneg _ _) (pow_nonneg hr _)
  calc
    _ ≤ ∑ y,event ν (fun x => f x=y)*r^(Fintype.card I-1) := sum_le_sum fun y _ => hb y
    _ = _ := by rw [← sum_mul,sum_event_fibers,one_mul]
lemma heavyavoid_bound (ν : Law (A×B)) {α : ℝ} (hα : 0<α) (hα1 : α<1) :
    event (independent ν I) (HeavyAvoid ν α) ≤ (2/α)*(1-α/2)^(Fintype.card I) := by
  have hr : 0 ≤ 1-α/2 := by linarith
  refine (event_exists_le _ _).trans ?_
  have hb : ∀ y,event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y) ≤
      ν.val y*((2/α)*(1-α/2)^(Fintype.card I)) := by
    intro y
    by_cases hy : α/2<ν.val y
    · have he : event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y) =
          event (independent ν I) (fun xs => ∀ i,xs i≠y) := by
        apply event_congr
        intro xs
        simp only [hy,true_and]
      rw [he,independent_all (I := I) ν (fun x => x≠y),event_compl,atom_eq]
      have hν : 0≤1-ν.val y := by
        have := event_le_one ν (fun x => x=y)
        rw [atom_eq] at this
        linarith
      have hpow := pow_le_pow_left₀ hν (show 1-ν.val y ≤ 1-α/2 by linarith) (Fintype.card I)
      have hfactor : 1≤ν.val y*(2/α) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hα).mpr
        linarith
      calc
        _ ≤ (1-α/2)^(Fintype.card I) := hpow
        _ ≤ (ν.val y*(2/α))*(1-α/2)^(Fintype.card I) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (pow_nonneg hr _)
        _ = _ := by ring
    · have he : event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y)=0 := by
        calc
          _ = event (independent ν I) (fun _ => False) := event_congr _ (by intro xs; simp only [hy,false_and])
          _ = 0 := event_false _
      rw [he]
      exact mul_nonneg (ν.nonneg y) (mul_nonneg (div_nonneg (by norm_num) hα.le) (pow_nonneg hr _))
  calc
    _ ≤ ∑ y,ν.val y*((2/α)*(1-α/2)^(Fintype.card I)) := sum_le_sum fun y _ => hb y
    _ = _ := by rw [← sum_mul,ν.total,one_mul]

abbrev Rest (i j : I) (hij : i≠j) := {l : {l : I // l≠i} // l≠⟨j,hij.symm⟩}
def fillTwo {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) : I → X :=
  (Equiv.piSplitAt i (fun _ => X)).symm (a,
    (Equiv.piSplitAt (⟨j,hij.symm⟩ : {l : I // l≠i}) (fun _ => X)).symm (b,xs))

omit [Fintype I] in
lemma fillTwo_i {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) :
    fillTwo i j hij a b xs i = a := by simp [fillTwo,Equiv.piSplitAt_symm_apply]
omit [Fintype I] in
lemma fillTwo_j {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) :
    fillTwo i j hij a b xs j = b := by simp [fillTwo,Equiv.piSplitAt_symm_apply,hij.symm]
omit [Fintype I] in
lemma fillTwo_rest {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X)
    (l : Rest i j hij) : fillTwo i j hij a b xs l.val.val = xs l := by
  have hl := l.val.property
  simp [fillTwo,Equiv.piSplitAt_symm_apply,hl,l.property]

lemma card_neq (i : I) : Fintype.card {l : I //l≠i}=Fintype.card I-1 := by
  rw [Fintype.card_subtype_compl (fun l : I => l=i)]
  simp
lemma card_rest (i j : I) (hij : i≠j) : Fintype.card (Rest i j hij)=Fintype.card I-2 := by
  rw [card_neq,card_neq]
  omega

lemma corner_bound (ν : Law (A×B)) {α : ℝ} (hα : α<1) (i j : I) :
    event (independent ν I) (fun xs => Corner ν α xs i j) ≤ (1-α)^(Fintype.card I-2) := by
  classical
  by_cases hij : i=j
  · subst j
    have he : event (independent ν I) (fun xs => Corner ν α xs i i)=0 := by
      simp [event,Corner,avg_const]
    rw [he]
    exact pow_nonneg (by linarith) _
  · rw [← avg_ite (independent ν I) (fun xs => Corner ν α xs i j),independent_two_split ν i j hij]
    apply avg_le_const
    intro a
    apply avg_le_const
    intro b
    change avg (independent ν (Rest i j hij)) (fun xs =>
      if Corner ν α (fillTwo i j hij a b xs) i j then 1 else 0) ≤ _
    by_cases hm : crossMass ν (a.1,b.2)<1-α
    · have hm' : ∀ xs, Corner ν α (fillTwo i j hij a b xs) i j →
          ∀ l,Adj (xs l) (a.1,b.2) := by
        intro xs hx l
        have he := hx.2.2 l.val.val
        simpa only [fillTwo_i,fillTwo_j,fillTwo_rest] using he
      have hh := event_mono (independent ν (Rest i j hij)) hm'
      rw [avg_ite]
      refine hh.trans ?_
      rw [independent_all (I := Rest i j hij) ν (fun x => Adj x (a.1,b.2)),card_rest]
      exact pow_le_pow_left₀ (event_nonneg _ _) hm.le _
    · have he : ∀ xs,¬Corner ν α (fillTwo i j hij a b xs) i j := by
        intro xs hx
        apply hm
        simpa only [fillTwo_i,fillTwo_j] using hx.2.1
      simp only [he,ite_false,avg_const]
      exact pow_nonneg (by linarith) _

lemma sampling_bound (ν : Law (A×B)) {α : ℝ} (hα : 0<α) (hα1 : α<1)
    (hI : 0<Fintype.card I) : event (independent ν I) (Bad ν α) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) +
      2*(1-α/2)^(Fintype.card I-1)+(2/α)*(1-α/2)^(Fintype.card I) := by
  have h := event_mono (independent ν I) (bad_decomposition ν α)
  have hu₁ := event_union_le (independent ν I) (fun xs => ∃ ij : I×I,Corner ν α xs ij.1 ij.2)
    (fun xs => LowRow ν α xs ∨ LowCol ν α xs ∨ HeavyAvoid ν α xs)
  have hu₂ := event_union_le (independent ν I) (LowRow ν α) (fun xs => LowCol ν α xs ∨ HeavyAvoid ν α xs)
  have hu₃ := event_union_le (independent ν I) (LowCol ν α) (HeavyAvoid ν α)
  have hc := event_exists_le (independent ν I) (fun ij : I×I => fun xs => Corner ν α xs ij.1 ij.2)
  have hcs : (∑ ij : I×I,event (independent ν I) (fun xs => Corner ν α xs ij.1 ij.2)) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) := by
    calc
      _ ≤ ∑ _ : I×I,(1-α)^(Fintype.card I-2) := sum_le_sum fun ij _ => corner_bound ν hα1 ij.1 ij.2
      _ = _ := by simp [Fintype.card_prod,pow_two]
  have hr := low_fiber_bound (I := I) ν Prod.fst (r := 1-α/2) (by linarith) hI
  have hcol := low_fiber_bound (I := I) ν Prod.snd (r := 1-α/2) (by linarith) hI
  have hh := heavyavoid_bound (I := I) ν hα hα1
  change event (independent ν I) (LowRow ν α) ≤ _ at hr
  change event (independent ν I) (LowCol ν α) ≤ _ at hcol
  linarith
end
end PlanarUnitDistances.CrossSampling

namespace PlanarUnitDistances.CrossTemplates
open Finset FiniteLaw StrictCross CrossSampling
open scoped Classical
noncomputable section
variable {H A B I : Type*} [Fintype H] [Fintype A] [Fintype B] [Fintype I]

def Candidates (ν : H → Law (A×B)) (ε : ℝ) (h : I → H) : Finset (A×B) :=
  univ.filter fun y => ∀i,1-ε≤crossMass (ν (h i)) y

def Failure (μ : Law H) (ν : H → Law (A×B)) (ε α : ℝ) (h : I → H) : Prop :=
  ∃y∈Candidates ν ε h,crossMass (mix μ ν) y<1-α

lemma all_cross_lower (ν : I → Law (A×B)) (y : A×B) {ε : ℝ}
    (h : ∀i,1-ε≤crossMass (ν i) y) :
    1-(Fintype.card I:ℝ)*ε ≤ event (tensor ν) (fun x => ∀i,Adj (x i) y) := by
  have hh := tensor_union_le ν (fun _ x => ¬Adj x y)
  simp_rw [event_compl] at hh
  have hc : (∑ i : I, (1 - event (ν i) (fun x => Adj x y))) ≤ (Fintype.card I:ℝ)*ε := by
    calc
      _ ≤ ∑ _ : I, ε := sum_le_sum fun i _ => by have := h i; change 1-ε≤event (ν i) _ at this; linarith
      _ = _ := by simp
  have he : event (tensor ν) (fun x => ∃i,¬Adj (x i) y) =
      1-event (tensor ν) (fun x => ∀i,Adj (x i) y) := by
    rw [← event_compl]
    apply event_congr
    intro x
    simp
  rw [he] at hh
  linarith

theorem failure_bound (μ : Law H) (ν : H → Law (A×B)) {ε α : ℝ}
    (hα : 0<α) (hα1 : α<1) (hI : 0<Fintype.card I) :
    (1-(Fintype.card I:ℝ)*ε)*event (independent μ I) (Failure μ ν ε α) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) +
      2*(1-α/2)^(Fintype.card I-1)+(2/α)*(1-α/2)^(Fintype.card I) := by
  let G := Bad (I := I) (mix μ ν) α
  have hl (h : I → H) :
      (if Failure μ ν ε α h then 1-(Fintype.card I:ℝ)*ε else 0) ≤
        event (tensor (fun i => ν (h i))) G := by
    split_ifs with hh
    · obtain ⟨y,hy,hmy⟩ := hh
      have hy' : ∀i,1-ε≤crossMass (ν (h i)) y := (mem_filter.mp hy).2
      refine (all_cross_lower _ y hy').trans (event_mono _ ?_)
      intro x hx
      exact ⟨y,hmy,hx⟩
    · exact event_nonneg _ _
  have ha := avg_mono (independent μ I) hl
  have he : avg (independent μ I) (fun h => if Failure μ ν ε α h then 1-(Fintype.card I:ℝ)*ε else 0) =
      (1-(Fintype.card I:ℝ)*ε)*event (independent μ I) (Failure μ ν ε α) := by
    rw [← avg_ite]
    rw [← avg_smul]
    apply avg_congr
    intro h
    split_ifs <;> simp_all
  rw [he] at ha
  have hm : avg (independent μ I) (fun h => event (tensor (fun i => ν (h i))) G) =
      event (independent (mix μ ν) I) G := by
    unfold event
    exact tensor_mixture μ ν _
  rw [hm] at ha
  exact ha.trans (sampling_bound (mix μ ν) hα hα1 hI)

lemma miss_markov (μ : Law H) (ν : H → Law (A×B)) (y : A×B) {ε : ℝ} :
    ε*event μ (fun h => crossMass (ν h) y<1-ε) ≤
      avg μ (fun h => 1-crossMass (ν h) y) := by
  rw [← avg_ite]
  rw [← avg_smul]
  apply avg_mono
  intro h
  split_ifs with hh
  · simp only [mul_one]
    linarith
  · simp only [mul_zero]
    exact sub_nonneg.mpr (event_le_one _ _)

theorem candidate_miss (μ : Law H) (ν : H → Law (A×B)) (y : A×B) {ε : ℝ} (hε : 0≤ε) :
    ε*event (independent μ I) (fun h => y∉Candidates ν ε h) ≤
      (Fintype.card I:ℝ)*avg μ (fun h => 1-crossMass (ν h) y) := by
  have he : event (independent μ I) (fun h => y∉Candidates ν ε h) =
      event (independent μ I) (fun h => ∃i,crossMass (ν (h i)) y<1-ε) := by
    apply event_congr
    intro h
    simp only [Candidates,mem_filter,mem_univ,true_and,not_forall,not_le]
  rw [he]
  have hu := tensor_union_le (fun _ : I => μ) (fun _ h => crossMass (ν h) y<1-ε)
  have heq : tensor (fun _ : I => μ)=independent μ I := by apply law_ext; intro x; rfl
  rw [heq] at hu
  have hh := mul_le_mul_of_nonneg_left hu hε
  have hm := miss_markov μ ν y (ε := ε)
  calc
    _ ≤ ε*∑_ : I,event μ (fun h => crossMass (ν h) y<1-ε) := hh
    _ = (Fintype.card I:ℝ)*(ε*event μ (fun h => crossMass (ν h) y<1-ε)) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
end
end PlanarUnitDistances.CrossTemplates

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ]

def posteriorState (π : Law (P×Q)) (h : P → H) (x : P → A×B) (v : H) : Law (A×B) :=
  push (cond (left π) h v) x

def historyLaw (π : Law (P×Q)) (h : P → H) (q : Q) : Law H := push (col π q) h

omit [Fintype H] in
lemma posterior_val (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (p : P) (s : A×B) :
    (posteriorState π h x (h p)).val s =
      RestrictedTransfer.statePosterior (left π).val h x (h p) s := by
  have hp : 0<fiberMass (left π) h (h p) := lt_of_lt_of_le (hμ p) (atom_le_fiber _ _ _)
  have he : fiberMass (left π) h (h p)=RestrictedTransfer.historyMass (left π).val h (h p) :=
    fiberMass_eq _ _ _
  simp only [posteriorState,push]
  simp only [FiniteLaw.cond,hp,↓reduceDIte]
  simp only [fiberMass_eq,RestrictedTransfer.statePosterior,RestrictedTransfer.posterior]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp_all [RestrictedTransfer.historyMass]

lemma mixture_val (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q) (q : Q) (s : A×B) :
    (mix (historyLaw π h q) (posteriorState π h x)).val s=
      RestrictedTransfer.centerMixture (left π).val h x (fun p q => π.val (p,q)) q s := by
  change avg (push (col π q) h) (fun v => (posteriorState π h x v).val s)=_
  rw [push_avg]
  simp only [avg,posterior_val π h x hμ,col_val π (hκ q),right_val,
    RestrictedTransfer.centerMixture]

lemma event_mem_mass {X : Type*} [Fintype X] (μ : Law X) (U : Finset X) :
    event μ (fun x => x∈U)=RestrictedTransfer.mass μ.val U := by
  rw [event_eq_sum]
  simp only [RestrictedTransfer.mass]
  calc
    _ = ∑x,if x∈U then μ.val x else 0 := by
      apply sum_congr rfl; intro x _; split_ifs <;> rfl
    _ = _ := by rw [sum_ite_mem]; simp

lemma witnesses_mass (μ : Law (A×B)) (W U : Finset (A×B)) {α : ℝ} (hα : 0≤α)
    (hw : W.card≤3) (hU : ∀x,(∀w∈W,Adj x w) → x∈U)
    (hm : ∀w∈W,1-α≤crossMass μ w) : 1-3*α≤event μ (fun x => x∈U) := by
  have hu := event_exists_le (I := W) μ (fun w x => ¬Adj x w.val)
  have hsum : (∑w : W,event μ (fun x => ¬Adj x w.val))≤3*α := by
    calc
      _ ≤ ∑_w : W,α := sum_le_sum fun w _ => by
        rw [event_compl]; have hh := hm w.val w.property
        change 1-α≤event μ (fun x => Adj x w.val) at hh
        linarith
      _ = (W.card:ℝ)*α := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hw) hα
  have hm' : event μ (fun x => x∉U)≤event μ (fun x => ∃w : W,¬Adj x w.val) := by
    apply event_mono
    intro x hx
    by_contra hn
    push Not at hn
    exact hx (hU x (fun w hw => hn ⟨w,hw⟩))
  rw [event_compl] at hm'
  linarith

theorem actual_transfer (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    (a : Q → Law Θ) (U : Θ → Finset (A×B)) (hU : ∀θ,U θ=univ ∨ RestrictedTransfer.Permitted (U θ))
    (G : Q → Θ → Prop) {η : ℝ} (hη : 0<η) (hη' : η<1/2)
    (hg : ∀q θ,G q θ → 1-3*η^2≤event (mix (historyLaw π h q) (posteriorState π h x)) (fun s => s∈U θ)) :
    avg π (fun pq => event (a pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ))≤8*η := by
  let U' : Q → Θ → Finset (A×B) := fun _ θ => if U θ=univ then ∅ else U θ
  let G' : Q → Θ → Prop := fun q θ => G q θ ∧ U θ≠univ
  have hu : ∀q θ,RestrictedTransfer.Permitted (U' q θ) := by
    intro q θ
    by_cases he : U θ=univ
    · simp only [U',he,↓reduceIte]
      exact Or.inr (Or.inr (by simp))
    · simp only [U',he,↓reduceIte]
      exact (hU θ).resolve_left he
  have hh : ∀q θ,G' q θ → 1-3*η^2≤RestrictedTransfer.mass
      (RestrictedTransfer.centerMixture (left π).val h x (fun p q => π.val (p,q)) q) (U' q θ) := by
    intro q θ hqt
    have ht := hg q θ hqt.1
    rw [event_mem_mass] at ht
    change 1-3*η^2≤∑s∈U θ,(mix (historyLaw π h q) (posteriorState π h x)).val s at ht
    simp_rw [mixture_val π h x hμ hκ] at ht
    simpa only [U',hqt.2,↓reduceIte,RestrictedTransfer.mass] using ht
  have ht := RestrictedTransfer.edge_template_transfer (left π).val hμ (left π).total h x
    (fun p q => π.val (p,q)) (fun p q => π.nonneg (p,q))
    (fun p => (left_val π p).symm) (fun q => by simpa only [← right_val] using hκ q)
    (fun q θ => (a q).val θ) (fun q θ => (a q).nonneg θ) (fun q => (a q).total)
    U' hu G' hη hη' hh
  have heq : avg π (fun pq => event (a pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ))=
      ∑p,∑q,∑θ,π.val (p,q)*(a q).val θ*(if G' q θ ∧ x p∉U' q θ then 1 else 0) := by
    simp only [avg,event,Fintype.sum_prod_type,mul_sum,← mul_assoc]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro θ _
    by_cases he : U θ=univ <;> simp [U',G',he]
  exact heq ▸ ht

omit [Fintype A] [Fintype B] in

theorem aggregate_score (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (Y U : Θ → Finset (A×B))
    (good : Θ → P → Q → Prop) (hs : ∀θ,Shape (Y θ) (U θ))
    (hg : ∀θ p q,good θ p q → x p∈U θ ∧ y q∈Y θ ∧ Consistent (bit p q) (x p) (y q)) :
    (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 -
      12*avg π (fun pq => event (a pq.2) (fun θ => ¬good θ pq.1 pq.2)) ≤
      avg (templates π a) (fun θ => DP (slice π a θ) bit y)+DQ π bit x := by
  have ht := avg_mono (templates π a) (fun θ => slice_score (slice π a θ) bit x y
    (good θ) (Y θ) (U θ) (hs θ) (hg θ))
  have he : avg (templates π a) (fun θ => (VP (slice π a θ) bit+VQ (slice π a θ) bit)/80000)=
      (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 := by
    simp only [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹,avg_smul,avg_add,center_variation]
  rw [avg_sub,he,avg_smul,avg_add,center_score] at ht
  simp only [bad,slice_event] at ht
  exact ht
end
end PlanarUnitDistances.CommonTemplate

end OAI
