import Mathlib
import OAI.Combinatorics.KServer.Partitions

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma probability_mono {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j,Fintype (Ω j)]
    {w : ∀ j, Ω j → ℝ} (hw : ∀ j a, 0 ≤ w j a) {E F : (∀ j, Ω j) → Prop}
    (hEF : ∀ o, E o → F o) : PartitionProbabilities.probability w E ≤ PartitionProbabilities.probability w F := by
  unfold PartitionProbabilities.probability
  apply sum_le_sum
  intro o _
  by_cases he : E o
  · simp [he,hEF o he]
  · simp only [ite_eq_right he]
    split_ifs
    · exact productWeight_nonneg hw o
    · rfl

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

lemma separates_iff_cover (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) (i : Fin H) :
    (present center I r life i ∧ separates r (center i) x y (rad i)) ↔
      (covered center I r life rad x i ∧ ¬covered center I r life rad y i) ∨
      (covered center I r life rad y i ∧ ¬covered center I r life rad x i) := by
  simp only [covered,separates]
  constructor
  · rintro ⟨hp,he|he⟩
    · exact Or.inl ⟨⟨hp,he.1⟩,fun hh=>not_le_of_gt he.2 hh.2⟩
    · exact Or.inr ⟨⟨hp,he.1⟩,fun hh=>not_le_of_gt he.2 hh.2⟩
  · rintro (⟨⟨hp,hx⟩,hy⟩|⟨⟨hp,hy⟩,hx⟩)
    · exact ⟨hp,Or.inl ⟨hx,lt_of_not_ge (fun h=>hy ⟨hp,h⟩)⟩⟩
    · exact ⟨hp,Or.inr ⟨hy,lt_of_not_ge (fun h=>hx ⟨hp,h⟩)⟩⟩

lemma hit_iff_cover (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) (i : Fin H) :
    (present center I r life i ∧ hit r (center i) x y (rad i)) ↔
      covered center I r life rad x i ∨ covered center I r life rad y i := by
  exact and_or_left

/-- The first-hit event is literally the event that the actual two chronological
keys differ, including absence on either or both sides. -/
theorem first_ne_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) :
    first center I r life rad x ≠ first center I r life rad y ↔
      firstSeparation (fun j d=>present center I r life j ∧ hit r (center j) x y d)
        (fun j d=>present center I r life j ∧ separates r (center j) x y d) rad := by
  constructor
  · intro hne
    cases hx : first center I r life rad x with
    | none =>
      have hnx := (first_none_iff _ _ _ _ _ _).mp hx
      cases hy : first center I r life rad y with
      | none => exact False.elim (hne (hx.trans hy.symm))
      | some i =>
        obtain ⟨hi,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hy
        refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr ⟨hi,hnx i⟩),?_⟩
        intro j hj hh
        rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
        · exact hnx j hh
        · exact hbefore j hj hh
    | some i =>
      obtain ⟨hi,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hx
      cases hy : first center I r life rad y with
      | none =>
        have hny := (first_none_iff _ _ _ _ _ _).mp hy
        refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl ⟨hi,hny i⟩),?_⟩
        intro j hj hh
        rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
        · exact hbefore j hj hh
        · exact hny j hh
      | some j =>
        obtain ⟨hj,hbeforej⟩ := (first_some_iff _ _ _ _ _ _ _).mp hy
        have hneij : i≠j := fun he=>hne (hx.trans (by rw [he,←hy]))
        rcases lt_or_gt_of_ne hneij with hij|hji
        · refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl ⟨hi,hbeforej i hij⟩),?_⟩
          intro a ha hh
          rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
          · exact hbefore a ha hh
          · exact hbeforej a (ha.trans hij) hh
        · refine ⟨j,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr ⟨hj,hbefore j hji⟩),?_⟩
          intro a ha hh
          rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
          · exact hbefore a (ha.trans hji) hh
          · exact hbeforej a ha hh
  · rintro ⟨i,hsep,hbefore⟩ heq
    have hn (j : Fin H) (hj : j < i) : ¬covered center I r life rad x j ∧ ¬covered center I r life rad y j := by
      exact ⟨fun h=>hbefore j hj ((hit_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl h)),
        fun h=>hbefore j hj ((hit_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr h))⟩
    rcases (separates_iff_cover _ _ _ _ _ _ _ _).mp hsep with ⟨hx,hy⟩|⟨hy,hx⟩
    · have hfirst := (first_some_iff _ _ _ _ _ _ _).mpr ⟨hx,fun j hj=>(hn j hj).1⟩
      rw [heq] at hfirst
      exact hy ((first_some_iff _ _ _ _ _ _ _).mp hfirst).1
    · have hfirst := (first_some_iff _ _ _ _ _ _ _).mpr ⟨hy,fun j hj=>(hn j hj).2⟩
      rw [←heq] at hfirst
      exact hx ((first_some_iff _ _ _ _ _ _ _).mp hfirst).1

/-- Uniform-in-history spatial bound for the actual fixed-lifetime keys. -/
theorem spatial_bound (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) (life : Fin H → Lifetime K) (x y : Y) (hxy : dist x y ≤ r) :
    PartitionProbabilities.probability (fun _ : Fin H=>law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (fun rad=>first center I r life rad x ≠ first center I r life rad y) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have he : (fun rad=>first center I r life rad x ≠ first center I r life rad y)=
      firstSeparation (fun j d=>present center I r life j ∧ hit r (center j) x y d)
        (fun j d=>present center I r life j ∧ separates r (center j) x y d) := by
    funext rad
    exact propext (first_ne_iff _ _ _ _ _ _ _)
  rw [he]
  exact first_hit_estimate center I hr hK life x y hxy

/-- Averaging independent lifetimes preserves the bound. No conditional
independence of any adaptive allocation state is used. -/
theorem averaged_spatial_bound (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) (x y : Y) (hxy : dist x y ≤ r) :
    (∑ life : Fin H → Lifetime K, productWeight (fun _ : Fin H=>lifetimeLaw K) life *
      PartitionProbabilities.probability (fun _ : Fin H=>law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
        (fun rad=>first center I r life rad x ≠ first center I r life rad y)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  calc _ ≤ ∑ life : Fin H → Lifetime K, productWeight (fun _ : Fin H=>lifetimeLaw K) life *
         (2*Real.log (1+(K:ℝ)^2)*dist x y/r) := by
        apply sum_le_sum
        intro life _
        exact mul_le_mul_of_nonneg_left (spatial_bound center I hr hK life x y hxy)
          (productWeight_nonneg (fun _=>lifetime_nonneg hK) life)
       _ = _ := by
         have hs : (∑ life : Fin H → Lifetime K, productWeight (fun _ : Fin H=>lifetimeLaw K) life)=1 :=
           by
             convert productWeight_sum (fun _ : Fin H=>lifetimeLaw K) (fun _=>lifetime_sum hK) using 1
             apply sum_congr
             · ext o; simp
             · intro o _; rfl
         rw [←sum_mul,hs,one_mul]

end KServer.ActualRoster

end


/-! Heavy keys of the constructed finite schedule and their exact full-input
spatial estimate; label reuse does not impose or assume a probability law. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyKeys
open HeavyCenters HeavySchedule HeavyLabels FiniteExperiment PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

def hits (C : Finset Y) (rad : Y → ℝ) (x : Y) : Finset Y :=
  C.filter (fun a=>dist a x≤rad a)

def centerKey (C : Finset Y) (rad : Y → ℝ) (x : Y) : Option Y :=
  if h:(hits C rad x).Nonempty then some h.choose else none

lemma hit_unique {r : ℝ} (hr : 0<r) {C : Finset Y} {rad : Y → ℝ} {x a b : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (ha : a∈hits C rad x) (hb : b∈hits C rad x) : a=b := by
  by_contra hn
  obtain ⟨ha,hax⟩:=mem_filter.mp ha
  obtain ⟨hb,hbx⟩:=mem_filter.mp hb
  have hd:=hC ha hb hn
  have ht:=dist_triangle a x b
  rw [dist_comm x b] at ht
  linarith [hrad a ha,hrad b hb]

lemma centerKey_some {r : ℝ} (hr : 0<r) {C : Finset Y} {rad : Y → ℝ} {x a : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) :
    centerKey C rad x=some a ↔ a∈C ∧ dist a x≤rad a := by
  unfold centerKey
  split_ifs with h
  · constructor
    · intro he
      have he':=Option.some.inj he
      rw [←he']
      exact mem_filter.mp h.choose_spec
    · intro ha
      rw [hit_unique hr hC hrad h.choose_spec (mem_filter.mpr ha)]
  · simp only [false_iff,not_and]
    intro ha hx
    exact h ⟨a,mem_filter.mpr ⟨ha,hx⟩⟩

lemma centerKey_none (C : Finset Y) (rad : Y → ℝ) (x : Y) :
    centerKey C rad x=none ↔ ∀ a∈C,rad a<dist a x := by
  unfold centerKey
  split_ifs with h
  · simp only [false_iff,not_forall]
    obtain ⟨a,ha⟩:=h
    obtain ⟨ha,hax⟩:=mem_filter.mp ha
    exact ⟨a,ha,not_lt_of_ge hax⟩
  · simp only [true_iff]
    intro a ha
    exact lt_of_not_ge (fun hx=>h ⟨a,mem_filter.mpr ⟨ha,hx⟩⟩)

def candidates (C : Finset Y) (r : ℝ) (x y : Y) : Finset Y :=
  C.filter (fun a=>dist a x≤20*r ∨ dist a y≤20*r)

lemma candidate_unique {C : Finset Y} {r : ℝ} (hr : 0<r) {x y a b : Y}
    (hxy : 4*dist x y<r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (ha : a∈candidates C r x y) (hb : b∈candidates C r x y) : a=b := by
  by_contra hn
  obtain ⟨ha,hax|hay⟩:=mem_filter.mp ha <;>
    obtain ⟨hb,hbx|hby⟩:=mem_filter.mp hb
  all_goals
    have hd:=hC ha hb hn
    have h1:=dist_triangle a x b
    have h2:=dist_triangle a y b
    have h3:=dist_triangle a x y
    have h4:=dist_triangle a y x
    have h5:=dist_triangle x y b
    have h6:=dist_triangle y x b
    simp only [dist_comm x b,dist_comm y b,dist_comm y x] at h1 h2 h4 h5 h6
    linarith [dist_nonneg (x:=x) (y:=y)]

lemma ne_separates {C : Finset Y} {rad : Y → ℝ} {r : ℝ} (hr : 0<r) {x y : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hne : centerKey C rad x≠centerKey C rad y) :
    ∃ a∈candidates C r x y,
      (dist a x≤rad a ∧ rad a<dist a y) ∨ (dist a y≤rad a ∧ rad a<dist a x) := by
  cases hx : centerKey C rad x with
  | none =>
    cases hy : centerKey C rad y with
    | none => exact False.elim (hne (hx.trans hy.symm))
    | some a =>
      obtain ⟨ha,hay⟩:=(centerKey_some hr hC hrad).mp hy
      exact ⟨a,mem_filter.mpr ⟨ha,Or.inr (hay.trans (hrad a ha))⟩,
        Or.inr ⟨hay,(centerKey_none C rad x).mp hx a ha⟩⟩
  | some a =>
    obtain ⟨ha,hax⟩:=(centerKey_some hr hC hrad).mp hx
    refine ⟨a,mem_filter.mpr ⟨ha,Or.inl (hax.trans (hrad a ha))⟩,Or.inl ⟨hax,?_⟩⟩
    apply lt_of_not_ge
    intro hay
    exact hne (hx.trans ((centerKey_some hr hC hrad).mpr ⟨ha,hay⟩).symm)

lemma cylinder {I Ω : Type*} [Fintype I] [Fintype Ω] (w : I → Ω → ℝ)
    (hsum : ∀ i,∑ a,w i a=1) (i : I) (E : Ω → Prop) :
    probability w (fun o=>E (o i))=∑ a,if E a then w i a else 0 := by
  have he : (fun o : I → Ω=>E (o i))=(fun o=>∀ j,j=i → E (o j)) := by
    funext o
    exact propext ⟨fun h j hj=>by simpa only [hj] using h,fun h=>h i rfl⟩
  rw [he,rectangle_probability w (fun j a=>j=i → E a)]
  trans ∏ j, if j=i then (∑ a,if E a then w i a else 0) else 1
  · apply prod_congr rfl
    intro j _
    by_cases hj : j=i
    · subst j; simp only [true_implies,ite_eq_left]
    · simp only [hj,false_implies,ite_true,ite_false,hsum]
  · simp

variable [Fintype Y] {k H : ℕ} [NeZero k]

def key (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) (t : ℕ) (x : Y) :
    Option (Pool Y) :=
  (centerKey (centers s law r γ δ σ t) (run s law r γ δ σ tape t).rad x).map
    (run s law r γ δ σ tape t).label

/-- The source's d/(4r) bound for the actual heavy key, conditioned only on
full input, with deterministic birth times and a genuine product radius tape. -/
theorem spatial_bound (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0<r) (γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) (x y : Y)
    (hxy : 4*dist x y<r) :
    probability (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
      (fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)≤dist x y/(4*r) := by
  let C:=centers s law r γ δ σ t
  have hC:=(centers_separated s law r γ δ σ t)
  by_cases hn : (candidates C r x y).Nonempty
  · obtain ⟨a,ha⟩:=hn
    obtain ⟨i,hi,_,_⟩:=present_birth s law hr γ δ σ t a (mem_filter.mp ha).1
    have hsub := ActualRoster.probability_mono
      (fun (_ : Fin H) b=>FiniteUniform.law_nonneg hr b)
      (E:=fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)
      (F:=fun tape=>FiniteUniform.separates r a x y (tape i)) (by
        intro tape hne
        have hc : centerKey C (run s law r γ δ σ tape t).rad x≠
            centerKey C (run s law r γ δ σ tape t).rad y := by
          intro he; exact hne (congrArg (Option.map (run s law r γ δ σ tape t).label) he)
        obtain ⟨b,hb,hsep⟩:=ne_separates hr hC (fun b hb=>(run_valid s law hr γ δ σ tape t).1 b hb |>.2) hc
        have he:=candidate_unique hr hxy hC hb ha
        subst b
        rw [radius_birth,hi] at hsep
        exact hsep)
    have he:=cylinder (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
      (fun _=>FiniteUniform.law_sum hr) i (FiniteUniform.separates r a x y)
    exact hsub.trans (he.le.trans (FiniteUniform.one_ball_bound hr a x y))
  · have he : ∀ tape,key s law r γ δ σ tape t x=key s law r γ δ σ tape t y := by
      intro tape
      apply congrArg (Option.map (run s law r γ δ σ tape t).label)
      by_contra hc
      obtain ⟨a,ha,_⟩:=ne_separates hr hC (fun b hb=>(run_valid s law hr γ δ σ tape t).1 b hb |>.2) hc
      exact hn ⟨a,ha⟩
    have hz : probability (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
        (fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)=0 := by
      simp [probability,he]
    rw [hz]
    positivity
end KServer.HeavyKeys

end


/-! Finite independent short-lifetime expectations used only for the pilot
profile in §07. No adaptive independence is postulated: all equalities below
are identities of finite product sums. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RosterExpectation
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

lemma product_pushforward (w : I → A → ℝ) (φ : I → A → B) (f : (I → B) → ℝ) :
    (∑ o,productWeight w o*f (fun i => φ i (o i))) =
      ∑ b,productWeight (fun i b => ∑ a,if φ i a=b then w i a else 0) b*f b := by
  have he (b : I → B) : productWeight (fun i b => ∑ a,if φ i a=b then w i a else 0) b =
      ∑ o,if (fun i=>φ i (o i))=b then productWeight w o else 0 := by
    rw [productWeight,←rectangle_probability,probability]
    apply sum_congr rfl
    intro o _
    congr 1
    exact propext ⟨fun h=>funext h,fun h i=>congrFun h i⟩
  simp_rw [he,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  symm
  rw [sum_eq_single (fun i=>φ i (o i))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

omit [Fintype B] in
lemma product_marginal (w : I → A → ℝ) (hw : ∀ i,∑ a,w i a=1)
    (i : I) (f : A → ℝ) :
    (∑ o,productWeight w o*f (o i))=∑ a,w i a*f a := by
  have he (o : I → A) : f (o i)=∏ j,if j=i then f (o j) else 1 := by simp
  simp_rw [he]
  rw [product_expectation w (fun j a => if j=i then f a else 1)]
  have hfac (j : I) : (∑ a,w j a*(if j=i then f a else 1))=
      if j=i then ∑ a,w i a*f a else 1 := by
    split_ifs with h
    · subst j; rfl
    · simpa using hw j
  simp_rw [hfac]
  simp

/-- Bernoulli weights, with `true` denoting that the record survives. -/
def bernoulli (q : ℝ) (b : Bool) : ℝ := if b then q else 1-q
lemma bernoulli_sum (q : ℝ) : ∑ b,bernoulli q b=1 := by
  simp [bernoulli]
lemma bernoulli_nonneg {q : ℝ} (hq : q∈Set.Icc 0 1) (b : Bool) : 0 ≤ bernoulli q b := by
  cases b <;> simp [bernoulli] <;> linarith [hq.1,hq.2]

omit [Fintype A] [Fintype B] in
lemma bernoulli_thinning (q d : I → ℝ) (f : (I → Bool) → ℝ) :
    (∑ o : I → Bool×Bool,productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
      f (fun i=>(o i).1 && !(o i).2))=
    ∑ b,productWeight (fun i=>bernoulli (q i*(1-d i))) b*f b := by
  rw [product_pushforward (fun i (b : Bool×Bool)=>bernoulli (q i) b.1*bernoulli (d i) b.2)
    (fun _ (b : Bool×Bool)=>b.1 && !b.2) f]
  congr 1
  funext b
  congr 1
  apply prod_congr rfl
  intro i _
  cases b i <;> simp [Fintype.sum_prod_type,bernoulli]
  ring

omit [Fintype A] [Fintype B] in
lemma paired_expectation (q d : I → ℝ) (f : (I → Bool) → (I → Bool) → ℝ) :
    (∑ o : I → Bool×Bool,productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
      f (fun i=>(o i).1) (fun i=>(o i).2))=
    ∑ a,productWeight (fun i=>bernoulli (q i)) a*
      ∑ b,productWeight (fun i=>bernoulli (d i)) b*f a b := by
  let e : (I → Bool×Bool) ≃ (I → Bool)×(I → Bool) :=
    { toFun := fun o=>(fun i=>(o i).1,fun i=>(o i).2)
      invFun := fun ab i=>(ab.1 i,ab.2 i)
      left_inv := fun _=>rfl
      right_inv := fun ab=>by cases ab; rfl }
  rw [Fintype.sum_equiv e (fun o=>productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
    f (fun i=>(o i).1) (fun i=>(o i).2))
    (fun ab=>productWeight (fun i=>bernoulli (q i)) ab.1*productWeight (fun i=>bernoulli (d i)) ab.2*f ab.1 ab.2)]
  · simp only [Fintype.sum_prod_type,mul_sum,mul_assoc]
  · intro o
    simp [e,productWeight,prod_mul_distrib]

/-- Finite minimum of the clipped ramps, with value 1 for an empty roster. -/
def minimum (v : I → ℝ) (a : I → Bool) : ℝ :=
  (insert 1 ((univ.filter (fun i=>a i=true)).image v)).min' ⟨1,mem_insert_self _ _⟩
lemma minimum_le_one (v : I → ℝ) (a : I → Bool) : minimum v a ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma minimum_le (v : I → ℝ) {a : I → Bool} {i : I} (hi : a i=true) : minimum v a ≤ v i :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩))
lemma le_minimum {v : I → ℝ} {a : I → Bool} {u : ℝ} (hu : u ≤ 1)
    (h : ∀ i,a i=true → u ≤ v i) : u ≤ minimum v a := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨i,hi,rfl⟩:=mem_image.mp hz
    exact h i (mem_filter.mp hi).2
lemma minimum_nonneg {v : I → ℝ} (hv : ∀ i,0 ≤ v i) (a : I → Bool) : 0 ≤ minimum v a :=
  le_minimum (by norm_num) (fun i _=>hv i)
lemma minimum_cases (v : I → ℝ) (a : I → Bool) :
    minimum v a=1 ∨ ∃ i,a i=true ∧ minimum v a=v i := by
  have hm := min'_mem (insert 1 ((univ.filter (fun i=>a i=true)).image v)) ⟨1,mem_insert_self _ _⟩
  rcases mem_insert.mp hm with h | h
  · exact Or.inl h
  · obtain ⟨i,hi,he⟩:=mem_image.mp h
    exact Or.inr ⟨i,(mem_filter.mp hi).2,he.symm⟩

/-- Expected ramp under independent survival probabilities. -/
def profile (q v : I → ℝ) : ℝ := ∑ a,productWeight (fun i=>bernoulli (q i)) a*minimum v a
lemma profile_bounds {q v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hv : ∀ i,v i∈Set.Icc 0 1) : profile q v∈Set.Icc 0 1 := by
  have hw := productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  refine ⟨sum_nonneg (fun a _=>mul_nonneg (hw a) (minimum_nonneg (fun i=>(hv i).1) a)),?_⟩
  calc profile q v  ≤  ∑ a,productWeight (fun i=>bernoulli (q i)) a*1 :=
        sum_le_sum (fun a _=>mul_le_mul_of_nonneg_left (minimum_le_one _ _) (hw a))
    _ = 1 := by simpa using productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)

/-- Continuing independent trials gives exactly the new survival marginal. -/
lemma profile_thinning (q d v : I → ℝ) :
    profile (fun i=>q i*(1-d i)) v=
      ∑ a,productWeight (fun i=>bernoulli (q i)) a*
        ∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i) := by
  rw [profile,←bernoulli_thinning]
  exact paired_expectation q d (fun a b=>minimum v (fun i=>a i && !b i))

lemma minimum_retirement {v : I → ℝ} (hv : ∀ i,0 ≤ v i) (a b : I → Bool)
    {i : I} (hai : a i=true) (hmin : minimum v a=v i) :
    minimum v (fun i=>a i && !b i)-minimum v a ≤ if b i then 1 else 0 := by
  cases hbi : b i
  · simp only [Bool.false_eq_true,ite_false]
    have hh := minimum_le v (a := fun i=>a i && !b i) (i := i) (by simp [hai,hbi])
    linarith
  · simp only [ite_true]
    linarith [minimum_le_one v (fun i=>a i && !b i),minimum_nonneg hv a]

/-- The selected old nearest survivor is tested by a fresh independent trial.
Compulsory deaths are charged without conditioning on survival. -/
lemma conditional_retirement {v d : I → ℝ} (hv : ∀ i,0 ≤ v i)
    (hd : ∀ i,d i∈Set.Icc 0 1) (a : I → Bool) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → d i ≤ α) :
    (∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i))-
      minimum v a ≤ α+∑ i∈C,if a i then 1 else 0 := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hd i))
  have hws:=productWeight_sum (fun i=>bernoulli (d i)) (fun i=>bernoulli_sum _)
  have hc : 0 ≤ ∑ i∈C,if a i then (1:ℝ) else 0 := sum_nonneg (fun i _=>by split_ifs <;> norm_num)
  have he : (∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i))-
      minimum v a = ∑ b,productWeight (fun i=>bernoulli (d i)) b*
        (minimum v (fun i=>a i && !b i)-minimum v a) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,←sum_mul,hws,one_mul]
  rw [he]
  rcases minimum_cases v a with hm | ⟨i,hai,hm⟩
  · have hb : (∑ b,productWeight (fun i=>bernoulli (d i)) b*
        (minimum v (fun i=>a i && !b i)-minimum v a)) ≤ 0 := by
      apply sum_nonpos
      intro b _
      exact mul_nonpos_of_nonneg_of_nonpos (hw b) (by linarith [minimum_le_one v (fun i=>a i && !b i)])
    exact hb.trans (add_nonneg hα hc)
  · calc (∑ b,productWeight (fun i=>bernoulli (d i)) b*
          (minimum v (fun i=>a i && !b i)-minimum v a))
        ≤ ∑ b,productWeight (fun i=>bernoulli (d i)) b*(if b i then 1 else 0) :=
          sum_le_sum (fun b _=>mul_le_mul_of_nonneg_left (minimum_retirement hv a b hai hm) (hw b))
      _ = d i := by
        rw [product_marginal (fun i=>bernoulli (d i)) (fun i=>bernoulli_sum _) i (fun b=>if b then 1 else 0)]
        simp [bernoulli]
      _ ≤ α+∑ j∈C,if a j then 1 else 0 := by
        by_cases hi : i∈C
        · have hb : (1:ℝ) ≤ ∑ j∈C,if a j then 1 else 0 := by
            have hh:=single_le_sum (f := fun j=>if a j then (1:ℝ) else 0)
              (fun j _=>by split_ifs <;> norm_num) hi
            simpa [hai] using hh
          linarith [(hd i).2]
        · exact (hnc i hi).trans (le_add_of_nonneg_right hc)

lemma profile_retirement_bound {q d v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hd : ∀ i,d i∈Set.Icc 0 1) (hv : ∀ i,0 ≤ v i) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → d i ≤ α) :
    profile (fun i=>q i*(1-d i)) v-profile q v ≤ α+∑ i∈C,q i := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  have hws:=productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)
  rw [profile_thinning,profile,←sum_sub_distrib]
  have he : (∑ a,productWeight (fun i=>bernoulli (q i)) a*(α+∑ i∈C,if a i then 1 else 0))=
      α+∑ i∈C,q i := by
    simp_rw [mul_add,mul_sum]
    rw [sum_add_distrib,←sum_mul,hws,one_mul,sum_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [product_marginal (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _) i (fun b=>if b then 1 else 0)]
    simp [bernoulli]
  rw [←he]
  apply sum_le_sum
  intro a _
  rw [←mul_sub]
  exact mul_le_mul_of_nonneg_left (conditional_retirement hv hd a hα C hnc) (hw a)

lemma minimum_force_le (v : I → ℝ) (a : I → Bool) (i : I) :
    minimum v (Function.update a i true) ≤ minimum v a := by
  apply le_minimum (minimum_le_one _ _)
  intro j hj
  apply minimum_le
  by_cases hji : j=i
  · subst j; simp
  · simp [Function.update_of_ne hji,hj]

lemma forced_expectation (q : I → ℝ) (i : I) (f : (I → Bool) → ℝ) :
    (∑ a,productWeight (fun i=>bernoulli (q i)) a*f (Function.update a i true))=
      ∑ a,productWeight (fun j=>bernoulli (Function.update q i 1 j)) a*f a := by
  have he (a : I → Bool) : Function.update a i true=(fun j=>if j=i then true else a j) := by
    funext j; by_cases hj : j=i <;> simp [hj,Function.update_of_ne]
  simp_rw [he]
  rw [product_pushforward (fun i=>bernoulli (q i)) (fun j b=>if j=i then true else b) f]
  apply sum_congr rfl
  intro a _
  congr 1
  apply prod_congr rfl
  intro j _
  by_cases hji : j=i
  · subst j
    cases a i <;> simp [bernoulli]
  · cases a j <;> simp [hji,Function.update_of_ne,bernoulli]

lemma profile_insertion_le {q : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1) (v : I → ℝ) (i : I) :
    profile (Function.update q i 1) v ≤ profile q v := by
  rw [profile,←forced_expectation]
  apply sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (minimum_force_le v a i)
    (productWeight_nonneg (fun i=>bernoulli_nonneg (hq i)) a)

lemma weight_zero_at {q : I → ℝ} {a : I → Bool} {i : I} (h : bernoulli (q i) (a i)=0) :
    productWeight (fun i=>bernoulli (q i)) a=0 := prod_eq_zero (mem_univ i) h

lemma profile_one {q v : I → ℝ} (h : ∀ i,q i≠0 → 1 ≤ v i) : profile q v=1 := by
  calc profile q v=∑ a,productWeight (fun i=>bernoulli (q i)) a := by
        apply sum_congr rfl
        intro a _
        by_cases hw : productWeight (fun i=>bernoulli (q i)) a=0
        · simp [hw]
        · have hm : minimum v a=1 := by
            apply le_antisymm (minimum_le_one _ _)
            apply le_minimum le_rfl
            intro i hi
            apply h i
            intro hq
            exact hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hq]))
          rw [hm,mul_one]
    _ = 1 := productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)

lemma profile_zero_of_certain {q v : I → ℝ} (hv : ∀ i,0 ≤ v i) {i : I}
    (hqi : q i=1) (hvi : v i=0) : profile q v=0 := by
  apply sum_eq_zero
  intro a _
  cases hai : a i
  · rw [weight_zero_at (i := i) (by simp [bernoulli,hai,hqi]),zero_mul]
  · have hm : minimum v a=0 := le_antisymm ((minimum_le v hai).trans_eq hvi) (minimum_nonneg hv a)
    rw [hm,mul_zero]

lemma minimum_lipschitz {v w : I → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ i,|v i-w i| ≤ L) (a : I → Bool) : |minimum v a-minimum w a| ≤ L := by
  have hdir (v w : I → ℝ) (h : ∀ i,v i-w i ≤ L) : minimum v a-minimum w a ≤ L := by
    suffices minimum v a-L ≤ minimum w a by linarith
    apply le_minimum (by linarith [minimum_le_one v a])
    intro i hi
    linarith [minimum_le v hi,h i]
  rw [abs_sub_le_iff]
  exact ⟨hdir v w (fun i=>(le_abs_self _).trans (h i)),
    hdir w v (fun i=>by linarith [(neg_le_abs (v i-w i)).trans (h i)])⟩

lemma profile_lipschitz {q v w : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1) {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ i,|v i-w i| ≤ L) : |profile q v-profile q w| ≤ L := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  unfold profile
  rw [←sum_sub_distrib]
  calc |∑ a,(productWeight (fun i=>bernoulli (q i)) a*minimum v a-
        productWeight (fun i=>bernoulli (q i)) a*minimum w a)|
      ≤ ∑ a,|productWeight (fun i=>bernoulli (q i)) a*minimum v a-
        productWeight (fun i=>bernoulli (q i)) a*minimum w a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,productWeight (fun i=>bernoulli (q i)) a*L := by
      apply sum_le_sum
      intro a _
      rw [←mul_sub,abs_mul,abs_of_nonneg (hw a)]
      exact mul_le_mul_of_nonneg_left (minimum_lipschitz hL h a) (hw a)
    _ = L := by rw [←sum_mul,productWeight_sum _ (fun i=>bernoulli_sum _),one_mul]

lemma minimum_cut {v : I → ℝ} (hv : ∀ i,v i ≤ 1) (a : I → Bool) :
    minimum v a=minimum v (fun i=>if v i<1 then a i else false) := by
  apply le_antisymm
  · apply le_minimum (minimum_le_one _ _)
    intro i hi
    split_ifs at hi with hh
    · exact minimum_le v hi
  · apply le_minimum (minimum_le_one _ _)
    intro i hi
    by_cases hh : v i<1
    · exact minimum_le v (i := i) (by simp [hh,hi])
    · exact (minimum_le_one _ _).trans_eq (le_antisymm (hv i) (le_of_not_gt hh)).symm

lemma profile_cut {q v : I → ℝ} (hv : ∀ i,v i ≤ 1) :
    profile q v=profile (fun i=>if v i<1 then q i else 0) v := by
  unfold profile
  have he (a : I → Bool) := minimum_cut hv a
  conv_lhs => arg 2; ext a; rw [he]
  rw [product_pushforward (fun i=>bernoulli (q i)) (fun i b=>if v i<1 then b else false) (minimum v)]
  apply sum_congr rfl
  intro a _
  congr 1
  apply prod_congr rfl
  intro i _
  by_cases hi : v i<1 <;> cases a i <;> simp [hi,bernoulli]

lemma profile_irrelevant {q q' v : I → ℝ} (hv : ∀ i,v i ≤ 1)
    (he : ∀ i,v i<1 → q i=q' i) : profile q v=profile q' v := by
  rw [profile_cut hv,profile_cut (q := q') hv]
  congr 1
  funext i
  by_cases hi : v i<1 <;> simp [hi,he i]

/-- Only compulsory candidates whose ramps are below one need be counted. -/
lemma profile_retirement_local {q d v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hd : ∀ i,d i∈Set.Icc 0 1) (hv : ∀ i,v i∈Set.Icc 0 1) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → v i<1 → d i ≤ α) :
    profile (fun i=>q i*(1-d i)) v-profile q v ≤ α+∑ i∈C,q i := by
  let d' : I → ℝ := fun i=>if v i<1 then d i else 0
  have he : profile (fun i=>q i*(1-d i)) v=profile (fun i=>q i*(1-d' i)) v := by
    apply profile_irrelevant (fun i=>(hv i).2)
    intro i hi
    simp [d',hi]
  rw [he]
  apply profile_retirement_bound hq (fun i=>?_) (fun i=>(hv i).1) hα C (fun i hi=>?_)
  · dsimp [d']
    split_ifs
    · exact hd i
    · exact ⟨le_rfl,zero_le_one⟩
  · dsimp [d']
    split_ifs with hh
    · exact hnc i hi hh
    · exact hα


/-- Coordinates with zero presence probability carry no information about
an expected profile. This is the exact causality fact for unused ordinals. -/
lemma profile_values_congr {q v w : I → ℝ}
    (h : ∀ i,q i≠0 → v i=w i) : profile q v=profile q w := by
  apply sum_congr rfl
  intro a _
  by_cases hw : productWeight (fun i=>bernoulli (q i)) a=0
  · simp [hw]
  · congr 1
    apply le_antisymm
    · apply le_minimum (minimum_le_one _ _)
      intro i hi
      have hq : q i≠0 := fun hz=>hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hz]))
      rw [←h i hq]
      exact minimum_le v hi
    · apply le_minimum (minimum_le_one _ _)
      intro i hi
      have hq : q i≠0 := fun hz=>hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hz]))
      rw [h i hq]
      exact minimum_le w hi

end KServer.RosterExpectation

end


/-! The genuine deterministic expected short-roster profile in §07, on the
finite preallocated set of insertion ordinals. The auxiliary lifetimes are
not the actual partition lifetimes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ShortRoster
open Chronological RosterLifetimes
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exact increasing clipped ramp on [1/8,1/4]. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (8*u-1))
lemma ramp_bounds (u : ℝ) : ramp u∈Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 1/8) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : 8*u-1 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 1/4 ≤ u) : ramp u=1 :=
  min_eq_left ((by linarith : 1 ≤ 8*u-1).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ 8*|u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;> simp only [min_def,max_def] <;> split_ifs <;>
    have h1:=le_abs_self (u-v) <;> have h2:=neg_le_abs (u-v) <;> linarith

lemma rate_bounds {K : ℕ} (hK : 2 ≤ K) : 1/Real.sqrt K∈Set.Icc (0:ℝ) 1 := by
  have hs : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ K by omega))
  exact ⟨by positivity,(div_le_one (by linarith)).mpr hs⟩
lemma short_bounds {K : ℕ} (hK : 2 ≤ K) (a : ℕ) : shortPresence K a∈Set.Icc (0:ℝ) 1 := by
  unfold shortPresence
  split_ifs
  · exact survive_range (rate_bounds hK) a
  · exact ⟨le_rfl,zero_le_one⟩

variable {Y : Type*} [MetricSpace Y] {H : ℕ}

def probability (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (i : Fin H) : ℝ :=
  if (i:ℕ)∈S then shortPresence K (age request S (20*r) i) else 0

def values (request : ℕ → Y) (r : ℝ) (p : Y) (i : Fin H) : ℝ := ramp (dist (request i) p/r)

def profile (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (p : Y) : ℝ :=
  RosterExpectation.profile (probability (H := H) request r K S) (values request r p)

lemma probability_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (i : Fin H) : probability request r K S i∈Set.Icc (0:ℝ) 1 := by
  unfold probability
  split_ifs
  · exact short_bounds hK _
  · exact ⟨le_rfl,zero_le_one⟩
lemma profile_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) : profile (H := H) request r K S p∈Set.Icc (0:ℝ) 1 :=
  RosterExpectation.profile_bounds (probability_bounds request r hK S) (fun _=>ramp_bounds _)

lemma values_lipschitz (request : ℕ → Y) {r : ℝ} (hr : 0<r) (p q : Y) (i : Fin H) :
    |values request r p i-values request r q i| ≤ 8*dist p q/r := by
  have hl:=ramp_lipschitz (dist (request i) p/r) (dist (request i) q/r)
  have hd : |dist (request i) p-dist (request i) q| ≤ dist p q := by
    simpa only [dist_comm (request i)] using abs_dist_sub_le p q (request i)
  rw [←sub_div,abs_div,abs_of_pos hr] at hl
  exact hl.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hd hr.le) (by norm_num : (0:ℝ) ≤ 8))

lemma profile_lipschitz (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p q : Y) : |profile (H := H) request r K S p-profile (H := H) request r K S q| ≤ 8*dist p q/r :=
  RosterExpectation.profile_lipschitz (probability_bounds request r hK S)
    (by positivity) (values_lipschitz request hr p q)

/-- Death trials for one actual age increment, including the compulsory
cutoff. Already absent records are assigned probability zero. -/
def death (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (t : Fin H) (i : Fin H) : ℝ :=
  if (i:ℕ)∈S ∧ age request S (20*r) i<K ∧ dist (request i) (request t) ≤ 20*r
  then if age request S (20*r) i+1<K then 1/Real.sqrt K else 1 else 0

lemma death_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t i : Fin H) : death request r K S t i∈Set.Icc (0:ℝ) 1 := by
  unfold death
  split_ifs
  · exact rate_bounds hK
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨le_rfl,zero_le_one⟩

lemma probability_insert (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) :
    probability (H := H) request r K (insert (t:ℕ) S)=
      Function.update (fun i=>probability request r K S i*(1-death request r K S t i)) t 1 := by
  have ht : (t:ℕ)∉S := fun h=>Nat.lt_irrefl _ (hbefore _ h)
  funext i
  by_cases hit : i=t
  · subst i
    simp [probability,age_new request S (20*r) hbefore,short_new (show 0<K by omega)]
  · have hin : (i:ℕ)≠(t:ℕ) := fun h=>hit (Fin.ext h)
    rw [Function.update_of_ne hit]
    by_cases hi : (i:ℕ)∈S
    · have he:=age_insert request S (20*r) ht (hbefore i hi)
      by_cases hd : dist (request i) (request t) ≤ 20*r
      · rw [ite_eq_left hd] at he
        by_cases ha : age request S (20*r) i<K
        · by_cases ha' : age request S (20*r) i+1<K
          · have hh : age request (insert (t:ℕ) S) (20*r) i<K := by omega
            simp [probability,hi,hin,he,death,ha,ha',hd,shortPresence,survive,pow_succ]
          · have hh : ¬age request (insert (t:ℕ) S) (20*r) i<K := by omega
            simp [probability,hi,hin,he,death,ha,ha',hd,shortPresence,survive]
        · have hh : ¬age request S (20*r) i+1<K := by omega
          simp [probability,hi,hin,he,death,ha,hh,hd,shortPresence]
      · simp only [ite_eq_right hd,add_zero] at he
        simp [probability,hi,hin,he,death,hd]
    · simp [probability,hin,hi,death]

lemma profile_unit_drop (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ))
    (htest : ¬∃ i∈S,age request S (20*r) i<K ∧ dist (request i) (request t) ≤ r/2)
    {p : Y} (hp : dist (request t) p ≤ r/8) :
    profile (H := H) request r K S p-profile (H := H) request r K (insert (t:ℕ) S) p=1 := by
  have hold : profile (H := H) request r K S p=1 := by
    apply RosterExpectation.profile_one
    intro i hi
    have hIS : (i:ℕ)∈S := by by_contra hn; exact hi (by simp [probability,hn])
    have hage : age request S (20*r) i<K := by
      by_contra hn
      exact hi (by simp [probability,hIS,shortPresence,hn])
    have hd : r/2<dist (request i) (request t) := lt_of_not_ge (fun hd=>htest ⟨i,hIS,hage,hd⟩)
    have hdp : r/4 ≤ dist (request i) p := by
      have hd':=dist_triangle (request i) p (request t)
      rw [dist_comm p (request t)] at hd'
      linarith
    rw [values,ramp_one ((le_div_iff₀ hr).mpr (by linarith))]
  have hnew : profile (H := H) request r K (insert (t:ℕ) S) p=0 := by
    apply RosterExpectation.profile_zero_of_certain (fun i=>(ramp_bounds _).1) (i := t)
    · rw [probability_insert request r hK S t hbefore]
      simp
    · exact ramp_zero ((div_le_iff₀ hr).mpr (by linarith))
  rw [hold,hnew,sub_zero]

lemma values_lt_one (request : ℕ → Y) {r : ℝ} (hr : 0<r) {p : Y} {i : Fin H}
    (hi : values request r p i<1) : dist (request i) p<r/4 := by
  by_contra hn
  have hh:=ramp_one ((le_div_iff₀ hr).mpr (by linarith [le_of_not_gt hn] : (1:ℝ)/4*r ≤ dist (request i) p))
  change ramp (dist (request i) p/r)<1 at hi
  rw [hh] at hi
  exact lt_irrefl _ hi

/-- Compulsory candidates that can actually affect the ramp at a test point. -/
def compulsory (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (p : Y) : Finset (Fin H) :=
  univ.filter (fun i=>(i:ℕ)∈S ∧ age request S (20*r) i=K-1 ∧ dist (request i) p<r/4)

lemma compulsory_count (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) : (compulsory (H := H) request r K S p).card ≤ K := by
  let C:=compulsory (H := H) request r K S p
  have hinj : Function.Injective (fun i : Fin H=>(i:ℕ)) := Fin.val_injective
  have he : (C.image (fun (i : Fin H)=>(i:ℕ))).card=C.card := card_image_of_injective C hinj
  rw [←he]
  apply local_age_count request S _ (20*r) K
  · intro n hn
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    subst n
    exact (mem_filter.mp hi).2.1
  · intro n hn
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    subst n
    have hage:=(mem_filter.mp hi).2.2.1
    omega
  · intro n hn m hm
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    obtain ⟨j,hj,hf⟩:=mem_image.mp hm
    subst n
    subst m
    have hi':=(mem_filter.mp hi).2.2.2
    have hj':=(mem_filter.mp hj).2.2.2
    have hd:=dist_triangle (request i) p (request j)
    rw [dist_comm p (request j)] at hd
    linarith

lemma compulsory_mass (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) :
    (∑ i∈compulsory (H := H) request r K S p,probability request r K S i) ≤
      (K:ℝ)*survive (1/Real.sqrt K) (K-1) := by
  let C:=compulsory (H := H) request r K S p
  have he : (∑ i∈C,probability request r K S i)=(C.card:ℝ)*survive (1/Real.sqrt K) (K-1) := by
    calc (∑ i∈C,probability request r K S i)=∑ _i∈C,survive (1/Real.sqrt K) (K-1) := by
          apply sum_congr rfl
          intro i hi
          obtain ⟨hi,ha,_⟩:=(mem_filter.mp hi).2
          simp [probability,hi,shortPresence,ha,show K-1<K by omega]
      _ = _ := by simp
  change (∑ i∈C,probability request r K S i) ≤ _
  rw [he]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast compulsory_count (H := H) request hr hK S p)
    (survive_range (rate_bounds hK) (K-1)).1

/-- The exact short-roster retirement bound, including compulsory deaths,
is uniform in the number of chronological records and the horizon. -/
theorem profile_error (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) (p : Y) :
    profile (H := H) request r K (insert (t:ℕ) S) p-profile (H := H) request r K S p ≤ 49/Real.sqrt K := by
  let q:=probability (H := H) request r K S
  let d:=death request r K S t
  let v:=values (H := H) request r p
  have hq : ∀ i,q i∈Set.Icc 0 1 := probability_bounds request r hK S
  have hd : ∀ i,d i∈Set.Icc 0 1 := death_bounds request r hK S t
  have hv : ∀ i,v i∈Set.Icc 0 1 := fun i=>ramp_bounds _
  have hthin : ∀ i,q i*(1-d i)∈Set.Icc 0 1 := by
    intro i
    refine ⟨mul_nonneg (hq i).1 (by linarith [(hd i).2]),?_⟩
    exact (mul_le_mul_of_nonneg_left (by linarith [(hd i).1] : 1-d i ≤ 1) (hq i).1).trans (by simpa using (hq i).2)
  have hinst : profile (H := H) request r K (insert (t:ℕ) S) p ≤ RosterExpectation.profile (fun i=>q i*(1-d i)) v := by
    unfold profile
    rw [probability_insert request r hK S t hbefore]
    convert RosterExpectation.profile_insertion_le hthin v t using 1
    congr 1
    funext i
    by_cases hi : i=t <;> simp [hi,q,d]
  have hret := RosterExpectation.profile_retirement_local hq hd hv (rate_bounds hK).1
    (compulsory (H := H) request r K S p) (fun i hi hvi=>by
      dsimp [d,death]
      split_ifs with ha ha'
      · rfl
      · apply False.elim
        apply hi
        apply mem_filter.mpr
        refine ⟨mem_univ _,ha.1,?_,values_lt_one request hr hvi⟩
        omega
      · exact (rate_bounds hK).1)
  have hmass:=compulsory_mass (H := H) request hr hK S p
  have hbound:=short_retirement_bound K hK
  change RosterExpectation.profile (fun i=>q i*(1-d i)) v-
    profile (H := H) request r K S p ≤ _ at hret
  linarith

lemma profile_outside (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) {p : Y}
    (hp : 21*r<dist (request t) p) :
    profile (H := H) request r K S p=profile (H := H) request r K (insert (t:ℕ) S) p := by
  unfold profile
  apply RosterExpectation.profile_irrelevant (fun i=>(ramp_bounds _).2)
  intro i hi
  have hdist:=values_lt_one request hr hi
  have hit : i≠t := by intro h; subst i; linarith
  have hfar : ¬dist (request i) (request t) ≤ 20*r := by
    intro hh
    have ht:=dist_triangle (request t) (request i) p
    rw [dist_comm (request t) (request i)] at ht
    linarith
  rw [probability_insert request r hK S t hbefore,Function.update_of_ne hit]
  simp [death,hfar]

lemma profile_increase_support (request : ℕ → Y) {r : ℝ} (hr : 0<r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ))
    (htest : ¬∃ i∈S,age request S (20*r) i<K ∧ dist (request i) (request t) ≤ r/2)
    {p : Y} (hp : profile (H := H) request r K S p<profile (H := H) request r K (insert (t:ℕ) S) p) :
    r/8<dist (request t) p ∧ dist (request t) p ≤ 21*r := by
  constructor
  · by_contra hn
    have he:=profile_unit_drop request hr hK S t hbefore htest (le_of_not_gt hn)
    linarith
  · by_contra hn
    have he:=profile_outside request hr hK S t hbefore (lt_of_not_ge hn)
    linarith


lemma age_congr {request request' : ℕ → Y} {S : Finset ℕ} {r : ℝ} {i : ℕ}
    (hi : request i=request' i) (h : ∀ j∈S,request j=request' j) :
    age request S r i=age request' S r i := by
  unfold age
  congr 1
  apply filter_congr
  intro j hj
  rw [hi,h j hj]

lemma profile_congr {request request' : ℕ → Y} {S : Finset ℕ}
    (h : ∀ j∈S,request j=request' j) (r : ℝ) (K : ℕ) (p : Y) :
    profile (H := H) request r K S p=profile (H := H) request' r K S p := by
  have hq : probability (H := H) request r K S=probability request' r K S := by
    funext i
    unfold probability
    split_ifs with hi
    · rw [age_congr (h i hi) h]
    · rfl
  unfold profile
  rw [hq]
  apply RosterExpectation.profile_values_congr
  intro i hi
  have hIS : (i:ℕ)∈S := by by_contra hn; exact hi (by simp [probability,hn])
  simp only [values,h i hIS]

end KServer.ShortRoster

end

end OAI
