import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryDelta
import OAI.Probability.CriticalPercolation.Entropy.FiberValue

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

noncomputable def freeze (D : Set E) (σ ω : E → A) : E → A :=
  fun e => if e ∈ D then σ e else ω e

omit [Fintype E] [Fintype A] in
lemma freeze_self (D : Set E) (σ ω : E → A) (h : ∀ e ∈ D, σ e = ω e) :
    freeze D σ ω = ω := by
  funext e
  by_cases he : e ∈ D <;> simp [freeze,he,h]

omit [Fintype E] [Fintype A] in
lemma freeze_depends (D : Set E) (σ : E → A) {X : Type*} (f : (E → A) → X) :
    DependsOn (fun ω => f (freeze D σ ω)) Dᶜ := by
  intro ω η h
  apply congrArg f
  funext e
  by_cases he : e ∈ D
  · simp [freeze,he]
  · simp only [freeze,ite_eq_right he]
    exact h e he

lemma expect_exposureLaw (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (D : Set E) (σ : E → A) (f : (E → A) → ℝ) :
    expect (exposureLaw w D σ) f = expect w (fun ω => f (freeze D σ ω)) := by
  have hv := exposureLaw_normalized w D σ hw
  calc
    _ = expect (exposureLaw w D σ) (fun ω => f (freeze D σ ω)) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : density (exposureLaw w D σ) ω = 0
      · simp only [hω,zero_mul]
      · dsimp only
        rw [freeze_self D σ ω (fun e he => (exposureLaw_support w D σ ω hω e he).symm)]
    _ = _ := expect_eq_on _ _ hv hw Dᶜ _ (freeze_depends D σ f)
      (fun e he => by funext a; have he' : e ∉ D := he; simp [exposureLaw,he'])

structure Exposure (E A B : Type*) where
  record : (E → A) → B
  domain : B → Set E
  bits : B → E → A
  atom : ∀ b, DependsOn (fun ω => record ω = b) (domain b)
  exact : ∀ ω e, e ∈ domain (record ω) → bits (record ω) e = ω e

namespace Exposure
variable (R : Exposure E A B)

lemma disintegrate (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (f : B → (E → A) → ℝ) :
    expect w (fun ω => f (R.record ω) ω) =
      expect w (fun ω => expect (exposureLaw w (R.domain (R.record ω))
        (R.bits (R.record ω))) (f (R.record ω))) := by
  simp_rw [expect_exposureLaw w hw]
  have hh := expect_exposure w hw R.record R.domain R.atom
    (fun b ω => f b (freeze (R.domain b) (R.bits b) ω))
    (fun b => freeze_depends _ _ _)
  convert hh using 1
  apply congrArg (expect w)
  funext ω
  rw [freeze_self _ _ _ (R.exact ω)]

lemma weighted_bound (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (hn : ∀ e a, 0 ≤ w e a) (g : B → ℝ) (hg : ∀ b, 0 ≤ g b)
    (f : B → (E → A) → ℝ) (C : ℝ)
    (hc : ∀ ω, expect (exposureLaw w (R.domain (R.record ω))
      (R.bits (R.record ω))) (f (R.record ω)) ≤ C) :
    expect w (fun ω => g (R.record ω) * f (R.record ω) ω) ≤
      C * expect w (fun ω => g (R.record ω)) := by
  rw [R.disintegrate w hw (fun b ω => g b * f b ω)]
  have he : ∀ b, expect (exposureLaw w (R.domain b) (R.bits b))
      (fun ω => g b*f b ω) = g b * expect (exposureLaw w (R.domain b) (R.bits b)) (f b) := by
    intro b
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [he]
  calc
    _ ≤ expect w (fun ω => g (R.record ω)*C) :=
      expect_mono hn (fun ω => mul_le_mul_of_nonneg_left (hc ω) (hg _))
    _ = _ := by rw [expect_mul_const]; ring

end Exposure
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def incidenceExposure (G : BondGraph V E) (S : Set V) :
    Exposure E Prop (ClusterObject V E) where
  record := fun ω => G.clusterObject ω S
  domain := fun C => G.incidentEdges C.1
  bits := Prod.snd
  atom := G.dependsOn_exact_clusterObject S
  exact := by
    intro ω e he
    apply propext
    change ω e ∧ e ∈ G.incidentEdges (G.clusterObject ω S).1 ↔ ω e
    exact ⟨fun h => h.1,fun h => ⟨h,he⟩⟩

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma clusterObject_cut_closed (ω : Set E) (S : Set V) :
    ∀ e ∈ G.cutEdges (G.clusterObject ω S).1, ¬(G.clusterObject ω S).2 e := by
  rintro e ⟨x,y,he,hx,hy⟩ ⟨hω,_⟩
  exact hx (G.openBond_roots hω (by simp [he] : y ∈ G.ends e)
    (by simp [he] : x ∈ G.ends e) hy)

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def scheduledContact (order : List (LazyDFS.Dart V E))
    (B : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ)
    (C : ClusterObject V E) (ω : E → Prop) : ℝ :=
  if a ∈ C.1 then 1 else
    (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
      (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω

lemma scheduledContact_second (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (B S : Set V) (hBS : B ⊆ S) (a : V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (σ : Set E) :
    let C := G.clusterObject σ S
    expect (exposureLaw w (G.incidentEdges C.1) C.2)
      (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) ≤ 4 := by
  dsimp only
  let C := G.clusterObject σ S
  let v := exposureLaw w (G.incidentEdges C.1) C.2
  have hw := homogeneous_normalized w p h0 h1
  have hv := exposureLaw_normalized w (G.incidentEdges C.1) C.2 hw
  have hn := exposureLaw_nonneg w (G.incidentEdges C.1) C.2
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
  by_cases ha : a ∈ C.1
  · have hh : (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) =
        (fun _ : E → Prop => (1 : ℝ)) := by
      funext ω
      simp [scheduledContact,ha]
    change expect v _ ≤ 4
    rw [hh,expect_const _ hv]
    norm_num
  · have hB : B ⊆ C.1 := by
      intro b hb
      exact ⟨b,hBS hb,SimpleGraph.Reachable.refl b⟩
    have hm := LazyDFS.search_contact_moments_exposure G order ho B C.1 a ha hB C.2
      (G.clusterObject_cut_closed σ S) p hp w h0 h1
    let A := (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
      (fun ω => ∃ b ∈ B, (G.openGraph ω).Reachable a b) w
    have he : (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) =
        (fun ω => (max 1 (A ω))^2) := by
      funext ω
      simp only [scheduledContact,ite_eq_right ha,A]
    change expect v _ ≤ 4
    rw [he]
    calc
      _ ≤ expect v (fun ω => 1+(A ω)^2) := expect_mono hn (fun ω => by
        by_cases hh : A ω ≤ 1
        · rw [max_eq_left hh]
          nlinarith [sq_nonneg (A ω)]
        · rw [max_eq_right (le_of_not_ge hh)]
          linarith)
      _ = 1 + expect v (fun ω => (A ω)^2) := by
        rw [expect_add v (fun _ => 1) (fun ω => (A ω)^2),expect_const v hv]
      _ ≤ 4 := by linarith [hm.2]

end CriticalPercolation.BondGraph

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_contactScore_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) :
    (compile G order B fuel st stack).contactScore p C F w ω =
      (compile G order B fuel st stack).contactScore p C F w η := by
  induction fuel generalizing st stack w with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hst
        · have htail : d.1 ∈ st.reached := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inr ht)))
          have hinc : ∃ r ∈ G.ends d.2.1, (G.openGraph ω).Reachable a r :=
            ⟨d.1,by simp [he],hst d.1 htail⟩
          simp only [contactScore,←propext (h d.2.1 hinc)]
          by_cases hopen : ω d.2.1
          · simp only [ite_eq_left hopen]
            have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                (G.openGraph ω).Reachable a v := by
              intro v hv
              rcases Finset.mem_insert.mp hv with rfl | hv
              · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
              · exact hst v hv
            exact congrArg (_ + ·) (ih _ _ _ hs')
          · simp only [ite_eq_right hopen]
            exact congrArg (_ + ·) (ih (st.closed d.2.1) rest (pin w d.2.1 False) hst)

variable [Fintype V]
lemma search_contactScore_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ)
    (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g)) :
    (search G order a B).contactScore p C F w ω =
      (search G order a B).contactScore p C F w η := by
  exact compile_contactScore_incidence G order B _ _ _ p C F w ω η a h
    (fun v hv => by have he : v=a := Finset.mem_singleton.mp hv; subst v; exact .refl _)

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.FiniteProduct.Exposure
variable {E A B : Type*} (R : Exposure E A B)
lemma bits_congr {ω η : E → A} (h : R.record ω = R.record η) {e : E}
    (he : e ∈ R.domain (R.record ω)) : ω e = η e := by
  rw [←R.exact ω e he,h]
  exact R.exact η e (h ▸ he)
end CriticalPercolation.FiniteProduct.Exposure

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} [Fintype E] [Fintype V] (G : BondGraph V E)

omit [Fintype E] [Fintype V] in
lemma clusterObject_refines {S T : Set V} (hST : S ⊆ T) (ω η : Set E)
    (h : G.clusterObject ω T = G.clusterObject η T) :
    G.clusterObject ω S = G.clusterObject η S := by
  apply Eq.symm
  apply G.clusterObject_eq_of_incident rfl
  intro e he
  have he' : e ∈ G.incidentEdges (G.clusterObject ω T).1 := by
    rcases he with ⟨v,⟨a,ha,hav⟩,hv⟩
    exact ⟨v,⟨a,hST ha,hav⟩,hv⟩
  exact ((G.incidenceExposure T).bits_congr h he').to_iff

variable [DecidableEq V] [DecidableEq E]
lemma scheduledContact_record (order : List (LazyDFS.Dart V E))
    (B S T : Set V) (a : V) (hST : S ⊆ T) (ha : a ∈ T)
    (p : ℝ) (w : E → Prop → ℝ) (ω η : E → Prop)
    (h : G.clusterObject ω T = G.clusterObject η T) :
    G.scheduledContact order B a p w (G.clusterObject ω S) ω =
      G.scheduledContact order B a p w (G.clusterObject η S) η := by
  have hC := G.clusterObject_refines hST ω η h
  unfold scheduledContact
  rw [←hC]
  split_ifs with hhold
  · rfl
  · apply LazyDFS.search_contactScore_incidence
    rintro e ⟨v,hv,hav⟩
    exact ((G.incidenceExposure T).bits_congr h ⟨v,⟨a,ha,hav⟩,hv⟩).to_iff

end CriticalPercolation.BondGraph

namespace CriticalPercolation.FiniteProduct
open scoped Classical
open FiniteEntropy

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

theorem sequential_bound (R : ℕ → Exposure E A B) (step : ℕ → B → (E → A) → ℝ)
    (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (hn : ∀ e a, 0 ≤ w e a)
    (hs : ∀ i b ω, 0 ≤ step i b ω) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ i ω, expect (exposureLaw w ((R i).domain ((R i).record ω))
      ((R i).bits ((R i).record ω))) (step i ((R i).record ω)) ≤ C)
    (hpast : ∀ i n, i<n → ∀ ω η, (R n).record ω = (R n).record η →
      step i ((R i).record ω) ω = step i ((R i).record η) η) (n : ℕ) :
    expect w (fun ω => ∏ i ∈ Finset.range n, step i ((R i).record ω) ω) ≤ C^n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,pow_zero,expect_const _ hw,le_refl]
  | succ n ih =>
    let f : (E → A) → ℝ := fun ω => ∏ i ∈ Finset.range n, step i ((R i).record ω) ω
    let g := fiberValue (R n).record f
    have hfn : ∀ ω, 0 ≤ f ω := fun ω => Finset.prod_nonneg (fun i _ => hs i _ ω)
    have hgn : ∀ b, 0 ≤ g b := fiberValue_nonneg _ _ hfn
    have hg : ∀ ω, g ((R n).record ω) = f ω := by
      apply fiberValue_apply
      intro ω η he
      exact Finset.prod_congr rfl (fun i hi => hpast i n (Finset.mem_range.mp hi) ω η he)
    calc
      _ = expect w (fun ω => g ((R n).record ω) * step n ((R n).record ω) ω) := by
        apply congrArg (expect w)
        funext ω
        rw [hg,Finset.prod_range_succ]
      _ ≤ C * expect w (fun ω => g ((R n).record ω)) :=
        (R n).weighted_bound w hw hn g hgn (step n) C (hstep n)
      _ = C * expect w f := by simp_rw [hg]
      _ ≤ C*C^n := mul_le_mul_of_nonneg_left ih hC
      _ = C^(n+1) := by rw [pow_succ]; ring

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*}

def anchorSet (S : Set V) (a : ℕ → V) (n : ℕ) : Set V :=
  S ∪ a '' {i | i<n}

lemma anchorSet_mono (S : Set V) (a : ℕ → V) {i n : ℕ} (hi : i ≤ n) :
    anchorSet S a i ⊆ anchorSet S a n := by
  rintro v (hv|⟨j,hj,rfl⟩)
  · exact Or.inl hv
  · exact Or.inr ⟨j,lt_of_lt_of_le hj hi,rfl⟩

lemma anchor_mem_anchorSet (S : Set V) (a : ℕ → V) {i n : ℕ} (hi : i<n) :
    a i ∈ anchorSet S a n := Or.inr ⟨i,hi,rfl⟩

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem scheduled_contact_product (G : BondGraph V E)
    (order : List (LazyDFS.Dart V E)) (ho : LazyDFS.Exhaustive G order)
    (S : Set V) (a : ℕ → V) (B : ℕ → Set V) (hB : ∀ i, B i ⊆ anchorSet S a i)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (n : ℕ) :
    expect w (fun ω => ∏ i ∈ Finset.range n,
      (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (anchorSet S a i)) ω))^2) ≤ 4^n := by
  apply sequential_bound (fun i => G.incidenceExposure (anchorSet S a i))
    (fun i C ω => (max 1 (G.scheduledContact order (B i) (a i) p w C ω))^2)
    w (homogeneous_normalized w p h0 h1)
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
    (fun _ _ _ => sq_nonneg _) 4 (by norm_num)
  · intro i ω
    exact G.scheduledContact_second order ho (B i) (anchorSet S a i) (hB i) (a i) hp w h0 h1 ω
  · intro i k hik ω η he
    congr 2
    exact G.scheduledContact_record order (B i) (anchorSet S a i) (anchorSet S a k) (a i)
      (anchorSet_mono S a hik.le) (anchor_mem_anchorSet S a hik) p w ω η he

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem scheduled_contact_exponential (G : BondGraph V E)
    (order : List (LazyDFS.Dart V E)) (ho : LazyDFS.Exhaustive G order)
    (S : Set V) (a : ℕ → V) (B : ℕ → Set V) (hB : ∀ i, B i ⊆ anchorSet S a i)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    expect w (fun ω => Real.exp (2*∑ i ∈ I,
      Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (anchorSet S a i)) ω)))) ≤ Real.exp (n*Real.log 4) := by
  let A := fun i ω => G.scheduledContact order (B i) (a i) p w
    (G.clusterObject ω (anchorSet S a i)) ω
  have hpow (ω : E → Prop) : Real.exp (2*∑ i ∈ I, Real.log (max 1 (A i ω))) =
      ∏ i ∈ I, (max 1 (A i ω))^2 := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [two_mul,Real.exp_add,Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    ring
  change expect w (fun ω => Real.exp (2*∑ i ∈ I, Real.log (max 1 (A i ω)))) ≤ _
  simp_rw [hpow]
  calc
    _ ≤ expect w (fun ω => ∏ i ∈ Finset.range n, (max 1 (A i ω))^2) := by
      apply expect_mono (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      intro ω
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hI
      · intro i _; exact sq_nonneg _
      · intro i _ _
        have hh : (1:ℝ) ≤ max 1 (A i ω) := le_max_left _ _
        nlinarith
    _ ≤ 4^n := G.scheduled_contact_product order ho S a B hB hp w h0 h1 n
    _ = Real.exp (n*Real.log 4) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]

end CriticalPercolation.BondGraph

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

theorem contactScore_eq_queryDelta_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) :
    T.contactScore p C F w ω = ∑ e, if e ∈ C then p*T.queryDelta F w ω e else 0 := by
  induction T generalizing used w with
  | done _ => simp [contactScore,queryDelta]
  | ask f l r hl hr =>
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, if e ∈ C then
          p*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
        (if f ∈ C then p*delta w F f else 0) +
          ∑ e, if e ∈ C then p*T'.queryDelta F w' ω e else 0 := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if e ∈ C then
          p*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
          (if e = f then (if f ∈ C then p*delta w F f else 0) else 0) +
          (if e ∈ C then p*T'.queryDelta F w' ω e else 0) := by
        by_cases he : e = f
        · subst e; rw [hz]; simp
        · simp only [ite_eq_right he,zero_add]
      simp only [heq,Finset.sum_add_distrib]
      simp
    change (if f ∈ C then p*delta w F f else 0) +
      (if ω f then r.contactScore p C F (pin w f True) ω
       else l.contactScore p C F (pin w f False) ω) = _
    by_cases hf : ω f
    · simp only [ite_eq_left hf,queryDelta]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
    · simp only [ite_eq_right hf,queryDelta]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def contactWeight (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E) : ℝ :=
  if e ∈ G.cutEdges O then p*(LazyDFS.search G order a B).queryDelta
    (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω e else 0

lemma sum_contactWeight (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) :
    (∑ e, G.contactWeight order B O a p w ω e) =
      (LazyDFS.search G order a B).contactScore p (G.cutEdges O)
        (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω := by
  exact (contactScore_eq_queryDelta_sum _ ∅ (LazyDFS.compile_valid G order B _ _ _)
    p _ _ w ω).symm

lemma contactWeight_nonneg (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) (e : E) :
    0 ≤ G.contactWeight order B O a p w ω e := by
  unfold contactWeight
  split_ifs
  · apply mul_nonneg hp.1.le
    apply queryDelta_nonneg _ ∅ (LazyDFS.compile_valid G order B _ _ _) hp _ _ w
      (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      (fun e _ => ⟨h0 e,h1 e⟩)
    rintro s t hst ⟨b,hb,hr⟩
    exact ⟨b,hb,hr.mono (G.openGraph_mono hst)⟩
  · exact le_rfl

noncomputable def contactKernel (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e /
        prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)

lemma contactKernel_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) :
    0 ≤ G.contactKernel order B a p w C ω mark := by
  unfold contactKernel
  by_cases ha : a ∈ C.1
  · rw [ite_eq_left ha]
    split_ifs <;> norm_num
  · rw [ite_eq_right ha]
    cases mark with
    | none => exact le_rfl
    | some e =>
      exact div_nonneg (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e)
        (prob_nonneg w (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)

theorem contactKernel_normalized (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (B S : Set V) (hBS : B ⊆ S) (a : V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hh : 0 < prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b))
    (σ : Set E) :
    let C := G.clusterObject σ S
    expect (exposureLaw w (G.incidentEdges C.1) C.2)
      (fun ω => ∑ m, G.contactKernel order B a p w C ω m) = 1 := by
  dsimp only
  let C := G.clusterObject σ S
  let v := exposureLaw w (G.incidentEdges C.1) C.2
  have hv := exposureLaw_normalized w (G.incidentEdges C.1) C.2
    (homogeneous_normalized w p h0 h1)
  change expect v (fun ω => ∑ m, G.contactKernel order B a p w C ω m) = 1
  by_cases ha : a ∈ C.1
  · have he : (fun ω => ∑ m, G.contactKernel order B a p w C ω m) =
        (fun _ : E → Prop => (1 : ℝ)) := by
      funext ω
      simp [contactKernel,ha]
    rw [he,expect_const v hv]
  · have hB : B ⊆ C.1 := by
      intro b hb
      exact ⟨b,hBS hb,SimpleGraph.Reachable.refl b⟩
    have hm := LazyDFS.search_contact_moments_exposure G order ho B C.1 a ha hB C.2
      (G.clusterObject_cut_closed σ S) p hp w h0 h1
    have he : (fun ω => ∑ m, G.contactKernel order B a p w C ω m) =
        (fun ω => (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
          (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω /
            prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)) := by
      funext ω
      simp only [contactKernel,ite_eq_right ha,Fintype.sum_option,zero_add]
      rw [←Finset.sum_div,G.sum_contactWeight]
    rw [he]
    simp_rw [div_eq_mul_inv]
    rw [expect_mul_const,hm.1,mul_inv_cancel₀ hh.ne']

end CriticalPercolation.BondGraph

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_queryDelta_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) (e : E) :
    (compile G order B fuel st stack).queryDelta F w ω e =
      (compile G order B fuel st stack).queryDelta F w η e := by
  induction fuel generalizing st stack w with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hst
        · have htail : d.1 ∈ st.reached := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inr ht)))
          have hinc : ∃ r ∈ G.ends d.2.1, (G.openGraph ω).Reachable a r :=
            ⟨d.1,by simp [he],hst d.1 htail⟩
          simp only [queryDelta,←propext (h d.2.1 hinc)]
          by_cases hed : e = d.2.1
          · simp only [ite_eq_left hed]
          · simp only [ite_eq_right hed]
            by_cases hopen : ω d.2.1
            · simp only [ite_eq_left hopen]
              have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                  (G.openGraph ω).Reachable a v := by
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
                · exact hst v hv
              exact ih _ _ _ hs'
            · simp only [ite_eq_right hopen]
              exact ih (st.closed d.2.1) rest (pin w d.2.1 False) hst

variable [Fintype V]
lemma search_queryDelta_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g)) (e : E) :
    (search G order a B).queryDelta F w ω e = (search G order a B).queryDelta F w η e := by
  exact compile_queryDelta_incidence G order B _ _ _ F w ω η a h
    (fun v hv => by have he : v=a := Finset.mem_singleton.mp hv; subst v; exact .refl _) e

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma contactKernel_record (order : List (LazyDFS.Dart V E))
    (B S T : Set V) (a : V) (hST : S ⊆ T) (ha : a ∈ T)
    (p : ℝ) (w : E → Prop → ℝ) (ω η : E → Prop)
    (h : G.clusterObject ω T = G.clusterObject η T) (mark : Option E) :
    G.contactKernel order B a p w (G.clusterObject ω S) ω mark =
      G.contactKernel order B a p w (G.clusterObject η S) η mark := by
  have hC := G.clusterObject_refines hST ω η h
  unfold contactKernel
  rw [←hC]
  by_cases hh : a ∈ (G.clusterObject ω S).1
  · simp only [ite_eq_left hh]
  · simp only [ite_eq_right hh]
    cases mark with
    | none => rfl
    | some e =>
      apply congrArg (· / _)
      unfold contactWeight
      split_ifs
      · apply congrArg (p*·)
        apply LazyDFS.search_queryDelta_incidence
        rintro g ⟨v,hv,hav⟩
        exact ((G.incidenceExposure T).bits_congr h ⟨v,⟨a,ha,hav⟩,hv⟩).to_iff
      · rfl

end CriticalPercolation.BondGraph

namespace CriticalPercolation.FiniteProduct.Exposure
open scoped Classical
open FiniteEntropy

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

lemma weighted_identity (R : Exposure E A B) (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (g : (E → A) → ℝ)
    (hg : ∀ ω η, R.record ω = R.record η → g ω = g η)
    (f : B → (E → A) → ℝ)
    (hf : ∀ ω, expect (exposureLaw w (R.domain (R.record ω))
      (R.bits (R.record ω))) (f (R.record ω)) = 1) :
    expect w (fun ω => g ω * f (R.record ω) ω) = expect w g := by
  let k := fiberValue R.record g
  have hk := fiberValue_apply R.record g hg
  calc
    _ = expect w (fun ω => k (R.record ω)*f (R.record ω) ω) := by
      simp only [k,hk]
    _ = expect w (fun ω => expect (exposureLaw w (R.domain (R.record ω))
        (R.bits (R.record ω))) (fun η => k (R.record ω)*f (R.record ω) η)) :=
      R.disintegrate w hw (fun b ω => k b*f b ω)
    _ = _ := by
      simp_rw [expect_const_mul,hf,mul_one]
      simp only [k,hk]

end CriticalPercolation.FiniteProduct.Exposure

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E H : Type*} [Fintype V] [Fintype E] [Fintype H]
variable [DecidableEq V] [DecidableEq E] (G : BondGraph V E)

theorem adaptive_marked_step (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (S B : H → Set V) (hBS : ∀ h, B h ⊆ S h)
    (a : H → V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hh : ∀ h, 0 < prob w (fun σ => ∃ b ∈ B h, (G.openGraph σ).Reachable (a h) b))
    (r : H → (E → Prop) → ℝ)
    (hr : ∀ h ω η, G.clusterObject ω (S h) = G.clusterObject η (S h) → r h ω = r h η)
    (side : H → (E → Prop) → Option E → Bool) :
    (∑ h, expect w (fun ω => ∑ m : Option E, ∑ b : Bool,
      if side h ω m = b then r h ω * G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m else 0)) = ∑ h, expect w (r h) := by
  apply Finset.sum_congr rfl
  intro h _
  have he : (fun ω => ∑ m : Option E, ∑ b : Bool,
      if side h ω m = b then r h ω * G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m else 0) =
      (fun ω => r h ω * ∑ m, G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m) := by
    funext ω
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact (Finset.mul_sum _ _ _).symm
  rw [he]
  apply (G.incidenceExposure (S h)).weighted_identity w (homogeneous_normalized w p h0 h1)
    (r h) (hr h) (fun C ω => ∑ m, G.contactKernel order (B h) (a h) p w C ω m)
  intro ω
  exact G.contactKernel_normalized order ho (B h) (S h) (hBS h) (a h) hp w h0 h1 (hh h) ω

end CriticalPercolation.BondGraph
end
end

end OAI
