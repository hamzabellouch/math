import Mathlib
import OAI.Combinatorics.KServer.Behavior

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer
universe u
namespace Episode
open Finset
variable {k : ℕ} {X : Type u} [MetricSpace X]

def traceCost (s : Configuration k X) : List (X × Fin k) → ℝ
  | [] => 0
  | (r,i)::h => dist (s i) r + traceCost (serve s i r) h

lemma traceCost_nonneg (s : Configuration k X) (h : List (X × Fin k)) :
    0  ≤  traceCost s h := by
  induction h generalizing s with
  | nil => simp [traceCost]
  | cons ri h ih => exact add_nonneg dist_nonneg (ih _)

omit [MetricSpace X] in
lemma configurationAfter_nil (s : Configuration k X) : configurationAfter s [] = s := rfl
omit [MetricSpace X] in
lemma configurationAfter_cons (s : Configuration k X) (r : X) (i : Fin k)
    (h : List (X × Fin k)) :
    configurationAfter s ((r,i)::h) = configurationAfter (serve s i r) h := rfl

lemma traceCost_append (s : Configuration k X) (h g : List (X × Fin k)) :
    traceCost s (h++g) = traceCost s h + traceCost (configurationAfter s h) g := by
  induction h generalizing s with
  | nil => simp [traceCost,configurationAfter]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simp only [List.cons_append,traceCost,configurationAfter_cons,ih]
    ring

omit [MetricSpace X] in
lemma configurationAfter_append' (s : Configuration k X) (h g : List (X × Fin k)) :
    configurationAfter s (h++g) = configurationAfter (configurationAfter s h) g := by
  simp [configurationAfter,List.foldl_append]

omit [MetricSpace X] in
lemma serve_undo (s : Configuration k X) (i : Fin k) (r : X) :
    serve (serve s i r) i (s i) = s := by
  funext j
  by_cases h : j=i <;> simp [serve,h]

def reverseTrace (s : Configuration k X) : List (X × Fin k) → List (X × Fin k)
  | [] => []
  | (r,i)::h => reverseTrace (serve s i r) h ++ [(s i,i)]

omit [MetricSpace X] in
/-- The literal reverse word returns the labeled tuple, not just its multiset. -/
lemma reverse_restores (s : Configuration k X) (h : List (X × Fin k)) :
    configurationAfter (configurationAfter s h) (reverseTrace s h) = s := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    rw [reverseTrace,configurationAfter_cons,configurationAfter_append',ih]
    exact serve_undo s i r

lemma reverse_cost (s : Configuration k X) (h : List (X × Fin k)) :
    traceCost (configurationAfter s h) (reverseTrace s h) = traceCost s h := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    rw [reverseTrace,configurationAfter_cons,traceCost_append,reverse_restores,ih]
    simp only [traceCost,add_zero,serve,Function.update_self]
    rw [dist_comm]
    ring

omit [MetricSpace X] in
lemma reverse_length (s : Configuration k X) (h : List (X × Fin k)) :
    (reverseTrace s h).length = h.length := by
  induction h generalizing s with
  | nil => rfl
  | cons ri h ih => rcases ri with ⟨r,i⟩; simp [reverseTrace,ih]

def serviceTrace : (σ : List X) → (Fin σ.length → Fin k) → List (X × Fin k)
  | [], _ => []
  | r::σ,j => (r,j 0)::serviceTrace σ (fun i => j i.succ)

lemma serviceTrace_cost (s : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) : traceCost s (serviceTrace σ j) = serviceCost s σ j := by
  induction σ generalizing s with
  | nil => rfl
  | cons r σ ih => exact congrArg (fun x => dist (s (j 0)) r+x) (ih _ _)

omit [MetricSpace X] in
lemma serviceTrace_requests (σ : List X) (j : Fin σ.length → Fin k) :
    (serviceTrace σ j).map Prod.fst = σ := by
  induction σ with
  | nil => rfl
  | cons r σ ih => simp only [serviceTrace,List.map_cons,ih]

omit [MetricSpace X] in
/-- Every legal designated trace gives a label string in the source lazy model. -/
lemma exists_labelString (h : List (X × Fin k)) :
    ∃ j : Fin (h.map Prod.fst).length → Fin k,
      serviceTrace (h.map Prod.fst) j = h := by
  induction h with
  | nil => exact ⟨Fin.elim0,rfl⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    obtain ⟨j,hj⟩ := ih
    refine ⟨Fin.cons i j,?_⟩
    change (r,i) :: serviceTrace (h.map Prod.fst) j = (r,i) :: h
    exact congrArg (List.cons (r,i)) hj

lemma optimalCost_le_trace [NeZero k] (s : Configuration k X) (h : List (X × Fin k)) :
    optimalCost s (h.map Prod.fst)  ≤  traceCost s h := by
  obtain ⟨j,hj⟩ := exists_labelString h
  have hc := serviceTrace_cost s (h.map Prod.fst) j
  rw [hj] at hc
  rw [hc]
  exact optimalCost_le_service s _ j

lemma cheap_closed_episode [NeZero k] (s : Configuration k X) (σ : List X) :
    ∃ h : List (X × Fin k), h.map Prod.fst = σ ∧
      traceCost s (h++reverseTrace s h) = 2*optimalCost s σ ∧
      configurationAfter s (h++reverseTrace s h) = s ∧
      (h++reverseTrace s h).length = 2*σ.length := by
  obtain ⟨j,hj⟩ := optimalCost_attained s σ
  let h := serviceTrace σ j
  have hc : traceCost s h = optimalCost s σ := by
    rw [serviceTrace_cost]; exact hj
  have hl : h.length = σ.length := by
    have hr := serviceTrace_requests σ j
    have he := congrArg List.length hr
    simpa only [List.length_map] using he
  refine ⟨h,serviceTrace_requests σ j,?_,?_,?_⟩
  · rw [traceCost_append,reverse_cost,hc]; ring
  · rw [configurationAfter_append',reverse_restores]
  · rw [List.length_append,reverse_length,hl]; omega

/-- Pathwise strong laziness, imposed only on the trace actually selected. -/
def LazyTrace (s : Configuration k X) : List (X × Fin k) → Prop
  | [] => True
  | (r,i)::h => ((∃ j, s j=r) → s i=r) ∧ LazyTrace (serve s i r) h

omit [MetricSpace X] in
lemma serve_same (s : Configuration k X) {i : Fin k} {r : X} (he : s i=r) :
    serve s i r = s := by
  funext j
  by_cases h : j=i <;> simp [serve,h,←he]

lemma zero_trace_unchanged (s : Configuration k X) (h : List (X × Fin k))
    (hz : traceCost s h=0) : configurationAfter s h=s ∧
      ∀ r ∈ h.map Prod.fst, ∃ i, s i=r := by
  induction h generalizing s with
  | nil => exact ⟨rfl,by simp⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    have hd : dist (s i) r=0 := by
      have hn := traceCost_nonneg (serve s i r) h
      have hn' : 0  ≤  dist (s i) r := dist_nonneg
      change dist (s i) r + traceCost (serve s i r) h=0 at hz
      linarith
    have he := dist_eq_zero.mp hd
    have hs := serve_same s he
    have ht : traceCost s h=0 := by simpa only [traceCost,hd,zero_add,hs] using hz
    obtain ⟨heq,hcov⟩ := ih s ht
    refine ⟨by simpa only [configurationAfter_cons,hs] using heq,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · exact ⟨i,he.trans hx.symm⟩
    · exact hcov x hx

lemma lazy_covered_trace (s : Configuration k X) (h : List (X × Fin k))
    (hl : LazyTrace s h) (hc : ∀ r ∈ h.map Prod.fst, ∃ i, s i=r) :
    configurationAfter s h=s ∧ traceCost s h=0 := by
  induction h generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    have he : s i=r := hl.1 (hc r (by simp))
    have hs := serve_same s he
    obtain ⟨heq,hcost⟩ := ih s (by simpa only [hs] using hl.2)
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    exact ⟨by simpa only [configurationAfter_cons,hs] using heq,
      by simp only [traceCost,he,dist_self,zero_add,hs,hcost]⟩

lemma matching_zero_of_covers (s A : Configuration k X) (hs : Function.Injective s)
    (hc : ∀ i, ∃ j, A j=s i) : matching A s=0 := by
  classical
  choose f hf using hc
  have hi : Function.Injective f := by
    intro i j hij
    apply hs
    rw [←hf i,←hf j,hij]
  let e : Equiv.Perm (Fin k) := Equiv.ofBijective f
    ⟨hi,Finite.surjective_of_injective hi⟩
  have hms : matchSum s A e=0 := by
    apply Finset.sum_eq_zero
    intro i _
    change dist (s i) (A (f i))=0
    rw [hf,dist_self]
  have hm := matching_le s A e
  rw [hms,matching_symmetric] at hm
  exact le_antisymm hm (matching_nonneg _ _)

/-- A zero-cost reset cycle covers all k distinct starting points; strong
laziness then keeps that multiset fixed through all following reset requests. -/
lemma zero_cycle_finishes_reset (s A : Configuration k X) (hs : Function.Injective s)
    (h g : List (X × Fin k))
    (hcycle : h.map Prod.fst = List.ofFn s) (hz : traceCost A h=0)
    (hg : LazyTrace (configurationAfter A h) g)
    (hrequests : ∀ r ∈ g.map Prod.fst, r ∈ Set.range s) :
    matching (configurationAfter A (h++g)) s=0 := by
  obtain ⟨heq,hcov⟩ := zero_trace_unchanged A h hz
  have hc : ∀ i, ∃ j, A j=s i := by
    intro i
    apply hcov
    rw [hcycle]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hga : LazyTrace A g := by simpa only [heq] using hg
  have hcover : ∀ r ∈ g.map Prod.fst, ∃ j, A j=r := by
    intro r hr
    obtain ⟨i,hi⟩ := hrequests r hr
    exact hi ▸ hc i
  rw [configurationAfter_append',heq,(lazy_covered_trace A g hga hcover).1]
  exact matching_zero_of_covers s A hs hc


omit [MetricSpace X] in
lemma lazyTrace_append (s : Configuration k X) (h g : List (X × Fin k)) :
    LazyTrace s (h++g) ↔ LazyTrace s h ∧ LazyTrace (configurationAfter s h) g := by
  induction h generalizing s with
  | nil => simp [LazyTrace,configurationAfter]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simp only [List.cons_append,LazyTrace,configurationAfter_cons,ih,and_assoc]

lemma discrete_trace_cost (δ : ℝ) (_hδ : 0  ≤  δ)
    (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (A : Configuration k X) (h : List (X × Fin k)) :
    traceCost A h=0 ∨ δ  ≤  traceCost A h := by
  induction h generalizing A with
  | nil => exact Or.inl rfl
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    by_cases he : A i=r
    · have hu := serve_same A he
      simpa only [traceCost,he,dist_self,zero_add,hu] using ih A
    · exact Or.inr (by
        have hd := hg (A i) r he
        have hn := traceCost_nonneg (serve A i r) h
        change δ  ≤  dist (A i) r + traceCost (serve A i r) h
        linarith)

def cycleTrace (s : Configuration k X) (j : Fin k → Fin k) : List (X × Fin k) :=
  List.ofFn (fun i => (s i,j i))

def resetTrace (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    List (X × Fin k) := ls.flatMap (cycleTrace s)

omit [MetricSpace X] in
lemma cycleTrace_requests (s : Configuration k X) (j : Fin k → Fin k) :
    (cycleTrace s j).map Prod.fst = List.ofFn s := by
  simp only [cycleTrace,List.map_ofFn]
  rfl

omit [MetricSpace X] in
lemma resetTrace_requests (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    ∀ r ∈ (resetTrace s ls).map Prod.fst, r ∈ Set.range s := by
  intro r hr
  obtain ⟨ri,hri,hr⟩ := List.mem_map.mp hr
  obtain ⟨j,hj,hri⟩ := List.mem_flatMap.mp hri
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hri
  exact ⟨i, by rw [←hr,←hi]⟩

lemma reset_dichotomy (s A : Configuration k X) (hs : Function.Injective s)
    (δ : ℝ) (hδ : 0  ≤  δ) (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (ls : List (Fin k → Fin k)) (hl : LazyTrace A (resetTrace s ls)) :
    matching (configurationAfter A (resetTrace s ls)) s=0 ∨
      (ls.length : ℝ)*δ  ≤  traceCost A (resetTrace s ls) := by
  induction ls generalizing A with
  | nil => exact Or.inr (by simp [resetTrace,traceCost])
  | cons j ls ih =>
    have he : resetTrace s (j::ls) = cycleTrace s j ++ resetTrace s ls := rfl
    rw [he] at hl ⊢
    obtain ⟨hlc,hlt⟩ := (lazyTrace_append _ _ _).mp hl
    rcases discrete_trace_cost δ hδ hg A (cycleTrace s j) with hz|hpos
    · exact Or.inl (zero_cycle_finishes_reset s A hs _ _ (cycleTrace_requests s j)
        hz hlt (resetTrace_requests s ls))
    · rcases ih (configurationAfter A (cycleTrace s j)) hlt with hm|hb
      · exact Or.inl (by rwa [configurationAfter_append'])
      · right
        rw [traceCost_append,List.length_cons,Nat.cast_add,Nat.cast_one]
        linarith

lemma matching_le_diameter (A s : Configuration k X) (Δ : ℝ)
    (hdiam : ∀ x y : X, dist x y  ≤  Δ) : matching A s  ≤  (k : ℝ)*Δ := by
  apply (matching_le A s (Equiv.refl _)).trans
  change (∑ i : Fin k, dist (A i) (s i))  ≤  _
  calc
    _  ≤  ∑ _i : Fin k, Δ := Finset.sum_le_sum fun _ _ => hdiam _ _
    _ = _ := by simp

/-- Equation reset-mismatch with its actual finite-reset cost. The metric gap
is used only to choose the number of cycles; no bound depends on the horizon. -/
theorem reset_mismatch (s A : Configuration k X) (hs : Function.Injective s)
    (δ Δ : ℝ) (hδ : 0  ≤  δ) (hg : ∀ x y : X, x ≠ y → δ  ≤  dist x y)
    (hdiam : ∀ x y : X, dist x y  ≤  Δ)
    (ls : List (Fin k → Fin k)) (hR : (k : ℝ)*Δ  ≤  (ls.length : ℝ)*δ)
    (hl : LazyTrace A (resetTrace s ls)) :
    matching (configurationAfter A (resetTrace s ls)) s  ≤ 
      traceCost A (resetTrace s ls) := by
  rcases reset_dichotomy s A hs δ hδ hg ls hl with hm|hc
  · rw [hm]; exact traceCost_nonneg _ _
  · exact (matching_le_diameter _ _ Δ hdiam).trans (hR.trans hc)


/-- Source's finite-space gap and diameter, with no assumption of discreteness
on the eventual arbitrary metric space. Only the local finite experiment uses
these constants. -/
lemma finite_gap_diameter [Fintype X] (hne : ∃ x y : X, x ≠ y) :
    ∃ δ Δ : ℝ, 0 < δ ∧ 0  ≤  Δ ∧
      (∀ x y : X, x ≠ y → δ  ≤  dist x y) ∧ (∀ x y : X, dist x y  ≤  Δ) := by
  classical
  let pairs : Finset (X × X) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hp : pairs.Nonempty := by
    obtain ⟨x,y,hxy⟩ := hne
    exact ⟨(x,y),by simp [pairs,hxy]⟩
  obtain ⟨p,hp,hm⟩ := Finset.exists_min_image pairs (fun p => dist p.1 p.2) hp
  have hup : (Finset.univ : Finset (X × X)).Nonempty := ⟨p,Finset.mem_univ _⟩
  obtain ⟨q,hq,hM⟩ := Finset.exists_max_image Finset.univ
    (fun p : X × X => dist p.1 p.2) hup
  refine ⟨dist p.1 p.2,dist q.1 q.2,?_,dist_nonneg,?_,?_⟩
  · apply dist_pos.mpr
    exact (Finset.mem_filter.mp hp).2
  · intro x y hxy; exact hm (x,y) (by simp [pairs,hxy])
  · intro x y; exact hM (x,y) (Finset.mem_univ _)

def resetCount (k : ℕ) (Δ δ : ℝ) : ℕ := ⌊(k : ℝ)*Δ/δ⌋₊+1

lemma resetCount_bound (Δ δ : ℝ) (hδ : 0 < δ) :
    (k : ℝ)*Δ < (resetCount k Δ δ : ℝ)*δ := by
  have h := Nat.lt_floor_add_one ((k : ℝ)*Δ/δ)
  have h' := (div_lt_iff₀ hδ).mp h
  simpa only [resetCount,Nat.cast_add,Nat.cast_one] using h'

/-- The finite reset length is chosen once for the metric and starting stock,
not for the law or horizon. It applies to every strongly lazy trace of that
reset word, including choices of labels occupying equal positions. -/
theorem exists_uniform_reset [Fintype X] (s : Configuration k X)
    (hs : Function.Injective s) (hne : ∃ x y : X, x ≠ y) :
    ∃ R : ℕ, 0 < R ∧ ∀ A : Configuration k X,
      ∀ ls : List (Fin k → Fin k), ls.length=R →
        LazyTrace A (resetTrace s ls) →
        matching (configurationAfter A (resetTrace s ls)) s  ≤  traceCost A (resetTrace s ls) := by
  obtain ⟨δ,Δ,hδ,hΔ,hg,hdiam⟩ := finite_gap_diameter hne
  refine ⟨resetCount k Δ δ,Nat.zero_lt_succ _,?_⟩
  intro A ls hlen hl
  apply reset_mismatch s A hs δ Δ hδ.le hg hdiam ls _ hl
  rw [hlen]
  exact (resetCount_bound Δ δ hδ).le

end Episode
end KServer

namespace KServer
namespace Amplification
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- Exact finite-input Bellman expectation of an arbitrary terminal observable.
The private action history, not only the current configuration, is retained. -/
def after (A : Policy k X) (h : List (X × Fin k)) : List X →
    (List (X × Fin k) → ℝ) → ℝ
  | [],f => f h
  | r::σ,f => ∑ i, (A h r).val i * after A (h++[(r,i)]) σ f

def cost (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (σ : List X) :=
  continuationCost A (configurationAfter s h) h σ

omit [NeZero k] in
lemma cost_nil (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) :
    cost A s h []=0 := continuationCost_nil _ _ _

omit [NeZero k] in
lemma cost_cons (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (r : X) (σ : List X) :
    cost A s h (r::σ)=∑ i, (A h r).val i *
      (dist (configurationAfter s h i) r+cost A s (h++[(r,i)]) σ) := by
  simp only [cost,continuationCost_cons,configurationAfter_append]

omit [NeZero k] [MetricSpace X] in
lemma after_const (A : Policy k X) (h : List (X × Fin k)) (σ : List X) (c : ℝ) :
    after A h σ (fun _=>c)=c := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,←sum_mul,(A h r).property.2,one_mul]

omit [NeZero k] [MetricSpace X] in
lemma after_mono (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {f g : List (X × Fin k) → ℝ} (hfg : ∀ h, f h ≤ g h) :
    after A h σ f ≤ after A h σ g := by
  induction σ generalizing h with
  | nil => exact hfg h
  | cons r σ ih =>
    exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (ih _) ((A h r).property.1 i)

omit [NeZero k] [MetricSpace X] in
lemma after_nonneg (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {f : List (X × Fin k) → ℝ} (hf : ∀ h, 0 ≤ f h) : 0 ≤ after A h σ f := by
  simpa only [after_const] using after_mono A h σ hf

omit [NeZero k] [MetricSpace X] in
lemma after_add (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (f g : List (X × Fin k) → ℝ) :
    after A h σ (fun h=>f h+g h)=after A h σ f+after A h σ g := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,mul_add,sum_add_distrib]

omit [NeZero k] [MetricSpace X] in
lemma after_mul (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (c : ℝ) (f : List (X × Fin k) → ℝ) :
    after A h σ (fun h=>c*f h)=c*after A h σ f := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,Finset.mul_sum]; congr 1; funext i; ring

omit [NeZero k] [MetricSpace X] in
lemma after_append (A : Policy k X) (h : List (X × Fin k)) (ρ σ : List X)
    (f : List (X × Fin k) → ℝ) :
    after A h (ρ++σ) f=after A h ρ (fun h=>after A h σ f) := by
  induction ρ generalizing h with
  | nil => rfl
  | cons r ρ ih => simp only [List.cons_append,after,ih]

omit [NeZero k] in
lemma cost_append (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (ρ σ : List X) :
    cost A s h (ρ++σ)=cost A s h ρ+after A h ρ (fun h=>cost A s h σ) := by
  induction ρ generalizing h with
  | nil => simp [cost_nil,after]
  | cons r ρ ih =>
    simp only [List.cons_append,cost_cons,ih,after,mul_add,sum_add_distrib]
    ring

omit [NeZero k] in
lemma cost_nonneg (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (σ : List X) : 0 ≤ cost A s h σ := by
  unfold cost continuationCost
  exact sum_nonneg fun j _=>mul_nonneg (pathProbability_nonneg _ _ _ _) (serviceCost_nonneg _ _ _)

omit [NeZero k] [MetricSpace X] in
lemma after_paths (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    (f : List (X × Fin k) → ℝ) :
    after A h σ f=∑ j : Fin σ.length → Fin k,
      pathProbability A h σ j * f (h++Episode.serviceTrace σ j) := by
  induction σ generalizing h with
  | nil => simp [after,pathProbability,Episode.serviceTrace]
  | cons r σ ih =>
    change after A h (r::σ) f = ∑ j : Fin (σ.length+1) → Fin k,
      pathProbability A h (r::σ) j * f (h++Episode.serviceTrace (r::σ) j)
    rw [sum_labelStrings]
    simp only [after,ih,pathProbability,Episode.serviceTrace,Fin.cons_zero,Fin.cons_succ,List.append_assoc,
      List.singleton_append,mul_assoc,Finset.mul_sum]

omit [NeZero k] in
lemma cost_paths (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k))
    (σ : List X) : cost A s h σ = ∑ j : Fin σ.length → Fin k,
      pathProbability A h σ j * Episode.traceCost (configurationAfter s h) (Episode.serviceTrace σ j) := by
  simp only [cost,continuationCost,Episode.serviceTrace_cost]

omit [NeZero k] [MetricSpace X] in
lemma supported_trace_lazy (A : Policy k X) (s : Configuration k X)
    (hl : StronglyLazy s A) (h : List (X × Fin k)) (σ : List X)
    (j : Fin σ.length → Fin k) (hp : pathProbability A h σ j ≠0) :
    Episode.LazyTrace (configurationAfter s h) (Episode.serviceTrace σ j) := by
  induction σ generalizing h with
  | nil => trivial
  | cons r σ ih =>
    have hn := mul_ne_zero_iff.mp hp
    refine ⟨?_,?_⟩
    · intro hc
      by_contra hh
      exact hn.1 (hl h r hc (j 0) hh)
    · have ht := ih (h++[(r,j 0)]) (fun i=>j i.succ) hn.2
      simpa only [configurationAfter_append] using ht

omit [NeZero k] [MetricSpace X] in
/-- Extract one cycle's label list from any trace whose requests are the fixed
starting tuple. This prevents an unjustified switch from label multisets to
labeled equality in the reset argument. -/
lemma trace_of_cycle_requests (s : Configuration k X) (h : List (X × Fin k))
    (hr : h.map Prod.fst=List.ofFn s) :
    ∃ j : Fin k → Fin k, h=Episode.cycleTrace s j := by
  have hlen : h.length=k := by
    have := congrArg List.length hr
    simpa only [List.length_map,List.length_ofFn] using this
  let j : Fin k → Fin k := fun i=>(h.get ⟨i.val,by simp [hlen]⟩).2
  refine ⟨j,?_⟩
  apply List.ext_getElem (by simp [Episode.cycleTrace,hlen])
  intro n hn hn'
  simp only [Episode.cycleTrace,List.getElem_ofFn]
  have hnk : n<k := by simpa [hlen] using hn
  have hrn := congrArg (fun l : List X=>l[n]?) hr
  have hx : h[n].1=s ⟨n,hnk⟩ := by
    simpa [List.getElem?_eq_getElem,hn,hnk] using hrn
  exact Prod.ext hx rfl

omit [NeZero k] [MetricSpace X] in
lemma trace_of_reset_requests (s : Configuration k X) (R : ℕ)
    (h : List (X × Fin k)) (hr : h.map Prod.fst=(List.replicate R (List.ofFn s)).flatten) :
    ∃ ls : List (Fin k → Fin k), ls.length=R ∧ h=Episode.resetTrace s ls := by
  induction R generalizing h with
  | zero =>
    have he : h=[] := by
      have hh := congrArg List.length hr
      simpa using hh
    exact ⟨[],rfl,he⟩
  | succ R ih =>
    have hr' : h.map Prod.fst=List.ofFn s++(List.replicate R (List.ofFn s)).flatten := by
      simpa only [List.replicate_succ,List.flatten_cons] using hr
    have ht : (h.take k).map Prod.fst=List.ofFn s := by
      rw [List.map_take,hr']
      simp
    have hd : (h.drop k).map Prod.fst=(List.replicate R (List.ofFn s)).flatten := by
      rw [List.map_drop,hr']
      simp
    obtain ⟨j,hj⟩ := trace_of_cycle_requests s (h.take k) ht
    obtain ⟨ls,hlen,hls⟩ := ih (h.drop k) hd
    refine ⟨j::ls,by simp [hlen],?_⟩
    change h=Episode.cycleTrace s j++Episode.resetTrace s ls
    rw [←hj,←hls,List.take_append_drop]

omit [NeZero k] in
/-- The reset bound for literal Bellman expectation under an actual strongly
lazy policy, not an assumed distribution of reset costs. -/
theorem expected_reset [Fintype X] (s : Configuration k X) (hs : Function.Injective s)
    (hne : ∃ x y : X, x ≠ y) :
    ∃ R : ℕ, 0<R ∧ ∀ A : Policy k X, StronglyLazy s A → ∀ h,
      after A h ((List.replicate R (List.ofFn s)).flatten)
        (fun g=>matching (configurationAfter s g) s)  ≤ 
      cost A s h ((List.replicate R (List.ofFn s)).flatten) := by
  obtain ⟨R,hR,hreset⟩ := Episode.exists_uniform_reset s hs hne
  refine ⟨R,hR,?_⟩
  intro A hA h
  rw [after_paths,cost_paths]
  apply sum_le_sum
  intro j _
  by_cases hzero : pathProbability A h ((List.replicate R (List.ofFn s)).flatten) j=0
  · simp [hzero]
  · obtain ⟨ls,hlen,htrace⟩ := trace_of_reset_requests s R
      (Episode.serviceTrace ((List.replicate R (List.ofFn s)).flatten) j)
      (Episode.serviceTrace_requests _ _)
    have htl := supported_trace_lazy A s hA h _ j hzero
    rw [htrace] at htl
    have hb := hreset (configurationAfter s h) ls hlen htl
    rw [←htrace] at hb
    rw [Episode.configurationAfter_append']
    exact mul_le_mul_of_nonneg_left hb (pathProbability_nonneg _ _ _ _)

variable {Ω : Type} [Fintype Ω]

/-- The minimum is attained in the full product of causal decision simplexes,
not in a horizon-dependent surrogate space. -/
lemma law_minimum (s : Configuration k X) (σ : Ω → List X) (w : Ω → ℝ) :
    ∃ P : Policy k X, ∀ A : Policy k X,
      (∑ ω, w ω*expectedCost P s (σ ω))  ≤  ∑ ω, w ω*expectedCost A s (σ ω) := by
  have hc : Continuous fun A : Policy k X => ∑ ω, w ω*expectedCost A s (σ ω) :=
    continuous_finsetSum _ fun ω _ => continuous_const.mul (continuous_expectedCost s (σ ω))
  obtain ⟨P,_,hP⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Policy k X)).Nonempty) hc.continuousOn
  exact ⟨P,fun A=>hP (Set.mem_univ A)⟩

/-- Minimum-law continuation and compactness give a causal policy without sampling fictitious prefixes. -/


lemma minimum_continuation (s : Configuration k X) (σ : Ω → List X) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1) (m : ℝ)
    (hmin : ∀ B : Policy k X, m  ≤  ∑ ω, w ω*expectedCost B s (σ ω))
    (A : Policy k X) (h : List (X × Fin k)) :
    m  ≤  matching (configurationAfter s h) s+∑ ω, w ω*cost A s h (σ ω) := by
  obtain ⟨B,hB⟩ := BoundedSimulation.global_simulation A h s (configurationAfter s h)
  have hb := (hmin B).trans (sum_le_sum fun ω _=>
    mul_le_mul_of_nonneg_left (hB (σ ω)) (hw ω))
  simpa only [mul_add,sum_add_distrib,←sum_mul,hsum,one_mul,
    matching_symmetric s (configurationAfter s h),cost] using hb

def lawAfter (A : Policy k X) (w : Ω → ℝ) (σ : Ω → List X)
    (h : List (X × Fin k)) (f : List (X × Fin k) → ℝ) :=
  ∑ ω, w ω * after A h (σ ω) f

def lawCost (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (σ : Ω → List X) (h : List (X × Fin k)) := ∑ ω, w ω*cost A s h (σ ω)

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_mono (A : Policy k X) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (σ : Ω → List X) (h : List (X × Fin k))
    {f g : List (X × Fin k) → ℝ} (hfg : ∀ h, f h ≤ g h) :
    lawAfter A w σ h f ≤ lawAfter A w σ h g :=
  sum_le_sum fun ω _=>mul_le_mul_of_nonneg_left (after_mono A h _ hfg) (hw ω)

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_const (A : Policy k X) (w : Ω → ℝ) (hsum : ∑ ω, w ω=1)
    (σ : Ω → List X) (h : List (X × Fin k)) (c : ℝ) :
    lawAfter A w σ h (fun _=>c)=c := by
  simp only [lawAfter,after_const,←sum_mul,hsum,one_mul]

omit [NeZero k] [MetricSpace X] in
lemma lawAfter_add (A : Policy k X) (w : Ω → ℝ) (σ : Ω → List X)
    (h : List (X × Fin k)) (f g : List (X × Fin k) → ℝ) :
    lawAfter A w σ h (fun h=>f h+g h)=lawAfter A w σ h f+lawAfter A w σ h g := by
  simp only [lawAfter,after_add,mul_add,sum_add_distrib]

def runCost (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (ep : Ω → List X) : ℕ → List (X × Fin k) → ℝ
  | 0,_ => 0
  | N+1,h => lawCost A s w ep h+lawAfter A w ep h (runCost A s w ep N)

omit [NeZero k] in
/-- Exact telescoping lower bound for repeated independent closed episodes.
The second premise here is derived from `expected_reset` below; it is not an
assumed policy-existence claim. -/
lemma episode_telescope (A : Policy k X) (s : Configuration k X)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1)
    (ep : Ω → List X) (m : ℝ)
    (hstep : ∀ h, m+lawAfter A w ep h (fun g=>matching (configurationAfter s g) s)  ≤ 
      matching (configurationAfter s h) s+lawCost A s w ep h) :
    ∀ (N : ℕ) h, (N : ℝ)*m  ≤  matching (configurationAfter s h) s+runCost A s w ep N h := by
  intro N
  induction N with
  | zero => intro h; simpa [runCost] using matching_nonneg (configurationAfter s h) s
  | succ N ih =>
    intro h
    have he := lawAfter_mono A w hw ep h ih
    rw [lawAfter_const A w hsum,lawAfter_add] at he
    have hs := hstep h
    simp only [runCost,Nat.cast_add,Nat.cast_one]
    linarith

/-- The reset charge and the minimum-continuation inequality together give the
one-episode drift needed for the preceding telescope. -/
lemma episode_step (A : Policy k X) (s : Configuration k X)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω=1)
    (σ ρ : Ω → List X) (z : List X) (m : ℝ)
    (hmin : ∀ B : Policy k X, m  ≤  ∑ ω, w ω*expectedCost B s (σ ω))
    (hz : ∀ h, after A h z (fun g=>matching (configurationAfter s g) s) ≤ cost A s h z) :
    ∀ h, m+lawAfter A w (fun ω=>σ ω++ρ ω++z) h
      (fun g=>matching (configurationAfter s g) s)  ≤ 
      matching (configurationAfter s h) s+lawCost A s w (fun ω=>σ ω++ρ ω++z) h := by
  intro h
  have hm := minimum_continuation s σ w hw hsum m hmin A h
  have hb : lawCost A s w σ h + lawAfter A w (fun ω=>σ ω++ρ ω++z) h
      (fun g=>matching (configurationAfter s g) s)  ≤ 
      lawCost A s w (fun ω=>σ ω++ρ ω++z) h := by
    unfold lawCost lawAfter
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro ω _
    rw [←mul_add]
    apply mul_le_mul_of_nonneg_left _ (hw ω)
    rw [after_append,after_append,cost_append,cost_append]
    have hr : after A h (σ ω) (fun g=>after A g (ρ ω) (fun g=>cost A s g z))  ≤ 
        after A h (σ ω) (fun g=>cost A s g (ρ ω))+
          after A h (σ ω) (fun g=>after A g (ρ ω) (fun g=>cost A s g z)) :=
      le_add_of_nonneg_left (after_nonneg A h _ (fun g=>cost_nonneg A s g _))
    have he := after_mono A h (σ ω) (fun g=>after_mono A g (ρ ω) hz)
    rw [after_append]
    linarith
  change m  ≤  matching (configurationAfter s h) s+lawCost A s w σ h at hm
  linarith

lemma sum_strings {N : ℕ} (f : (Fin (N+1) → Ω) → ℝ) :
    ∑ v, f v=∑ ω, ∑ v : Fin N → Ω, f (Fin.cons ω v) := by
  rw [←Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N+1)=>Ω))
    (fun p=>f (Fin.cons p.1 p.2)) f (fun _=>rfl),Fintype.sum_prod_type]

def iidWord (ep : Ω → List X) : (N : ℕ) → (Fin N → Ω) → List X
  | 0,_ => []
  | N+1,v => ep (v 0)++iidWord ep N (fun i=>v i.succ)

def iidWeight (w : Ω → ℝ) : (N : ℕ) → (Fin N → Ω) → ℝ
  | 0,_ => 1
  | N+1,v => w (v 0)*iidWeight w N (fun i=>v i.succ)

omit [Fintype Ω] in
lemma iidWeight_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    ∀ N v, 0 ≤ iidWeight w N v := by
  intro N
  induction N with
  | zero => intro v; exact zero_le_one
  | succ N ih => intro v; exact mul_nonneg (hw _) (ih _)

lemma iidWeight_sum (w : Ω → ℝ) (hsum : ∑ ω, w ω=1) :
    ∀ N, ∑ v, iidWeight w N v=1 := by
  intro N
  induction N with
  | zero => simp [iidWeight]
  | succ N ih =>
    rw [sum_strings]
    simp only [iidWeight,Fin.cons_zero,Fin.cons_succ,←Finset.mul_sum,ih,mul_one,hsum]

omit [NeZero k] [MetricSpace X] in
lemma after_sum (A : Policy k X) (h : List (X × Fin k)) (σ : List X)
    {ι : Type} [Fintype ι] (f : ι → List (X × Fin k) → ℝ) :
    after A h σ (fun h=>∑ i, f i h)=∑ i, after A h σ (f i) := by
  induction σ generalizing h with
  | nil => rfl
  | cons r σ ih => simp only [after,ih,Finset.mul_sum]; exact sum_comm

omit [NeZero k] in
/-- The Bellman recursion is exactly the expectation under the concrete finite
product law on iid forward words, including the algorithm's labels. -/
lemma runCost_iid (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (hsum : ∑ ω, w ω=1) (ep : Ω → List X) :
    ∀ N h, runCost A s w ep N h=
      ∑ v, iidWeight w N v*cost A s h (iidWord ep N v) := by
  intro N
  induction N with
  | zero => intro h; simp [runCost,iidWord,cost_nil]
  | succ N ih =>
    intro h
    rw [sum_strings]
    simp only [runCost,iidWord,iidWeight,Fin.cons_zero,Fin.cons_succ,cost_append,
      mul_add,sum_add_distrib]
    simp_rw [mul_assoc,←Finset.mul_sum,←sum_mul,iidWeight_sum w hsum,one_mul]
    rw [←sum_add_distrib]
    unfold lawCost lawAfter
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro ω _
    rw [←mul_add,←mul_add]
    congr 2
    rw [show runCost A s w ep N = (fun h=>∑ v, iidWeight w N v*cost A s h (iidWord ep N v)) from funext ih,after_sum]
    simp only [after_mul]

omit [MetricSpace X] [Fintype Ω] in
lemma iidWord_length (ep : Ω → List X) (L : ℕ) (hL : ∀ ω, (ep ω).length=L) :
    ∀ N v, (iidWord ep N v).length=N*L := by
  intro N
  induction N with
  | zero => simp [iidWord]
  | succ N ih => intro v; simp [iidWord,List.length_append,hL,ih,Nat.succ_mul,Nat.add_comm]

omit [NeZero k] in
lemma stationary_trace (s : Configuration k X) (t : List (X × Fin k))
    (ht : ∀ ri ∈ t, s ri.2=ri.1) :
    configurationAfter s t=s ∧ Episode.traceCost s t=0 := by
  induction t with
  | nil => exact ⟨rfl,rfl⟩
  | cons ri t ih =>
    rcases ri with ⟨r,i⟩
    obtain ⟨he,hc⟩ := ih (fun x hx=>ht x (List.mem_cons_of_mem _ hx))
    have hs := Episode.serve_same s (ht (r,i) (List.mem_cons_self))
    simp only [Episode.configurationAfter_cons,hs,he,Episode.traceCost,
      ht (r,i) (List.mem_cons_self),dist_self,zero_add,hc,and_self]

omit [NeZero k] in
lemma stationary_reset (s : Configuration k X) (R : ℕ) :
    configurationAfter s (Episode.resetTrace s (List.replicate R id))=s ∧
      Episode.traceCost s (Episode.resetTrace s (List.replicate R id))=0 := by
  apply stationary_trace
  intro ri hri
  obtain ⟨j,hj,hri⟩ := List.mem_flatMap.mp hri
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hj
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hri
  simp only [←hi,Function.id_def]

omit [NeZero k] [MetricSpace X] in
lemma reset_length (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    (Episode.resetTrace s ls).length=ls.length*k := by
  induction ls with
  | nil => simp [Episode.resetTrace]
  | cons j ls ih =>
    change (Episode.cycleTrace s j++Episode.resetTrace s ls).length=(ls.length+1)*k
    simp only [List.length_append,Episode.cycleTrace,List.length_ofFn,ih]
    ring

omit [NeZero k] [MetricSpace X] in
lemma reset_requests_eq (s : Configuration k X) (R : ℕ) :
    (Episode.resetTrace s (List.replicate R id)).map Prod.fst=
      (List.replicate R (List.ofFn s)).flatten := by
  induction R with
  | zero => rfl
  | succ R ih =>
    change (Episode.cycleTrace s id++Episode.resetTrace s (List.replicate R id)).map Prod.fst=_
    rw [List.map_append,Episode.cycleTrace_requests,ih]
    rfl

/-- Padded *closed* episodes, valid even when forward lengths differ. Padding
is inserted after the reverse path and before the reset, so it costs the closed
offline trace zero and does not compromise the online reset-mismatch bound. -/
lemma closed_padded_episodes (s : Configuration k X) (σ : Ω → List X) (R : ℕ) :
    ∃ L : ℕ, ∃ ρ : Ω → List X, ∃ t : Ω → List (X × Fin k),
      ∀ ω, (t ω).map Prod.fst=σ ω++ρ ω++(List.replicate R (List.ofFn s)).flatten ∧
        configurationAfter s (t ω)=s ∧ Episode.traceCost s (t ω)=2*optimalCost s (σ ω) ∧
        (t ω).length=L := by
  classical
  choose h hreq hcost hend hlen using fun ω=>Episode.cheap_closed_episode s (σ ω)
  let M := Finset.univ.sup (fun ω=>(σ ω).length)
  let pad (ω : Ω) := List.replicate (2*(M-(σ ω).length)) (s 0,(0 : Fin k))
  let z := Episode.resetTrace s (List.replicate R id)
  have hz := stationary_reset s R
  have hp (ω : Ω) : configurationAfter s (pad ω)=s ∧ Episode.traceCost s (pad ω)=0 := by
    apply stationary_trace
    intro ri hri
    have he := (List.mem_replicate.mp hri).2
    subst ri
    rfl
  refine ⟨2*M+R*k,fun ω=>(Episode.reverseTrace s (h ω)++pad ω).map Prod.fst,
    fun ω=>((h ω++Episode.reverseTrace s (h ω))++pad ω)++z,?_⟩
  intro ω
  have hM : (σ ω).length ≤ M := by
    dsimp [M]
    exact Finset.le_sup (f := fun ω : Ω => (σ ω).length) (Finset.mem_univ ω)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.map_append,hreq]
    simp only [z,reset_requests_eq,List.append_assoc]
  · rw [Episode.configurationAfter_append',Episode.configurationAfter_append',hend,(hp ω).1]
    exact hz.1
  · have hf : configurationAfter s ((h ω++Episode.reverseTrace s (h ω))++pad ω)=s := by
      rw [Episode.configurationAfter_append',hend,(hp ω).1]
    rw [Episode.traceCost_append,hf,Episode.traceCost_append,hcost,hend,(hp ω).2,hz.2]
    ring
  · simp only [List.length_append,hlen,pad,List.length_replicate,z,reset_length]
    omega

def iidTrace (t : Ω → List (X × Fin k)) : (N : ℕ) → (Fin N → Ω) → List (X × Fin k)
  | 0,_ => []
  | N+1,v => t (v 0)++iidTrace t N (fun i=>v i.succ)

def iidSum (q : Ω → ℝ) : (N : ℕ) → (Fin N → Ω) → ℝ
  | 0,_ => 0
  | N+1,v => q (v 0)+iidSum q N (fun i=>v i.succ)

omit [NeZero k] [MetricSpace X] [Fintype Ω] in
lemma iidTrace_requests (t : Ω → List (X × Fin k)) :
    ∀ N v, (iidTrace t N v).map Prod.fst=iidWord (fun ω=>(t ω).map Prod.fst) N v := by
  intro N
  induction N with
  | zero => intro v; rfl
  | succ N ih => intro v; simp only [iidTrace,List.map_append,iidWord,ih]

omit [NeZero k] [Fintype Ω] in
lemma iidTrace_cost (s : Configuration k X) (t : Ω → List (X × Fin k))
    (ht : ∀ ω, configurationAfter s (t ω)=s) :
    ∀ N v, Episode.traceCost s (iidTrace t N v)=iidSum (fun ω=>Episode.traceCost s (t ω)) N v := by
  intro N
  induction N with
  | zero => intro v; rfl
  | succ N ih => intro v; simp only [iidTrace,Episode.traceCost_append,ht,ih,iidSum]

lemma iidSum_expectation (w q : Ω → ℝ) (hsum : ∑ ω,w ω=1) :
    ∀ N, (∑ v, iidWeight w N v*iidSum q N v)=(N : ℝ)*∑ ω,w ω*q ω := by
  intro N
  induction N with
  | zero => simp [iidSum]
  | succ N ih =>
    rw [sum_strings]
    simp only [iidWeight,iidSum,Fin.cons_zero,Fin.cons_succ,mul_add,sum_add_distrib]
    simp_rw [mul_assoc,←Finset.mul_sum,←sum_mul,iidWeight_sum w hsum,one_mul,ih]
    rw [hsum,one_mul]
    push_cast
    ring

lemma iid_offline (s : Configuration k X) (σ : Ω → List X)
    (t : Ω → List (X × Fin k)) (ht : ∀ ω, configurationAfter s (t ω)=s)
    (hc : ∀ ω, Episode.traceCost s (t ω)=2*optimalCost s (σ ω))
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω,w ω=1) (N : ℕ) :
    (∑ v, iidWeight w N v*optimalCost s (iidWord (fun ω=>(t ω).map Prod.fst) N v)) ≤
      2*(N : ℝ)*(∑ ω,w ω*optimalCost s (σ ω)) := by
  have hb := sum_le_sum (s:=Finset.univ) (fun v _=>mul_le_mul_of_nonneg_left
    (Episode.optimalCost_le_trace s (iidTrace t N v)) (iidWeight_nonneg w hw N v))
  simp only [iidTrace_requests,iidTrace_cost s t ht] at hb
  refine hb.trans_eq ?_
  rw [iidSum_expectation w _ hsum]
  simp_rw [hc]
  rw [show (∑ ω,w ω*(2*optimalCost s (σ ω)))=2*∑ ω,w ω*optimalCost s (σ ω) by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro ω _; ring]
  ring

universe v
variable {Λ : Type v} [Fintype Λ]

def pushWeights (f : Ω → Λ) (w : Ω → ℝ) : Λ → ℝ :=
  by classical exact fun y=>∑ ω, if f ω=y then w ω else 0

omit [Fintype Λ] in
lemma pushWeights_nonneg (f : Ω → Λ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    ∀ y, 0 ≤ pushWeights f w y := by
  classical
  intro y
  unfold pushWeights
  exact sum_nonneg fun ω _=>by split_ifs; exact hw ω; exact le_rfl

lemma pushWeights_expectation (f : Ω → Λ) (w : Ω → ℝ) (g : Λ → ℝ) :
    (∑ y, pushWeights f w y*g y)=∑ ω,w ω*g (f ω) := by
  classical
  simp only [pushWeights,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp

lemma pushWeights_sum (f : Ω → Λ) (w : Ω → ℝ) (hsum : ∑ ω,w ω=1) :
    ∑ y,pushWeights f w y=1 := by
  simpa only [mul_one,hsum] using pushWeights_expectation f w (fun _=>1)

omit [NeZero k] in
/-- Exact transport of a horizon law to a finite indexed family; identically
valued words are grouped rather than incorrectly treated as different inputs. -/
lemma fixed_law_indexed [Fintype X] (s : Configuration k X) (c D : ℝ)
    (hfinite : ∀ H : ℕ, ∀ q : (Fin H → X) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k X, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v))  ≤ 
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D)
    (σ : Ω → List X) (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hsum : ∑ ω,w ω=1)
    (H : ℕ) (hH : ∀ ω,(σ ω).length=H) :
    ∃ A : Policy k X, StronglyLazy s A ∧
      (∑ ω,w ω*expectedCost A s (σ ω))  ≤  c*(∑ ω,w ω*optimalCost s (σ ω))+D := by
  let f : Ω → (Fin H → X) := fun ω i=>(σ ω).get (Fin.cast (hH ω).symm i)
  have hf (ω : Ω) : List.ofFn (f ω)=σ ω := by
    apply List.ext_getElem (by simpa using (hH ω).symm)
    intro n hn hn'
    simp [f]
  obtain ⟨A,hA,hb⟩ := hfinite H (pushWeights f w)
    (pushWeights_nonneg f w hw) (pushWeights_sum f w hsum)
  rw [pushWeights_expectation,pushWeights_expectation] at hb
  simp only [hf] at hb
  exact ⟨A,hA,hb⟩

/-- Removing a fixed additive term by arbitrarily many repetitions. This
argument includes the zero-optimum case without assuming a positive Q. -/
lemma remove_additive (m q D : ℝ) (h : ∀ N : ℕ, (N : ℝ)*m ≤ (N : ℝ)*q+D) : m ≤ q := by
  by_contra hmq
  have hp : 0 < m-q := sub_pos.mpr (lt_of_not_ge hmq)
  obtain ⟨N,hN⟩ := exists_nat_gt (D/(m-q))
  have hmul : D<(N : ℝ)*(m-q) := (div_lt_iff₀ hp).mp hN
  have hb := h N
  nlinarith

/-- Episode amplification transfers the finite-law estimate to a horizon-uniform competitive bound. -/


theorem amplification_of_uniform_finite_law [Fintype X]
    (s : Configuration k X) (hs : Function.Injective s) (hne : ∃ x y : X,x≠y)
    (c D : ℝ) (hc : 0 ≤ c)
    (hfinite : ∀ H : ℕ, ∀ q : (Fin H → X) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k X, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v))  ≤ 
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D)
    (σ : Ω → List X) (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hsum : ∑ ω,w ω=1) :
    ∃ P : Policy k X, (∑ ω,w ω*expectedCost P s (σ ω))  ≤ 
      2*c*(∑ ω,w ω*optimalCost s (σ ω)) := by
  obtain ⟨P,hP⟩ := law_minimum s σ w
  let m := ∑ ω,w ω*expectedCost P s (σ ω)
  let Q := ∑ ω,w ω*optimalCost s (σ ω)
  obtain ⟨R,hR,hreset⟩ := expected_reset s hs hne
  obtain ⟨L,ρ,t,ht⟩ := closed_padded_episodes s σ R
  let ep : Ω → List X := fun ω=>(t ω).map Prod.fst
  have hep : ep=(fun ω=>σ ω++ρ ω++(List.replicate R (List.ofFn s)).flatten) :=
    funext fun ω=>(ht ω).1
  have hlen (ω : Ω) : (ep ω).length=L := by
    simp only [ep,List.length_map,(ht ω).2.2.2]
  have hcN : ∀ N : ℕ, (N : ℝ)*m  ≤  (N : ℝ)*(2*c*Q)+D := by
    intro N
    obtain ⟨A,hA,hcost⟩ := fixed_law_indexed s c D hfinite (iidWord ep N)
      (iidWeight w N) (iidWeight_nonneg w hw N) (iidWeight_sum w hsum N)
      (N*L) (iidWord_length ep L hlen N)
    have hupper := iid_offline s σ t (fun ω=>(ht ω).2.1) (fun ω=>(ht ω).2.2.1) w hw hsum N
    have hc' := hcost.trans (add_le_add (mul_le_mul_of_nonneg_left hupper hc) le_rfl)
    have hstep := episode_step A s w hw hsum σ ρ
      ((List.replicate R (List.ofFn s)).flatten) m hP (hreset A hA)
    rw [←hep] at hstep
    have hlower := episode_telescope A s w hw hsum ep m hstep N []
    rw [Episode.configurationAfter_nil,matching_self,zero_add,runCost_iid A s w hsum] at hlower
    have hid (v : Fin N → Ω) : cost A s [] (iidWord ep N v)=expectedCost A s (iidWord ep N v) := rfl
    simp only [hid] at hlower
    change (N : ℝ)*m  ≤  _ at hlower
    dsimp [Q]
    nlinarith
  exact ⟨P,remove_additive m (2*c*Q) D hcN⟩

end
end Amplification
end KServer

namespace KServer
noncomputable section
open Finset
universe u

def FiniteDistribution (Ω : Type*) [Fintype Ω] :=
  {w : Ω → ℝ // (∀ ω, 0 ≤ w ω) ∧ ∑ ω, w ω = 1}

def FiniteLawStatement : Prop :=
  ∃ a : ℝ, ∀ (Y : Type u) (_ : MetricSpace Y) (_ : Fintype Y),
    (∃ x y : Y, x ≠ y) → ∀ k : ℕ, 2 ≤ k → ∀ s : Configuration k Y,
      ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ H : ℕ, ∀ law : FiniteDistribution (Fin H → Y),
        ∃ A : Policy k Y, StronglyLazy s A ∧
          (∑ σ, law.val σ * expectedCost A s (List.ofFn σ)) ≤
            a * (1 + Real.log (k + 1)) ^ 2 *
              (∑ σ, law.val σ * optimalCost s (List.ofFn σ)) + D₀


/-- The finite-law estimate implies the arbitrary-metric competitive bound
through closed-episode amplification and product compactness. -/
theorem finite_law_suffices_for_main : FiniteLawStatement.{u} → ReductionStatement.{u} := by
  intro h
  obtain ⟨a,ha⟩ := h
  apply main_reduction
  refine ⟨2*max a 0,mul_nonneg (by norm_num) (le_max_right _ _),?_⟩
  intro k hk Y _ _ s hs Ω _ σ w hw hsum
  let : NeZero k := ⟨by omega⟩
  have hne : ∃ x y : Y, x≠y := by
    refine ⟨s ⟨0,by omega⟩,s ⟨1,by omega⟩,?_⟩
    intro he
    have hi := congrArg Fin.val (hs he)
    exact Nat.zero_ne_one hi
  obtain ⟨D,hD,hF⟩ := ha Y inferInstance inferInstance hne k hk s
  let c := max a 0*(1+Real.log (k+1))^2
  have hc : 0 ≤ c := mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hfinite : ∀ H : ℕ, ∀ q : (Fin H → Y) → ℝ,
      (∀ v,0 ≤ q v) → (∑ v,q v=1) → ∃ A : Policy k Y, StronglyLazy s A ∧
        (∑ v,q v*expectedCost A s (List.ofFn v)) ≤
          c*(∑ v,q v*optimalCost s (List.ofFn v))+D := by
    intro H q hq hqsum
    obtain ⟨A,hA,hb⟩ := hF H ⟨q,hq,hqsum⟩
    refine ⟨A,hA,hb.trans ?_⟩
    refine add_le_add ?_ le_rfl
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · exact sum_nonneg fun v _=>mul_nonneg (hq v) (optimalCost_nonneg s _)
  obtain ⟨P,hP⟩ := Amplification.amplification_of_uniform_finite_law
    s hs hne c D hc hfinite σ w hw hsum
  refine ⟨P,hP.trans_eq ?_⟩
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro ω _
  dsimp [c]
  ring

end
end KServer

end

end OAI
