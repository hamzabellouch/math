import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pool
import OAI.Combinatorics.KMedianRecovery.Recovery.PhasesBounded

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

abbrev Label (V : Type*) := V ⊕ (ℕ × V × ℚ)

def root (c : ℕ × V × ℚ) : V := c.2.1
def height (c : ℕ × V × ℚ) : ℝ := (max c.2.2 0:ℚ)

@[instance_reducible] noncomputable def metric : PseudoMetricSpace (Label V) :=
  LeafMetric.attachedMetric root height (fun c=>by
    dsimp only [height]
    exact_mod_cast (le_max_right c.2.2 0))

attribute [local instance] metric

def original : V ↪ Label V := ⟨Sum.inl,Sum.inl_injective⟩
def leaf (key : ℕ) (i : V) (s : ℚ) : Label V := Sum.inr (key,i,s)

def parent : Label V → V := Sum.elim id root

def rows {d : ℕ} (distance : V → Fin d → ℚ) : Label V → Fin d → ℚ :=
  fun x j=>match x with
  | .inl i => distance i j
  | .inr c => distance (root c) j+max c.2.2 0

lemma original_dist (i j : V) :
    dist (original i) (original j)=dist i j := LeafMetric.original_distance root height i j

lemma leaf_dist (i j : V) (key : ℕ) (s : ℚ) :
    dist (original i) (leaf key j s)=dist i j+(max s 0:ℚ) :=
  LeafMetric.copy_distance root height i (key,j,s)

lemma rows_spec {d : ℕ} (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hd : ∀ i j,(distance i j:ℝ)=dist i (loc j)) :
    ∀ x j,(rows distance x j:ℝ)=dist x (original (loc j)) := by
  intro x j
  cases x with
  | inl x =>
    change (distance x j:ℝ)=dist (original x) (original (loc j))
    rw [original_dist,hd]
  | inr c =>
    rw [dist_comm]
    change ((distance (root c) j+max c.2.2 0:ℚ):ℝ)=dist (original (loc j)) (leaf c.1 c.2.1 c.2.2)
    rw [Rat.cast_add,leaf_dist,hd,dist_comm]
    rfl

variable [DecidableEq V]

def Before (key : ℕ) (B : Finset (Label V)) : Prop :=
  ∀ c,Sum.inr c∈B → c.1<key

omit [PseudoMetricSpace V] in
lemma fresh (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (s : ℚ) : leaf key i s ∉ F.image original ∪ B := by
  intro h
  rcases Finset.mem_union.mp h with h|h
  · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    cases hx
  · exact (lt_irrefl key) (hB (key,i,s) h)

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma Before.mono {B : Finset (Label V)} {a b : ℕ} (h : Before a B) (hab : a≤b) : Before b B :=
  fun c hc=>(h c hc).trans_le hab

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma Before.subset {B C : Finset (Label V)} {key : ℕ} (h : Before key C) (hB : B⊆C) : Before key B :=
  fun c hc=>h c (hB hc)

def copy (key : ℕ) : Label V → Label V :=
  Sum.elim (fun i=>leaf key i 0) Sum.inr

omit [DecidableEq V] in
lemma copy_dist (key : ℕ) (i j : V) :
    dist (original i) (copy key (original j))=dist i j := by
  rw [show copy key (original j)=leaf key j 0 from rfl,leaf_dist]
  simp

omit [PseudoMetricSpace V] in
lemma pool_before (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B) :
    Before (key+1) (PhaseMergePath.pool (F.image original) B (copy key)) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc|hc
  · exact (hB c hc).trans (by omega)
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have hh : c=(key,j,0) := by simpa only [copy,original,leaf,Function.Embedding.coeFn_mk,Sum.elim_inl,Sum.inr.injEq] using he.symm
    subst c
    omega

omit [PseudoMetricSpace V] in
lemma singleton_before (key : ℕ) (i : V) (s : ℚ) (B : Finset (Label V)) (hB : Before key B) :
    Before (key+1) (insert (leaf key i s) B) := by
  intro c hc
  rcases Finset.mem_insert.mp hc with he|hc
  · have hh : c=(key,i,s) := Sum.inr.inj he
    subst c
    omega
  · exact (hB c hc).trans (by omega)

def shorten (key : ℕ) (i : V) (l u : ℚ) : Label V → Label V :=
  Equiv.swap (leaf key i u) (leaf key i l)

omit [PseudoMetricSpace V] in
lemma shorten_injective (key : ℕ) (i : V) (l u : ℚ) : Function.Injective (shorten key i l u) :=
  (Equiv.swap _ _).injective

omit [PseudoMetricSpace V] in
lemma shorten_original (key : ℕ) (i j : V) (l u : ℚ) : shorten key i l u (original j)=original j :=
  Equiv.swap_apply_of_ne_of_ne (by simp [original,leaf]) (by simp [original,leaf])

omit [PseudoMetricSpace V] in
lemma shorten_old (key : ℕ) (i : V) (l u : ℚ) (B : Finset (Label V)) (hB : Before key B)
    (x : Label V) (hx : x∈B) : shorten key i l u x=x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; subst x; exact (lt_irrefl key) (hB (key,i,u) hx)
  · intro he; subst x; exact (lt_irrefl key) (hB (key,i,l) hx)

lemma shorten_dist (key : ℕ) (i : V) (l u : ℚ) (hl : 0≤l) (hlu : l≤u)
    (F : Finset V) (B : Finset (Label V)) (hB : Before key B) (j : V)
    (x : Label V) (hx : x∈F.image original ∪ insert (leaf key i u) B) :
    dist (original j) (shorten key i l u x) ≤ dist (original j) x ∧
      dist (original j) x ≤ dist (original j) (shorten key i l u x)+(u-l:ℚ) := by
  have heps : (0:ℝ)≤(u-l:ℚ) := by exact_mod_cast sub_nonneg.mpr hlu
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    rw [shorten_original]
    exact ⟨le_rfl,le_add_of_nonneg_right heps⟩
  · rcases Finset.mem_insert.mp hx with rfl|hx
    · rw [shorten,Equiv.swap_apply_left,leaf_dist,leaf_dist,max_eq_left hl,max_eq_left (hl.trans hlu)]
      constructor
      · have hh : (l:ℝ)≤(u:ℝ) := by exact_mod_cast hlu
        linarith
      · push_cast; linarith
    · rw [shorten_old key i l u B hB x hx]
      exact ⟨le_rfl,le_add_of_nonneg_right heps⟩

end MetricKMedianRecovery.RationalLeaves

end OAI
