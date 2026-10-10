import OAI.Combinatorics.ContingencyTables.Model
import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpAlgorithm
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Positivity

namespace OAI

/-! # The source-row-column-sink network for bounded tables

The only nonzero capacities are the three layers prescribed in the
manuscript. Both antiparallel orientations are stored as one skew flow.
-/

namespace ContingencyTables.LayeredTableNetwork

open scoped BigOperators

abbrev Vertex (m n : ℕ) := Bool ⊕ (Fin m ⊕ Fin n)

variable {m n : ℕ}

def source : Vertex m n := Sum.inl false
def sink : Vertex m n := Sum.inl true
def row (i : Fin m) : Vertex m n := Sum.inr (Sum.inl i)
def column (j : Fin n) : Vertex m n := Sum.inr (Sum.inr j)

def capacity (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℕ
  | .inl false,.inr (.inl i) => r i
  | .inr (.inl i),.inr (.inr j) => b i j
  | .inr (.inr j),.inl true => c j
  | _,_ => 0

def Feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : Vertex m n → Vertex m n → ℤ) : Prop :=
  (∀ u v,f u v= -f v u) ∧
  (∀ u v,f u v≤capacity r c b u v) ∧
  ∀ u,u≠source → u≠sink → (∑ v,f u v)=0

def value (f : Vertex m n → Vertex m n → ℤ) : ℤ := ∑ v,f source v

def tableFlow (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℤ
  | .inl false,.inr (.inl i) => r i
  | .inr (.inl i),.inl false => -(r i:ℤ)
  | .inr (.inl i),.inr (.inr j) => X i j
  | .inr (.inr j),.inr (.inl i) => -(X i j:ℤ)
  | .inr (.inr j),.inl true => c j
  | .inl true,.inr (.inr j) => -(c j:ℤ)
  | _,_ => 0

lemma capacity_diagonal (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (v : Vertex m n) : capacity r c b v v=0 := by
  rcases v with a | (i | j)
  · cases a <;> rfl
  · rfl
  · rfl

lemma tableFlow_skew (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Fin m → Fin n → ℕ) :
    ∀ u v,tableFlow r c X u v= -tableFlow r c X v u := by
  rintro (a | i | j) (d | k | l)
  all_goals (try cases a) <;> (try cases d) <;> simp [tableFlow]

theorem tableFlow_feasible (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b X : Fin m → Fin n → ℕ) (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    Feasible r c b (tableFlow r c X) := by
  refine ⟨tableFlow_skew r c X,?_,?_⟩
  · rintro (a | i | j) (d | k | l)
    all_goals (try cases a) <;> (try cases d) <;> simp [tableFlow,capacity]
    all_goals exact_mod_cast hb _ _
  · rintro (a | i | j) hs ht
    · cases a
      · exact False.elim (hs rfl)
      · exact False.elim (ht rfl)
    · have h : (∑ j,(X i j:ℤ))=(r i:ℤ) := by exact_mod_cast hm.1 i
      simp [Fintype.sum_sum_type,tableFlow,h]
    · have h : (∑ i,(X i j:ℤ))=(c j:ℤ) := by exact_mod_cast hm.2 j
      simp [Fintype.sum_sum_type,tableFlow,h]

theorem tableFlow_value (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : Fin m → Fin n → ℕ) : value (tableFlow r c X)=∑ i,(r i:ℤ) := by
  simp [value,source,tableFlow,Fintype.sum_sum_type]

lemma zero_of_no_capacity (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (u v : Vertex m n)
    (huv : capacity r c b u v=0) (hvu : capacity r c b v u=0) : f u v=0 := by
  have h1 := hf.2.1 u v
  have h2 := hf.2.1 v u
  rw [huv] at h1
  rw [hvu] at h2
  have hs := hf.1 u v
  omega

lemma row_column_nonnegative (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (i : Fin m) (j : Fin n) : 0≤f (row i) (column j) := by
  have h := hf.2.1 (column j) (row i)
  have hs := hf.1 (row i) (column j)
  change f (column j) (row i)≤(0:ℤ) at h
  omega

lemma source_value (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) : value f=∑ i,f source (row i) := by
  have hss : f source source=0 := by have h:=hf.1 source source; omega
  have hst : f source sink=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hsc : ∀ j,f source (column j)=0 := fun j=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  simp only [source,sink,column] at hss hst hsc
  simp [value,source,row,Fintype.sum_sum_type,hss,hst,hsc]

theorem value_le_total (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) : value f≤∑ i,(r i:ℤ) := by
  rw [source_value r c b f hf]
  exact Finset.sum_le_sum (fun i _=>hf.2.1 source (row i))

lemma row_balance (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (i : Fin m) :
    (∑ j,f (row i) (column j))=f source (row i) := by
  have hr : ∀ k,f (row i) (row k)=0 := fun k=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  have ht : f (row i) sink=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hs := hf.1 (row i) source
  have h := hf.2.2 (row i) (by simp [row,source]) (by simp [row,sink])
  have he : (∑ v,f (row i) v)=f (row i) source+(∑ j,f (row i) (column j)) := by
    simp only [row,sink] at hr ht
    simp [Fintype.sum_sum_type,source,row,column,hr,ht]
  rw [he] at h
  omega

lemma column_balance (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (j : Fin n) :
    (∑ i,f (row i) (column j))=f (column j) sink := by
  have hc : ∀ k,f (column j) (column k)=0 := fun k=>
    zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hs : f (column j) source=0 := zero_of_no_capacity r c b f hf _ _ rfl rfl
  have hneg : ∀ i,f (column j) (row i)= -f (row i) (column j) :=
    fun i=>hf.1 _ _
  have h := hf.2.2 (column j) (by simp [column,source]) (by simp [column,sink])
  have he : (∑ v,f (column j) v)=f (column j) sink-(∑ i,f (row i) (column j)) := by
    simp only [row,column,source] at hc hs hneg
    simp [Fintype.sum_sum_type,sink,row,column,hc,hs,hneg,sub_eq_add_neg]
  rw [he] at h
  omega

lemma saturation {q : ℕ} (f g : Fin q → ℤ) (hfg : ∀ i,f i≤g i)
    (hs : (∑ i,f i)=∑ i,g i) : ∀ i,f i=g i := by
  have hsum : (∑ i,(g i-f i))=0 := by
    rw [Finset.sum_sub_distrib,hs]
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>sub_nonneg.mpr (hfg i))).mp hsum
  intro i
  have hi := hz i (Finset.mem_univ i)
  omega

lemma source_saturated (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ)) :
    ∀ i,f source (row i)=r i := by
  apply saturation
  · intro i
    exact hf.2.1 source (row i)
  · simpa only [source_value r c b f hf] using hv

lemma column_saturated (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ))
    (htotal : (∑ i,r i)=∑ j,c j) :
    ∀ j,f (column j) sink=c j := by
  apply saturation
  · intro j
    exact hf.2.1 (column j) sink
  · calc
      (∑ j,f (column j) sink) = ∑ j,∑ i,f (row i) (column j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (column_balance r c b f hf j).symm
      _ = ∑ i,∑ j,f (row i) (column j) := Finset.sum_comm
      _ = ∑ i,(r i:ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (row_balance r c b f hf i).trans (source_saturated r c b f hf hv i)
      _ = ∑ j,(c j:ℤ) := by exact_mod_cast htotal

def decode (f : Vertex m n → Vertex m n → ℤ) (i : Fin m) (j : Fin n) : ℕ :=
  (f (row i) (column j)).toNat

theorem decode_boundedTable (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (f : Vertex m n → Vertex m n → ℤ)
    (hf : Feasible r c b f) (hv : value f=∑ i,(r i:ℤ))
    (htotal : (∑ i,r i)=∑ j,c j) :
    HasMargins (decode f) r c ∧ ∀ i j,decode f i j≤b i j := by
  have hd : ∀ i j,(decode f i j:ℤ)=f (row i) (column j) := fun i j=>
    Int.toNat_of_nonneg (row_column_nonnegative r c b f hf i j)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    have he : (∑ j,(decode f i j:ℤ))=(r i:ℤ) := by
      simp only [hd]
      exact (row_balance r c b f hf i).trans (source_saturated r c b f hf hv i)
    exact_mod_cast he
  · intro j
    have he : (∑ i,(decode f i j:ℤ))=(c j:ℤ) := by
      simp only [hd]
      exact (column_balance r c b f hf j).trans
        (column_saturated r c b f hf hv htotal j)
    exact_mod_cast he
  · intro i j
    have he := hf.2.1 (row i) (column j)
    change f (row i) (column j)≤(b i j:ℤ) at he
    rw [←hd] at he
    exact_mod_cast he

end ContingencyTables.LayeredTableNetwork

end OAI
