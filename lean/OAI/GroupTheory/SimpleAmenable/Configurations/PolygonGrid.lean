import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGrid
open Classical Set MeasureTheory Metric
namespace PolygonGrid

abbrev PlaneTracks := ℕ × ℝ × ℝ
abbrev Index (m N : ℕ) := Fin m × Fin N × Fin N
noncomputable def μ : Measure PlaneTracks := Measure.count.prod ((volume : Measure ℝ).prod volume)
noncomputable def interval (ε : ℝ) (i : ℕ) : Set ℝ := Ico (ε*i) (ε*(i+1))
noncomputable def cell {m N : ℕ} (ε : ℝ) (i : Index m N) : Set PlaneTracks :=
  {i.1.val} ×ˢ interval ε i.2.1.val ×ˢ interval ε i.2.2.val
noncomputable def region (m : ℕ) : Set PlaneTracks :=
  {i : ℕ | i < m} ×ˢ Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1

@[simp] theorem measurable_cell {m N : ℕ} (ε : ℝ) (i : Index m N) : MeasurableSet (cell ε i) :=
  (measurableSet_singleton _).prod (measurableSet_Ico.prod measurableSet_Ico)

@[simp] theorem volume_cell {m N : ℕ} (ε : ℝ) (i : Index m N) :
    μ (cell ε i)=ENNReal.ofReal ε * ENNReal.ofReal ε := by
  simp only [μ,cell,interval,Measure.prod_prod,Measure.count_singleton,one_mul,Real.volume_Ico]
  congr 2 <;> ring

theorem cells_disjoint {m N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun i j : Index m N => Disjoint (cell ε i) (cell ε j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have ht : i.1=j.1 := Fin.ext (hi.1.symm.trans hj.1)
  have coord {i j : ℕ} {x : ℝ} (hi : x∈interval ε i) (hj : x∈interval ε j) : i=j := by
    rcases lt_trichotomy i j with h|h|h
    · have h' : (i:ℝ)+1 ≤ j := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hε.le
      change ε*i ≤ x ∧ x < ε*(i+1) at hi
      change ε*j ≤ x ∧ x < ε*(j+1) at hj
      linarith
    · exact h
    · have h' : (j:ℝ)+1 ≤ i := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hε.le
      change ε*i ≤ x ∧ x < ε*(i+1) at hi
      change ε*j ≤ x ∧ x < ε*(j+1) at hj
      linarith
  exact hij (Prod.ext ht (Prod.ext (Fin.ext (coord hi.2.1 hj.2.1)) (Fin.ext (coord hi.2.2 hj.2.2))))

theorem cell_dist {m N : ℕ} {ε : ℝ} (hε : 0 < ε) {i : Index m N} {p q : PlaneTracks}
    (hp : p∈cell ε i) (hq : q∈cell ε i) : dist p q < ε := by
  have coord {i : ℕ} {x y : ℝ} (hx : x∈interval ε i) (hy : y∈interval ε i) : dist x y < ε := by
    rw [Real.dist_eq,abs_lt]
    change ε*i ≤ x ∧ x < ε*(i+1) at hx
    change ε*i ≤ y ∧ y < ε*(i+1) at hy
    constructor <;> nlinarith
  have ht : p.1=q.1 := hp.1.trans hq.1.symm
  rw [Prod.dist_eq,Prod.dist_eq,ht,dist_self,max_lt_iff,max_lt_iff]
  exact ⟨hε,coord hp.2.1 hq.2.1,coord hp.2.2 hq.2.2⟩

theorem region_covered {m N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : 1/ε < (N:ℝ)) :
    region m⊆⋃i : Index m N,cell ε i := by
  rintro ⟨t,x,y⟩ ⟨ht,hx,hy⟩
  have coord {x : ℝ} (hx : x∈Ico (0:ℝ) 1) : ∃i : Fin N,x∈interval ε i.val := by
    have hnon : 0 ≤ x/ε := div_nonneg hx.1 hε.le
    have hlt : x/ε < (N:ℝ) := (div_lt_div_of_pos_right hx.2 hε).trans hN
    have hi : ⌊x/ε⌋₊ < N := by
      exact_mod_cast lt_of_le_of_lt (Nat.floor_le hnon) hlt
    refine ⟨⟨⌊x/ε⌋₊,hi⟩,?_,?_⟩
    · have h := (le_div_iff₀ hε).mp (Nat.floor_le hnon)
      nlinarith
    · have h := (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (x/ε))
      nlinarith
  obtain ⟨i,hi⟩ := coord hx
  obtain ⟨j,hj⟩ := coord hy
  exact Set.mem_iUnion.mpr ⟨(⟨t,ht⟩,i,j),rfl,hi,hj⟩

theorem volume_cells {m N : ℕ} {ε : ℝ} (hε : 0 < ε) (I : Finset (Index m N)) :
    μ (⋃i∈I,cell ε i)=I.card*(ENNReal.ofReal ε * ENNReal.ofReal ε) := by
  rw [measure_biUnion_finset (fun i hi j hj hij => cells_disjoint hε hij)
    (fun i _ => measurable_cell ε i)]
  simp only [volume_cell,Finset.sum_const, nsmul_eq_mul]

theorem matching_of_volume {m N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (I J : Finset (Index m N))
    (hμ : μ (⋃i∈I,cell ε i) < μ (⋃j∈J,cell ε j)) : Nonempty (I ↪ J) := by
  have hc : I.card ≤ J.card := by
    by_contra hn
    have hnat : J.card ≤ I.card := by omega
    have hcast : (J.card : ENNReal) ≤ I.card := by exact_mod_cast hnat
    rw [volume_cells hε,volume_cells hε] at hμ
    exact not_lt_of_ge (mul_le_mul hcast le_rfl (by positivity) (by positivity)) hμ
  have hf : Fintype.card I ≤ Fintype.card J := by simpa using hc
  exact Function.Embedding.nonempty_of_card_le hf

end PolygonGrid
end PolygonGrid

end SimpleAmenable
end
end

end OAI
