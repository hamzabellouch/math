import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodUniqueness

namespace OAI

namespace ConvexSkorokhod

open Set MeasureTheory

noncomputable def unitGrid (m j : ℕ) : unitInterval :=
  ⟨min ((j:ℝ)/m) 1,⟨le_min (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) zero_le_one,min_le_right _ _⟩⟩

noncomputable def vectorStep {E : Type*} [AddCommMonoid E] (f : unitInterval → E) (m : ℕ) : unitInterval → E :=
  fun t => ∑j∈Finset.range m,(Ioc (unitGrid m j) (unitGrid m (j+1))).indicator (fun _ => f (unitGrid m j)) t

end ConvexSkorokhod

namespace ConvexSkorokhod

open Set Filter MeasureTheory

lemma unitGrid_val (m j : ℕ) (hm : 0 < m) (hj : j ≤ m) :
    (unitGrid m j : ℝ)=(j:ℝ)/m := min_eq_left (uniform_grid_mem m j hm hj).2

@[simp] lemma unitGrid_zero (m : ℕ) : unitGrid m 0=0 := by
  apply Subtype.ext;simp [unitGrid]

lemma grid_cell_unique (m j k : ℕ) (hm : 0 < m) (hj : j < m) (hk : k < m)
    (t : unitInterval) (htj : t∈Ioc (unitGrid m j) (unitGrid m (j+1)))
    (htk : t∈Ioc (unitGrid m k) (unitGrid m (k+1))) : j=k := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have h₁ : (j:ℝ)/m < t ∧ (t:ℝ) ≤ ((j+1:ℕ):ℝ)/m := by
    change (unitGrid m j : ℝ)<t ∧ (t:ℝ) ≤ (unitGrid m (j+1) : ℝ) at htj
    simpa only [unitGrid_val m j hm hj.le,unitGrid_val m (j+1) hm hj] using htj
  have h₂ : (k:ℝ)/m < t ∧ (t:ℝ) ≤ ((k+1:ℕ):ℝ)/m := by
    change (unitGrid m k : ℝ)<t ∧ (t:ℝ) ≤ (unitGrid m (k+1) : ℝ) at htk
    simpa only [unitGrid_val m k hm hk.le,unitGrid_val m (k+1) hm hk] using htk
  rcases lt_trichotomy j k with h|h|h
  · have hle : ((j+1:ℕ):ℝ)/m ≤ (k:ℝ)/m :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) hm'.le
    exact False.elim (not_lt_of_ge (h₁.2.trans hle) h₂.1)
  · exact h
  · have hle : ((k+1:ℕ):ℝ)/m ≤ (j:ℝ)/m :=
      div_le_div_of_nonneg_right (by exact_mod_cast h) hm'.le
    exact False.elim (not_lt_of_ge (h₂.2.trans hle) h₁.1)

lemma exists_grid_cell (m : ℕ) (hm : 0 < m) (t : unitInterval) (ht : t≠0) :
    ∃j < m,t∈Ioc (unitGrid m j) (unitGrid m (j+1)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have htpos : (0:ℝ) < t := lt_of_le_of_ne t.property.1 (by intro h;apply ht;exact Subtype.ext h.symm)
  have hp : 0 < (t:ℝ)*m := mul_pos htpos hm'
  have hcpos : 0 < ⌈(t:ℝ)*m⌉₊ := Nat.ceil_pos.mpr hp
  have hcle : ⌈(t:ℝ)*m⌉₊ ≤ m := Nat.ceil_le.mpr (by nlinarith [t.property.2])
  let j := ⌈(t:ℝ)*m⌉₊-1
  have he : j+1=⌈(t:ℝ)*m⌉₊ := Nat.sub_add_cancel hcpos
  have hj : j < m := by omega
  refine ⟨j,hj,?_⟩
  have hlow := Nat.ceil_lt_add_one hp.le
  have hup := Nat.le_ceil ((t:ℝ)*m)
  have he' : (j:ℝ)+1=(⌈(t:ℝ)*m⌉₊:ℝ) := by exact_mod_cast he
  change (unitGrid m j : ℝ)<t ∧ (t:ℝ) ≤ (unitGrid m (j+1) : ℝ)
  rw [unitGrid_val m j hm hj.le,unitGrid_val m (j+1) hm hj]
  constructor
  · apply (div_lt_iff₀ hm').mpr;linarith
  · apply (le_div_iff₀ hm').mpr;rw [he];exact hup

lemma grid_cell_dist (m j : ℕ) (hm : 0 < m) (hj : j < m)
    (t : unitInterval) (ht : t∈Ioc (unitGrid m j) (unitGrid m (j+1))) :
    dist t (unitGrid m j) ≤ 1/(m:ℝ) := by
  have hlo : (unitGrid m j : ℝ) < t := ht.1
  have hup : (t:ℝ) ≤ (unitGrid m (j+1) : ℝ) := ht.2
  rw [unitGrid_val m j hm hj.le] at hlo
  rw [unitGrid_val m (j+1) hm hj] at hup
  rw [Subtype.dist_eq,Real.dist_eq,unitGrid_val m j hm hj.le,abs_of_nonneg (sub_nonneg.mpr hlo.le)]
  have he : (((j+1:ℕ):ℝ)/m)-(j:ℝ)/m=1/m := by push_cast;ring
  linarith

lemma vectorStep_eq_cell {E : Type*} [AddCommMonoid E] (f : unitInterval → E)
    (m j : ℕ) (hm : 0 < m) (hj : j < m) (t : unitInterval)
    (ht : t∈Ioc (unitGrid m j) (unitGrid m (j+1))) : vectorStep f m t=f (unitGrid m j) := by
  classical
  rw [vectorStep,Finset.sum_eq_single j]
  · exact Set.indicator_of_mem ht _
  · intro i hi hij
    apply Set.indicator_of_notMem
    intro hti
    exact hij (grid_cell_unique m i j hm (Finset.mem_range.mp hi) hj t hti ht)
  · intro hj';exact False.elim (hj' (Finset.mem_range.mpr hj))

@[simp] lemma vectorStep_zero {E : Type*} [AddCommMonoid E] (f : unitInterval → E) (m : ℕ) :
    vectorStep f m 0=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply Set.indicator_of_notMem
  intro ht
  exact not_lt_of_ge (show (0:unitInterval) ≤ unitGrid m j from bot_le) ht.1

end ConvexSkorokhod

end OAI
