import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.Dirac

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

open Set MeasureTheory

attribute [local instance] Classical.propDecidable

theorem record_annular_bound {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (p : ι → X) (w : ι → ℝ) (M M' E D L : ℝ) (hM : 0 < M)
    (hE : 0 ≤ E) (_hL : 0 < L) (hrecord : M' ≤ M/L)
    (S : Set X) (hS : MeasurableSet S)
    (hbound : D^2 ≤ E*M'*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2)) :
    D^2 ≤ (E/L)*(atomic p w M hM.le S : ℝ) := by
  classical
  rw [atomic_apply p w M hM.le S hS]
  have hs : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc
    D^2 ≤ E*M'*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) := hbound
    _ ≤ E*(M/L)*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrecord hE) hs
    _ = (E/L)*(M*(∑ i ∈ Finset.univ.filter (fun i => p i ∈ S), (w i)^2)) := by ring

end CannonAtomic

open Set Filter Metric Topology

namespace CannonAnnularCompactness

variable {X : Type*} [PseudoMetricSpace X]

def closedAnnulus (x : X) (R : ℝ) : Set X :=
  {y | R/4 ≤ dist y x ∧ dist y x ≤ 4*R}

lemma annuli_disjoint (x : X) (R S : ℝ) (h : 16*S < R) :
    Disjoint (closedAnnulus x R) (closedAnnulus x S) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  dsimp [closedAnnulus] at hy hz
  linarith [hy.1, hz.2]

theorem disjoint_atomic_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Finset ι) (w : ι → ℝ) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (∑ k, ∑ i ∈ A k, (w i)^2) ≤ ∑ i, (w i)^2 := by
  classical
  rw [← Finset.sum_biUnion (fun _ _ _ _ hne => hA hne)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  exact fun i _ _ => sq_nonneg _

theorem many_annuli_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Finset ι) (w : ι → ℝ) (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (D C E : ℝ) (hC : 0 ≤ C) (hmass : (∑ i, (w i)^2) ≤ E)
    (hlocal : ∀ k, D^2 ≤ C * (∑ i ∈ A k, (w i)^2)) :
    (Fintype.card κ : ℝ)*D^2 ≤ C*E := by
  calc
    _ = ∑ k : κ, D^2 := by simp
    _ ≤ ∑ k : κ, C * (∑ i ∈ A k, (w i)^2) :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = C * (∑ k : κ, ∑ i ∈ A k, (w i)^2) := (Finset.mul_sum ..).symm
    _ ≤ C * (∑ i, (w i)^2) :=
      mul_le_mul_of_nonneg_left (disjoint_atomic_energy A w hA) hC
    _ ≤ C*E := mul_le_mul_of_nonneg_left hmass hC

theorem equicontinuousAt_of_tail_quadratic (f : ℕ → X → ℝ) (x : X) (E : ℝ)
    (hE : 0 ≤ E) (hf : ∀ n, ContinuousAt (f n) x)
    (hb : ∀ m : ℕ, ∃ δ > 0, ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ y, dist y x < δ →
        (m : ℝ)*(f n x-f n y)^2 ≤ E) :
    EquicontinuousAt f x := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (E/ε^2)
  have hmpos : (0:ℝ) < m := (div_nonneg hE (sq_nonneg ε)).trans_lt hm
  have hsmall : E < (m:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hm
  obtain ⟨δ, hδ, N, hN⟩ := hb m
  have heq : EquicontinuousAt (fun n : Fin N => f n) x :=
    equicontinuousAt_finite.mpr (fun n => hf n)
  have hfin := Metric.equicontinuousAt_iff_right.mp heq ε hε
  filter_upwards [hfin, Metric.ball_mem_nhds x hδ] with y hy hyr n
  by_cases hn : n < N
  · exact hy ⟨n, hn⟩
  · have hbound := hN n (le_of_not_gt hn) y hyr
    rw [Real.dist_eq]
    by_contra hh
    have hge : ε ≤ |f n x-f n y| := le_of_not_gt hh
    have hsq := pow_le_pow_left₀ hε.le hge 2
    rw [sq_abs] at hsq
    have := mul_le_mul_of_nonneg_left hsq hmpos.le
    linarith

end CannonAnnularCompactness

namespace CannonAnnularCompactness

open MeasureTheory
open scoped NNReal ENNReal

lemma finite_measure_disjoint_sum {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : FiniteMeasure X) (A : ι → Set X) (hmeas : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (∑ i, (μ (A i) : ℝ)) ≤ (μ.mass : ℝ) := by
  classical
  have h := sum_measure_le_measure_univ (μ := (μ : Measure X))
    (s := Finset.univ) (t := A) (fun i _ => (hmeas i).nullMeasurableSet)
    (fun i _ j _ hij => (hdis hij).aedisjoint)
  simp only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  have h' : (∑ i, μ (A i) : ℝ≥0) ≤ μ univ := by exact_mod_cast h
  exact_mod_cast h'

theorem equicontinuousAt_of_disjoint_measures {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace Y]
    (f : ℕ → X → ℝ) (x : X) (μ : ℕ → FiniteMeasure Y) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hmass : ∀ n, ((μ n).mass : ℝ) ≤ E)
    (hf : ∀ n, ContinuousAt (f n) x)
    (hb : ∀ m : ℕ, ∃ A : Fin (m+1) → Set Y,
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∃ δ > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ y, dist y x < δ →
        (f n x - f n y)^2 ≤ C*(μ n (A i) : ℝ)) :
    EquicontinuousAt f x := by
  classical
  apply equicontinuousAt_of_tail_quadratic f x (C*E) (mul_nonneg hC hE) hf
  intro m
  obtain ⟨A,hA,hdis,hb⟩ := hb m
  choose δ hδ N hN using hb
  let d := Finset.univ.inf' Finset.univ_nonempty δ
  have hd : 0 < d := (Finset.lt_inf'_iff _).mpr (fun i _ => hδ i)
  let n₀ := Finset.univ.sup N
  refine ⟨d,hd,n₀,?_⟩
  intro n hn y hy
  have hlocal (i : Fin (m+1)) : (f n x-f n y)^2 ≤ C*(μ n (A i) : ℝ) := by
    apply hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) y
    exact hy.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  have he : ((m+1 : ℕ) : ℝ)*(f n x-f n y)^2 ≤ C*E := by
    calc
      _ = ∑ i : Fin (m+1), (f n x-f n y)^2 := by simp
      _ ≤ ∑ i : Fin (m+1), C*(μ n (A i) : ℝ) := Finset.sum_le_sum (fun i _ => hlocal i)
      _ = C*(∑ i : Fin (m+1), (μ n (A i) : ℝ)) := (Finset.mul_sum ..).symm
      _ ≤ C*((μ n).mass : ℝ) := mul_le_mul_of_nonneg_left
        (finite_measure_disjoint_sum (μ n) A hA hdis) hC
      _ ≤ C*E := mul_le_mul_of_nonneg_left (hmass n) hC
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m)
    (sq_nonneg (f n x-f n y))).trans he

theorem equicontinuousAt_of_annular_tails {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (f : ℕ → X → ℝ) (x : X) (μ : ℕ → FiniteMeasure X) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hmass : ∀ n, ((μ n).mass : ℝ) ≤ E)
    (hf : ∀ n, ContinuousAt (f n) x)
    (R : ℕ → ℝ) (hR : ∀ i j, i < j → 16*R j < R i)
    (hb : ∀ i, ∃ δ > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ y, dist y x < δ →
      (f n x - f n y)^2 ≤ C*(μ n (closedAnnulus x (R i)) : ℝ)) :
    EquicontinuousAt f x := by
  apply equicontinuousAt_of_disjoint_measures f x μ C E hC hE hmass hf
  intro m
  refine ⟨fun i => closedAnnulus x (R i), ?_, ?_, fun i => hb i⟩
  · intro i
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact annuli_disjoint x (R i) (R j) (hR i j h)
    · exact (annuli_disjoint x (R j) (R i) (hR j i h)).symm

end CannonAnnularCompactness

open Set Filter Topology

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
