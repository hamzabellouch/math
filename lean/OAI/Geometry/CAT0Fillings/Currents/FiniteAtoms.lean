import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.RectifiableCoarea
import OAI.Geometry.CAT0Fillings.Currents.Atoms

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology

lemma finite_support_int_of_summable_abs {ι : Type*} (a : ι → ℤ)
    (h : Summable (fun i => |(a i : ℝ)|)) : (Function.support a).Finite := by
  have he : ∀ᶠ i in cofinite, |(a i : ℝ)| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply (eventually_cofinite.mp he).subset
  intro i hi
  have hi' : a i ≠ 0 := hi
  have hab : (1 : ℝ) ≤ |(a i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact not_lt.mpr hab

noncomputable def padFinite {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A) : Fin N → A :=
  fun i => Fin.addCases f (fun _ => z) ((finCongr (Nat.add_sub_of_le hm).symm) i)

lemma padFinite_property {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A)
    (P : A → Prop) (hf : ∀ i, P (f i)) (hz : P z) : ∀ i, P (padFinite hm f z i) := by
  intro i
  dsimp only [padFinite]
  generalize (finCongr (Nat.add_sub_of_le hm).symm) i = j
  exact Fin.addCases (fun i => by simp only [Fin.addCases_left]; exact hf i)
    (fun i => by simp only [Fin.addCases_right]; exact hz) j

lemma sum_padFinite {A : Type*} {m N : ℕ} (hm : m ≤ N) (f : Fin m → A) (z : A)
    (g : A → ℝ) (hz : g z = 0) :
    (∑ i, g (padFinite hm f z i)) = ∑ i, g (f i) := by
  classical
  unfold padFinite
  rw [(finCongr (Nat.add_sub_of_le hm).symm).sum_comp (fun j => g (Fin.addCases f (fun _ => z) j)),
    Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,hz,Finset.sum_const_zero,add_zero]

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

theorem integerRectifiable_zero_finite_representation {T : Functional X 0}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (m : ℝ) ≤ mass T ∧ (∀ i, |(a i : ℝ)| ≤ mass T) ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hI
  choose a x hact using fun i => (C i).zero_exists_atom
  have hmass i : mass (C i).action = |(a i : ℝ)| := by rw [hact i,mass_atomCurrent]
  have haS : Summable (fun i => |(a i : ℝ)|) := by simpa only [hmass] using hCS
  have hfinite := finite_support_int_of_summable_abs a haS
  let s := hfinite.toFinset
  have hs : ∀ i, i ∈ s ↔ a i ≠ 0 := fun i => hfinite.mem_toFinset
  let e := s.equivFin.symm
  have hnorm i : |(a i : ℝ)| ≤ mass T := by
    apply (haS.le_tsum i (fun j _ => abs_nonneg ((a j : ℤ) : ℝ))).trans
    have hm := chartFamily_mass_sum_le hT C hd hC hCS heq
    simpa only [hmass] using hm
  have hmcard : (s.card : ℝ) ≤ mass T := by
    calc (s.card : ℝ) = ∑ i ∈ s, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ s, |(a i : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast Int.one_le_abs ((hs i).mp hi)
      _ ≤ ∑' i, |(a i : ℝ)| := haS.sum_le_tsum s (fun i _ => abs_nonneg _)
      _ ≤ mass T := by
        have hm := chartFamily_mass_sum_le hT C hd hC hCS heq
        simpa only [hmass] using hm
  refine ⟨s.card,fun i => a (e i),fun i => x (e i),hmcard,fun i => hnorm (e i),?_⟩
  intro b π
  rw [heq]
  simp_rw [hact]
  rw [tsum_eq_sum (s := s) (fun i hi => by
    have hai : a i = 0 := not_not.mp (fun hn => hi ((hs i).mpr hn))
    simp only [atomCurrent,hai,Int.cast_zero,zero_mul,ite_self])]
  rw [←Finset.sum_attach]
  exact (e.sum_comp (fun i : s => atomCurrent (a i) (x i) b π)).symm

end CAT0Fillings

end

end OAI
