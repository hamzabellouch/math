import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Order.Disjointed

namespace OAI

/-! # Finite translate coverings from a Haar-volume ratio -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem disjoint_translate_card_mul_le (μ : Measure G) [μ.IsMulLeftInvariant]
    (S Q R : Set G) (hQ : MeasurableSet Q)
    (hcontain : ∀ a ∈ S, a • Q ⊆ R)
    (t : Finset G) (ht : (t : Set G) ⊆ S)
    (hdisj : (t : Set G).PairwiseDisjoint (fun a => a • Q)) :
    (t.card : ℝ≥0∞) * μ Q ≤ μ R := by
  calc
    (t.card : ℝ≥0∞) * μ Q = μ (⋃ a ∈ t, a • Q) := by
      rw [measure_biUnion_finset hdisj (fun a _ => hQ.const_smul a)]
      simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ μ R := measure_mono (iUnion₂_subset fun a ha => hcontain a (ht ha))

/-- A finite maximal disjoint family exists because every such family has
cardinality bounded by the containing region's volume. Its doubled tiles
cover every allowed anchor. -/
theorem exists_finite_translate_cover (μ : Measure G) [μ.IsMulLeftInvariant]
    (S Q R : Set G) (hQ : MeasurableSet Q)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ⊤) (hRtop : μ R ≠ ⊤)
    (hcontain : ∀ a ∈ S, a • Q ⊆ R) :
    ∃ t : Finset G, (t : Set G) ⊆ S ∧
      (t : Set G).PairwiseDisjoint (fun a => a • Q) ∧
      (t.card : ℝ≥0∞) * μ Q ≤ μ R ∧
      S ⊆ ⋃ a ∈ t, a • (Q * Q⁻¹) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge ((μ R).toReal / (μ Q).toReal)
  have hbound (t : Finset G) (ht : (t : Set G) ⊆ S)
      (hd : (t : Set G).PairwiseDisjoint (fun a => a • Q)) : t.card ≤ N := by
    have hc := disjoint_translate_card_mul_le μ S Q R hQ hcontain t ht hd
    have hr := ENNReal.toReal_mono hRtop hc
    have hr' : (t.card : ℝ) * (μ Q).toReal ≤ (μ R).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hr
    have hh := (le_div_iff₀ (ENNReal.toReal_pos hQ0 hQtop)).mpr hr'
    exact_mod_cast hh.trans hN
  let P (k : ℕ) := ∃ t : Finset G, (t : Set G) ⊆ S ∧
    (t : Set G).PairwiseDisjoint (fun a => a • Q) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hd, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset G) (hu : (u : Set G) ⊆ S)
      (hud : (u : Set G).PairwiseDisjoint (fun a => a • Q)) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu hud) ⟨u, hu, hud, rfl⟩
  refine ⟨t, hts, hd, disjoint_translate_card_mul_le μ S Q R hQ hcontain t hts hd, ?_⟩
  intro x hx
  have hinter : ∃ a ∈ t, ¬Disjoint (x • Q) (a • Q) := by
    by_contra hn
    have hxdisj : ∀ a ∈ t, Disjoint (x • Q) (a • Q) := by simpa using hn
    have hxt : x ∉ t := by
      intro hxt
      obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero hQ0
      have hpoint : x * q ∈ x • Q := mem_smul_set.mpr ⟨q, hq, rfl⟩
      exact Set.disjoint_left.mp (hxdisj x hxt) hpoint hpoint
    have hi : ((insert x t : Finset G) : Set G) ⊆ S := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx
      · exact hts ha
    have hdi : ((insert x t : Finset G) : Set G).PairwiseDisjoint (fun a => a • Q) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | hat
      · subst a
        rcases Finset.mem_insert.mp hb with hbx | hbt
        · exact (hab hbx.symm).elim
        · exact hxdisj b hbt
      · rcases Finset.mem_insert.mp hb with hbx | hbt
        · subst b
          exact (hxdisj a hat).symm
        · exact hd hat hbt hab
    have hh := hmax (insert x t) hi hdi
    rw [Finset.card_insert_of_notMem hxt] at hh
    omega
  obtain ⟨a, ha, hint⟩ := hinter
  obtain ⟨z, hzx, hza⟩ := Set.not_disjoint_iff.mp hint
  obtain ⟨q, hq, hqz⟩ := mem_smul_set.mp hzx
  obtain ⟨p, hp, hpz⟩ := mem_smul_set.mp hza
  have he : x = a * (p * q⁻¹) := by
    have hh : x * q = a * p := hqz.trans hpz.symm
    calc
      x = (x * q) * q⁻¹ := by group
      _ = (a * p) * q⁻¹ := by rw [hh]
      _ = a * (p * q⁻¹) := mul_assoc _ _ _
  refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, ?_⟩⟩
  exact mem_smul_set.mpr ⟨p * q⁻¹, Set.mul_mem_mul hp (Set.inv_mem_inv.mpr hq), he.symm⟩

theorem measurable_partition_of_finite_cover {X : Type*} [MeasurableSpace X] {n : ℕ}
    (S : Set X) (hS : MeasurableSet S) (U : Fin n → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ T : Fin n → Set X, (∀ i, MeasurableSet (T i)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      (⋃ i, T i) = S ∧ ∀ i, T i ⊆ S ∩ U i := by
  let f := fun i => S ∩ U i
  refine ⟨disjointed f, ?_, disjoint_disjointed f, ?_, disjointed_subset f⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hS.inter (hU i)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hS.inter (hU j)).compl)
  · rw [iUnion_disjointed]
    change (⋃ i, S ∩ U i) = S
    rw [← inter_iUnion, inter_eq_left.mpr hcover]

end PolycyclicRecognition

end

end OAI
