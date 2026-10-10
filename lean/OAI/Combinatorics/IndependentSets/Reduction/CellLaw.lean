import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Mix

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

lemma uniformLaw_singleton {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    uniformLaw α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp only [uniformLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

lemma uniformLaw_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    uniformLaw (ι → α) = Measure.pi (fun _ : ι => uniformLaw α) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [uniformLaw_singleton, Measure.pi_singleton, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

noncomputable def cellLaw (n m : ℕ) : Measure (Fin n → Cube m) := uniformLaw (Fin n → Cube m)
instance cellLaw_probability (n m : ℕ) : IsProbabilityMeasure (cellLaw n m) :=
  inferInstanceAs (IsProbabilityMeasure (uniformLaw (Fin n → Cube m)))

noncomputable def mergeSeed {n m : ℕ} (p : (Fin n → Cube m) × (Fin n → ℝ)) :
    Fin n → Cube m × ℝ := fun i => (p.1 i,p.2 i)

lemma mergeSeed_preserving (n m : ℕ) :
    MeasurePreserving (mergeSeed (n:=n) (m:=m))
      ((cellLaw n m).prod (unitCubeLaw n)) (seedCubeLaw n m) := by
  have h := (measurePreserving_arrowProdEquivProdArrow (Cube m) ℝ (Fin n)
    (fun _ => uniformLaw (Cube m)) (fun _ => unitLaw)).symm
  change MeasurePreserving _ ((uniformLaw (Fin n → Cube m)).prod _) _
  rw [uniformLaw_pi (ι:=Fin n) (α:=Cube m)]
  exact h

lemma cells_preserving (n m : ℕ) :
    MeasurePreserving (fun p : Fin n → Cube m × ℝ => fun i => (p i).1)
      (seedCubeLaw n m) (cellLaw n m) := by
  have h := measurePreserving_pi (fun _ : Fin n => seedLaw m) (fun _ : Fin n => uniformLaw (Cube m))
    (fun _ => measurePreserving_fst (μ:=uniformLaw (Cube m)) (ν:=unitLaw))
  change MeasurePreserving _ _ (uniformLaw (Fin n → Cube m))
  rw [uniformLaw_pi (ι:=Fin n) (α:=Cube m)]
  exact h

noncomputable def cellPoint {n m : ℕ} (q : Fin n → Cube m) : Fin n → ℝ :=
  fun i => scalarCell (q i) 0

lemma scalarCell_distance {m : ℕ} (q : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    dist (scalarCell q y) (scalarCell q 0) ≤ (1/2:ℝ)^m := by
  have h := (scalarCell_lipschitz q).dist_le_mul y 0
  have hd : dist y 0 ≤ 1 := by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hy.1] using hy.2
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hd (show 0 ≤ ((1/2:ℝ≥0)^m:ℝ) from pow_nonneg (NNReal.coe_nonneg _) _))

lemma sample_cell_distance {n m : ℕ} (p : Fin n → Cube m × ℝ)
    (hp : ∀ i, (p i).2 ∈ Icc (0:ℝ) 1) :
    dist (cubeSampler p) (cellPoint (fun i => (p i).1)) ≤ (1/2:ℝ)^m := by
  apply (dist_pi_le_iff (pow_nonneg (by norm_num) _)).mpr
  intro i
  exact scalarCell_distance _ (hp i)

lemma seeds_in_unit (n m : ℕ) :
    ∀ᵐ p ∂seedCubeLaw n m, ∀ i, (p i).2 ∈ Icc (0:ℝ) 1 := by
  have hu : ∀ᵐ x ∂unitLaw, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hs : ∀ᵐ t ∂seedLaw m, t.2 ∈ Icc (0:ℝ) 1 :=
    (measurePreserving_snd (μ:=uniformLaw (Cube m)) (ν:=unitLaw)).quasiMeasurePreserving.ae hu
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => seedLaw m) i).quasiMeasurePreserving.ae hs

lemma sample_cell_error {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) :
    ∀ᵐ p ∂seedCubeLaw n m,
      |f (cubeSampler p) - f (cellPoint (fun i => (p i).1))| ≤ L * (1/2:ℝ)^m := by
  filter_upwards [seeds_in_unit n m] with p hp
  simpa only [Real.dist_eq] using (hf.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (sample_cell_distance p hp) L.coe_nonneg)

noncomputable def rowFlip {n m : ℕ} (i : Fin n) (k : Fin m) (q : Fin n → Cube m) :
    Fin n → Cube m := Function.update q i (flip k (q i))
noncomputable def rowInfluence {n m : ℕ} (h : (Fin n → Cube m) → ℝ)
    (i : Fin n) (k : Fin m) : ℝ := 𝔼 q, |(h q-h (rowFlip i k q))/2|

lemma cells_update_flip {n m : ℕ} (p : Fin n → Cube m × ℝ) (i : Fin n) (k : Fin m) :
    (fun j => (Function.update p i (flipSeed k (p i)) j).1) =
      rowFlip i k (fun j => (p j).1) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [rowFlip, flipSeed]
  · simp [rowFlip, hj]

lemma rowInfluence_eq_integral {n m : ℕ} (h : (Fin n → Cube m) → ℝ)
    (i : Fin n) (k : Fin m) :
    rowInfluence h i k = ∫ p, |(h (fun j => (p j).1)-
      h (rowFlip i k (fun j => (p j).1)))/2| ∂seedCubeLaw n m := by
  symm
  calc
    _ = ∫ q, |(h q-h (rowFlip i k q))/2| ∂cellLaw n m :=
      ProductAveraging.integral_preserving (cells_preserving n m) Integrable.of_finite.aestronglyMeasurable
    _ = _ := integral_uniformLaw _

lemma rowInfluence_cell_bound {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) :
    rowInfluence (f ∘ cellPoint) i k ≤
      (∫ p, sampledDiff f i k p ∂seedCubeLaw n m) + L*(1/2:ℝ)^m := by
  rw [rowInfluence_eq_integral]
  have hcell : Integrable (fun p : Fin n → Cube m × ℝ =>
      |((f ∘ cellPoint) (fun j => (p j).1)-(f ∘ cellPoint) (rowFlip i k (fun j => (p j).1)))/2|)
      (seedCubeLaw n m) := by
    have hfin : Integrable (fun q => |((f ∘ cellPoint) q-(f ∘ cellPoint) (rowFlip i k q))/2|)
        (cellLaw n m) := Integrable.of_finite
    exact (cells_preserving n m).integrable_comp_of_integrable hfin
  have hi := sampledDiff_integrable hf.continuous.measurable hb i k
  have he : (∫ p, sampledDiff f i k p + L*(1/2:ℝ)^m ∂seedCubeLaw n m) =
      (∫ p, sampledDiff f i k p ∂seedCubeLaw n m)+L*(1/2:ℝ)^m := by
    rw [integral_add hi (integrable_const _)]; simp
  rw [← he]
  have his : Integrable (fun p => sampledDiff f i k p + L*(1/2:ℝ)^m) (seedCubeLaw n m) :=
    hi.add (integrable_const _)
  apply integral_mono_ae hcell his
  filter_upwards [seeds_in_unit n m] with p hp
  have hup : ∀ j, (Function.update p i (flipSeed k (p i)) j).2 ∈ Icc (0:ℝ) 1 := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [flipSeed] using hp i
    · simpa [hj] using hp j
  have ha : |f (cubeSampler p)-f (cellPoint (fun j => (p j).1))| ≤ L*(1/2:ℝ)^m := by
    simpa only [Real.dist_eq] using (hf.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (sample_cell_distance p hp) L.coe_nonneg)
  have hb' : |f (cubeSampler (Function.update p i (flipSeed k (p i))))-
      f (cellPoint (rowFlip i k (fun j => (p j).1)))| ≤ L*(1/2:ℝ)^m := by
    have h := (hf.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (sample_cell_distance _ hup) L.coe_nonneg)
    simpa only [Real.dist_eq, cells_update_flip] using h
  dsimp only [sampledDiff, Function.comp_def]
  rw [abs_div, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hx (a b c d : ℝ) : |a-b| ≤ |c-d| + |c-a| + |d-b| := by
    calc
      _ = |(a-c)+(c-d)+(d-b)| := by congr 1; ring
      _ ≤ |a-c|+|c-d|+|d-b| := by linarith [abs_add_le (a-c) (c-d), abs_add_le ((a-c)+(c-d)) (d-b)]
      _ = _ := by rw [abs_sub_comm a c]; ring
  have hh := hx (f (cellPoint (fun j => (p j).1)))
    (f (cellPoint (rowFlip i k (fun j => (p j).1)))) (f (cubeSampler p))
    (f (cubeSampler (Function.update p i (flipSeed k (p i)))))
  linarith

lemma total_rowInfluence_cell_bound {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i, ∑ k, rowInfluence (f ∘ cellPoint (n:=n) (m:=m)) i k) ≤
      L + (n:ℝ)*m*(L*(1/2:ℝ)^m) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin n) _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun (k : Fin m) _ => rowInfluence_cell_bound hf hb i k))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have ht := total_sampled_influence (n:=n) (m:=m) hf hb
  nlinarith

end LargeIndependentSets.BooleanJunta

end OAI
