import Mathlib
import OAI.Probability.Perceptron.Pressure.PatternMatrices

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma triangleConstraints_diag (a b c t : ℝ) (k : Fin 3) :
    triangleConstraints a b c t k k = Iio t := by simp [triangleConstraints]

lemma triangleConstraints_cut {a : ℝ} (b c t : ℝ) (hat : a ≤ t) (k l : Fin 3) :
    triangleConstraints a b c t k l ⊆ Iio t := by
  unfold triangleConstraints
  split_ifs
  · exact Subset.rfl
  · exact Iio_subset_Iio hat
  · exact Ioo_subset_Iio_self
  · exact Ioo_subset_Iio_self

def tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) : Fin (3 * n) :=
  ⟨3 * i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩

@[simp] lemma tripleLabels_tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) :
    tripleLabels (3 * n) (tripleIndex k i) = k := by
  apply Fin.ext
  simp [tripleLabels, tripleIndex, Nat.add_mod]

lemma tripleIndex_ne {n : ℕ} {k l : Fin 3} (hkl : k ≠ l) (i j : Fin n) :
    tripleIndex k i ≠ tripleIndex l j := by
  intro h
  have := congrArg (tripleLabels (3 * n)) h
  exact hkl (by simpa using this)

lemma tripleIndex_inj {n : ℕ} (k : Fin 3) {i j : Fin n} (hij : i ≠ j) :
    tripleIndex k i ≠ tripleIndex k j := by
  intro h
  apply hij
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [tripleIndex] at h'
  omega

lemma triangle_pattern_psd_bound {n : ℕ} (hn : 0 < n)
    (B : OverlapBlock (3 * n)) (hB : Matrix.PosSemidef B)
    (hdiag : ∀ i, B i i ≤ 1) {a b c t : ℝ} (hab : a ≤ b)
    (hpattern : B ∈ patternMatrices (tripleLabels (3 * n)) (triangleConstraints a b c t)) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let _ := Matrix.toSeminormedAddCommGroup B hB
  let _ := Matrix.toInnerProductSpace B hB
  let v : Fin 3 → Fin n → (Fin (3 * n) → ℝ) := fun k i => Pi.single (tripleIndex k i) 1
  have hv (k l : Fin 3) (i j : Fin n) :
      ⟪v k i, v l j⟫_ℝ = B (tripleIndex k i) (tripleIndex l j) :=
    posSemidef_standard_basis_inner B hB _ _
  apply duplicate_ordered_blocks_bound hn v hab
  · intro k i
    rw [← real_inner_self_eq_norm_sq, hv]
    exact hdiag _
  · intro k i j hij
    rw [hv]
    have h := hpattern _ _ (tripleIndex_inj k hij)
    simp only [tripleLabels_tripleIndex, triangleConstraints_diag, mem_Iio] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 1) i j)
    simp [triangleConstraints] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (1 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le

theorem gg_triangle_pattern_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹'
      patternMatrices (tripleLabels 3) (triangleConstraints a b c t))) :
    (b - a) ^ 2 ≤ 2 * (t - c) := by
  have hall := gg_triple_pattern μ hEx hGG hSym (triangleConstraints a b c t)
    (triangleConstraints_measurable a b c t) t (triangleConstraints_diag a b c t)
    (triangleConstraints_cut b c t hat) hA
  have hbound (n : ℕ) : (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ)) := by
    have hpos := hall (3 * (n + 1)) (by omega)
    have hne : μ (overlapBlock id (3 * (n + 1)) ⁻¹'
        patternMatrices (tripleLabels (3 * (n + 1))) (triangleConstraints a b c t)) ≠ 0 := by
      intro hz
      simp [Measure.real, hz] at hpos
    obtain ⟨Q, hQ, hG, hD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (hGram.and hdiag))
    have h := triangle_pattern_psd_bound (by omega : 0 < n + 1)
      (overlapBlock id (3 * (n + 1)) Q) (hG _) (fun i => hD i) hab hQ
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have ht : Tendsto (fun n : ℕ => 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ))) atTop
      (𝓝 (2 * (t - c))) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul (2 * (1 - t))
    have h' := h.const_add (2 * (t - c))
    simpa only [mul_zero, add_zero, mul_one_div, mul_div_assoc] using h'
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

def triangleEvent (a b c t : ℝ) : Set OverlapArray :=
  {Q | Q 0 1 < a ∧ b < Q 0 2 ∧ Q 0 2 < t ∧ c < Q 1 2 ∧ Q 1 2 < t}

lemma triangleEvent_pattern {a b c t : ℝ} (hat : a ≤ t) (Q : OverlapArray)
    (hSym : ∀ i j, Q i j = Q j i) (hQ : Q ∈ triangleEvent a b c t) :
    overlapBlock id 3 Q ∈ patternMatrices (tripleLabels 3) (triangleConstraints a b c t) := by
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  have hQt : Q 0 1 < t := hQ.1.trans_le hat
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapBlock, tripleLabels, triangleConstraints, triangleEvent]

lemma gg_triangleEvent_null (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t) (hgap : 2 * (t - c) < (b - a) ^ 2) :
    μ (triangleEvent a b c t) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (triangleEvent a b c t) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hle : μ.real (triangleEvent a b c t) ≤ μ.real
      (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) (triangleConstraints a b c t)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hSym] with Q hQ
    exact triangleEvent_pattern hat Q hQ
  exact hgap.not_ge (gg_triangle_pattern_bound μ hEx hGG hSym hGram hdiag hab hat (hpos.trans_le hle))

lemma exists_rational_triangle_box {x y z : ℝ} (hxy : x < y) (hyz : y ≤ z) :
    ∃ a b c t : ℚ, (a : ℝ) ≤ b ∧ (a : ℝ) ≤ t ∧
      2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 ∧
      x < a ∧ (b : ℝ) < y ∧ y < t ∧ (c : ℝ) < z ∧ z < t := by
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  have hδ : 0 < ((b : ℝ) - a) ^ 2 / 8 := by positivity
  obtain ⟨c, hzc, hcz⟩ := exists_rat_btwn (show z - ((b : ℝ) - a) ^ 2 / 8 < z by linarith)
  obtain ⟨t, hzt, htz⟩ := exists_rat_btwn (show z < z + ((b : ℝ) - a) ^ 2 / 8 by linarith)
  refine ⟨a, b, c, t, hab.le, (hay.trans_le hyz).le.trans hzt.le, ?_, hxa, hby,
    hyz.trans_lt hzt, hcz, hzt⟩
  nlinarith

lemma gg_no_ordered_crossing (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ (Q 0 1 < Q 0 2 ∧ Q 0 2 ≤ Q 1 2) := by
  have hBoxes : ∀ᵐ Q ∂μ, ∀ a b c t : ℚ,
      (a : ℝ) ≤ b → (a : ℝ) ≤ t → 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 →
      Q ∉ triangleEvent a b c t := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro t
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hat : (a : ℝ) ≤ t
      · by_cases hgap : 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
            (gg_triangleEvent_null μ hEx hGG hSym hGram hdiag hab hat hgap)] with Q hQ
          exact fun _ _ _ => hQ
        · exact Eventually.of_forall fun _ _ _ h => (hgap h).elim
      · exact Eventually.of_forall fun _ _ h => (hat h).elim
    · exact Eventually.of_forall fun _ h => (hab h).elim
  filter_upwards [hBoxes] with Q hQ
  rintro ⟨hxy, hyz⟩
  obtain ⟨a, b, c, t, hab, hat, hgap, hbox⟩ := exists_rational_triangle_box hxy hyz
  exact hQ a b c t hab hat hgap hbox

lemma gram_array_symmetric (Q : OverlapArray)
    (hGram : ∀ n, Matrix.PosSemidef (overlapBlock id n Q)) : ∀ i j, Q i j = Q j i := by
  intro i j
  let n := max i j + 1
  let a : Fin n := ⟨i, by dsimp [n]; omega⟩
  let b : Fin n := ⟨j, by dsimp [n]; omega⟩
  have h := (hGram n).isHermitian.apply b a
  simpa [overlapBlock, a, b] using h

theorem gg_ultrametric (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, min (Q 0 1) (Q 0 2) ≤ Q 1 2 := by
  have hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i :=
    hGram.mono fun Q hQ => gram_array_symmetric Q hQ
  have hno := gg_no_ordered_crossing μ hEx hGG hSym hGram hdiag
  have hno' := (hEx 0 1).quasiMeasurePreserving.ae hno
  have hsmall : ∀ᵐ Q ∂μ, min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
    filter_upwards [hno, hno', hSym] with Q hQ hQ' hs
    simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide] at hQ'
    rw [hs 1 0] at hQ'
    by_cases h : Q 0 2 ≤ Q 1 2
    · rw [min_eq_left h]
      exact le_of_not_gt fun hh => hQ ⟨hh, h⟩
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact le_of_not_gt fun hh => hQ' ⟨hh, h'⟩
  have hsmall' := (hEx 0 2).quasiMeasurePreserving.ae hsmall
  filter_upwards [hsmall', hSym] with Q hQ hs
  simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
    show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide] at hQ
  simpa only [hs 2 0, hs 1 0, hs 2 1, min_comm] using hQ

abbrev PairedOverlapArray := ℕ → ℕ → ℝ × ℝ
abbrev PairedOverlapBlock (n : ℕ) := Fin n → Fin n → ℝ × ℝ

def pairedBlock (n : ℕ) (Q : PairedOverlapArray) : PairedOverlapBlock n :=
  fun i j => Q i j

def pairedRelabel (π : Equiv.Perm ℕ) (Q : PairedOverlapArray) : PairedOverlapArray :=
  fun i j => Q (π i) (π j)

def PairedSwapInvariant (μ : Measure PairedOverlapArray) : Prop :=
  ∀ i j : ℕ, MeasurePreserving (pairedRelabel (Equiv.swap i j)) μ μ

def JointGhirlandaGuerra (μ : Measure PairedOverlapArray) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n) (s : Set (PairedOverlapBlock n)), MeasurableSet s →
    ∀ t : Set (ℝ × ℝ), MeasurableSet t →
    μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i n ∈ t}) =
      μ.real (pairedBlock n ⁻¹' s) * μ.real {Q | Q 0 1 ∈ t} / n +
      (∑ j ∈ (Finset.univ.erase i),
        μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i j ∈ t})) / n

def scalarArray (f : ℝ × ℝ → ℝ) (Q : PairedOverlapArray) : OverlapArray :=
  fun i j => f (Q i j)

def scalarBlock (f : ℝ × ℝ → ℝ) {n : ℕ} (Q : PairedOverlapBlock n) : OverlapBlock n :=
  fun i j => f (Q i j)

lemma scalarArray_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (scalarArray f) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarBlock_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) {n : ℕ} :
    Measurable (scalarBlock f (n := n)) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarArray_swap_invariant (μ : Measure PairedOverlapArray)
    (hEx : PairedSwapInvariant μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    OverlapSwapInvariant (μ.map (scalarArray f)) := by
  intro i j
  have heq : relabelArray (Equiv.swap i j) ∘ scalarArray f =
      scalarArray f ∘ pairedRelabel (Equiv.swap i j) := rfl
  refine ⟨Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _), ?_⟩
  rw [Measure.map_map _ (scalarArray_measurable hf), heq,
    ← Measure.map_map (scalarArray_measurable hf) (hEx i j).measurable,
    (hEx i j).map_eq]
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma scalarArray_gg (μ : Measure PairedOverlapArray)
    (hGG : JointGhirlandaGuerra μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    GhirlandaGuerra (μ.map (scalarArray f)) id := by
  intro n hn i s hs t ht
  have hblock : Measurable (overlapBlock (id : OverlapArray → OverlapArray) n) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hedge (i j : ℕ) : Measurable (fun Q : OverlapArray => Q i j) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hmap (u : Set OverlapArray) (hu : MeasurableSet u) :
      (μ.map (scalarArray f)).real u = μ.real (scalarArray f ⁻¹' u) := by
    rw [measureReal_def, Measure.map_apply (scalarArray_measurable hf) hu]
    rfl
  simp only [id_eq]
  rw [hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i n ∈ t})
      ((hs.preimage hblock).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hblock), hmap {Q | Q 0 1 ∈ t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i j ∈ t})
    ((hs.preimage hblock).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact hGG n hn i (scalarBlock f ⁻¹' s) (hs.preimage (scalarBlock_measurable hf))
    (f ⁻¹' t) (ht.preimage hf)

lemma measurableSet_gram_arrays :
    MeasurableSet {Q : OverlapArray | ∀ n, Matrix.PosSemidef (overlapBlock id n Q)} := by
  apply IsClosed.measurableSet
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  have hiff (Q : OverlapArray) :=
    Matrix.posSemidef_iff_dotProduct_mulVec (M := overlapBlock id n Q)
  simp_rw [hiff]
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {Q : OverlapArray | Matrix.conjTranspose (overlapBlock id n Q) = overlapBlock id n Q}
    apply isClosed_eq <;> unfold overlapBlock <;> fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold overlapBlock
    fun_prop

lemma scalarArray_ultrametric (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, min (f (Q 0 1)) (f (Q 0 2)) ≤ f (Q 1 2) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hu := gg_ultrametric ν (scalarArray_swap_invariant μ hEx hf)
    (scalarArray_gg μ hGG hf) hg hd
  exact ae_of_ae_map hm.aemeasurable hu

def UltrametricTriangle (x y z : ℝ) : Prop :=
  min x y ≤ z ∧ min x z ≤ y ∧ min y z ≤ x

lemma gg_ultrametric_triangle (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (Q 0 1) (Q 0 2) (Q 1 2) := by
  have h := gg_ultrametric μ hEx hGG hGram hdiag
  have h₁ := (hEx 0 1).quasiMeasurePreserving.ae h
  have h₂ := (hEx 0 2).quasiMeasurePreserving.ae h
  filter_upwards [h, h₁, h₂, hGram] with Q hQ hQ₁ hQ₂ hg
  have hs := gram_array_symmetric Q hg
  refine ⟨hQ, ?_, ?_⟩
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide, hs 1 0] using hQ₁
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide, hs 2 0, hs 2 1, hs 1 0,
      min_comm] using hQ₂

lemma scalarArray_ultrametric_triangle (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (f (Q 0 1)) (f (Q 0 2)) (f (Q 1 2)) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  exact ae_of_ae_map hm.aemeasurable
    (gg_ultrametric_triangle ν (scalarArray_swap_invariant μ hEx hf)
      (scalarArray_gg μ hGG hf) hg hd)

lemma ultrametric_triangle_small_eq {a b c : ℝ} (h : UltrametricTriangle a b c)
    (hab : a < b) : c = a := by
  have hlo : a ≤ c := by simpa only [min_eq_left hab.le] using h.1
  have hhi : c ≤ a := by
    rcases le_total b c with hbc | hcb
    · have : b ≤ a := by simpa only [min_eq_left hbc] using h.2.2
      exact (hab.not_ge this).elim
    · simpa only [min_eq_right hcb] using h.2.2
  exact le_antisymm hhi hlo

lemma ultrametric_sum_no_crossing {a b c x y z : ℝ}
    (hR : UltrametricTriangle a b c) (hT : UltrametricTriangle x y z)
    (hSum : min ((a + x) / 2) ((b + y) / 2) ≤ (c + z) / 2) :
    ¬ (a < b ∧ y < x) := by
  rintro ⟨hab, hyx⟩
  have hc := ultrametric_triangle_small_eq hR hab
  have hz : z = y := ultrametric_triangle_small_eq
    (show UltrametricTriangle y x z from ⟨by simpa only [min_comm] using hT.1,
      hT.2.2, hT.2.1⟩) hyx
  rw [hc, hz] at hSum
  rcases le_total ((a + x) / 2) ((b + y) / 2) with h | h
  · rw [min_eq_left h] at hSum
    linarith
  · rw [min_eq_right h] at hSum
    linarith

theorem joint_gg_no_crossing (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    (hR : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)))
    (hT : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.snd Q)))
    (hdR : ∀ᵐ Q ∂μ, ∀ i, (Q i i).1 ≤ 1)
    (hdT : ∀ᵐ Q ∂μ, ∀ i, (Q i i).2 ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2) := by
  have huR := scalarArray_ultrametric_triangle μ hEx hGG measurable_fst hR hdR
  have huT := scalarArray_ultrametric_triangle μ hEx hGG measurable_snd hT hdT
  let f : ℝ × ℝ → ℝ := fun x => (x.1 + x.2) / 2
  have hf : Measurable f := by fun_prop
  have hG : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)) := by
    filter_upwards [hR, hT] with Q hQ₁ hQ₂ n
    have heq : overlapBlock id n (scalarArray f Q) =
        (1 / 2 : ℝ) • (overlapBlock id n (scalarArray Prod.fst Q) +
          overlapBlock id n (scalarArray Prod.snd Q)) := by
      ext i j
      simp [overlapBlock, scalarArray, f, smul_eq_mul, div_eq_mul_inv, add_mul,
        mul_comm]
    rw [heq]
    exact ((hQ₁ n).add (hQ₂ n)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hd : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1 := by
    filter_upwards [hdR, hdT] with Q hQ₁ hQ₂ i
    dsimp [f]
    linarith [hQ₁ i, hQ₂ i]
  have huS := scalarArray_ultrametric μ hEx hGG hf hG hd
  filter_upwards [huR, huT, huS] with Q hQ₁ hQ₂ hQ₃
  exact ultrametric_sum_no_crossing hQ₁ hQ₂ hQ₃

end SphericalPerceptronFreeEnergy
end

end OAI
