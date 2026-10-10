import OAI.Analysis.TracialSplitting.SpectralCutoffs

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ScalarCompression

variable {D : Type uD} [CStarAlgebra D]

lemma spectralAtom_ne_zero {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) {t : ℝ} (ht : t ∈ spectrum ℝ a) :
    spectralAtom a t ≠ 0 := by
  intro h
  have hn := norm_apply_le_norm_cfc (fun x : ℝ => if x = t then 1 else 0) a ht
    (hf.continuousOn _) ha
  change ‖if t = t then (1 : ℝ) else 0‖ ≤ ‖spectralAtom a t‖ at hn
  rw [h] at hn
  norm_num at hn

structure ProjectionPartition (r : D) where
  Index : Type
  [indexFintype : Fintype Index]
  piece : Index → D
  isProjection : ∀ i, IsStarProjection (piece i)
  nonzero : ∀ i, piece i ≠ 0
  orthogonal : Pairwise (fun i j => piece i * piece j = 0)
  sum_eq : ∑ i, piece i = r

attribute [instance] ProjectionPartition.indexFintype

namespace ProjectionPartition

variable {r : D} (P : ProjectionPartition r)

lemma mul_parent (i : P.Index) : P.piece i * r = P.piece i := by
  classical
  calc
    _ = P.piece i * ∑ j, P.piece j := congrArg (P.piece i * ·) P.sum_eq.symm
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_eq_single i]
      · exact (P.isProjection i).isIdempotentElem
      · intro j _ hji
        exact P.orthogonal hji.symm
      · simp

lemma parent_mul (i : P.Index) : r * P.piece i = P.piece i := by
  classical
  calc
    _ = (∑ j, P.piece j) * P.piece i := congrArg (· * P.piece i) P.sum_eq.symm
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_eq_single i]
      · exact (P.isProjection i).isIdempotentElem
      · intro j _ hji
        exact P.orthogonal hji
      · simp

lemma piece_le [PartialOrder D] [StarOrderedRing D] (hr : IsStarProjection r)
    (i : P.Index) : P.piece i ≤ r :=
  ((P.isProjection i).le_iff_mul_eq_left hr).mpr (P.mul_parent i)

end ProjectionPartition

lemma norm_compress_le {q : D} (hq : IsStarProjection q) (a : D) :
    ‖q * a * q‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖q‖ * ‖a‖ * ‖q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a‖ * 1 := by
      gcongr <;> exact IsStarProjection.norm_le q hq
    _ = _ := by ring

lemma compression_persist {q r : D} (hq : IsStarProjection q)
    (hqr : q * r = q) (hrq : r * q = q) (a : D) (α : ℂ) :
    ‖q * a * q - α • q‖ ≤ ‖r * a * r - α • r‖ := by
  have he : q * (r * a * r - α • r) * q = q * a * q - α • q := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    simp only [← mul_assoc, hqr, hq.isIdempotentElem.eq]
    rw [mul_assoc (q * a), hrq]
  rw [← he]
  exact norm_compress_le hq _

def cornerSpectralPartition {r : D} (hr : IsStarProjection r)
    {b : ProjectionCorner hr} (hb : IsSelfAdjoint b) (hf : (spectrum ℝ b).Finite) :
    ProjectionPartition r where
  Index := hf.toFinset
  piece t := (spectralAtom b t : ProjectionCorner hr)
  isProjection t := (spectralAtom_projection hf t).map (ProjectionCorner.inclusion hr)
  nonzero t := by
    intro hz
    apply spectralAtom_ne_zero hb hf (by simpa only [Set.Finite.mem_toFinset] using t.property)
    exact Subtype.ext hz
  orthogonal := by
    intro s t hst
    have hst' : (s : ℝ) ≠ (t : ℝ) := fun he => hst (Subtype.ext he)
    exact congrArg Subtype.val (spectralAtom_orthogonal hf hst')
  sum_eq := by
    change ∑ i : hf.toFinset, (ProjectionCorner.inclusion hr) (spectralAtom b (i : ℝ)) = r
    rw [Finset.sum_coe_sort hf.toFinset (fun t : ℝ =>
      (ProjectionCorner.inclusion hr) (spectralAtom b t)), ← map_sum, spectralAtom_sum hb hf]
    rfl

lemma scalarCompression_selfAdjoint (hD : RealRankZero D) {r : D}
    (hr : IsStarProjection r) (a : D) (ha : IsSelfAdjoint a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ i, ∃ α : ℂ,
      ‖P.piece i * a * P.piece i - α • P.piece i‖ < ε := by
  let c := ProjectionCorner.compress hr a
  have hc : IsSelfAdjoint c := by
    apply Subtype.ext
    change star (r * a * r) = r * a * r
    simpa only [hr.isSelfAdjoint.star_eq] using (ha.conjugate r).star_eq
  obtain ⟨b, hb, hbf, hcb⟩ := realRankZero_corner hD hr c hc ε hε
  let hf := realSpectrum_finite hb hbf
  let P := cornerSpectralPartition hr hb hf
  refine ⟨P, ?_⟩
  intro i
  let t : hf.toFinset := i
  refine ⟨((t : ℝ) : ℂ), ?_⟩
  have hie : (b : D) * P.piece i = (t : ℝ) • P.piece i :=
    congrArg Subtype.val (spectralAtom_eigenvalue hb hf (t : ℝ))
  have he : P.piece i * ((c : D) - (b : D)) * P.piece i =
      P.piece i * a * P.piece i - ((t : ℝ) : ℂ) • P.piece i := by
    rw [mul_sub, sub_mul]
    change P.piece i * (r * a * r) * P.piece i -
      P.piece i * (b : D) * P.piece i = _
    simp only [← mul_assoc, P.mul_parent i]
    rw [mul_assoc (P.piece i * a), P.parent_mul i,
      mul_assoc (P.piece i) (b : D), hie, mul_smul_comm,
      (P.isProjection i).isIdempotentElem.eq]
    simp only [Complex.coe_smul]
  rw [← he]
  exact (norm_compress_le (P.isProjection i) _).trans_lt hcb

namespace ProjectionPartition

variable {r : D}

def refine (P : ProjectionPartition r) (Q : ∀ i, ProjectionPartition (P.piece i)) :
    ProjectionPartition r where
  Index := Σ i : P.Index, (Q i).Index
  piece i := (Q i.1).piece i.2
  isProjection i := (Q i.1).isProjection i.2
  nonzero i := (Q i.1).nonzero i.2
  orthogonal := by
    rintro ⟨i, s⟩ ⟨j, t⟩ hst
    by_cases hij : i = j
    · subst j
      exact (Q i).orthogonal (fun h => hst (congrArg (Sigma.mk i) h))
    · calc
        _ = ((Q i).piece s * P.piece i) * (P.piece j * (Q j).piece t) := by
          rw [(Q i).mul_parent, (Q j).parent_mul]
        _ = (Q i).piece s * (P.piece i * P.piece j) * (Q j).piece t := by
          simp only [mul_assoc]
        _ = 0 := by rw [P.orthogonal hij, mul_zero, zero_mul]
  sum_eq := by
    rw [Fintype.sum_sigma]
    simp only [(Q _).sum_eq]
    exact P.sum_eq

def empty : ProjectionPartition (0 : D) where
  Index := Empty
  piece := Empty.elim
  isProjection i := Empty.elim i
  nonzero i := Empty.elim i
  orthogonal i := Empty.elim i
  sum_eq := by simp

def singleton (hr : IsStarProjection r) (hr0 : r ≠ 0) : ProjectionPartition r where
  Index := Unit
  piece _ := r
  isProjection _ := hr
  nonzero _ := hr0
  orthogonal := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  sum_eq := by simp

end ProjectionPartition

lemma scalarCompressions_selfAdjoint (hD : RealRankZero D) {r : D}
    (hr : IsStarProjection r) (F : Finset (selfAdjoint D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ a ∈ F, ∀ i, ∃ α : ℂ,
      ‖P.piece i * (a : D) * P.piece i - α • P.piece i‖ < ε := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    by_cases hr0 : r = 0
    · subst r
      exact ⟨ProjectionPartition.empty, by simp⟩
    · exact ⟨ProjectionPartition.singleton hr hr0, by simp⟩
  | @insert a F _ ih =>
    obtain ⟨P, hP⟩ := ih
    have hQ := fun i : P.Index =>
      scalarCompression_selfAdjoint hD (P.isProjection i) (a : D) a.property hε
    choose Q hQ using hQ
    refine ⟨P.refine Q, ?_⟩
    intro b hb i
    change (Σ j : P.Index, (Q j).Index) at i
    rcases i with ⟨i, j⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hQ i j
    · obtain ⟨α, hα⟩ := hP b hb i
      refine ⟨α, ?_⟩
      exact (compression_persist ((Q i).isProjection j) ((Q i).mul_parent j)
        ((Q i).parent_mul j) (b : D) α).trans_lt hα

lemma scalar_compressions (hD : RealRankZero D) {r : D} (hr : IsStarProjection r)
    (F : Finset D) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ProjectionPartition r, ∀ a ∈ F, ∀ i, ∃ α : ℂ,
      ‖P.piece i * a * P.piece i - α • P.piece i‖ < ε := by
  classical
  let S := F.image realPart ∪ F.image imaginaryPart
  obtain ⟨P, hP⟩ := scalarCompressions_selfAdjoint hD hr S (half_pos hε)
  refine ⟨P, ?_⟩
  intro a ha i
  obtain ⟨α, hα⟩ := hP (realPart a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) i
  obtain ⟨β, hβ⟩ := hP (imaginaryPart a)
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)) i
  refine ⟨α + Complex.I * β, ?_⟩
  have he : P.piece i * a * P.piece i - (α + Complex.I * β) • P.piece i =
      (P.piece i * (realPart a : D) * P.piece i - α • P.piece i) +
      Complex.I • (P.piece i * (imaginaryPart a : D) * P.piece i - β • P.piece i) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, add_smul,
      smul_sub, smul_smul]
    abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul, Complex.norm_I, one_mul]
  linarith

end ScalarCompression

section ProjectionOrder

variable {D : Type uD} [CStarAlgebra D]

namespace ProjectionCorner

variable {p : D} (hp : IsStarProjection p)

variable [PartialOrder D] [StarOrderedRing D]

instance : StarOrderedRing (ProjectionCorner hp) := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z : D) + (x : D) ≤ (z : D) + (y : D)
    simpa only [add_comm] using add_le_add_left
      (show (x : D) ≤ (y : D) from h) (z : D)
  · intro a
    constructor
    · intro ha
      have hsa : IsSelfAdjoint a :=
        Subtype.ext (IsSelfAdjoint.of_nonneg (show 0 ≤ (a : D) from ha)).star_eq
      have hspec : ∀ t ∈ spectrum ℝ a, 0 ≤ t := by
        intro t ht
        have hc : (t : ℂ) ∈ spectrum ℂ (a : D) :=
          spectrum_subset_coe hp a (hsa.coe_mem_spectrum_complex.mpr ht)
        exact spectrum_nonneg_of_nonneg (show 0 ≤ (a : D) from ha)
          ((isSelfAdjoint_coe hp hsa).coe_mem_spectrum_complex.mp hc)
      refine ⟨cfc Real.sqrt a, ?_⟩
      rw [(cfc_predicate Real.sqrt a).star_eq,
        ← cfc_mul Real.sqrt Real.sqrt a Real.continuous_sqrt.continuousOn
          Real.continuous_sqrt.continuousOn]
      nth_rw 1 [← cfc_id ℝ a hsa]
      exact cfc_congr (fun t ht => (Real.mul_self_sqrt (hspec t ht)).symm)
    · rintro ⟨s, rfl⟩
      exact star_mul_self_nonneg (s : D)

omit [StarOrderedRing D] in
lemma coe_nonneg_iff (a : ProjectionCorner hp) : 0 ≤ (a : D) ↔ 0 ≤ a := Iff.rfl

omit [StarOrderedRing D] in
lemma coe_le_iff (a b : ProjectionCorner hp) : (a : D) ≤ (b : D) ↔ a ≤ b := Iff.rfl

lemma compress_nonneg {a : D} (ha : 0 ≤ a) : 0 ≤ compress hp a := by
  rw [← coe_nonneg_iff]
  exact hp.isSelfAdjoint.conjugate_nonneg ha

end ProjectionCorner

end ProjectionOrder

section SpectralThresholds

variable {D : Type uD} [CStarAlgebra D]

def spectralThreshold (a : D) (t : ℝ) : D :=
  cfc (fun s : ℝ => if t ≤ s then (1 : ℝ) else 0) a

lemma spectralThreshold_projection {a : D} (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    IsStarProjection (spectralThreshold a t) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc _ a * cfc _ a = cfc _ a
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma spectralThreshold_complement {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    1 - spectralThreshold a t = cfc (fun s : ℝ => if t ≤ s then (0 : ℝ) else 1) a := by
  rw [spectralThreshold, ← cfc_one ℝ a ha,
    ← cfc_sub _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

variable [PartialOrder D] [StarOrderedRing D]

lemma spectralThreshold_lower {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    t • spectralThreshold a t ≤ spectralThreshold a t * a * spectralThreshold a t := by
  unfold spectralThreshold
  nth_rw 3 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simpa using hx
  · simp

lemma spectralThreshold_complement_upper {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    (1 - spectralThreshold a t) * a * (1 - spectralThreshold a t) ≤
      t • (1 - spectralThreshold a t) := by
  rw [spectralThreshold_complement ha hf]
  nth_rw 2 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simp
  · simpa using (le_of_lt (lt_of_not_ge hx))

lemma compress_perturbation_lower {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * a * p - ‖a - b‖ • p ≤ p * b * p := by
  have h := star_left_conjugate_le_conjugate (ha.sub hb).le_algebraMap_norm_self p
  simp only [hp.isSelfAdjoint.star_eq, mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, smul_mul_assoc, mul_one, hp.isIdempotentElem.eq] at h
  exact sub_le_comm.mp h

lemma compress_perturbation_upper {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * b * p ≤ p * a * p + ‖a - b‖ • p := by
  have h := compress_perturbation_lower hb ha hp
  rw [norm_sub_rev] at h
  exact sub_le_iff_le_add.mp h

end SpectralThresholds

end CurrentMain

end

end

end OAI
