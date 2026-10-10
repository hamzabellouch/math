import OAI.Analysis.CStarAlgebra.PureInfiniteness.ClosedIdeal
import OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealDetection

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance idealComparisonPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance idealComparisonStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma ScalarCuntzLE.conjugate_scalar {u v : A} (h : ScalarCuntzLE u v) (x : A) :
    ScalarCuntzLE (star x * u * x) v := by
  have hc : Continuous (fun z : A => star x * z * x) := by fun_prop
  have hm := image_closure_subset_closure_image hc ⟨u, h, rfl⟩
  apply closure_mono (s := (fun z : A => star x * z * x) ''
      Set.range (fun w : A => star w * v * w)) _ hm
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨w * x, by simp only [star_mul, mul_assoc]⟩

lemma scalarCuntzLE_left_square (x z : A) :
    ScalarCuntzLE (star (x * z) * (x * z)) (star z * z) := by
  have hnorm : star x * x ≤ (‖x‖ ^ 2 + 1) • (1 : A) := by
    apply (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := x)).trans
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right (by linarith) (zero_le_one : (0 : A) ≤ 1)
  have h := star_left_conjugate_le_conjugate hnorm z
  have hh : star (x * z) * (x * z) ≤ (‖x‖ ^ 2 + 1) • (star z * z) := by
    simpa only [star_mul, mul_assoc, mul_smul_comm, smul_mul_assoc, mul_one] using h
  exact (scalarCuntzLE_of_order (star_mul_self_nonneg _) hh).trans
    (scalarCuntzLE_smul (star_mul_self_nonneg _) (by positivity))

lemma scalarCuntzLE_add_of_proper {u w v : A} (hv : ProperlyInfinite v)
    (hu : ScalarCuntzLE u v) (hw : ScalarCuntzLE w v) : ScalarCuntzLE (u + w) v := by
  have h := ((scalarCuntzLE_iff_finite _ _).mp hu).block
    ((scalarCuntzLE_iff_finite _ _).mp hw)
  have heq : matrixBlock (scalarCorner v) (scalarCorner v) = doubleCorner v := by
    rw [← diagonalCorner_one v, matrixBlock_diagonal]
    rfl
  rw [heq] at h
  have hh := h.trans hv
  let Y : CStarMatrix (Fin 2) (Fin 1) A := CStarMatrix.ofMatrix (fun _ _ => 1)
  have hy : Y.conjTranspose * matrixBlock (scalarCorner u) (scalarCorner w) * Y =
      scalarCorner (u + w) := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i
    fin_cases j
    simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    change ((star (1 : A) * u + star 1 * 0) * 1 +
      (star 1 * 0 + star 1 * w) * 1) = u + w
    simp
  exact (scalarCuntzLE_iff_finite _ _).mpr (by simpa only [hy] using hh.conjugate Y)

lemma square_add_le (x y : A) :
    star (x + y) * (x + y) ≤ (2 : ℝ) • (star x * x + star y * y) := by
  have hh := star_mul_self_nonneg (x - y)
  have heq : (2 : ℝ) • (star x * x + star y * y) - star (x + y) * (x + y) =
      star (x - y) * (x - y) := by
    simp only [star_add, star_sub, two_smul]
    noncomm_ring
  rw [← sub_nonneg, heq]
  exact hh

lemma square_comparison_add {x y v : A} (hv : ProperlyInfinite v)
    (hx : ScalarCuntzLE (star x * x) v) (hy : ScalarCuntzLE (star y * y) v) :
    ScalarCuntzLE (star (x + y) * (x + y)) v := by
  exact (scalarCuntzLE_of_order (star_mul_self_nonneg _) (square_add_le x y)).trans
    ((scalarCuntzLE_smul (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
      (by norm_num : (0 : ℝ) < 2)).trans (scalarCuntzLE_add_of_proper hv hx hy))

lemma idealSpan_square_comparison {v z : A} (hv : 0 ≤ v) (hpi : ProperlyInfinite v)
    (hz : z ∈ idealSpan v) : ScalarCuntzLE (star z * z) v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    have hvv : ScalarCuntzLE (star v * v) v := by
      apply scalarCuntzLE_of_mem_Her (star_mul_self_nonneg _) hv
      rw [hv.isSelfAdjoint.star_eq]
      exact mul_mem (self_mem_Her hv) (self_mem_Her hv)
    have hh := ((scalarCuntzLE_left_square x v).trans hvv).conjugate_scalar y
    simpa only [star_mul, mul_assoc] using hh
  | zero =>
    exact subset_closure ⟨0, by simp⟩
  | add x y hx hy ihx ihy => exact square_comparison_add hpi ihx ihy
  | smul c x hx ih =>
    have hh := (scalarCuntzLE_left_square (c • (1 : A)) x).trans ih
    simpa only [smul_mul_assoc, one_mul] using hh

theorem closedIdeal_comparison {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hpi : ProperlyInfinite v) (h : u ∈ closedIdeal v hv.isSelfAdjoint) :
    ScalarCuntzLE u v := by
  let J := closedIdeal v hv.isSelfAdjoint
  have hs : CFC.sqrt u ∈ J := by
    rw [CFC.sqrt_eq_real_sqrt u hu]
    let : IsClosed (J : Set A) := closedIdeal_closed v hv.isSelfAdjoint
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt h
  have hc : Continuous (fun x : A => star x * x) := by fun_prop
  have hh := image_closure_subset_closure_image hc ⟨CFC.sqrt u, hs, rfl⟩
  simp only [(CFC.sqrt_nonneg u).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self u hu] at hh
  apply isClosed_closure.closure_subset_iff.mpr _ hh
  rintro _ ⟨x, hx, rfl⟩
  exact idealSpan_square_comparison hv hpi hx

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance idealComparisonNonUnitalPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance idealComparisonNonUnitalStarOrderedRing : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

lemma scalarCuntzLE_of_inr {u v : A} (hv : 0 ≤ v)
    (h : ScalarCuntzLE (Unitization.inr u : Unitization ℂ A) (Unitization.inr v)) :
    ScalarCuntzLE u v := by
  let V : Unitization ℂ A := Unitization.inr v
  have hc : IsClosed {z : Unitization ℂ A | ScalarCuntzLE z.snd v} :=
    isClosed_closure.preimage Unitization.continuous_snd
  apply closure_minimal (s := Set.range (fun w : Unitization ℂ A => star w * V * w)) _ hc h
  rintro _ ⟨w, rfl⟩
  change ScalarCuntzLE (star w * V * w).snd v
  let hau := CStarAlgebra.increasingApproximateUnit A
  let x := CFC.sqrt v
  have hxx : star x * x = v := by
    rw [(CFC.sqrt_nonneg v).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self v]
  have ht : Tendsto (fun e : A => star (x * e) * (x * e))
      (CStarAlgebra.approximateUnit A) (𝓝 v) := by
    simpa only [hxx] using (hau.tendsto_mul_left x).star.mul (hau.tendsto_mul_left x)
  have hti := (Unitization.continuous_inr (𝕜 := ℂ)).tendsto v |>.comp ht
  have htfinal : Tendsto
      (fun e : A => (star w * (Unitization.inr (star (x*e)*(x*e)) : Unitization ℂ A) * w).snd)
      (CStarAlgebra.approximateUnit A) (𝓝 (star w * V * w).snd) :=
    Unitization.continuous_snd.tendsto _ |>.comp (tendsto_const_nhds.mul hti |>.mul tendsto_const_nhds)
  apply isClosed_closure.mem_of_tendsto htfinal
  apply Filter.Eventually.of_forall
  intro e
  let r : A := ((Unitization.inr e : Unitization ℂ A) * w).snd
  have hr : (Unitization.inr r : Unitization ℂ A) = Unitization.inr e * w := by
    have he := Unitization.inl_fst_add_inr_snd_eq ((Unitization.inr e : Unitization ℂ A) * w)
    simpa [r] using he
  have heq : (star w * (Unitization.inr (star (x*e)*(x*e)) : Unitization ℂ A) * w).snd =
      star r * v * r := by
    apply Unitization.inr_injective (R := ℂ)
    have hs : (Unitization.inr (star r * v * r) : Unitization ℂ A) =
        star w * Unitization.inr (star (x*e)*(x*e)) * w := by
      simp only [Unitization.inr_mul, Unitization.inr_star, hr, star_mul]
      have hx := congrArg (Unitization.inr : A → Unitization ℂ A) hxx
      simp only [Unitization.inr_mul, Unitization.inr_star] at hx
      simp only [mul_assoc] at hx ⊢
      rw [← hx]
      simp only [mul_assoc]
    rw [← hs]
    rfl
  exact heq ▸ subset_closure ⟨r, rfl⟩

end MainGap

end

end OAI
