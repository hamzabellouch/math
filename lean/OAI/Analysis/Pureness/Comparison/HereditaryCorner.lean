import OAI.Analysis.Pureness.Comparison.TraceCompressionExistence
import OAI.Analysis.Pureness.Comparison.ComparisonIsometry
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

namespace OAI
open Filter Topology
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sandwichSubalgebra (b : A) (hb : IsSelfAdjoint b) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range fun a : A => b * a * b
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, by simp [mul_add, add_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * b * b * y, by simp only [mul_assoc]⟩
  smul_mem' := by rintro z _ ⟨x, rfl⟩; exact ⟨z • x, by simp⟩
  star_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨star x, by simp [hb.star_eq, mul_assoc]⟩

noncomputable def hereditaryCorner (b : A) (hb : 0 ≤ b) : NonUnitalStarSubalgebra ℂ A :=
  (sandwichSubalgebra b hb.isSelfAdjoint).topologicalClosure

@[simp] theorem coe_hereditaryCorner (b : A) (hb : 0 ≤ b) :
    (hereditaryCorner b hb : Set A) = closure (Set.range fun a : A => b * a * b) := rfl

theorem self_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) : b ∈ hereditaryCorner b hb := by
  nontriviality A
  change b ∈ closure (Set.range fun a : A => b * a * b)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let f : ℝ → ℝ := fun t => (t + δ)⁻¹
  have hf : ContinuousOn f (spectrum ℝ b) :=
    (continuousOn_id.add continuousOn_const).inv₀ (fun t ht =>
      ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hb ht) hδ))
  have hm : ContinuousOn (fun t : ℝ => t * f t * t) (spectrum ℝ b) :=
    (continuousOn_id.mul hf).mul continuousOn_id
  have hid : IsSelfAdjoint b := hb.isSelfAdjoint
  have heq : cfc (fun t : ℝ => t - t * f t * t) b = b - b * cfc f b * b := by
    rw [cfc_sub (fun t : ℝ => t) (fun t => t * f t * t) b continuousOn_id hm,
      cfc_mul (fun t : ℝ => t * f t) (fun t => t) b (continuousOn_id.mul hf) continuousOn_id,
      cfc_mul (fun t : ℝ => t) f b continuousOn_id hf, cfc_id' ℝ b]
  have hn : ‖b - b * cfc f b * b‖ ≤ δ := by
    rw [← heq]
    apply norm_cfc_le hδ.le
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hb ht
    have hden : 0 < t + δ := add_pos_of_nonneg_of_pos ht0 hδ
    have hid' : t - t * f t * t = δ * t / (t + δ) := by
      dsimp [f]
      field_simp
      ring
    rw [hid', Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  refine ⟨b * cfc f b * b, ⟨cfc f b, rfl⟩, ?_⟩
  simpa only [dist_eq_norm] using hn.trans_lt (half_lt_self hε)

theorem sqrt_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) :
    CFC.sqrt b ∈ hereditaryCorner b hb := by
  let : IsClosed (hereditaryCorner b hb : Set A) := isClosed_closure
  rw [CFC.sqrt_eq_real_sqrt b hb]
  exact cfcₙ_mem Real.sqrt (self_mem_hereditaryCorner b hb)

theorem hereditaryCorner_sandwich (b : A) (hb : 0 ≤ b) {x y : A}
    (hx : x ∈ hereditaryCorner b hb) (hy : y ∈ hereditaryCorner b hb) (a : A) :
    x * a * y ∈ hereditaryCorner b hb := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvt⟩ := mem_closure_iff_seq_limit.mp hy
  apply mem_closure_of_tendsto ((hut.mul_const a).mul hvt)
  apply Eventually.of_forall
  intro n
  obtain ⟨c, hc⟩ := hu n
  obtain ⟨d, hd⟩ := hv n
  exact ⟨c * b * a * b * d, by rw [← hc, ← hd]; simp only [mul_assoc]⟩

theorem sqrt_sandwich_mem_hereditaryCorner (b : A) (hb : 0 ≤ b) (a : A) :
    CFC.sqrt b * a * CFC.sqrt b ∈ hereditaryCorner b hb :=
  hereditaryCorner_sandwich b hb (sqrt_mem_hereditaryCorner b hb)
    (sqrt_mem_hereditaryCorner b hb) a

theorem exists_hereditary_trace_compression [IsSimpleCStarAlgebra A]
    {e b : A} (he : 0 ≤ e) (hne : e ≠ 0) (hb : 0 ≤ b) :
    ∃ c : A, 0 ≤ c ∧ c ∈ hereditaryCorner e he ∧
      ∀ τ : TracialState A, τ.toPositiveLinearMap c = τ.toPositiveLinearMap b := by
  obtain ⟨c, a, hc, ha, hca, ht⟩ := exists_trace_compression he hne hb
  exact ⟨c, hc, hca ▸ sqrt_sandwich_mem_hereditaryCorner e he a, ht⟩

theorem exists_hereditary_isometry_range {b : A} (hb : 0 ≤ b)
    (hcomp : CuntzSubequiv 1 b) :
    ∃ w : A, star w * w = 1 ∧ IsStarProjection (w * star w) ∧
      w * star w ∈ hereditaryCorner b hb := by
  obtain ⟨w, x, z, hz, hw, hww, hp, hfactor⟩ := exists_isometry_of_one_cuntzSubequiv hb hcomp
  exact ⟨w, hww, hp, hfactor ▸ sqrt_sandwich_mem_hereditaryCorner b hb _⟩

theorem hereditaryCorner_le_of_mem {b c : A} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcb : c ∈ hereditaryCorner b hb) :
    hereditaryCorner c hc ≤ hereditaryCorner b hb := by
  apply closure_minimal
  · rintro _ ⟨a, rfl⟩
    exact hereditaryCorner_sandwich b hb hcb hcb a
  · exact isClosed_closure

theorem hereditaryCorner_mul_eq_zero {b c x : A} (hb : 0 ≤ b)
    (hbc : b * c = 0) (hx : x ∈ hereditaryCorner b hb) : x * c = 0 := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hx
  have hz : ∀ n, u n * c = 0 := by
    intro n
    obtain ⟨a, ha⟩ := hu n
    rw [← ha]
    change b * a * b * c = 0
    rw [mul_assoc, hbc, mul_zero]
  exact tendsto_nhds_unique (hut.mul_const c)
    (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : A)) atTop (𝓝 0)))

theorem exists_hereditary_linking_squares [IsSimpleCStarAlgebra A]
    {c d : A} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcn : c ≠ 0) (hdn : d ≠ 0) :
    ∃ z : A, z ≠ 0 ∧ star z * z ≠ 0 ∧ z * star z ≠ 0 ∧
      0 ≤ star z * z ∧ 0 ≤ z * star z ∧
      star z * z ∈ hereditaryCorner d hd ∧ z * star z ∈ hereditaryCorner c hc ∧
      ∀ τ : TracialState A, τ.toPositiveLinearMap (star z * z) =
        τ.toPositiveLinearMap (z * star z) := by
  obtain ⟨y, z, heq, hzn, hpos, hn, hpos', hn', hfactor, hfactor'⟩ :=
    exists_linking_positive_squares hc hd hcn hdn
  refine ⟨z, hzn, hn, hn', hpos, hpos', ?_, ?_, fun τ => τ.tracial _ _⟩
  · exact subset_closure ⟨_, hfactor.symm⟩
  · exact subset_closure ⟨_, hfactor'.symm⟩

theorem exists_proper_isometry_of_orthogonal_comparison {b c : A}
    (hb : 0 ≤ b) (hcn : c ≠ 0) (hbc : b * c = 0) (hcomp : CuntzSubequiv 1 b) :
    ∃ w : A, star w * w = 1 ∧ IsStarProjection (w * star w) ∧ w * star w ≠ 1 := by
  obtain ⟨w, hw, hp, hmem⟩ := exists_hereditary_isometry_range hb hcomp
  refine ⟨w, hw, hp, ?_⟩
  intro heq
  have hz := hereditaryCorner_mul_eq_zero hb hbc hmem
  rw [heq, one_mul] at hz
  exact hcn hz

end CuntzComparison

end OAI
