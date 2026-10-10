import Mathlib
import OAI.Geometry.SmoothYau.Limits.CompactFullProfileMargin

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
namespace YauCounterexamples
open Set Filter Submodule
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_preparation_covector (hd : Module.finrank ℝ E = 3)
    {a : E} (ha : a ≠ 0) {H : ProfileForm E} (hs : profileStrict H a) :
    ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ l a = 0 ∧
      (∀ c : ℝ, profileStrict (H + c • profileRankOne l) a) ∧
      ∃ C : ℕ, ∀ c : ℝ, C ≤ c → profileFull (H + c • profileRankOne l) a := by
  obtain ⟨w,hw,haw,hpos⟩ := hs
  let K := (ℝ ∙ a)ᗮ
  let wK : K := ⟨w,mem_orthogonal_singleton_iff_inner_right.mpr haw⟩
  have hwK : wK ≠ 0 := by
    intro h
    have hh := congrArg (fun z : K => ‖(z:E)‖) h
    simp [wK,hw] at hh
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton ha
  let : Fact (Module.finrank ℝ K = 1+1) := ⟨hK⟩
  let L := (ℝ ∙ wK)ᗮ
  have hL : Module.finrank ℝ L = 1 := finrank_orthogonal_span_singleton hwK
  let b : OrthonormalBasis (Fin 1) ℝ L := OrthonormalBasis.fromOrthogonalSpanSingleton 1 hwK
  let e : K := b 0
  have hen : e ≠ 0 := by
    intro h
    have hh : ‖b 0‖ = 0 := by change ‖e‖ = 0; rw [h,norm_zero]
    rw [b.norm_eq_one] at hh
    norm_num at hh
  have heL : e ∈ L := (b 0).property
  have hspan : L = ℝ ∙ e := eq_span_singleton_of_mem_of_finrank_eq_one hL heL hen
  let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E (e:E)
  have hla : l a = 0 := by
    change inner ℝ (e:E) a = 0
    rw [real_inner_comm]
    exact mem_orthogonal_singleton_iff_inner_right.mp e.property
  have hlw : l w = 0 := by
    change inner ℝ (e:E) w = 0
    have hh := mem_orthogonal_singleton_iff_inner_right.mp heL
    rw [real_inner_comm]
    exact hh
  have hlne : l ≠ 0 := by
    intro h
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f (e:E)) h
    change inner ℝ (e:E) (e:E) = 0 at hh
    exact hen (Subtype.ext (inner_self_eq_zero.mp hh))
  have hker : ∀ v, ‖v‖ = 1 → inner ℝ a v = 0 → l v = 0 →
      0 < profileTrace H a v := by
    intro v hv hav hlv
    let vK : K := ⟨v,mem_orthogonal_singleton_iff_inner_right.mpr hav⟩
    have hvL : vK ∈ Lᗮ := by
      apply (L.mem_orthogonal vK).mpr
      intro z hz
      rw [hspan] at hz
      obtain ⟨c,rfl⟩ := mem_span_singleton.mp hz
      simp only [inner_smul_left,conj_trivial]
      change c * l v = 0
      rw [hlv,mul_zero]
    have hvspan : vK ∈ ℝ ∙ wK := by
      simpa only [L,orthogonal_orthogonal] using hvL
    obtain ⟨c,hc⟩ := mem_span_singleton.mp hvspan
    have hcv : c • w = v := congrArg (fun z : K => (z:E)) hc
    have hcn : |c| = 1 := by simpa only [←hcv,norm_smul,Real.norm_eq_abs,hw,mul_one] using hv
    have hcsq : c*c = 1 := by nlinarith [sq_abs c]
    rw [←hcv]
    unfold profileTrace
    simp only [map_smul,smul_apply,smul_eq_mul]
    have heq : c*(c*H w w) = H w w := by rw [←mul_assoc,hcsq,one_mul]
    rw [heq]
    exact hpos
  have hfull := preparation_rankOne_full (show IsCompact ({()} : Set Unit) from isCompact_singleton) (fun _ : Unit => H)
    (fun _ : Unit => a) (fun _ : Unit => l) continuous_const continuous_const continuous_const
    (fun _ _ => hker)
  obtain ⟨C,hC⟩ := hfull
  exact ⟨l,hlne,hla,profileStrict_rankOne H a l hla ⟨w,hw,haw,hlw,hpos⟩,
    C,fun c hc => hC () (mem_singleton ()) c hc⟩

end YauCounterexamples

end

end OAI
