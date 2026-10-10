import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RealForm

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Submodule
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma critical_transverse_positive (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) {ν : E} (hν : ‖ν‖ = 1)
    (hP : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b : E, ‖b‖ = 1 ∧ inner ℝ ν b = 0 ∧ 0 < H b b := by
  obtain ⟨P, hdP, hP⟩ := hP
  have hνne : ν ≠ 0 := by intro he; simp [he] at hν
  let : Fact (Module.finrank ℝ E = 2 + 1) := ⟨hd⟩
  let K := (ℝ ∙ ν)ᗮ
  have hdK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton hνne
  have hdim := P.finrank_sup_add_finrank_inf_eq K
  have hle : Module.finrank ℝ (P ⊔ K : Submodule ℝ E) ≤ 3 := (Submodule.finrank_le _).trans_eq hd
  have hpos : 0 < Module.finrank ℝ (P ⊓ K : Submodule ℝ E) := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hvE : (v : E) ≠ 0 := fun he => hv (Subtype.ext he)
  let b : E := ‖(v : E)‖⁻¹ • (v : E)
  have hnp : 0 < ‖(v : E)‖ := norm_pos_iff.mpr hvE
  refine ⟨b, ?_, ?_, ?_⟩
  · simp [b, norm_smul, hnp.ne']
  · have ho := mem_orthogonal_singleton_iff_inner_right.mp v.property.2
    simp [b, inner_smul_right, ho]
  · have hvpos := hP (v : E) v.property.1 hvE
    dsimp [b]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    positivity

lemma exists_good_transverse (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1) (haν : a = ‖a‖ • ν)
    (hnc : a ≠ 0 → ∃ b, inner ℝ a b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b)
    (hc : a = 0 → ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b, inner ℝ ν b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧ 0 < H a a + H b b := by
  by_cases ha : a = 0
  · obtain ⟨b, hb, hνb, hH⟩ := critical_transverse_positive hd H hν (hc ha)
    exact ⟨b, hνb, by simp [ha, hb], by simpa [ha] using hH⟩
  · obtain ⟨b, hab, hb, hH⟩ := hnc ha
    refine ⟨b, ?_, hb, hH⟩
    have he : ‖a‖ * inner ℝ ν b = 0 := by
      rw [haν, inner_smul_left, conj_trivial] at hab
      exact hab
    exact (mul_eq_zero.mp he).resolve_left (norm_ne_zero_iff.mpr ha)

omit [FiniteDimensional ℝ E] in
lemma exists_second_transverse_unit (hd : Module.finrank ℝ E = 3)
    {ν b : E} (hν : ν ≠ 0) (hb : b ≠ 0) (hνb : inner ℝ ν b = 0) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ ν w = 0 ∧ inner ℝ b w = 0 := by
  let K := (ℝ ∙ ν)ᗮ
  let bK : K := ⟨b, mem_orthogonal_singleton_iff_inner_right.mpr hνb⟩
  have hbK : bK ≠ 0 := fun he => hb (congrArg Subtype.val he)
  let : Fact (Module.finrank ℝ E = 2 + 1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := finrank_orthogonal_span_singleton hν
  let : Fact (Module.finrank ℝ K = 1 + 1) := ⟨hK⟩
  let B : OrthonormalBasis (Fin 1) ℝ ((ℝ ∙ bK)ᗮ : Submodule ℝ K) :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 1 hbK
  let wK : K := B 0
  refine ⟨wK, B.norm_eq_one 0, ?_, ?_⟩
  · exact mem_orthogonal_singleton_iff_inner_right.mp wK.property
  · have h : inner ℝ bK wK = 0 :=
      mem_orthogonal_singleton_iff_inner_right.mp (B 0).property
    exact h

theorem two_good_transverse (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1)
    (b : E) (hνb : inner ℝ ν b = 0) (hb : ‖b‖^2 = 1 + ‖a‖^2)
    (hgood : 0 < H a a + H b b) :
    ∃ c : E, inner ℝ ν c = 0 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H c c ∧
      0 < ‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2 := by
  have hbpos : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a‖]
  have hνne : ν ≠ 0 := by intro he; simp [he] at hν
  obtain ⟨w, hw, hνw, hbw⟩ := exists_second_transverse_unit hd hνne
    (norm_ne_zero_iff.mp hbpos.ne') hνb
  let f : ℝ → E := fun t => Real.cos t • b + (‖b‖ * Real.sin t) • w
  have hf : Continuous f := by unfold f; fun_prop
  have hf0 : f 0 = b := by simp [f]
  have hc : Continuous (fun t => H a a + H (f t) (f t)) :=
    continuous_const.add ((H.toContinuousBilinearMap.continuous.comp hf).clm_apply hf)
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < H a a + H (f t) (f t) :=
    (hc.tendsto 0).eventually_const_lt (by simpa [hf0] using hgood)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  let t : ℝ := min (ε / 2) (Real.pi / 2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have htπ : t < Real.pi := (min_le_right _ _).trans_lt (by nlinarith [Real.pi_pos])
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htπ
  have hn : inner ℝ b b = ‖b‖^2 := real_inner_self_eq_norm_sq b
  have hnw : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwb : inner ℝ w b = 0 := by simpa [real_inner_comm] using hbw
  have hfn : ‖f t‖^2 = ‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [f, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial, hn, hnw, hbw, hwb, mul_zero, zero_add, add_zero]
    calc
      _ = ‖b‖^2 * ((Real.sin t)^2 + (Real.cos t)^2) := by ring
      _ = ‖b‖^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hinner : inner ℝ b (f t) = Real.cos t * ‖b‖^2 := by
    simp only [f, inner_add_right, inner_smul_right, hn, hbw, mul_zero, add_zero]
  refine ⟨f t, ?_, hfn.trans hb, ?_, ?_⟩
  · simp [f, inner_add_right, inner_smul_right, hνb, hνw]
  · exact he (by simpa [Real.dist_eq, abs_of_pos ht] using htε)
  · rw [hfn, hinner]
    have heq : ‖b‖^2 * ‖b‖^2 - (Real.cos t * ‖b‖^2)^2 =
        ‖b‖^4 * (Real.sin t)^2 := by
      calc
        _ = ‖b‖^4 * (1 - (Real.cos t)^2) := by ring
        _ = ‖b‖^4 * (Real.sin t)^2 := by
          rw [show 1 - (Real.cos t)^2 = (Real.sin t)^2 by
            linarith [Real.sin_sq_add_cos_sq t]]
    rw [heq]
    positivity

theorem actual_two_transverse_phases (hd : Module.finrank ℝ E = 3)
    (H : RealForm E) (a ν : E) (hν : ‖ν‖ = 1) (haν : a = ‖a‖ • ν)
    (hnc : a ≠ 0 → ∃ b, inner ℝ a b = 0 ∧ ‖b‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b)
    (hc : a = 0 → ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H v v) :
    ∃ b c, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
      ‖b‖^2 = 1 + ‖a‖^2 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
      0 < H a a + H b b ∧ 0 < H a a + H c c ∧
      0 < ‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2 := by
  obtain ⟨b, hνb, hb, hgood⟩ := exists_good_transverse hd H a ν hν haν hnc hc
  obtain ⟨c, hνc, hcn, hcg, hangle⟩ := two_good_transverse hd H a ν hν b hνb hb hgood
  exact ⟨b, c, hνb, hνc, hb, hcn, hgood, hcg, hangle⟩

end YauCounterexamples


end

end OAI
