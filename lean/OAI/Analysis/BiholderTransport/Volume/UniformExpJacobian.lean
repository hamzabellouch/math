import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactCrossing

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteUniformExpJac (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end WeakMTWTransport

end



noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_bilinear_interval_crossing {K : Set Q} (hK : IsCompact K)
    {H : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ}
    (hH : ∀ q∈K, ContDiffAt ℝ ∞ H (1,q))
    (hneg : ∀ q∈K, ∀ v:E, ‖v‖=1 → 0 < -(fderiv ℝ H (1,q) (1,0) v v)) :
    ∃ c > 0, ∃ C > 0, ∃ ε > 0,
      ∀ s t : ℝ, s∈ball 1 ε → t∈ball 1 ε → s≤t → ∀ q∈K, ∀ v:E,
      c*(t-s)*‖v‖^2 ≤ H (s,q) v v-H (t,q) v v ∧
      H (s,q) v v-H (t,q) v v ≤ C*(t-s)*‖v‖^2 := by
  let J : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ := fun z => fderiv ℝ H z (1,0)
  have hJ : ∀ q∈K, ContinuousAt J (1,q) := by
    intro q hq
    exact ((hH q hq).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  let S : Set (Q×E) := K ×ˢ sphere (0:E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  let F : ℝ×(Q×E) → ℝ := fun z => -(J (z.1,z.2.1) z.2.2 z.2.2)
  have hF : ∀ z∈S, ContinuousAt F (1,z) := by
    intro z hz
    exact ((((hJ z.1 hz.1).comp (x := (1,z))
      (continuousAt_fst.prodMk continuousAt_snd.fst)).clm_apply
        continuousAt_snd.snd).clm_apply continuousAt_snd.snd).neg
  have hFc : ContinuousOn (fun z => F (1,z)) S := by
    intro z hz
    exact ((hF z hz).comp (x := z) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨c,hc,HS⟩ : ∃ c>0, ∀ z∈S, c < F (1,z) := by
    by_cases hne : S.Nonempty
    · obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn hne hFc
      have hp : 0 < F (1,z) := hneg z.1 hz.1 z.2
        (by simpa only [mem_sphere,dist_zero_right] using hz.2)
      exact ⟨F (1,z)/2,half_pos hp,fun y hy => (half_lt_self hp).trans_le (hmin hy)⟩
    · exact ⟨1,zero_lt_one,fun z hz => (hne ⟨z,hz⟩).elim⟩
  have HF : ∀ᶠ t in 𝓝 (1:ℝ), ∀ z∈S, c < F (t,z) :=
    hS.eventually_forall_of_forall_eventually (fun z hz =>
      (continuousAt_const.eventually_lt (hF z hz) (HS z hz)))
  obtain ⟨C,hC,HC⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := 1)) (h := J) (fun q hq _ => hJ q hq)
  have HD : ∀ᶠ t in 𝓝 (1:ℝ), ∀ q∈K, DifferentiableAt ℝ H (t,q) :=
    hK.eventually_forall_of_forall_eventually (fun q hq =>
      (((hH q hq).of_le (m := 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).eventually (by simp)).mono (fun z hz => hz.differentiableAt (by norm_num)))
  obtain ⟨ε,hε,Hε⟩ := Metric.mem_nhds_iff.mp (HF.and (HC.and HD))
  refine ⟨c,hc,C,hC,ε,hε,?_⟩
  intro t₀ t₁ ht₀ ht₁ htt q hq v
  have hall : ∀ s∈Icc t₀ t₁,
      DifferentiableAt ℝ (fun s => H (s,q) v v) s ∧
      deriv (fun s => H (s,q) v v) s ≤ -c*‖v‖^2 ∧
      -C*‖v‖^2 ≤ deriv (fun s => H (s,q) v v) s := by
    intro s hs
    have hsb : s∈ball (1:ℝ) ε := by
      rw [mem_ball,Real.dist_eq,abs_lt] at ht₀ ht₁ ⊢
      constructor <;> linarith only [ht₀.1,ht₀.2,ht₁.1,ht₁.2,hs.1,hs.2]
    have HE := Hε hsb
    have HDs := bilinear_time_hasDerivAt (HE.2.2 q hq) v
    refine ⟨HDs.differentiableAt,?_,?_⟩
    · rw [HDs.deriv]
      have HL := bilinear_lower_of_unit (-J (s,q)) (c := c) (by
        intro w hw
        have H := (HE.1 (q,w) ⟨hq,by simpa only [mem_sphere,dist_zero_right] using hw⟩).le
        exact H) v
      change c*‖v‖^2 ≤ -(J (s,q) v v) at HL
      change J (s,q) v v ≤ -c*‖v‖^2
      linarith only [HL]
    · rw [HDs.deriv]
      have HL := (bilinear_diag_abs_le (J (s,q)) v).trans
        (mul_le_mul_of_nonneg_right (HE.2.1 q hq rfl) (sq_nonneg ‖v‖))
      have HL' := (abs_le.mp HL).1
      change -C*‖v‖^2 ≤ J (s,q) v v
      linarith only [HL']
  have Hcont : ContinuousOn (fun s => H (s,q) v v) (Icc t₀ t₁) :=
    fun s hs => (hall s hs).1.continuousAt.continuousWithinAt
  have HDiff : DifferentiableOn ℝ (fun s => H (s,q) v v) (interior (Icc t₀ t₁)) :=
    fun s hs => (hall s (interior_subset hs)).1.differentiableWithinAt
  have HU := (convex_Icc t₀ t₁).image_sub_le_mul_sub_of_deriv_le Hcont HDiff
    (fun s hs => (hall s (interior_subset hs)).2.1) t₀ ⟨le_rfl,htt⟩ t₁ ⟨htt,le_rfl⟩ htt
  have HL := (convex_Icc t₀ t₁).mul_sub_le_image_sub_of_le_deriv Hcont HDiff
    (fun s hs => (hall s (interior_subset hs)).2.2) t₀ ⟨le_rfl,htt⟩ t₁ ⟨htt,le_rfl⟩ htt
  constructor <;> nlinarith only [HU,HL]

end WeakMTWTransport

end

end OAI
