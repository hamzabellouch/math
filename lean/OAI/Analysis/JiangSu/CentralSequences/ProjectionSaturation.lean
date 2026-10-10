import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.CoefficientSplit

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] (τ : I → TracialState A) [Nonempty I]
  (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U

include hfree in
lemma projection_saturation (S : Finset D) (h : D) (p : ℕ → D)
    (hp : ∀ m, IsStarProjection (p m))
    (hfix : ∀ m a, a ∈ S → a*p m=p m)
    (htr : Tendsto (fun m => familyTraceNorm Λ (p m-h)) atTop (𝓝 0)) :
    ∃ q : D, IsStarProjection q ∧ (∀ a ∈ S, a*q=q) ∧
      ∀ s : ℕ → I, (Λ s).functional q=(Λ s).functional h := by
  classical
  let J := familyNullIdeal τ (U : Filter ℕ)
  choose c hc0 hcn hc using fun m =>
    positive_contraction_lift J (hp m).nonneg (hp m).norm_le
  choose lift hlift using J.quotientMap_surjective
  let e : ℕ → ℝ := fun m => 1/((m : ℝ)+1)
  have he (m : ℕ) : 0 < e m := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m k =>
    familyTwoNorm τ (c m k*c m k-c m k) < e m ∧
    (∀ a ∈ S, familyTwoNorm τ (lift a k*c m k-c m k) < e m) ∧
    familyTraceNorm τ (c m k-lift h k) < familyTraceNorm Λ (p m-h)+e m
  have hP (m : ℕ) : ∀ᶠ k in (U : Filter ℕ), P m k := by
    have hd : ∀ᶠ k in (U : Filter ℕ),
        familyTwoNorm τ (c m k*c m k-c m k) < e m := by
      have ht := familyTwoNorm_limitTrace_tendsto τ U (c m*c m-c m)
      rw [map_sub,map_mul,hc m,(hp m).isIdempotentElem.eq,sub_self,
        familyTwoNorm_zero] at ht
      exact ht.eventually (gt_mem_nhds (he m))
    have hf (a : D) (ha : a ∈ S) : ∀ᶠ k in (U : Filter ℕ),
        familyTwoNorm τ (lift a k*c m k-c m k) < e m := by
      have ht := familyTwoNorm_limitTrace_tendsto τ U (lift a*c m-c m)
      rw [map_sub,map_mul,hlift a,hc m,hfix m a ha,sub_self,
        familyTwoNorm_zero] at ht
      exact ht.eventually (gt_mem_nhds (he m))
    have ht : ∀ᶠ k in (U : Filter ℕ),
        familyTraceNorm τ (c m k-lift h k) < familyTraceNorm Λ (p m-h)+e m := by
      have ht := familyTraceNorm_limitTrace_tendsto τ U (c m-lift h)
      rw [map_sub,hc m,hlift h] at ht
      exact ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ (he m)))
    exact hd.and (((eventually_all_finset S).mpr hf).and ht)
  obtain ⟨j,hj,hjP⟩ := diagonal_choice U hfree P hP
  let C : lp (fun _ : ℕ => A) ∞ :=
    ⟨fun k => c (j k) k,memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨k,rfl⟩
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (c (j k)) k).trans (hcn (j k))⟩⟩
  have hCsa (k : ℕ) : IsSelfAdjoint (C k) := by
    exact (map_nonneg (boundedFamilyEval k) (hc0 (j k))).isSelfAdjoint
  have hdiag : Tendsto (fun k => e (j k)) (U : Filter ℕ) (𝓝 0) := helim.comp hj
  have hd : IsFamilyNull τ (U : Filter ℕ) (fun k => C k*C k-C k) := by
    apply squeeze_zero'
      (Eventually.of_forall (fun k => familyTwoNorm_nonneg τ (C k*C k-C k))) _ hdiag
    filter_upwards [hjP] with k hk
    exact hk.1.le
  refine ⟨J.quotientMap C,projection_of_bounded_sequence τ U C hCsa hd,?_,?_⟩
  · intro a ha
    have hn : IsFamilyNull τ (U : Filter ℕ) (fun k => (lift a*C-C) k) := by
      apply squeeze_zero'
        (Eventually.of_forall (fun k => familyTwoNorm_nonneg τ ((lift a*C-C) k))) _ hdiag
      filter_upwards [hjP] with k hk
      exact (hk.2.1 a ha).le
    have hz := (familyQuotientMap_eq_zero τ U (lift a*C-C)).mpr hn
    rw [map_sub,map_mul,hlift a,sub_eq_zero] at hz
    exact hz
  · intro s
    have ht : Tendsto (fun k => familyTraceNorm τ ((C-lift h) k))
        (U : Filter ℕ) (𝓝 0) := by
      have herr : Tendsto (fun k => familyTraceNorm Λ (p (j k)-h)+e (j k))
          (U : Filter ℕ) (𝓝 0) := by simpa using (htr.comp hj).add hdiag
      apply squeeze_zero'
        (Eventually.of_forall (fun k => familyTraceNorm_nonneg τ ((C-lift h) k))) _ herr
      filter_upwards [hjP] with k hk
      exact hk.2.2.le
    have hz := tendsto_nhds_unique (familyTraceNorm_limitTrace_tendsto τ U (C-lift h)) ht
    have hs : (Λ s).functional (J.quotientMap (C-lift h))=0 :=
      norm_eq_zero.mp (le_antisymm ((traceNorm_le_family Λ s _).trans hz.le) (norm_nonneg _))
    simpa only [map_sub,hlift h,sub_eq_zero] using hs

end DirectComparison
end
end

end OAI
