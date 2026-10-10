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
lemma coefficient_projection_saturation (x : ℕ → D) {r : D} (hr : IsStarProjection r)
    (t : ℂ) (p : ℕ → D) (hp : ∀ m, IsStarProjection (p m))
    (hpr : ∀ m, p m ≤ r) (hpc : ∀ m k, p m*x k=x k*p m)
    (htr : ∀ k, Tendsto (fun m => familyTraceNorm Λ (p m*x k-t • (r*x k))) atTop (𝓝 0)) :
    ∃ q : D, IsStarProjection q ∧ q ≤ r ∧ ∀ k, q*x k=x k*q ∧
      ∀ s : ℕ → I, (Λ s).functional (q*x k)=t*(Λ s).functional (r*x k) := by
  classical
  let J := familyNullIdeal τ (U : Filter ℕ)
  choose c hc0 hcn hc using fun m => positive_contraction_lift J (hp m).nonneg (hp m).norm_le
  choose a ha using J.quotientMap_surjective
  let e : ℕ → ℝ := fun m => 1/((m:ℝ)+1)
  have he (m : ℕ) : 0 < e m := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m j =>
    familyTwoNorm τ (c m j*c m j-c m j) < e m ∧
    familyTwoNorm τ (a r j*c m j-c m j) < e m ∧
    ∀ k ∈ Finset.range (m+1),
      familyTwoNorm τ (c m j*a (x k) j-a (x k) j*c m j) < e m ∧
      familyTraceNorm τ (c m j*a (x k) j-t • (a r j*a (x k) j)) <
        familyTraceNorm Λ (p m*x k-t • (r*x k))+e m
  have hP (m : ℕ) : ∀ᶠ j in (U : Filter ℕ), P m j := by
    have hd : ∀ᶠ j in (U : Filter ℕ), familyTwoNorm τ (c m j*c m j-c m j) < e m := by
      have ht := familyTwoNorm_limitTrace_tendsto τ U (c m*c m-c m)
      rw [map_sub,map_mul,hc m,(hp m).isIdempotentElem.eq,sub_self,familyTwoNorm_zero] at ht
      exact ht.eventually (gt_mem_nhds (he m))
    have hf : ∀ᶠ j in (U : Filter ℕ), familyTwoNorm τ (a r j*c m j-c m j) < e m := by
      have ht := familyTwoNorm_limitTrace_tendsto τ U (a r*c m-c m)
      rw [map_sub,map_mul,ha r,hc m,(hp m).le_iff_mul_eq_right hr |>.mp (hpr m),
        sub_self,familyTwoNorm_zero] at ht
      exact ht.eventually (gt_mem_nhds (he m))
    have ht (k : ℕ) : ∀ᶠ j in (U : Filter ℕ),
        familyTwoNorm τ (c m j*a (x k) j-a (x k) j*c m j) < e m ∧
        familyTraceNorm τ (c m j*a (x k) j-t • (a r j*a (x k) j)) <
          familyTraceNorm Λ (p m*x k-t • (r*x k))+e m := by
      have h1 := familyTwoNorm_limitTrace_tendsto τ U (c m*a (x k)-a (x k)*c m)
      rw [map_sub,map_mul,map_mul,ha (x k),hc m,hpc m k,sub_self,familyTwoNorm_zero] at h1
      have h2 := familyTraceNorm_limitTrace_tendsto τ U (c m*a (x k)-t • (a r*a (x k)))
      rw [map_sub,map_mul,map_smul,map_mul,ha (x k),ha r,hc m] at h2
      exact (h1.eventually (gt_mem_nhds (he m))).and
        (h2.eventually (gt_mem_nhds (lt_add_of_pos_right _ (he m))))
    exact hd.and (hf.and ((eventually_all_finset _).mpr (fun k _ => ht k)))
  obtain ⟨j,hj,hjP⟩ := diagonal_choice U hfree P hP
  let C : lp (fun _ : ℕ => A) ∞ :=
    ⟨fun n => c (j n) n,memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨n,rfl⟩
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (c (j n)) n).trans (hcn (j n))⟩⟩
  have hCsa (n : ℕ) : IsSelfAdjoint (C n) :=
    (map_nonneg (boundedFamilyEval n) (hc0 (j n))).isSelfAdjoint
  have hdiag : Tendsto (fun n => e (j n)) (U : Filter ℕ) (𝓝 0) := helim.comp hj
  have hd : IsFamilyNull τ (U : Filter ℕ) (fun n => C n*C n-C n) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => familyTwoNorm_nonneg τ _)) _ hdiag
    filter_upwards [hjP] with n hn
    exact hn.1.le
  have hq := projection_of_bounded_sequence τ U C hCsa hd
  refine ⟨J.quotientMap C,hq,?_,?_⟩
  · apply (hq.le_iff_mul_eq_right hr).mpr
    have hn : IsFamilyNull τ (U : Filter ℕ) (fun n => (a r*C-C) n) := by
      apply squeeze_zero' (Eventually.of_forall (fun n => familyTwoNorm_nonneg τ _)) _ hdiag
      filter_upwards [hjP] with n hn
      exact hn.2.1.le
    have hz := (familyQuotientMap_eq_zero τ U (a r*C-C)).mpr hn
    rwa [map_sub,map_mul,ha r,sub_eq_zero] at hz
  · intro k
    have hkU : ∀ᶠ n in (U : Filter ℕ), k ∈ Finset.range (j n+1) := by
      filter_upwards [hj.eventually (eventually_ge_atTop k)] with n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
    constructor
    · have hn : IsFamilyNull τ (U : Filter ℕ) (fun n => (C*a (x k)-a (x k)*C) n) := by
        apply squeeze_zero' (Eventually.of_forall (fun n => familyTwoNorm_nonneg τ _)) _ hdiag
        filter_upwards [hjP,hkU] with n hn hk
        exact (hn.2.2 k hk).1.le
      have hz := (familyQuotientMap_eq_zero τ U (C*a (x k)-a (x k)*C)).mpr hn
      rwa [map_sub,map_mul,map_mul,ha (x k),sub_eq_zero] at hz
    · intro s
      have ht : Tendsto (fun n => familyTraceNorm τ ((C*a (x k)-t • (a r*a (x k))) n))
          (U : Filter ℕ) (𝓝 0) := by
        have herr : Tendsto (fun n => familyTraceNorm Λ (p (j n)*x k-t • (r*x k))+e (j n))
            (U : Filter ℕ) (𝓝 0) := by
          simpa only [Function.comp_def, zero_add] using ((htr k).comp hj).add hdiag
        apply squeeze_zero' (Eventually.of_forall (fun n => familyTraceNorm_nonneg τ _)) _ herr
        filter_upwards [hjP,hkU] with n hn hk
        exact (hn.2.2 k hk).2.le
      have hz := tendsto_nhds_unique (familyTraceNorm_limitTrace_tendsto τ U
        (C*a (x k)-t • (a r*a (x k)))) ht
      have hs : (Λ s).functional (J.quotientMap (C*a (x k)-t • (a r*a (x k))))=0 :=
        norm_eq_zero.mp (le_antisymm ((traceNorm_le_family Λ s _).trans hz.le) (norm_nonneg _))
      simpa only [map_sub,map_mul,map_smul,ha (x k),ha r,smul_eq_mul,sub_eq_zero] using hs

end DirectComparison
end
end

end OAI
