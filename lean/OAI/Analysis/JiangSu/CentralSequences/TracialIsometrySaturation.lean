import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.CoefficientSplit
import OAI.Analysis.JiangSu.CStarAlgebras.ContractionLift

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] (τ : I → TracialState A) [Nonempty I]
  (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
local notation "D" => FamilyUltrapower τ U
local notation "L" => familyLimitTrace τ U

include hfree in
lemma tracial_isometry_saturation (p q : D) (v : ℕ → D) (hvn : ∀ n,‖v n‖≤1)
    (hp : Tendsto (fun n => familyTwoNorm L (star (v n)*v n-p)) atTop (𝓝 0))
    (hq : Tendsto (fun n => familyTwoNorm L (q*v n-v n)) atTop (𝓝 0)) :
    ∃ w : D,star w*w=p ∧ q*w=w := by
  classical
  let J := familyNullIdeal τ (U : Filter ℕ)
  choose b hb hbn using fun n => CStarLift.exists_contraction J.quotientStarHom
    J.quotientMap_surjective (hvn n)
  obtain ⟨a,ha⟩ := J.quotientMap_surjective p
  obtain ⟨c,hc⟩ := J.quotientMap_surjective q
  let e : ℕ → ℝ := fun m => 1/((m:ℝ)+1)
  have he (m : ℕ) : 0<e m := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m j =>
    familyTwoNorm τ (star (b m j)*b m j-a j)<familyTwoNorm L (star (v m)*v m-p)+e m ∧
    familyTwoNorm τ (c j*b m j-b m j)<familyTwoNorm L (q*v m-v m)+e m
  have hP (m : ℕ) : ∀ᶠ j in (U : Filter ℕ),P m j := by
    have h1 := familyTwoNorm_limitTrace_tendsto τ U (star (b m)*b m-a)
    have h2 := familyTwoNorm_limitTrace_tendsto τ U (c*b m-b m)
    change Tendsto _ _ (𝓝 (familyTwoNorm L (J.quotientStarHom (star (b m)*b m-a)))) at h1
    change Tendsto _ _ (𝓝 (familyTwoNorm L (J.quotientStarHom (c*b m-b m)))) at h2
    rw [map_sub,map_mul,map_star,hb m,show J.quotientStarHom a=p from ha] at h1
    rw [map_sub,map_mul,hb m,show J.quotientStarHom c=q from hc] at h2
    exact (h1.eventually_lt_const (lt_add_of_pos_right _ (he m))).and
      (h2.eventually_lt_const (lt_add_of_pos_right _ (he m)))
  obtain ⟨j,hj,hjP⟩ := diagonal_choice U hfree P hP
  let B : lp (fun _ : ℕ => A) ∞ := ⟨fun n => b (j n) n,memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (b (j n)) n).trans (hbn (j n))⟩⟩
  have h1 : IsFamilyNull τ (U : Filter ℕ) (fun n => (star B*B-a) n) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => familyTwoNorm_nonneg τ _)) ?_
      (by simpa using ((hp.add helim).comp hj))
    filter_upwards [hjP] with n hn
    exact hn.1.le
  have h2 : IsFamilyNull τ (U : Filter ℕ) (fun n => (c*B-B) n) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => familyTwoNorm_nonneg τ _)) ?_
      (by simpa using ((hq.add helim).comp hj))
    filter_upwards [hjP] with n hn
    exact hn.2.le
  refine ⟨J.quotientStarHom B,?_,?_⟩
  · have h := (familyQuotientMap_eq_zero τ U (star B*B-a)).mpr h1
    rwa [map_sub,map_mul,J.quotientMap_star,ha,sub_eq_zero] at h
  · have h := (familyQuotientMap_eq_zero τ U (c*B-B)).mpr h2
    rwa [map_sub,map_mul,hc,sub_eq_zero] at h

end DirectComparison

end
end

end OAI
