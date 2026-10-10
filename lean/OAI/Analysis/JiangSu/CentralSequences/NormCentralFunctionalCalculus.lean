import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.ExcisionUpperCut

namespace OAI

section

noncomputable section
namespace DirectComparison
open Filter Topology CStarAlgebra
open scoped ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance : Module ℝ (lp (fun _ : ℕ => A) ∞) := Module.complexToReal _

 def boundedEvaluation (n : ℕ) : (lp (fun _ : ℕ => A) ∞) →⋆ₙₐ[ℂ] A where
  toFun x := x n
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

 def boundedDiagonal (a : A) : lp (fun _ : ℕ => A) ∞ :=
  ⟨fun _ => a,memℓp_infty ⟨‖a‖,by simp⟩⟩

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma bounded_selfAdjoint (x : lp (fun _ : ℕ => A) ∞)
    (hx : ∀ n,IsSelfAdjoint (x n)) : IsSelfAdjoint x := by
  change star x = x
  ext n
  exact (hx n).star_eq

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma bounded_cfc_apply (g : ℝ → ℝ) (hg : Continuous g) (hg0 : g 0=0)
    (x : lp (fun _ : ℕ => A) ∞) (hx : ∀ n,IsSelfAdjoint (x n)) (n : ℕ) :
    (cfcₙ g x) n=cfcₙ g (x n) := by
  exact (boundedEvaluation n).map_cfcₙ g x hg.continuousOn hg0 (by fun_prop)
    (bounded_selfAdjoint x hx) (hx n)

 omit [PartialOrder A] [StarOrderedRing A] in
 theorem norm_central_cfc (U : Ultrafilter ℕ) (x : lp (fun _ : ℕ => A) ∞)
    (hx : ∀ n,IsSelfAdjoint (x n)) (a : A)
    (hcentral : Tendsto (fun n => ‖x n*a-a*x n‖) (U : Filter ℕ) (𝓝 0))
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : g 0=0) :
    Tendsto (fun n => ‖cfcₙ g (x n)*a-a*cfcₙ g (x n)‖) (U : Filter ℕ) (𝓝 0) := by
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  have hc : Commute (q x) (q (boundedDiagonal a)) :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (x*boundedDiagonal a) (boundedDiagonal a*x)).mpr hcentral
  have hsa : IsSelfAdjoint (q x) := (bounded_selfAdjoint x hx).map q
  have hcfc := (hsa.commute_cfcₙ hc g).eq
  rw [←q.map_cfcₙ g x hg.continuousOn hg0 (by fun_prop) (bounded_selfAdjoint x hx) hsa] at hcfc
  have hv : Tendsto (fun n => ‖(cfcₙ g x) n*a-a*(cfcₙ g x) n‖) (U : Filter ℕ) (𝓝 0) :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (cfcₙ g x*boundedDiagonal a)
      (boundedDiagonal a*cfcₙ g x)).mp hcfc
  simpa only [bounded_cfc_apply g hg hg0 x hx] using hv

 theorem norm_central_upperCut_sqrt (U : Ultrafilter ℕ) (f : lp (fun _ : ℕ => A) ∞)
    (hf : ∀ n,0 ≤ f n) (a : A)
    (hcentral : Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n => ‖CFC.sqrt (upperCut δ (f n))*a-a*CFC.sqrt (upperCut δ (f n))‖)
      (U : Filter ℕ) (𝓝 0) := by
  let g : ℝ → ℝ := fun t => δ⁻¹*max (t-(1-δ)) 0
  have hg : Continuous g := by fun_prop
  have hg0 : g 0=0 := by
    dsimp [g]
    rw [max_eq_right (sub_nonpos.mpr (sub_nonneg.mpr hδ1)),mul_zero]
  let q := cfcₙ g f
  have hq (n : ℕ) : q n=upperCut δ (f n) := by
    rw [bounded_cfc_apply g hg hg0 f (fun n => (hf n).isSelfAdjoint) n,
      cfcₙ_eq_cfc hg.continuousOn hg0,upperCut_cfc]
  have hqc := norm_central_cfc U f (fun n => (hf n).isSelfAdjoint) a hcentral g hg hg0
  have hqc' : Tendsto (fun n => ‖q n*a-a*q n‖) (U : Filter ℕ) (𝓝 0) := by
    simpa only [q,bounded_cfc_apply g hg hg0 f (fun n => (hf n).isSelfAdjoint)] using hqc
  have he := norm_central_cfc U q (fun n => by rw [hq]; exact (upperCut_nonneg hδ.le _).isSelfAdjoint)
    a hqc' Real.sqrt Real.continuous_sqrt Real.sqrt_zero
  have hs (n : ℕ) := CFC.sqrt_eq_real_sqrt (upperCut δ (f n)) (upperCut_nonneg hδ.le _)
  simpa only [hq,←hs] using he

end DirectComparison

end
end

end OAI
