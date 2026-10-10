import OAI.Analysis.HenonEmden.CutoffSmooth

namespace OAI

section WeightedVirial

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma continuousOn_radialDir {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u ({0}ᶜ : Set (Space n))) :
    ContinuousOn (fun x => dir u x x) ({0}ᶜ : Set (Space n)) :=
  (hu.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).clm_apply continuousOn_id

lemma weighted_virial_off_origin {n : ℕ} {u θ : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (q B : ℝ) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hθ0 : 0 ∉ tsupport θ) :
    (∫ x, energyDensity u q B x*((n+B)*θ x+dir θ x x)) =
      -(q+1)*(∫ x, θ x*source u q B x*dir u x x) := by
  have hF := regular_energyDensity hu hup q B
  have hs : tsupport θ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff]
    intro he; subst x; exact hθ0 hx
  have hθc' : HasCompactSupport (fun x => B*θ x) := hθc.mul_left
  have hiFθ : Integrable (fun x => energyDensity u q B x*θ x) :=
    integrable_mul_compact hθc (hF.continuousOn.mono hs) hθ.continuous.continuousOn
  have hiG : Integrable (fun x => θ x*source u q B x*dir u x x) := by
    have hc := (regular_source hu hup q B).continuousOn.mul (continuousOn_radialDir (hu.of_le (by norm_num)))
    exact (integrable_mul_compact hθc (hc.mono hs) hθ.continuous.continuousOn).congr
      (ae_of_all _ (fun _ => by dsimp only [Pi.mul_apply]; ring))
  have hiFD : Integrable (fun x => θ x*dir (energyDensity u q B) x x) := by
    exact (integrable_mul_compact hθc ((continuousOn_radialDir (hF.of_le (by norm_num))).mono hs)
      hθ.continuous.continuousOn).congr (ae_of_all _ (fun _ => mul_comm _ _))
  have hpoint (x : Space n) : θ x*dir (energyDensity u q B) x x =
      B*(energyDensity u q B x*θ x)+(q+1)*(θ x*source u q B x*dir u x x) := by
    by_cases hx : x ∈ tsupport θ
    · have hx0 := hs hx
      have hr := norm_ne_zero_iff.mpr hx0
      rw [dir_energyDensity hu hup q B hx0,real_inner_self_eq_norm_sq]
      field_simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      ring
  have hrad := integral_radial_test (hF.of_le (by norm_num)) hθ hθc hθ0
  have hiL : Integrable (fun x => energyDensity u q B x*((n:ℝ)*θ x+dir θ x x)) := by
    have hc : Continuous (fun x : Space n => (n:ℝ)*θ x+dir θ x x) := (continuous_const.mul hθ.continuous).add ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_id)
    have hk : HasCompactSupport (fun x => (n:ℝ)*θ x+dir θ x x) := by
      apply HasCompactSupport.intro hθc
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx]
      have hd : fderiv ℝ θ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [dir,hd]
    have hsub : tsupport (fun x => (n:ℝ)*θ x+dir θ x x) ⊆ tsupport θ := by
      apply closure_minimal _ (isClosed_tsupport θ)
      intro x hx
      contrapose! hx
      simp only [Function.mem_support,not_not]
      rw [image_eq_zero_of_notMem_tsupport hx]
      have hd : fderiv ℝ θ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      simp [dir,hd]
    exact integrable_mul_compact hk (hF.continuousOn.mono (hsub.trans hs)) hc.continuousOn
  have hsumF := integral_add hiL (hiFθ.const_mul B)
  have hsumG := integral_add (hiFθ.const_mul B) (hiG.const_mul (q+1))
  simp_rw [hpoint] at hrad
  rw [hsumG,integral_const_mul,integral_const_mul] at hrad
  calc
    _ = (∫ x, energyDensity u q B x*((n:ℝ)*θ x+dir θ x x))+
        B*(∫ x, energyDensity u q B x*θ x) := by
      rw [← integral_const_mul,← hsumF]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := by linarith

end HenonLaneEmden
end
end WeightedVirial

end OAI
