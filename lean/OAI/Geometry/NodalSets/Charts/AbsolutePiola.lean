import OAI.Geometry.NodalSets.Charts.PiolaFlux

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

def absolutePiola (F : Coord → Coord) (V : Fin 4 → Coord → ℂ)
    (i : Fin 4) (x : Coord) : ℂ :=
  (|(jacobian F x).det| / (jacobian F x).det : ℝ) * signedPiola F V i x

lemma local_absolute_ratio (d : Coord → ℝ) (x : Coord)
    (hd : ContinuousAt d x) (hn : d x ≠ 0) :
    ∃ s : ℝ, s * d x = |d x| ∧ ∀ᶠ z in 𝓝 x, |d z| / d z = s := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨-1, by simp [abs_of_neg hneg], ?_⟩
    filter_upwards [hd.eventually (gt_mem_nhds hneg)] with z hz
    simp [abs_of_neg hz, ne_of_lt hz]
  · refine ⟨1, by simp [abs_of_pos hpos], ?_⟩
    filter_upwards [hd.eventually (lt_mem_nhds hpos)] with z hz
    simp [abs_of_pos hz, ne_of_gt hz]

lemma signedPiola_differentiableAt (F : Coord → Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → Coord → ℂ) (x : Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) (i : Fin 4) :
    DifferentiableAt ℝ (signedPiola F V i) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  exact (Complex.ofRealCLM.differentiableAt.comp x
    ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)).mul
      ((hV a).comp x (hF.differentiable (by simp) x))

theorem absolutePiola_divergence (F : Coord → Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → Coord → ℂ) (x : Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x))
    (hdet : (jacobian F x).det ≠ 0) :
    complexDivergence (absolutePiola F V) x =
      ((|(jacobian F x).det| : ℝ) : ℂ) * complexDivergence V (F x) := by
  have hd : ContinuousAt (fun z ↦ (jacobian F z).det) x :=
    (coordDet_smooth.continuous.comp (hF.fderiv_right (m := ∞) (by simp)).continuous).continuousAt
  obtain ⟨s,hs,hr⟩ := local_absolute_ratio _ x hd hdet
  have he (i : Fin 4) : absolutePiola F V i =ᶠ[𝓝 x]
      fun z ↦ (s:ℂ) * signedPiola F V i z := by
    filter_upwards [hr] with z hz
    simp only [absolutePiola,hz]
  have hpartial (i : Fin 4) : coordPartial i (absolutePiola F V i) x =
      (s:ℂ) * coordPartial i (signedPiola F V i) x := by
    unfold coordPartial
    rw [(he i).fderiv_eq]
    rw [fderiv_const_mul (signedPiola_differentiableAt F hF V x hV i)]
    simp
  unfold complexDivergence
  simp_rw [hpartial]
  rw [← Finset.mul_sum]
  change (s:ℂ) * complexDivergence (signedPiola F V) x = _
  rw [signedPiola_divergence F hF V x hV, ← mul_assoc, ← Complex.ofReal_mul, hs]
  rfl

end
end Yau.Geometry

end OAI
