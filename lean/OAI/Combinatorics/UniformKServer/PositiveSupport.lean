import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalLaw

namespace OAI

                                      
section

/-! Removing zero atoms of a finite nonnegative law does not change any
weighted observable or conditional law on its support. This justifies the
positive-law presentation, without an assertion on impossible histories. -/
noncomputable section
namespace UniformKServer.PositiveSupport
open Finset ConditionalLaw
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

abbrev Support (w : Ω → ℝ) := {ω : Ω // 0 < w ω}

theorem sum_support (w f : Ω → ℝ) (hz : ∀ ω, ¬ 0 < w ω → f ω = 0) :
    (∑ ω : Support w, f ω) = ∑ ω, f ω := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun ω => 0 < w ω) f
  have he : (∑ ω : {ω : Ω // ¬0 < w ω}, f ω) = 0 := by
    exact sum_eq_zero fun ω _ => hz ω ω.property
  rw [he,add_zero] at h
  exact h

theorem weighted_sum (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (f : Ω → ℝ) :
    (∑ ω : Support w, w ω*f ω) = ∑ ω, w ω*f ω := by
  apply sum_support w (fun ω => w ω*f ω)
  intro ω hω
  have hz : w ω=0 := le_antisymm (le_of_not_gt hω) (hw ω)
  simp only [hz,zero_mul]

theorem total (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (ht : ∑ ω, w ω=1) :
    (∑ ω : Support w, w ω)=1 := by
  have h := weighted_sum w hw (fun _ => 1)
  simpa only [mul_one,ht] using h

def filtration (w : Ω → ℝ) (F : Setoid Ω) : Setoid (Support w) := Setoid.comap Subtype.val F

theorem mass_eq (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω : Support w) :
    ConditionalLaw.mass (fun v : Support w => w v) (filtration w F) ω = ConditionalLaw.mass w F ω := by
  unfold ConditionalLaw.mass filtration Setoid.comap
  apply sum_support w (fun v => if F.r ω v then w v else 0)
  intro v hv
  have hz : w v=0 := le_antisymm (le_of_not_gt hv) (hw v)
  simp only [hz,ite_self]

theorem kernel_eq (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω v : Support w) :
    kernel (fun v : Support w => w v) (filtration w F) ω v = kernel w F ω v := by
  unfold kernel
  rw [mass_eq w hw]
  rfl

theorem posterior_eq (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (f : Ω → ℝ) (ω : Support w) :
    posterior (fun v : Support w => w v) (filtration w F) (fun v => f v) ω =
      posterior w F f ω := by
  unfold posterior
  simp only [kernel_eq w hw]
  apply sum_support w (fun v => kernel w F ω v*f v)
  intro v hv
  have hz : w v=0 := le_antisymm (le_of_not_gt hv) (hw v)
  simp only [kernel,hz,zero_div,ite_self,zero_mul]

end UniformKServer.PositiveSupport

end


end

end OAI
