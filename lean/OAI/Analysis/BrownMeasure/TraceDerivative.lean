import Mathlib
import OAI.Analysis.BrownMeasure.Mercator

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))

include hτ in
lemma trace_mercator_deriv_of_bounds
    {f d : ℝ → A} {s : Set ℝ} {x r D : ℝ}
    (hs : IsOpen s) (hsp : IsPreconnected s) (hx : x∈s)
    (hr0 : 0≤r) (hr1 : r<1) (_hD : 0≤D)
    (hf : ∀ t∈s, HasDerivAt f (d t) t)
    (hfn : ∀ t∈s,‖f t‖≤r) (hdn : ∀ t∈s,‖d t‖≤D) :
    HasDerivAt (fun t=>τ (mercator (f t))) (-τ ((1-f x)⁻¹ʳ*d x)) x := by
  let g : ℕ → ℝ → ℝ := fun n t=>-((n+1:ℝ)⁻¹)*τ (f t^(n+1))
  let g' : ℕ → ℝ → ℝ := fun n t=>-τ (f t^n*d t)
  have hg (n : ℕ) (t : ℝ) (ht : t∈s) : HasDerivAt (g n) (g' n t) t := by
    have hd := (trace_pow_deriv τ hτ (hf t ht) n).const_mul (-((n+1:ℝ)⁻¹))
    have he : -((n+1:ℝ)⁻¹)*((n+1:ℝ)*τ (f t^n*d t))= -τ (f t^n*d t) := by
      field_simp
    simpa only [g,g',he] using hd
  have hgn (n : ℕ) (t : ℝ) (ht : t∈s) : ‖g' n t‖≤r^n*(‖τ‖*D) := by
    dsimp [g']
    rw [abs_neg]
    calc
      _ ≤ ‖τ‖*‖f t^n*d t‖ := τ.le_opNorm _
      _ ≤ ‖τ‖*(‖f t‖^n*‖d t‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _))
      _ ≤ ‖τ‖*(r^n*D) := by gcongr; exact hfn t ht; exact hdn t ht
      _ = r^n*(‖τ‖*D) := by ring
  have h0 : Summable (fun n=>g n x) :=
    (trace_mercator_hasSum τ ((hfn x hx).trans_lt hr1)).summable
  have hder := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hr0 hr1).mul_right (‖τ‖*D)) hs hsp hg hgn hx h0 hx
  have hsD := (hasSum_geom_series_inverse (f x) ((hfn x hx).trans_lt hr1)).mul_right (d x)
  have hsd : HasSum (fun n=>g' n x) (-τ ((1-f x)⁻¹ʳ*d x)) := by
    simpa [g'] using (τ.hasSum hsD).neg
  rw [hsd.tsum_eq] at hder
  apply hder.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with t ht
  exact (trace_mercator_hasSum τ ((hfn t ht).trans_lt hr1)).tsum_eq.symm
end BrownLog
end

end OAI
