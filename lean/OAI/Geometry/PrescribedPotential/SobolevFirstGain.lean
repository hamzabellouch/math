import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevReconstruction
import OAI.Geometry.PrescribedPotential.WeakDerivativeLocalization

namespace OAI

/-! Sobolev First Gain. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma completedLocalize_plus_one_embed (k : ℕ) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (f : Smooth A) :
    D.completedLocalize ((k : ℝ)+1) i ρ hρ (D.localizers.embed ((k : ℝ)+1) f) =
      schwartzCoord ((k : ℝ)+1) (localize A i ρ hρ f) := by
  obtain ⟨C,_,hC⟩ := D.localization_integer_bound i ρ hρ (k+1)
  rw [Nat.cast_add,Nat.cast_one] at hC
  exact LinearMap.extendOfNorm_eq (D.localizers.embed_dense ((k : ℝ)+1)) ⟨C,hC⟩ f

lemma completedLocalize_lower_one (k : ℕ) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source)
    (u : D.localizers.Sobolev ((k : ℝ)+1)) :
    realize (k : ℝ) (D.completedLocalize (k : ℝ) i ρ hρ
      (D.localizers.lower ((k : ℝ)+1) (k : ℝ) u)) =
      realize ((k : ℝ)+1) (D.completedLocalize ((k : ℝ)+1) i ρ hρ u) := by
  have he : (fun u : D.localizers.Sobolev ((k : ℝ)+1) => realize (k : ℝ)
      (D.completedLocalize (k : ℝ) i ρ hρ (D.localizers.lower ((k : ℝ)+1) (k : ℝ) u))) =
      (fun u => realize ((k : ℝ)+1) (D.completedLocalize ((k : ℝ)+1) i ρ hρ u)) := by
    apply (D.localizers.embed_dense ((k : ℝ)+1)).equalizer (by fun_prop) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    simp only [D.localizers.lower_embed (by linarith : (k : ℝ) ≤ (k : ℝ)+1),
      D.completedLocalize_embed,D.completedLocalize_plus_one_embed,realize_schwartzCoord]
  exact congr_fun he u

lemma local_mem_of_derivative_lifts (k : ℕ) (u : D.localizers.Sobolev ((k : ℝ)+1))
    (hD : ∀ (p : ι) (v : EC d), ∃ w : D.localizers.Sobolev ((k : ℝ)+1),
      D.localizers.lower ((k : ℝ)+1) (k : ℝ) w = D.completedDerivative k p v u)
    (p : ι) :
    MemSobolev ((k : ℝ)+2) 2 (D.localizers.distribution ((k : ℝ)+1) p u) := by
  have hu : MemSobolev ((k : ℝ)+1) 2 (D.localizers.distribution ((k : ℝ)+1) p u) :=
    realize_memSobolev _ _
  have hder (v : EC d) : MemSobolev ((k : ℝ)+1) 2
      (∂_{v} (D.localizers.distribution ((k : ℝ)+1) p u)) := by
    obtain ⟨w,hw⟩ := hD p v
    rw [D.distribution_derivative,D.completedLocalize_lower_one,← hw,
      D.localizers.distribution_lower (by linarith : (k : ℝ) ≤ (k : ℝ)+1)]
    exact (realize_memSobolev _ _).add (realize_memSobolev _ _)
  convert memSobolev_of_first_basis hu (fun j => hder (stdOrthonormalBasis ℝ (EC d) j)) using 1
  ring

 

theorem sobolev_first_gain (k : ℕ) (u : D.localizers.Sobolev ((k : ℝ)+1))
    (hD : ∀ (p : ι) (v : EC d), ∃ w : D.localizers.Sobolev ((k : ℝ)+1),
      D.localizers.lower ((k : ℝ)+1) (k : ℝ) w = D.completedDerivative k p v u) :
    ∃ w : D.localizers.Sobolev ((k+2 : ℕ) : ℝ),
      D.localizers.lower ((k+2 : ℕ) : ℝ) ((k : ℝ)+1) w = u := by
  have h0 : 0 ≤ (k : ℝ)+1 := by positivity
  have hh : ∀ p, MemSobolev ((k+2 : ℕ) : ℝ) 2
      (D.localizers.distribution 0 p (D.localizers.lower ((k : ℝ)+1) 0 u)) := by
    intro p
    rw [D.localizers.distribution_lower h0]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using D.local_mem_of_derivative_lifts k u hD p
  obtain ⟨w,hw⟩ := D.sobolev_of_local_order (k+2) (D.localizers.lower ((k : ℝ)+1) 0 u) hh
  refine ⟨w, (D.localizers.lower_injective h0) ?_⟩
  have hc := congrArg (fun L : D.localizers.Sobolev ((k+2 : ℕ) : ℝ) →L[ℝ]
      D.localizers.Sobolev 0 => L w)
    (D.localizers.lower_comp (by push_cast; linarith : (k : ℝ)+1 ≤ ((k+2 : ℕ) : ℝ)) h0)
  exact hc.trans hw

end GluingData
end GlobalElliptic

end
end

end OAI
