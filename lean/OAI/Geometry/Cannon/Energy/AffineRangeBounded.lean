import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergySumFilter

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology
open Set Metric Filter Topology

namespace CannonApprox

open Set Metric Filter Topology CannonCrossEnergy

lemma affine_range_bounded {X : Type*} (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) :
    BddAbove (range (fun x => (F x-c)/σ)) ∧ BddBelow (range (fun x => (F x-c)/σ)) := by
  obtain ⟨A,hA⟩ := hhi
  obtain ⟨B,hB⟩ := hlo
  constructor
  · refine ⟨(A-c)/σ,?_⟩
    rintro _ ⟨x,rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hA (mem_range_self x)) c) hσ.le
  · refine ⟨(B-c)/σ,?_⟩
    rintro _ ⟨x,rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hB (mem_range_self x)) c) hσ.le

lemma oscillation_affine_le {X : Type*} (F : X → ℝ)
    (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) (A : Set X) (hA : A.Nonempty) :
    0 ≤ oscillation (fun x => (F x-c)/σ) A ∧
      oscillation (fun x => (F x-c)/σ) A ≤ oscillation F A/σ := by
  have hbounded := affine_range_bounded F hhi hlo c σ hσ
  refine ⟨(oscillation_mono_of_bounded _ hbounded.1 hbounded.2 hA Subset.rfl).1,?_⟩
  have hupper : sSup ((fun x => (F x-c)/σ) '' A) ≤ (sSup (F '' A)-c)/σ := by
    apply csSup_le (hA.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (le_csSup (hhi.mono (image_subset_range F A)) (mem_image_of_mem F hx)) c) hσ.le
  have hlower : (sInf (F '' A)-c)/σ ≤ sInf ((fun x => (F x-c)/σ) '' A) := by
    apply le_csInf (hA.image _)
    rintro _ ⟨x,hx,rfl⟩
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (csInf_le (hlo.mono (image_subset_range F A)) (mem_image_of_mem F hx)) c) hσ.le
  calc
    _ ≤ (sSup (F '' A)-c)/σ - (sInf (F '' A)-c)/σ := sub_le_sub hupper hlower
    _ = _ := by unfold CannonCrossEnergy.oscillation; ring

lemma meshEnergy_affine_le {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (hr : 0 ≤ r) (hJ : 0 ≤ J)
    (F : X → ℝ) (hhi : BddAbove (range F)) (hlo : BddBelow (range F))
    (c σ : ℝ) (hσ : 0 < σ) (K : Set X) :
    meshEnergy p r J (fun x => (F x-c)/σ) K ≤ (σ⁻¹)^2*meshEnergy p r J F K := by
  classical
  unfold meshEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := oscillation_affine_le F hhi hlo c σ hσ
    (closedBall (p i.val) (J*r)) (nonempty_closedBall.mpr (mul_nonneg hJ hr))
  calc
    _ ≤ (oscillation F (closedBall (p i.val) (J*r))/σ)^2 := pow_le_pow_left₀ hh.1 hh.2 2
    _ = _ := by ring

lemma meshEnergy_affine_tendsto {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (J : ℝ) (hJ : 0 ≤ J)
    (F : ℕ → X → ℝ) (hF : ∀ n, BddAbove (range (F n)) ∧ BddBelow (range (F n)))
    (c σ : ℝ) (hσ : 0 < σ) (K : Set X)
    (hE : Tendsto (fun n => meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0)) :
    Tendsto (fun n => meshEnergy (p n) (r n) J (fun x => (F n x-c)/σ) K) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => (σ⁻¹)^2*meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hE :
      Tendsto (fun n => (σ⁻¹)^2*meshEnergy (p n) (r n) J (F n) K) atTop (𝓝 ((σ⁻¹)^2*0)))
  exact squeeze_zero' (Eventually.of_forall (fun n => meshEnergy_nonneg _ _ _ _ _))
    (Eventually.of_forall (fun n => meshEnergy_affine_le (p n) (r n) J (hr n) hJ
      (F n) (hF n).1 (hF n).2 c σ hσ K)) ht

lemma uniformly_affine {X : Type*} (F : ℕ → X → ℝ) (f : X → ℝ) (K : Set X)
    (hf : TendstoUniformlyOn F f atTop K) (c σ : ℝ) (hσ : 0 < σ) :
    TendstoUniformlyOn (fun n x => (F n x-c)/σ) (fun x => (f x-c)/σ) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (ε*σ) (mul_pos hε hσ)] with n hn
  intro x hx
  have hdist : dist ((f x-c)/σ) ((F n x-c)/σ) = dist (f x) (F n x)/σ := by
    rw [Real.dist_eq,Real.dist_eq,show (f x-c)/σ-(F n x-c)/σ = (f x-F n x)/σ by ring,
      abs_div,abs_of_pos hσ]
  rw [hdist]
  exact (div_lt_iff₀ hσ).mpr (hn x hx)

end CannonApprox

end
end
end
end
end
end
end
end
end
end

end OAI
