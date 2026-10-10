import OAI.Geometry.PinnedDistances.BoundedRates

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace WeakPinned
open Bounded Global Variance Hierarchy NumberField

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))

/-- The bounded arithmetic regime is impossible as well. The embedding and
normalization are chosen from the actual global mass and finite graph laws. -/
theorem arithmetic_no_bounded (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j,0≤η j) (hηb : ∀ j,η j≤θ/2)
    (hG : ∀ j,PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j,I j → K j) (ht : ∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (C : ℝ) (hC : 0≤C) (hscale : ∀ j,overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+
      potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤C) : False := by
  let n := fun j => (Fintype.card (V j):ℝ)
  let T := fun j => n j^(1-c)
  let S := fun j => n j^γ
  let q := fun j => varianceCell (G j).fiberWeight (G j).targets (T j)
  let r := fun j => varianceCell ((G j).retainedWeight (S j)) ((G j).retainedSet (S j)) (T j)
  have hq (j D) : 0≤q j D := varianceCell_nonneg _ _ _ (G j).fiberWeight_nonneg D
  have hr (j D) : 0≤r j D := varianceCell_nonneg _ _ _ ((G j).retainedWeight_nonneg _) D
  have h2 (j) : 2≤Fintype.card (V j) := (hG j).card_ge
  have hn2 (j) : (2:ℝ)≤n j := by dsimp only [n]; exact_mod_cast h2 j
  have hn0 (j) : 0<n j := by linarith [hn2 j]
  have hpos (j) : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
  have hdom (j x y) := (hG j).uniform_domination hθ (hηb j) x y
  have hT (j) : 1≤T j := Real.one_le_rpow (by linarith [hn2 j]) (by linarith)
  have hS (j) : 1<S j := Real.one_lt_rpow (by linarith [hn2 j]) hγ
  have hSn (j) : S j≤n j := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith [hn2 j]) hγ1.le
  have hB (j e) : 2≤((G j).targets e).card := by
    have hh := (hS j).trans ((hG j).fiber e)
    exact_mod_cast hh
  have hR (j y) : 2≤((G j).retainedSet (S j) y).card := by
    have hh := (hS j).trans_le ((G j).retainedSet_size (S j) (hSn j) y)
    exact_mod_cast hh
  have hvar := sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let W := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  have hW (j) : 0≤W j := add_nonneg (overlapScale_nonneg _ _ _ _) (potentialScale_nonneg _ _ _ _)
  have hf0 (j) : 0≤fiberVariance G c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ D) (hq j D))
  have hr0 (j) : 0≤ incomingVariance G γ c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ D) (hr j D))
  have hft := bounded_denominator_rate _ W C hf0 hW hscale hvar.1
  have hrt := bounded_denominator_rate _ W C hr0 hW hscale hvar.2
  obtain ⟨v,hv,hvf,hvr⟩ := bounded_place_selection Z₁ Z₂ h₁ h₂ h2 q r hq hr C hC hscale hft hrt
  let z₁ := fun j x => (v j).embedding (Z₁ j x)
  let z₂ := fun j x => (v j).embedding (Z₂ j x)
  have hz₁ (j) : Function.Injective (z₁ j) := (v j).embedding.injective.comp (h₁ j)
  have hz₂ (j) : Function.Injective (z₂ j) := (v j).embedding.injective.comp (h₂ j)
  let u₁ := fun j => logNormalize (z₁ j)
  let u₂ := fun j => logNormalize (z₂ j)
  let D : ℝ := 4*(2*C+1)+8
  have hD : 0≤D := by dsimp [D]; positivity
  have hlog₁ (j) : logAverage (u₁ j)≤D := by
    rw [logNormalize_bound _ (hz₁ j) (h2 j)]
    exact (arch_log_center_bound (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) (h2 j) (v j)).trans (by dsimp [D]; linarith [hv j])
  have hlog₂ (j) : logAverage (u₂ j)≤D := by
    rw [logNormalize_bound _ (hz₂ j) (h2 j)]
    have hh := arch_log_center_bound (Z₂ j) (Z₁ j) (h₂ j) (h₁ j) (h2 j) (v j)
    rw [archMean_scale_swap] at hh
    exact hh.trans (by dsimp [D]; linarith [hv j])
  choose x₁ hx₁ using (fun j => log_center (u₁ j) D (h2 j) (hlog₁ j))
  choose x₂ hx₂ using (fun j => log_center (u₂ j) D (h2 j) (hlog₂ j))
  have hsmall := power_fraction_rate n hn0 hn c hc
  let m₁ := fun j => pairMean (rawDepth (z₁ j))
  let m₂ := fun j => pairMean (rawDepth (z₂ j))
  have hd₁ := sphere_arch_test_rate Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j => (G j).fiberWeight) (fun j => (G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).fiberWeight_nonneg) (fun j => (G j).sum_fiberWeight (hpos j) |>.le) hB
    (fun j => (G j).fiber_domination _ (hdom j) (h2 j)) hvf hsmall
  have hvf₂ : Tendsto (fun j => archMean (Z₂ j) (Z₁ j) (massEval (q j)) (v j)) atTop (𝓝 0) := by
    simpa only [archMean_mass_swap] using hvf
  have hd₂ := sphere_arch_test_rate Z₂ Z₁ h₂ h₁ v m₂ (fun j => -u₂ j (x₂ j))
    (fun j => (G j).fiberWeight) (fun j => (G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).fiberWeight_nonneg) (fun j => (G j).sum_fiberWeight (hpos j) |>.le) hB
    (fun j => (G j).fiber_domination _ (hdom j) (h2 j)) hvf₂ hsmall
  have hdR := sphere_arch_test_rate Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j => (G j).retainedWeight (S j)) (fun j => (G j).retainedSet (S j)) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).retainedWeight_nonneg _) (fun j => (G j).sum_retainedWeight _ (hpos j)) hR
    (fun j => (G j).retained_domination _ _ (hdom j) (h2 j)) hvr hsmall
  apply normalized_graph_impossible G u₁ u₂ x₁ x₂
    (fun j => logNormalize_injective _ (hz₁ j)) (fun j => logNormalize_injective _ (hz₂ j))
    hpos (fun j e => Finset.card_pos.mp (by have := hB j e; omega)) h2 hn D hD hlog₁ hlog₂ hx₁ hx₂
    (by simpa only [sub_eq_add_neg,u₁,logNormalize,z₁,m₁] using hd₁)
    (by simpa only [sub_eq_add_neg,u₂,logNormalize,z₂,m₂] using hd₂)
    S (fun j => Real.rpow_pos_of_pos (hn0 j) γ)
    (by simpa only [sub_eq_add_neg,u₁,logNormalize,z₁,m₁] using hdR)
    (omitted_rate G θ γ c η hθ hγ1 hηb hn hG) (2/θ) (by positivity) hdom
  intro j e y z hy hz
  have he := (ht j e y hy).trans (ht j e z hz).symm
  have hem := congrArg (v j).embedding he
  simp only [map_mul,map_sub] at hem
  dsimp only [u₁,u₂,logNormalize,z₁,z₂]
  linear_combination (Real.exp (pairMean (rawDepth (z₁ j))):ℂ)*
    (Real.exp (pairMean (rawDepth (z₂ j))):ℂ)*hem

end WeakPinned

end
end

end OAI
