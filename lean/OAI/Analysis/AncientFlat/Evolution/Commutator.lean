import OAI.Analysis.AncientFlat.Evolution.RowLinearity

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenOrder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_commutator_lipschitz (K : SchwartzMap V ℂ) (j : ℕ) (α β : ℝ) (hα : 0<α) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      ∀ (r q L : ℝ), 0<r → 0≤q → q≤r → 0≤L →
      ∀ (a₀ a₁ f : V →ᵇ ℂ),
      (∀ x y, ‖a₁ x-a₀ y‖≤L*(‖x-y‖+q)) →
      (∀ x y, ‖a₁ x-a₁ y‖≤L*‖x-y‖) → ∀ x y,
      ‖(a₁ x*value K A r f j x-value K A r (a₀*f) j x)-
        (a₁ y*value K A r f j y-value K A r (a₀*f) j y)‖ ≤
        (r⁻¹)^j*‖f‖*L*C*‖x-y‖ := by
  obtain ⟨N,hN,hNb⟩ := exists_norm_bound K j α β hα
  obtain ⟨B,hB,hBb⟩ := exists_weighted_norm_bound K j α β hα
  obtain ⟨D,hD,hDb⟩ := exists_weighted_norm_bound (SchwartzMap.fderivCLM ℝ V ℂ K) (j+1) α β hα
  refine ⟨N+3*D+4*B,by positivity,fun A hA hAr r q L hr hq hqr hL a₀ a₁ f hc hl x y => ?_⟩
  let g (y : V) : V →ᵇ ℂ := a₁ y • f-a₀*f
  have hg (w z u : V) : ‖g w u‖≤(L*‖f‖)*(‖z-u‖+(‖z-w‖+q)) := by
    have he : g w u=(a₁ w-a₀ u)*f u := by simp only [g,BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_smul,BoundedContinuousFunction.coe_mul,Pi.sub_apply,Pi.mul_apply,smul_eq_mul]; ring
    rw [he,norm_mul]
    have ht : ‖w-u‖≤‖z-u‖+‖z-w‖ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub w z u
      rw [norm_sub_rev w z] at hh
      linarith
    calc
      _ ≤ (L*(‖w-u‖+q))*‖f‖ := mul_le_mul (hc w u) (f.norm_coe_le_norm u) (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hL (norm_nonneg f)) (sub_nonneg.mpr ht)]
  have he (w z : V) : value K A r (g w) j z=a₁ w*value K A r f j z-value K A r (a₀*f) j z := by
    simpa only [smul_eq_mul] using value_smul_sub K j α β hα A hA hAr r hr f (a₀*f) (a₁ w) z
  have ha (w : V) : ‖value K A r (g w) j w‖≤(r⁻¹)^j*(L*‖f‖)*(2*r)*B := by
    have hb := hBb A hA hAr r hr (g w) w (L*‖f‖) q (by positivity) hq
      (by simpa only [sub_self,norm_zero,zero_add] using hg w w)
    exact hb.trans (by gcongr; linarith)
  by_cases hxy : ‖x-y‖≤r
  · have hd (z : V) (hz : z∈Metric.closedBall y ‖x-y‖) :
        ‖value (SchwartzMap.fderivCLM ℝ V ℂ K) A r (g y) (j+1) z‖≤
        (r⁻¹)^j*(L*‖f‖)*(3*D) := by
      have hz' : ‖z-y‖≤‖x-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
      have hb := hDb A hA hAr r hr (g y) z (L*‖f‖) (‖z-y‖+q) (by positivity) (by positivity) (hg y z)
      calc
        _ ≤ (r⁻¹)^(j+1)*(L*‖f‖)*(3*r)*D := hb.trans (by gcongr; linarith)
        _ = _ := by rw [pow_succ]; field_simp
    have hv : ‖value K A r (g y) j x-value K A r (g y) j y‖≤
        ((r⁻¹)^j*(L*‖f‖)*(3*D))*‖x-y‖ := by
      exact (convex_closedBall y ‖x-y‖ : Convex ℝ _).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ => (hasFDerivAt_value K A hA α β hα hAr r hr (g y) j z).hasFDerivWithinAt)
        hd (Metric.mem_closedBall_self (norm_nonneg _)) (by simpa only [Metric.mem_closedBall,dist_eq_norm] using (le_rfl : ‖x-y‖≤‖x-y‖))
    calc
      _ = ‖(a₁ x-a₁ y)*value K A r f j x+(value K A r (g y) j x-value K A r (g y) j y)‖ := by rw [he,he]; congr 1; ring
      _ ≤ ‖a₁ x-a₁ y‖*‖value K A r f j x‖+‖value K A r (g y) j x-value K A r (g y) j y‖ := by simpa only [norm_mul] using norm_add_le ((a₁ x-a₁ y)*value K A r f j x) _
      _ ≤ (L*‖x-y‖)*((r⁻¹)^j*(‖f‖*N)) + ((r⁻¹)^j*(L*‖f‖)*(3*D))*‖x-y‖ :=
        add_le_add (mul_le_mul (hl x y) (hNb A hA hAr r hr f x) (norm_nonneg _) (by positivity)) hv
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0≤(r⁻¹)^j*‖f‖*L*‖x-y‖) hB]
  · have hrxy : r≤‖x-y‖ := le_of_not_ge hxy
    rw [← he x x,← he y y]
    calc
      _ ≤ ‖value K A r (g x) j x‖+‖value K A r (g y) j y‖ := norm_sub_le ..
      _ ≤ (r⁻¹)^j*(L*‖f‖)*(2*r)*B+(r⁻¹)^j*(L*‖f‖)*(2*r)*B := add_le_add (ha x) (ha y)
      _ = (r⁻¹)^j*‖f‖*L*(4*B)*r := by ring
      _ ≤ (r⁻¹)^j*‖f‖*L*(N+3*D+4*B)*‖x-y‖ := by gcongr; linarith
end SourceFrozenOrder

end

end OAI
