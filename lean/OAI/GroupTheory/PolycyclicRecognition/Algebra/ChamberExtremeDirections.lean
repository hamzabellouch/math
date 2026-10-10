import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChamberBase

namespace OAI

/-! # Extreme directions span a full-dimensional weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def chamberExtremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | w ≠ 0 ∧ IsExtreme ℝ (closedWeightChamber α σ) (nonnegativeRay w)}

theorem extremePoint_base_extreme_ray (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ (chamberBase α σ).extremePoints ℝ) :
    x ∈ chamberExtremeDirections α σ := by
  have hxbase := extremePoints_subset hx
  have hx0 : x ≠ 0 := by
    intro h
    simpa only [h, map_zero, zero_ne_one] using hxbase.2
  refine ⟨hx0, ⟨?_, ?_⟩⟩
  · rintro _ ⟨r, hr, rfl⟩ i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hr (hxbase.1 i)
  · intro u hu v hv z hz hseg
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
    by_cases hu0 : u = 0
    · exact ⟨0, le_rfl, by simp [hu0]⟩
    by_cases hv0 : v = 0
    · have hau : a • u = r • x := by simpa only [hv0, smul_zero, add_zero] using he
      refine ⟨a⁻¹ * r, mul_nonneg (inv_nonneg.mpr ha.le) hr, ?_⟩
      calc
        u = a⁻¹ • (a • u) := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
        _ = (a⁻¹ * r) • x := by rw [hau, smul_smul]
    have hpu := chamberFunctional_pos α σ hsep hu hu0
    have hpv := chamberFunctional_pos α σ hsep hv hv0
    have hsum : a * chamberFunctional α σ u + b * chamberFunctional α σ v = r := by
      have hh := congrArg (chamberFunctional α σ) he
      simpa only [map_add, map_smul, smul_eq_mul, hxbase.2, mul_one] using hh
    have hrpos : 0 < r := by
      rw [← hsum]
      exact add_pos (mul_pos ha hpu) (mul_pos hb hpv)
    have hnormseg : x ∈ openSegment ℝ
        ((chamberFunctional α σ u)⁻¹ • u) ((chamberFunctional α σ v)⁻¹ • v) := by
      refine ⟨a * chamberFunctional α σ u / r, b * chamberFunctional α σ v / r,
        div_pos (mul_pos ha hpu) hrpos, div_pos (mul_pos hb hpv) hrpos, ?_, ?_⟩
      · rw [← add_div, hsum, div_self hrpos.ne']
      · have hau : (a * chamberFunctional α σ u / r) * (chamberFunctional α σ u)⁻¹ =
            r⁻¹ * a := by field_simp
        have hbv : (b * chamberFunctional α σ v / r) * (chamberFunctional α σ v)⁻¹ =
            r⁻¹ * b := by field_simp
        rw [smul_smul, smul_smul, hau, hbv, ← smul_smul, ← smul_smul,
          ← smul_add, he, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    have hueq : (chamberFunctional α σ u)⁻¹ • u = x :=
      hx.2 (normalize_mem_chamberBase α σ hsep hu hu0)
        (normalize_mem_chamberBase α σ hsep hv hv0) hnormseg
    refine ⟨chamberFunctional α σ u, hpu.le, ?_⟩
    calc
      u = chamberFunctional α σ u • ((chamberFunctional α σ u)⁻¹ • u) := by
        rw [smul_smul, mul_inv_cancel₀ hpu.ne', one_smul]
      _ = chamberFunctional α σ u • x := by rw [hueq]

variable [FiniteDimensional ℝ W]

theorem chamberBase_subset_span_extremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    chamberBase α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) := by
  rw [← closure_convexHull_extremePoints (isCompact_chamberBase α σ hsep)
    (convex_chamberBase α σ)]
  apply closure_minimal
  · apply convexHull_min
    · exact fun _ hx => Submodule.subset_span (extremePoint_base_extreme_ray α σ hsep hx)
    · exact Submodule.convex _
  · exact Submodule.closed_of_finiteDimensional _

theorem closedChamber_subset_span_extremeDirections (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    closedWeightChamber α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) := by
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact Submodule.zero_mem _
  have hn := chamberBase_subset_span_extremeDirections α σ hsep
    (normalize_mem_chamberBase α σ hsep hx hx0)
  have hp := chamberFunctional_pos α σ hsep hx hx0
  have hh := Submodule.smul_mem (Submodule.span ℝ (chamberExtremeDirections α σ))
    (chamberFunctional α σ x) hn
  rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul] at hh
  exact hh

theorem span_chamberExtremeDirections_eq_top (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    (hne : (weightChamber α σ).Nonempty) :
    Submodule.span ℝ (chamberExtremeDirections α σ) = ⊤ := by
  have hopen : IsOpen (weightChamber α σ) := by
    change IsOpen {w | ∀ i, 0 < orientedWeight α σ i w}
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun i =>
      isOpen_lt continuous_const (orientedWeight α σ i).continuous)
  have hsub : weightChamber α σ ⊆ Submodule.span ℝ (chamberExtremeDirections α σ) :=
    fun _ hx => closedChamber_subset_span_extremeDirections α σ hsep (fun i => (hx i).le)
  apply Submodule.eq_top_of_nonempty_interior'
  exact hne.mono (hopen.subset_interior_iff.mpr hsub)

end PolycyclicRecognition

end

end OAI
