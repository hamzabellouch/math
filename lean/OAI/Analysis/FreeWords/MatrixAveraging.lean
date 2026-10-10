import Mathlib

namespace OAI

noncomputable section

namespace KKMatrixAveraging

noncomputable section

open MeasureTheory TopologicalSpace

open scoped Topology

theorem finite_dimensional_commutant_approximation
    {B A : Type*} [CStarAlgebra B] [FiniteDimensional ℂ B] [CStarAlgebra A]
    (ρ : B →⋆ₐ[ℂ] A) (h : A) (δ : ℝ)
    (hδ : ∀ u : unitary B, ‖h * ρ u.val - ρ u.val * h‖ ≤ δ) :
    ∃ h₀ : A, (∀ b : B, Commute h₀ (ρ b)) ∧ ‖h-h₀‖ ≤ δ := by
  classical
  have hδ0 : 0 ≤ δ := by simpa using hδ 1
  rcases subsingleton_or_nontrivial B with hB|hB
  · let := hB
    refine ⟨h,?_,by simpa using hδ0⟩
    intro b
    rw [Subsingleton.elim b 0,map_zero]
    exact Commute.zero_right h
  let := hB
  let : CompactSpace (unitary B) := by
    apply isCompact_iff_compactSpace.mp
    apply (isCompact_closedBall (0:B) 1).of_isClosed_subset isClosed_unitary
    intro b hb
    simp [Metric.mem_closedBall,dist_zero_right,CStarRing.norm_coe_unitary (⟨b,hb⟩:unitary B)]
  let : MeasurableSpace (unitary B) := borel (unitary B)
  let : BorelSpace (unitary B) := ⟨rfl⟩
  let K : PositiveCompacts (unitary B) := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let μ : Measure (unitary B) := Measure.haarMeasure K
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  let U (u:unitary B) : unitary A := ⟨ρ u.val,by
    constructor
    · rw [← map_star,← map_mul,u.property.1,map_one]
    · rw [← map_star,← map_mul,u.property.2,map_one]⟩
  let f (u:unitary B) : A := ρ u.val*h*star (ρ u.val)
  have hρ : Continuous ρ := ρ.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  let h₀ : A := ∫ u, f u ∂μ
  have hfix (u:unitary B) : ρ u.val*h₀*star (ρ u.val)=h₀ := by
    have hfi' : Integrable (fun v => ρ u.val*f v) μ :=
      (by fun_prop : Continuous (fun v => ρ u.val*f v)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change ρ u.val*(∫v,f v ∂μ)*star (ρ u.val)=∫v,f v ∂μ
    rw [← integral_const_mul_of_integrable hfi,← integral_mul_const_of_integrable hfi']
    convert integral_mul_left_eq_self (μ:=μ) f u using 1
    congr 1
    funext v
    simp only [f,Submonoid.coe_mul,map_mul,star_mul]
    simp only [mul_assoc]
  have hcomm (u:unitary B) : Commute h₀ (ρ u.val) := by
    have hh := congrArg (fun x:A => x*ρ u.val) (hfix u)
    have hu : star (ρ u.val)*ρ u.val=1 := (U u).property.1
    change h₀*ρ u.val=ρ u.val*h₀
    simpa only [mul_assoc,hu,mul_one] using hh.symm
  refine ⟨h₀,?_,?_⟩
  · intro b
    have hb : b∈Submodule.span ℂ (unitary B:Set B) := by rw [CStarAlgebra.span_unitary]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb => exact hcomm ⟨b,hb⟩
    | zero => rw [map_zero]; exact Commute.zero_right _
    | add x y hx hy ihx ihy => rw [map_add]; exact ihx.add_right ihy
    | smul c x hx ih => rw [map_smul]; exact ih.smul_right c
  · have hn (u:unitary B) : ‖h-f u‖≤δ := by
      have hu : ρ u.val*star (ρ u.val)=1 := (U u).property.2
      have he : h-f u=(h*ρ u.val-ρ u.val*h)*star (ρ u.val) := by
        dsimp only [f]
        rw [sub_mul,mul_assoc h,hu,mul_one]
      rw [he]
      change ‖(h*ρ u.val-ρ u.val*h)*((star (U u)).val)‖≤δ
      rw [CStarRing.norm_mul_coe_unitary]
      exact hδ u
    have he : h-h₀=∫u,h-f u ∂μ := by
      rw [integral_sub (integrable_const h) hfi,integral_const]
      simp [h₀]
    rw [he]
    simpa using norm_integral_le_of_norm_le_const (μ:=μ) (Filter.Eventually.of_forall hn)

end

end KKMatrixAveraging
end

end OAI
