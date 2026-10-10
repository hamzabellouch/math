import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.ProductMeasure.FreshRegionLaw
import OAI.Probability.CriticalPercolation.Gluing.CollarErrorBudget
import OAI.Probability.CriticalPercolation.Gluing.SourceCollarTransfer

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fresh_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (m R : ℕ) (hcR : m<R) (Dstar : Set E)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (hregion : G.inducedEdges (G.vertexCollar Input R)⊆Dstar)
    (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ e∈Dstar, q (Sum.inl e)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hη₀ : 0≤η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
        ((forceOn Dstarᶜ ∅) ⁻¹' G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤ κ := by
  by_cases hI : Input.Nonempty
  · let p₀ : unitInterval := ⟨(pc : ℝ)/2,by constructor <;> linarith [pc.2.1,pc.2.2]⟩
    let J : Finset ℤ := Finset.Icc ((m : ℤ)+1) (R : ℤ)
    have hJ : J.Nonempty := Finset.nonempty_Icc.mpr (by omega)
    have hJcard : (J.card : ℝ)=(R : ℝ)-m := by
      have hjc : J.card=R-m := by
        change (Finset.Icc ((m : ℤ)+1) (R : ℤ)).card=R-m
        rw [Int.card_Icc]
        omega
      rw [hjc,Nat.cast_sub hcR.le]
    have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by linarith))
    have hs : 0<((pc : ℝ)/2)^(m+1+VM) := positive_trial_power _ hpc₀ _ _
    have hh := G.source_distance_collar_transfer hc hl A Input T hA q hI m R J hJ
      (by intro j hj; have hh := Finset.mem_Icc.mp hj; omega) houtside p₀ pc hpc
      (by
        intro e he
        rw [hq e (hregion he)]
        exact ⟨hpp,hppc⟩)
      D k M ⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ VM hD hM hk hMbound hVM
      (Real.log (4/κ)) η (κ/4) hK hη₀ (by linarith)
      (trial_ceiling_budget _ _ hs)
      (by
        intro y hy
        exact (hmean y hy).trans (fresh_region_lower (fun e => q (Sum.inl e))
          (fun _ => p') Dstar hq _ (G.measurableSet_seedHitEvent _ _)
          (G.seedHitEvent_upper _ _)))
    rw [hJcard] at hh
    exact hh.trans (collar_error_budget κ η ((R : ℝ)-m) _ hκ hκ1 hη
      (pow_pos (by linarith) _) hR)
  · have he : Input=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    subst Input
    have he : (G.withSource A).hitEvent none (some '' (∅ : Set V))=∅ := by
      ext ω
      simp [hitEvent]
    rw [he,Set.empty_sdiff,measureReal_empty]
    exact hκ.le

end CriticalPercolation.BondGraph
end
end
end

end OAI
