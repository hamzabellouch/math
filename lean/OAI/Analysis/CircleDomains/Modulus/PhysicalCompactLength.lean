import OAI.Analysis.CircleDomains.Probability.DyadicPhysicalOccupation
import OAI.Analysis.CircleDomains.Selection.DyadicPartition

namespace OAI

/-! Finite dyadic domain length controls every compact physical subinterval.
In particular it implies the local rectifiability required by the manuscript. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem timeClip_mapsTo_of_inter {a b c d : PathTime}
    (hi : (Icc a b ∩ Icc c d).Nonempty) : MapsTo (timeClip a b) (Icc c d) (Icc c d) := by
  obtain ⟨p, hp, hpc⟩ := hi
  intro t ht
  change c ≤ max a (min b t) ∧ max a (min b t) ≤ d
  exact ⟨le_max_of_le_right (le_min (hpc.1.trans hp.2) ht.1),
    max_le (hp.1.trans hpc.2) ((min_le_right _ _).trans ht.2)⟩

theorem timeClip_eq_const_of_disjoint {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (hi : ¬ (Icc a b ∩ Icc c d).Nonempty) :
    (EqOn (timeClip a b) (fun _ => a) (Icc c d)) ∨
    (EqOn (timeClip a b) (fun _ => b) (Icc c d)) := by
  have hsep : b < c ∨ d < a := by
    rw [Icc_inter_Icc, nonempty_Icc] at hi
    by_contra h
    push Not at h
    exact hi (max_le (le_min hab h.2) (le_min h.1 hcd))
  rcases hsep with h | h
  · right
    intro t ht
    change max a (min b t) = b
    rw [min_eq_left (h.le.trans ht.1), max_eq_right hab]
  · left
    intro t ht
    change max a (min b t) = a
    exact max_eq_left ((min_le_right _ _).trans (ht.2.trans h.le))

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalSubpath_clip_agree (e : G ≃ₜ U) {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (hi : (Icc a b ∩ Icc c d).Nonempty) :
    EqOn (physicalSubpath e hab ⟨γ, h₁⟩)
      ((physicalSubpath e hcd ⟨γ, h₂⟩) ∘ timeClip a b) (Icc c d) := by
  intro t ht
  have hclip : timeClip a b t ∈ Icc a b := by
    rw [← range_timeClip hab]
    exact mem_range_self t
  have hfix := congrArg (fun f : C(PathTime, Y) => f t)
    (physicalSubpath_comp_clip e hab ⟨γ, h₁⟩)
  exact hfix.symm.trans (physicalSubpath_eq_on e hab hcd γ h₁ h₂ hclip
    (timeClip_mapsTo_of_inter hi ht))

theorem physicalSubpath_variation_le_cell (e : G ≃ₜ U) {a b : PathTime}
    (hab : a ≤ b) (γ : C(PathTime, X)) (hγ : γ ∈ pathsInsideOn U a b)
    (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (hgood : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩)
      (Icc (dyadicLeft n i) (dyadicRight n i)) ≤ physicalDyadicLength e y₀ n i γ := by
  by_cases hi : (Icc a b ∩ Icc (dyadicLeft n i) (dyadicRight n i)).Nonempty
  · have hg := hgood (by rwa [inter_comm])
    rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i γ hg,
      eVariationOn.congr (physicalSubpath_clip_agree e hab (dyadicLeft_le_right n i) γ hγ hg hi)]
    exact (eVariationOn.comp_le_of_monotoneOn _ (timeClip a b)
      ((monotone_timeClip a b).monotoneOn _) (timeClip_mapsTo_of_inter hi)).trans
      (eVariationOn.mono _ (subset_univ _))
  · have hf : ∀ t, physicalSubpath e hab ⟨γ, hγ⟩ t =
        physicalSubpath e hab ⟨γ, hγ⟩ (timeClip a b t) := by
      intro t
      exact (congrArg (fun f : C(PathTime, Y) => f t)
        (physicalSubpath_comp_clip e hab ⟨γ, hγ⟩)).symm
    have hc := timeClip_eq_const_of_disjoint hab (dyadicLeft_le_right n i) hi
    have hz : eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩)
        (Icc (dyadicLeft n i) (dyadicRight n i)) = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      rcases hc with hc | hc <;> intro s hs t ht <;> rw [hf s, hf t, hc hs, hc ht, edist_self]
    rw [hz]
    exact bot_le

theorem physicalSubpath_length_le_domain (e : G ≃ₜ U) (hU : IsOpen U)
    {a b : PathTime} (hab : a ≤ b) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a b) (y₀ : Y) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ ≤ physicalDomainLength e y₀ γ := by
  obtain ⟨n, hn⟩ := exists_dyadic_cells_inside (hU.preimage γ.continuous) hγ
  rw [← sum_dyadic_variations _ n]
  exact (Finset.sum_le_sum fun i _ => physicalSubpath_variation_le_cell e hab γ hγ y₀ n i
    (fun hi => hn i hi)).trans (le_iSup (fun n => physicalStageLength e y₀ n γ) n)

theorem physicalSubpath_rectifiable (e : G ≃ₜ U) (hU : IsOpen U)
    {a b : PathTime} (hab : a ≤ b) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a b) (y₀ : Y) (hfin : physicalDomainLength e y₀ γ < ∞) :
    BoundedVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ :=
  ne_of_lt ((physicalSubpath_length_le_domain e hU hab γ hγ y₀).trans_lt hfin)

end CircleDomainRigidity

end

end OAI
