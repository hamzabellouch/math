import OAI.GroupTheory.PolycyclicRecognition.Finiteness.UnitaryReducedVanishing

namespace OAI

/-! # Reduced cocycle vanishing through the central quotient

The central moving summand is handled by central averaging. On the central
fixed summand, cocycle values at central elements are globally fixed and
therefore zero; the cocycle descends to the quotient by the center.
-/

noncomputable section

namespace PolycyclicRecognition

universe u v

open Set

variable {G : Type u} [Group G] [TopologicalSpace G]

theorem unitaryReducedVanishing_of_centerQuotient
    (ih : UnitaryReducedVanishing.{u, v} (G ⧸ Subgroup.center G)) :
    UnitaryReducedVanishing.{u, v} G := by
  intro E _ _ _ ρ hfix hρ b hbc hb Q hQ ε hε
  let K := unitaryCentralFixed ρ
  let ρF := centralFixedUnitary ρ
  let ρM := centralMovingUnitary ρ
  let bF := centralFixedProjection ρ ∘ b
  let bM := centralMovingProjection ρ ∘ b
  have hbF : IsUnitaryCocycle ρF bF := centralFixedCocycle ρ hb
  have hbM : IsUnitaryCocycle ρM bM := centralMovingCocycle ρ hb
  have hfixF : ∀ x : K, (∀ g, ρF g x = x) → x = 0 := centralFixedUnitary_no_fixed ρ hfix
  have hzF : ∀ z : Subgroup.center G, ρF z = 1 := centralFixedUnitary_center ρ
  have hbFz (z : Subgroup.center G) : bF z = 0 :=
    hfixF _ (hbF.central_value_fixed hzF z)
  let ρQ := centerQuotientUnitary ρF hzF
  let bQ := centerQuotientCocycle bF hbF hbFz
  have hfixQ : ∀ x : K, (∀ q, ρQ q x = x) → x = 0 := by
    intro x hx
    exact hfixF x (fun g => hx (QuotientGroup.mk g))
  have hρF := centralFixedUnitary_continuous ρ hρ
  have hbFc : Continuous bF := (centralFixedProjection ρ).continuous.comp hbc
  have hbMc : Continuous bM := (centralMovingProjection ρ).continuous.comp hbc
  obtain ⟨φF, hφF⟩ := ih K ρQ hfixQ
    (centerQuotientUnitary_continuous (ρ := ρF) (hz := hzF) hρF)
    bQ (centerQuotientCocycle_continuous bF hbF hbFz hbFc)
    (centerQuotientCocycle_isCocycle bF hbF hbFz)
    ((QuotientGroup.mk : G → G ⧸ Subgroup.center G) '' Q)
    (hQ.image QuotientGroup.continuous_mk) (ε / 2) (half_pos hε)
  obtain ⟨φM, hφM⟩ := hbM.small_correction_of_no_central_invariants
    (centralMovingUnitary_no_central_fixed ρ) hbMc Q hQ (half_pos hε)
  refine ⟨(φF : E) + (φM : E), fun q hq => ?_⟩
  have hfq : ‖bF q + ρF q φF - φF‖ ≤ ε / 2 :=
    hφF (QuotientGroup.mk q) ⟨q, hq, rfl⟩
  have hmq := hφM q hq
  have he : b q + ρ q ((φF : E) + (φM : E)) - ((φF : E) + (φM : E)) =
      ((bF q + ρF q φF - φF : K) : E) +
      ((bM q + ρM q φM - φM : Kᗮ) : E) := by
    change b q + ρ q ((φF : E) + (φM : E)) - ((φF : E) + (φM : E)) =
      ((centralFixedProjection ρ (b q) : E) + ρ q φF - φF) +
      ((centralMovingProjection ρ (b q) : E) + ρ q φM - φM)
    rw [map_add]
    conv_lhs => rw [← centralProjections_add ρ (b q)]
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hfq hmq).trans_eq (add_halves ε))

end PolycyclicRecognition

end

end OAI
