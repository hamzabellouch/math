import Mathlib
import OAI.Probability.Ballisticity.Estimates.ObservedPotential

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def pairOrigin {d : ℕ} (P : Path d × Path d) : Lattice d × Lattice d := (P.1 0,P.2 0)

lemma measurable_pairOrigin {d : ℕ} : Measurable (pairOrigin (d := d)) := by
  unfold pairOrigin
  fun_prop

lemma pairOrigin_selectedBoundarySuffix {d : ℕ} (ℓ : Vector d)
    (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    pairOrigin (selectedBoundarySuffix ℓ B P) = (selectedBoundaryData ℓ B P).endpoints := by
  rw [selectedBoundaryData_endpoints]
  simp [pairOrigin,selectedBoundarySuffix,commonPairSuffix]

lemma pairOrigin_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y, pairOrigin P=(x,y) := by
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with P hP
  exact Prod.ext hP.1.1.1 hP.2.1.1

lemma selectedBoundaryData_height {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    selectedBoundaryData ℓ (fun uv => H ≤ dot (realPosition uv.1) ℓ) = boundaryData ℓ H := rfl

noncomputable def commonCutObserver {d : ℕ} (ℓ : Vector d)
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop)
    (P : Path d × Path d) : Path d × Path d :=
  if active (pairOrigin P) then selectedBoundarySuffix ℓ (B (pairOrigin P)) P else P

lemma measurable_commonCutObserver {d : ℕ} (ℓ : Vector d)
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop) :
    Measurable (commonCutObserver ℓ active B) := by
  have hm : Measurable (fun Z : (Path d × Path d) × (Lattice d × Lattice d) =>
      if active Z.2 then selectedBoundarySuffix ℓ (B Z.2) Z.1 else Z.1) := by
    apply measurable_from_prod_countable_left
    intro i
    by_cases hi : active i
    · simpa only [ite_eq_left hi] using measurable_selectedBoundarySuffix ℓ (B i)
    · simp only [ite_eq_right hi]
      exact measurable_id
  exact hm.comp (measurable_id.prodMk measurable_pairOrigin)

theorem commonCutObserver_restart {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop)
    (K : Lattice d × Lattice d → ℕ)
    (hK : ∀ i, signedHeight e i.1=signedHeight e i.2 → active i → 0<K i)
    (hB : ∀ i, active i → ∀ z w, signedHeight e i.1+K i ≤ signedHeight e z → B i (z,w))
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2)
    (g : Path d × Path d → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ P, g (commonCutObserver (realPosition (step e)) active B P)
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) =
    ∫⁻ P, (∫⁻ Q, g Q ∂sharedConditionedPairLaw ν (realPosition (step e))
      (pairOrigin (commonCutObserver (realPosition (step e)) active B P)).1
      (pairOrigin (commonCutObserver (realPosition (step e)) active B P)).2)
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2 := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ i.1 i.2
  have ho := pairOrigin_ae ν ℓ htrans i.1 i.2
  have : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ i.1 i.2
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans i.1 i.2))
  by_cases ha : active i
  · have hc : (commonCutObserver ℓ active B) =ᵐ[μ] selectedBoundarySuffix ℓ (B i) := by
      filter_upwards [ho] with P hP
      simp only [commonCutObserver,hP,ite_eq_left ha]
    calc
      _ = ∫⁻ P, g (selectedBoundarySuffix ℓ (B i) P) ∂μ := lintegral_congr_ae (hc.fun_comp g)
      _ = ∫⁻ P, (∫⁻ Q, g Q ∂sharedConditionedPairLaw ν ℓ
            (selectedBoundaryData ℓ (B i) P).endpoints.1
            (selectedBoundaryData ℓ (B i) P).endpoints.2) ∂μ :=
        shared_selected_jointPast_restart ν hue ℓ (signed_direction_unit e) htrans
          (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) i.1 i.2 hi
          (K i) (hK i hi ha) (B i) (hB i ha) (fun _ => g) (fun _ => hg)
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [hc] with P hP
        rw [hP,pairOrigin_selectedBoundarySuffix]
  · have hc : (commonCutObserver ℓ active B) =ᵐ[μ] id := by
      filter_upwards [ho] with P hP
      simp only [commonCutObserver,hP,ite_eq_right ha,id_eq]
    calc
      _ = ∫⁻ P, g P ∂μ := lintegral_congr_ae (hc.fun_comp g)
      _ = ∫⁻ P, (∫⁻ Q, g Q ∂μ) ∂μ := by simp
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [hc,ho] with P hP hO
        rw [hP,id_eq,hO]

lemma commonCutObserver_sameHeight {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop)
    (K : Lattice d × Lattice d → ℕ)
    (hK : ∀ i, signedHeight e i.1=signedHeight e i.2 → active i → 0<K i)
    (hB : ∀ i, active i → ∀ z w, signedHeight e i.1+K i ≤ signedHeight e z → B i (z,w))
    (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2,
      signedHeight e ((commonCutObserver (realPosition (step e)) active B P).1 0) =
      signedHeight e ((commonCutObserver (realPosition (step e)) active B P).2 0) := by
  let ℓ := realPosition (step e)
  have ho := pairOrigin_ae ν ℓ htrans i.1 i.2
  by_cases ha : active i
  · filter_upwards [ho,shared_selectedBoundaryTimes_spec ν hue ℓ (signed_direction_unit e)
      htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
      i.1 i.2 hi (K i) (hK i hi ha) (B i) (hB i ha)] with P hP hcut
    have he := hcut.2.2.1.2.2
    rw [signedHeight_projection,signedHeight_projection] at he
    simp only [commonCutObserver,hP,ite_eq_left ha,selectedBoundarySuffix,commonPairSuffix,
      Nat.add_zero]
    exact_mod_cast he
  · filter_upwards [ho] with P hP
    simp only [commonCutObserver,hP,ite_eq_right ha]
    exact (congrArg (fun j : Lattice d × Lattice d => signedHeight e j.1) hP).trans
      (hi.trans (congrArg (fun j : Lattice d × Lattice d => signedHeight e j.2) hP).symm)

end DirectionalTransience

end

end

end OAI
