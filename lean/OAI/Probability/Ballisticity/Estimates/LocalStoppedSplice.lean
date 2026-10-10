import Mathlib
import OAI.Probability.Ballisticity.Entropy.StoppedWindowEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma prod_dependent_map_const {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν]
    (ρ : Measure C) [IsFiniteMeasure ρ] (f : A → B → C)
    (hf : Measurable (fun p : A × B => f p.1 p.2))
    (h : ∀ a, ν.map (f a) = ρ) :
    (μ.prod ν).map (fun p => (p.1, f p.1 p.2)) = μ.prod ρ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (measurable_fst.prodMk hf) (hs.prod ht),
    Measure.prod_apply ((hs.prod ht).preimage (measurable_fst.prodMk hf)),
    Measure.prod_prod]
  have inner (a : A) : ν (Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t))) =
      s.indicator (fun _ => ρ t) a := by
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
      have he : Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t)) =
          f a ⁻¹' t := by ext b; simp [ha]
      have hfa : Measurable (f a) := hf.comp measurable_prodMk_left
      rw [he, ← Measure.map_apply hfa ht, h a]
    · have he : Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t)) = ∅ := by
        ext b; simp [ha]
      simp [he,ha]
  simp_rw [inner]
  rw [lintegral_indicator hs, lintegral_const]
  simp [mul_comm]

abbrev LocalUpperField {d : ℕ} (e : Direction d) := (ℕ × HorizontalSpace e) → Row d

noncomputable def localStoppedField {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (p : Environment d × LocalUpperField e) : LocalUpperField e :=
  fun q => if q.1 < σ p.1 - τ p.1 then
    p.1 (horizontalLift e (τ p.1 + q.1) q.2) else p.2 q

lemma localStoppedField_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτ : Measurable τ) (hσ : Measurable σ) :
    Measurable (localStoppedField e τ σ) := by
  apply Measurable.of_eval
  intro q
  apply Measurable.ite (measurableSet_lt measurable_const ((hσ.comp measurable_fst).sub
    (hτ.comp measurable_fst)))
  · have hx : Measurable (fun p : Environment d × LocalUpperField e =>
        horizontalLift e (τ p.1 + q.1) q.2) :=
      (measurable_of_countable (fun n : ℕ => horizontalLift e (n + q.1) q.2)).comp
        (hτ.comp measurable_fst)
    exact measurable_current_row.comp (measurable_fst.prodMk hx)
  · exact (measurable_pi_apply q).comp measurable_snd

lemma localStoppedField_full_graft {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω) (ω η : Environment d) :
    localStoppedField e τ σ (ω, upperField e (τ ω) η) =
      upperField e (τ ω)
        (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ ω η) := by
  funext q
  have hn : horizontalLift e (τ ω + q.1) q.2 ∈
      BelowHeight (realPosition (step e)) (σ ω) ↔ q.1 < σ ω - τ ω := by
    simp only [BelowHeight, Set.mem_ofPred_eq, signedHeight_projection, signedHeight_horizontalLift]
    have hle := hτσ ω
    norm_cast
    omega
  change (if q.1 < σ ω - τ ω then _ else _) =
    (if horizontalLift e (τ ω + q.1) q.2 ∈ BelowHeight (realPosition (step e)) (σ ω) then _ else _)
  simp only [hn, upperField]

theorem localStoppedField_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    (Q.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))).map
      (fun p => (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
        localStoppedField e τ σ p)) = stoppedWindowLaw e ν Q τ σ filler := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hτm := measurable_of_stop_events S τ hτ
  have hσm := measurable_of_stop_events S σ hσ
  have hf : Measurable (fun p : Environment d × Environment d => upperField e (τ p.1) p.2) :=
    (upperField_joint_measurable e).comp (measurable_snd.prodMk (hτm.comp measurable_fst))
  have hh := prod_dependent_map_const Q (environmentLaw ν)
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))
    (fun ω η => upperField e (τ ω) η) hf (fun ω => upperField_map e ν (τ ω))
  have hF : Measurable (fun p : Environment d × LocalUpperField e =>
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
        localStoppedField e τ σ p)) :=
    ((stoppedObservation_measurable S τ hτ filler).comp measurable_fst).prodMk
      (localStoppedField_measurable e τ σ hτm hσm)
  rw [← hh, Measure.map_map hF (measurable_fst.prodMk hf)]
  unfold stoppedWindowLaw
  congr 1
  funext p
  exact Prod.ext rfl (localStoppedField_full_graft e τ σ hτσ p.1 p.2)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

variable {H : Type*} [AddCommGroup H]

abbrev Offsets (H : Type*) := (ℕ × ℕ) → OnePoint H

structure Consistent (O : Offsets H) : Prop where
  self : ∀ a, O (a,a) = (0 : H)
  symm : ∀ (a b : ℕ) (z : H), O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)
  add : ∀ (a b c : ℕ) (z w : H), O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
    O (a,c) = ((z+w : H) : OnePoint H)

abbrev Data (H : Type*) [AddCommGroup H] := {O : Offsets H // Consistent O}

def related (O : Data H) (a b : ℕ) : Prop := ∃ z : H, O.1 (a,b) = (z : OnePoint H)

lemma related_self (O : Data H) (a : ℕ) : related O a a := ⟨0,O.2.self a⟩
lemma related_symm {O : Data H} {a b : ℕ} (h : related O a b) : related O b a := by
  obtain ⟨z,hz⟩ := h
  exact ⟨-z,O.2.symm a b z hz⟩
lemma related_trans {O : Data H} {a b c : ℕ}
    (hab : related O a b) (hbc : related O b c) : related O a c := by
  obtain ⟨z,hz⟩ := hab
  obtain ⟨w,hw⟩ := hbc
  exact ⟨z+w,O.2.add a b c z w hz hw⟩

noncomputable def representative (O : Data H) (a : ℕ) : ℕ :=
  @Nat.find (fun b => related O b a) (Classical.decPred _) ⟨a, related_self O a⟩

lemma representative_related (O : Data H) (a : ℕ) : related O (representative O a) a :=
  by
    classical
    exact Nat.find_spec (p := fun b => related O b a) ⟨a,related_self O a⟩

lemma representative_le {O : Data H} {a b : ℕ} (h : related O b a) :
    representative O a ≤ b := by
  classical
  exact Nat.find_min' (p := fun b => related O b a) ⟨a,related_self O a⟩ h

lemma representative_eq_iff (O : Data H) (a b : ℕ) :
    representative O a = representative O b ↔ related O a b := by
  constructor
  · intro h
    exact related_trans (related_symm (representative_related O a))
      (h ▸ representative_related O b)
  · intro hab
    exact le_antisymm (representative_le (related_trans (representative_related O b)
      (related_symm hab))) (representative_le (related_trans (representative_related O a) hab))

noncomputable def displacement (O : Data H) (a : ℕ) : H :=
  Classical.choose (representative_related O a)

lemma displacement_spec (O : Data H) (a : ℕ) :
    O.1 (representative O a,a) = (↑(displacement O a) : OnePoint H) :=
  Classical.choose_spec (representative_related O a)

lemma offset_eq (O : Data H) {a b : ℕ} {z : H}
    (h : O.1 (a,b) = (z : OnePoint H)) :
    displacement O b = displacement O a + z := by
  have hr := (representative_eq_iff O a b).mpr ⟨z,h⟩
  have hh := O.2.add (representative O a) a b (displacement O a) z (displacement_spec O a) h
  rw [hr, displacement_spec] at hh
  exact OnePoint.coe_injective hh

noncomputable def inputSite (O : Data H) (p : ℕ × ℕ × H) : ℕ × ℕ × H :=
  (representative O p.1,p.2.1,displacement O p.1+p.2.2)

lemma inputSite_eq_iff (O : Data H) (a b l l' : ℕ) (z z' : H) :
    inputSite O (a,l,z) = inputSite O (b,l',z') ↔
      l = l' ∧ O.1 (a,b) = ((z-z' : H) : OnePoint H) := by
  constructor
  · intro h
    have hr : representative O a = representative O b := congrArg Prod.fst h
    have hl : l = l' := congrArg (fun p : ℕ × ℕ × H => p.2.1) h
    have hx : displacement O a+z = displacement O b+z' :=
      congrArg (fun p : ℕ × ℕ × H => p.2.2) h
    obtain ⟨u,hu⟩ := (representative_eq_iff O a b).mp hr
    have hd := offset_eq O hu
    have hu' : u = z-z' := (eq_sub_iff_add_eq).mpr (by
      apply add_left_cancel (a := displacement O a)
      simpa only [hd,add_assoc] using hx.symm)
    exact ⟨hl,by simpa only [hu'] using hu⟩
  · rintro ⟨rfl,h⟩
    have hr := (representative_eq_iff O a b).mpr ⟨z-z',h⟩
    have hd := offset_eq O h
    dsimp only [inputSite]
    apply Prod.ext hr
    change (l,displacement O a+z) = (l,displacement O b+z')
    congr 1
    rw [hd]
    abel

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [BorelSpace (OnePoint H)] in
lemma measurable_offset (a b : ℕ) : Measurable (fun O : Data H => O.1 (a,b)) :=
  (measurable_pi_apply (a,b)).comp measurable_subtype_coe

omit [MeasurableSpace H] [BorelSpace H] in
lemma measurable_related (a b : ℕ) : MeasurableSet {O : Data H | related O a b} := by
  simp only [related,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => (measurable_offset a b) (measurableSet_singleton _)

omit [MeasurableSpace H] [BorelSpace H] in
lemma measurable_representative (a : ℕ) : Measurable (fun O : Data H => representative O a) := by
  classical
  exact measurable_find (p := fun O b => related O b a) (fun O => ⟨a,related_self O a⟩) (fun b => measurable_related b a)

omit [BorelSpace H] in
lemma measurable_displacement (a : ℕ) : Measurable (fun O : Data H => displacement O a) := by
  apply measurable_to_countable'
  intro z
  have hm : Measurable (fun O : Data H => O.1 (representative O a,a)) := by
    have h : Measurable (fun p : Data H × ℕ => p.1.1 (p.2,a)) :=
      measurable_from_prod_countable_left fun b => measurable_offset b a
    exact h.comp (measurable_id.prodMk (measurable_representative a))
  have heq : {O : Data H | displacement O a = z} =
      {O | O.1 (representative O a,a) = (z : OnePoint H)} := by
    ext O
    simp only [Set.mem_ofPred_eq,displacement_spec,OnePoint.coe_eq_coe]
  change MeasurableSet {O : Data H | displacement O a = z}
  rw [heq]
  exact hm (measurableSet_singleton _)

lemma measurable_inputSite (p : ℕ × ℕ × H) : Measurable (fun O : Data H => inputSite O p) := by
  exact (measurable_representative p.1).prodMk
    (measurable_const.prodMk ((measurable_displacement p.1).add measurable_const))

variable {R : Type*} [MeasurableSpace R]

abbrev Site (H : Type*) := ℕ × ℕ × H
abbrev UpperField (H R : Type*) := (ℕ × H) → R
abbrev AllFields (H R : Type*) := Site H → R

noncomputable def fields (O : Data H) (ξ : AllFields H R) : AllFields H R :=
  fun p => ξ (inputSite O p)

lemma measurable_fields : Measurable (fun p : Data H × AllFields H R => fields p.1 p.2) := by
  apply Measurable.of_eval
  intro p
  have hm : Measurable (fun u : AllFields H R × Site H => u.1 u.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  exact hm.comp (measurable_snd.prodMk ((measurable_inputSite p).comp measurable_fst))

noncomputable def reference (ν : Measure R) [IsProbabilityMeasure ν] :
    Kernel (Data H) (AllFields H R) :=
  ((Kernel.id : Kernel (Data H) (Data H)).prod
    (Kernel.const (Data H) (Measure.infinitePi (fun _ : Site H => ν)))).map
    (fun p => fields p.1 p.2)

instance reference_markov (ν : Measure R) [IsProbabilityMeasure ν] : IsMarkovKernel (reference (H := H) ν) := by
  unfold reference
  exact Kernel.IsMarkovKernel.map _ measurable_fields

lemma reference_apply (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) :
    reference ν O = (Measure.infinitePi (fun _ : Site H => ν)).map (fields O) := by
  rw [reference,Kernel.map_apply _ measurable_fields,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map measurable_fields measurable_prodMk_left]
  rfl

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_injective_at_label (O : Data H) (a : ℕ) :
    Function.Injective (fun p : ℕ × H => inputSite O (a,p)) := by
  rintro ⟨l,z⟩ ⟨l',z'⟩ h
  have hh := (inputSite_eq_iff O a a l l' z z').mp h
  rw [O.2.self,OnePoint.coe_eq_coe] at hh
  exact Prod.ext hh.1 (sub_eq_zero.mp hh.2.symm)

lemma reference_single_field (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) (a : ℕ) :
    (reference ν O).map (fun φ => fun p : ℕ × H => φ (a,p)) =
      Measure.infinitePi (fun _ : ℕ × H => ν) := by
  have hm : Measurable (fields O : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,Measure.map_map (by fun_prop) hm]
  exact Measure.map_infinitePi_infinitePi_of_inj (inputSite_injective_at_label O a)

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_injective_distinct_classes {I : Type*} (O : Data H) (a : I → ℕ)
    (ha : ∀ i j, i ≠ j → ¬ related O (a i) (a j)) :
    Function.Injective (fun p : I × (ℕ × H) => inputSite O (a p.1,p.2)) := by
  rintro ⟨i,l,z⟩ ⟨j,l',z'⟩ h
  have hh := (inputSite_eq_iff O (a i) (a j) l l' z z').mp h
  have hij : i = j := by
    by_contra he
    exact ha i j he ⟨z-z',hh.2⟩
  subst j
  exact Prod.ext rfl (inputSite_injective_at_label O (a i) h)

lemma reference_distinct_classes {I : Type*} (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (a : I → ℕ) (ha : ∀ i j, i ≠ j → ¬ related O (a i) (a j)) :
    (reference ν O).map (fun φ => fun p : I × (ℕ × H) => φ (a p.1,p.2)) =
      Measure.infinitePi (fun _ : I × (ℕ × H) => ν) := by
  have hm : Measurable (fields O : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,Measure.map_map (by fun_prop) hm]
  exact Measure.map_infinitePi_infinitePi_of_inj (inputSite_injective_distinct_classes O a ha)

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
