import OAI.Probability.SATComputability.ClauseProcess
import OAI.Probability.SATComputability.PoissonMaskAggregation

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

abbrev SingleIncident (n : ℕ) := Fin 3 × SignedLiteral n × SignedLiteral n
abbrev BadIncident (n : ℕ) := (Fin 3 × SignedLiteral n) ⊕ Unit

def singleIncidentEquiv (n : ℕ) : SingleIncident n ≃ (Fin 2 → SignedLiteral n) × Fin 3 where
  toFun p := (![p.2.1,p.2.2],p.1)
  invFun p := (p.2,p.1 0,p.1 1)
  left_inv := by rintro ⟨i,a,b⟩; rfl
  right_inv := by
    rintro ⟨f,i⟩
    apply Prod.ext
    · funext j; fin_cases j <;> rfl
    · rfl

noncomputable def singleIncidentMask {n : ℕ} (p : SingleIncident n) :
    Finset (DeletionCandidate n) := clauseMask ![p.2.1,p.2.2]

theorem singleIncident_law {n : ℕ} [NeZero n] (r : ℝ≥0)
    (f : Finset (DeletionCandidate n) → ℝ) :
    (∫ c, f (countsMask singleIncidentMask c) ∂poissonCountLaw (SingleIncident n) r) =
      (candidateBlock (3*r*Fintype.card (Fin 2 → SignedLiteral n)) 2 Finset.univ).expect f := by
  have he : singleIncidentMask (n := n) =
      (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) ∘ singleIncidentEquiv n := rfl
  rw [he]
  simp_rw [countsMask_equiv]
  rw [show (∫ c, f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1)
      (c ∘ (singleIncidentEquiv n).symm)) ∂poissonCountLaw (SingleIncident n) r) =
      ∫ c, f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) c)
        ∂poissonCountLaw ((Fin 2 → SignedLiteral n) × Fin 3) r from by
      simpa only [Function.comp_def] using poissonCountLaw_equiv (singleIncidentEquiv n) r
        (fun c => f (countsMask (fun p : (Fin 2 → SignedLiteral n) × Fin 3 => clauseMask p.1) c)),
    poissonCountLaw_redundant_mask]
  rw [candidateBlock_counts]
  congr 2
  simp only [Fintype.card_fin, mul_div_cancel_right₀ _ (show
    (Fintype.card (Fin 2 → SignedLiteral n) : ℝ≥0) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero)]
  norm_num

theorem incident_killing_pointwise {n : ℕ} (U : Finset (DeletionCandidate n))
    (c : IncidentClass n → ℕ) :
    (if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0) ≤
      (if U ∩ countsMask singleIncidentMask (fun a => c (.inl a)) = ∅ then 1 else 0) +
      (∑ b : BadIncident n, c (.inr b) : ℕ) := by
  by_cases hz : ∑ b : BadIncident n, c (.inr b) = 0
  · have hb (b : BadIncident n) : c (.inr b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (c (.inr j)))).mp hz b
        (Finset.mem_univ b)
    have hm : countsMask incidentMask c =
        countsMask singleIncidentMask (fun a => c (.inl a)) := by
      ext x
      simp [countsMask, incidentMask, singleIncidentMask, Sum.forall, hb]
    rw [hm,hz,Nat.cast_zero,add_zero]
  · have hpos : (1 : ℝ) ≤ (∑ b : BadIncident n, c (.inr b) : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    split_ifs <;> linarith

theorem incident_killing_bound {n : ℕ} [NeZero n] (r : ℝ≥0)
    (U : Finset (DeletionCandidate n)) :
    (∫ c, if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0
      ∂poissonCountLaw (IncidentClass n) r) ≤
      poissonKillProbability U 2 (3*r*Fintype.card (Fin 2 → SignedLiteral n)) +
      Fintype.card (BadIncident n)*(r : ℝ) := by
  let μ := poissonCountLaw (IncidentClass n) r
  let g := fun c : IncidentClass n → ℕ =>
    if U ∩ countsMask singleIncidentMask (fun a => c (.inl a)) = ∅ then (1 : ℝ) else 0
  let b := fun c : IncidentClass n → ℕ => ((∑ a : BadIncident n, c (.inr a) : ℕ) : ℝ)
  have hg : Integrable g μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with c
    dsimp only [g]
    split_ifs <;> norm_num
  have hres : HasLaw (fun c : IncidentClass n → ℕ => fun a : BadIncident n => c (.inr a))
      (poissonCountLaw (BadIncident n) r) μ :=
    ⟨(measurable_of_countable _).aemeasurable,
      poissonCountLaw_embedding Sum.inr Sum.inr_injective r⟩
  have hsum := (poissonCountLaw_hasLaw_sum (fun _ : BadIncident n => r)).comp hres
  have hb : Integrable b μ :=
    hsum.integrable_comp (poisson_integrable_count _)
  have hi : Integrable (fun c : IncidentClass n → ℕ =>
      if U ∩ countsMask incidentMask c = ∅ then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with c
    split_ifs <;> norm_num
  have h := integral_mono hi (hg.add hb) (incident_killing_pointwise U)
  simp only [Pi.add_apply] at h
  rw [integral_add hg hb] at h
  have hbg : (∫ c, b c ∂μ) = Fintype.card (BadIncident n)*(r : ℝ) := by
    have he := hsum.integral_comp (f := fun k : ℕ => (k : ℝ))
      (measurable_of_countable _).aestronglyMeasurable
    rw [poisson_mean] at he
    simpa only [Function.comp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      NNReal.coe_mul, NNReal.coe_natCast] using he
  have hgg : (∫ c, g c ∂μ) =
      poissonKillProbability U 2 (3*r*Fintype.card (Fin 2 → SignedLiteral n)) := by
    have he := poissonCountLaw_embedding_integral (A := IncidentClass n) (B := SingleIncident n)
      Sum.inl Sum.inl_injective r
      (fun c => if U ∩ countsMask singleIncidentMask c = ∅ then (1 : ℝ) else 0)
    change (∫ c, g c ∂μ) = _ at he
    rw [he, singleIncident_law r (fun I => if U ∩ I = ∅ then (1 : ℝ) else 0)]
    rw [candidateBlock_mask _ _ U (fun V => if V = ∅ then (1 : ℝ) else 0), candidateBlock_kill]
  rwa [hbg,hgg] at h

end FixedClauseThreshold.Computability

end OAI
