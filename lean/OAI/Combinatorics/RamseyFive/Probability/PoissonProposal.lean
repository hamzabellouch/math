import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.MeasurePreservingSplitSchedule
import OAI.Combinatorics.RamseyFive.Probability.SumPoissonPow
import OAI.Combinatorics.RamseyFive.Probability.PoissonLikelihood

namespace OAI

namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma schedule_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (R : ℕ) (E : Set (Fin R→ι→ℕ)) (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-D*K)*(scheduleMeasure trueRate R).real E≤(scheduleMeasure proposal R).real E := by
  have hh := batch_event_likelihood (fun p : Fin R×ι=>proposal p.2) (fun p : Fin R×ι=>trueRate p.2)
    (by simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];rw [htotal])
    hD (fun p=>hrate p.2) {ω | Function.curry ω∈E} (by
      intro ω hω
      simpa only [sampleCount,Fintype.sum_prod_type,Function.curry] using hsize (Function.curry ω) hω)
  have ht := (measurePreserving_uncurry_schedule trueRate R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  have hp := (measurePreserving_uncurry_schedule proposal R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  simpa only [Function.curry_uncurry] using (ht▸hp▸hh)

theorem uniform_schedule_likelihood (H : Finset ι) (hH : H.Nonempty)
    (rho : ℝ≥0) (R : ℕ) (K : ℝ) (E : Set (Fin R→ι→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-Real.log ((Fintype.card ι:ℝ)/H.card)*K)*
      (scheduleMeasure (fun i=>if i∈H then rho/(H.card:ℝ≥0) else 0) R).real E≤
      (scheduleMeasure (fun _ : ι=>rho/(Fintype.card ι:ℝ≥0)) R).real E := by
  have hH0 : (0:ℝ)<H.card := Nat.cast_pos.mpr hH.card_pos
  have hI0 : (0:ℝ)<Fintype.card ι := hH0.trans_le (Nat.cast_le.mpr H.card_le_univ)
  have hHI : (H.card:ℝ)≤Fintype.card ι := Nat.cast_le.mpr H.card_le_univ
  apply schedule_event_likelihood _ _ _ _ _ R E hsize
  · simp only [apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_mem,Finset.univ_inter]
    field_simp
  · apply Real.log_nonneg
    exact (one_le_div hH0).mpr hHI
  · intro i
    by_cases hi : i∈H
    · simp only [ite_eq_left hi,NNReal.coe_div,NNReal.coe_natCast]
      rw [Real.exp_neg,Real.exp_log (div_pos hI0 hH0)]
      field_simp
      rfl
    · simp only [ite_eq_right hi,NNReal.coe_zero,mul_zero]
      positivity

noncomputable def ambientSuccess (H : Finset ι) {R : ℕ} (E : Set (Fin R→H→ℕ)) : Set (Fin R→ι→ℕ) :=
  {ω | (∀r i,i∉H → ω r i=0) ∧ (fun r (i : H)=>ω r i)∈E}

lemma measurePreserving_restrict_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ=>fun r (i : H)=>ω r i)
      (scheduleMeasure (fun i=>if i∈H then rho else 0) R)
      (scheduleMeasure (fun _ : H=>rho) R) := by
  have h := measurePreserving_fst.comp
    (measurePreserving_split_schedule (fun i=>if i∈H then rho else 0) (fun i=>i∈H) R)
  convert h using 1 <;> try rfl
  congr 1
  · exact Subsingleton.elim _ _
  · funext i
    exact (ite_eq_left i.prop).symm

lemma ae_zero_outside_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    ∀ᵐω∂scheduleMeasure (fun i=>if i∈H then rho else 0) R,∀r i,i∉H → ω r i=0 := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈H
  · exact Filter.Eventually.of_forall fun _ h=>False.elim (h hi)
  · have h := (hasLaw_coordinate (fun i=>if i∈H then rho else 0) i).comp
      (measurePreserving_eval (fun _ : Fin R=>batchMeasure (fun i=>if i∈H then rho else 0)) r).hasLaw
    simp only [ite_eq_right hi,poisson_zero] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _=>hω

lemma ambientSuccess_true_mass (H : Finset ι) (rho : ℝ≥0) (R : ℕ)
    (E : Set (Fin R→H→ℕ)) :
    (scheduleMeasure (fun i=>if i∈H then rho else 0) R).real (ambientSuccess H E)=
      (scheduleMeasure (fun _ : H=>rho) R).real E := by
  have h := (measurePreserving_restrict_schedule H rho R).hasLaw.measureReal_eq
    (p:=fun ω=>ω∈E) (Set.to_countable _ |>.measurableSet)
  apply Eq.trans _ h
  apply measureReal_congr
  filter_upwards [ae_zero_outside_schedule H rho R] with ω hω
  change (((∀r i,i∉H → ω r i=0) ∧ (fun r (i : H)=>ω r i)∈E) = ((fun r (i : H)=>ω r i)∈E))
  exact propext ⟨And.right,fun hh=>⟨hω,hh⟩⟩

omit [DecidableEq ι] in
lemma sampleCount_restrict (H : Finset ι) {R : ℕ} (ω : Fin R→ι→ℕ)
    (hω : ∀r i,i∉H → ω r i=0) : sampleCount ω=sampleCount (fun r (i : H)=>ω r i) := by
  unfold sampleCount
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_coe_sort]
  apply (Finset.sum_subset (Finset.subset_univ H) (fun i _ hi=>hω r i hi)).symm

theorem uniform_hidden_event_likelihood (H : Finset ι) (hH : H.Nonempty)
    (rho : ℝ≥0) (R : ℕ) (K : ℝ) (E : Set (Fin R→H→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-Real.log ((Fintype.card ι:ℝ)/H.card)*K)*
      (scheduleMeasure (fun _ : H=>rho/(H.card:ℝ≥0)) R).real E≤
      (scheduleMeasure (fun _ : ι=>rho/(Fintype.card ι:ℝ≥0)) R).real (ambientSuccess H E) := by
  have hh := uniform_schedule_likelihood H hH rho R K (ambientSuccess H E) (by
    intro ω hω
    rw [sampleCount_restrict H ω hω.1]
    exact hsize _ hω.2)
  rwa [ambientSuccess_true_mass] at hh

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_set_rate (H : Finset ι) (hH : H.Nonempty) (rho : ℝ≥0) :
    (∑i,((if i∈H then rho/(H.card:ℝ≥0) else 0):ℝ≥0):ℝ)=rho := by
  have hH0 : (0:ℝ)<H.card := Nat.cast_pos.mpr hH.card_pos
  simp only [apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  field_simp

theorem enclosure_hidden_event_likelihood (S U : Finset ι) (hS : S.Nonempty)
    (hSU : S⊆U) (rho : ℝ≥0) (R : ℕ) (K : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*
      (scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hU : U.Nonempty := hS.mono hSU
  have hS0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hU0 : (0:ℝ)<U.card := Nat.cast_pos.mpr hU.card_pos
  have hSUc : (S.card:ℝ)≤U.card := Nat.cast_le.mpr (Finset.card_le_card hSU)
  have hr (i : ι) : Real.exp (-Real.log ((U.card:ℝ)/S.card))*
      ((if i∈S then rho/(S.card:ℝ≥0) else 0):ℝ≥0)≤
      ((if i∈U then rho/(U.card:ℝ≥0) else 0):ℝ≥0) := by
    by_cases hi : i∈S
    · simp only [ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [Real.exp_neg,Real.exp_log (div_pos hU0 hS0)]
      field_simp
      rfl
    · simp only [ite_eq_right hi,NNReal.coe_zero,mul_zero]
      positivity
  have hh := schedule_event_likelihood
    (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0)
    (fun i=>if i∈S then rho/(S.card:ℝ≥0) else 0)
    (by rw [sum_set_rate U hU rho,sum_set_rate S hS rho])
    (Real.log_nonneg ((one_le_div hS0).mpr hSUc)) hr R (ambientSuccess S E) (K:=K) (by
      intro ω hω
      rw [sampleCount_restrict S ω hω.1]
      exact hsize _ hω.2)
  rwa [ambientSuccess_true_mass] at hh

end SharpRamseyFive.PoissonScore

end OAI
