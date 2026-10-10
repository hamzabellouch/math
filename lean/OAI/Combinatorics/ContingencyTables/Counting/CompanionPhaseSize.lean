import OAI.Combinatorics.ContingencyTables.Counting.CompanionCodeBounds
import OAI.Combinatorics.ContingencyTables.Counting.CompanionStoredShape

namespace OAI

/-! # Phase query sizes do not depend on the heights of old multipliers -/
namespace ContingencyTables.CompanionPhaseSize
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionOuterPhaseProgram

lemma list_weight_bound {X : Type} [Codec X] (xs : List X) (B : ℕ)
    (hx : ∀ x∈xs,weight x ≤ B) : weight xs ≤ xs.length*(B+1)+1 := by
  have h := weight_map_bound (f := id) (as := xs) hx
  simpa only [List.map_id] using h

lemma initialInput_bound (z : Input) :
    weight (CompanionInitializedRestartProgram.initialInput (restartInput z)) ≤
      weight (z.1.1.1,z.2) := by
  have ht := weight_sublist (List.take_sublist
    (CompanionInitializedRestartProgram.initialWidth (restartInput z)) z.2)
  change weight (z.1.1.1,z.2.take _) ≤ weight (z.1.1.1,z.2)
  simp only [weight_prod]
  omega

lemma start_bound : ∃ p : Polynomial ℕ,∀ z : Input,
    weight (startCode z) ≤ p.eval (weight (z.1.1.1,z.2)) := by
  obtain ⟨p,hp⟩ := CompanionRestartInitializer.polynomial_output
  refine ⟨7*p+1,?_⟩
  intro z
  have hi := hp (CompanionInitializedRestartProgram.initialInput (restartInput z))
  have hm := polynomial_eval_monotone p (initialInput_bound z)
  dsimp only at hm
  have hs := CompanionCodeBounds.initialized_output (restartInput z)
  change weight (startCode z) ≤ _ at hs
  change _+weight (CompanionInitializedRestartProgram.initialCode (restartInput z)) ≤ _ at hi
  simp only [eval_add,eval_mul,eval_ofNat,eval_one]
  omega

lemma config_bound : ∃ p : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → z.2.length ≤ S → (history z).length ≤ S →
      weight (configAt 0 z) ≤ p.eval S ∧ weight (configAt 1 z) ≤ p.eval S := by
  obtain ⟨p,hp⟩ := CompanionPhaseContextProgram.polynomial_config
  refine ⟨p.comp (9*X+12),?_⟩
  intro z S hprep hbits hhist
  have hreserve : weight (reserve z) ≤ 4*S+1 := by
    have h := weight_map_bound (f := fun _ : Bool => false) (as := z.2)
      (fun _ _ => weight_bool false)
    change weight (reserve z) ≤ _ at h
    omega
  have hb (i : ℕ) (hi : i ≤ 1) : weight (contextInput (z,i)) ≤ 9*S+12 := by
    have hj := weight_nat_numeric (phase z+i)
    have hlen : phase z ≤ S := hhist
    change weight ((z.1.1.1,phase z+i),reserve z) ≤ _
    simp only [weight_prod]
    omega
  constructor
  · have h := hp (contextInput (z,0))
    have hm := polynomial_eval_monotone p (hb 0 (by omega))
    dsimp only at hm
    simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X]
    change _+weight (configAt 0 z) ≤ _ at h
    omega
  · have h := hp (contextInput (z,1))
    have hm := polynomial_eval_monotone p (hb 1 (by omega))
    dsimp only at hm
    simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X]
    change _+weight (configAt 1 z) ≤ _ at h
    omega

lemma trajectory_bounds : ∃ p : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S →
      (CompanionPhaseTrialProgram.trajectory (trialInput z)).length ≤ S+1 ∧
      (∀ code∈CompanionPhaseTrialProgram.trajectory (trialInput z),weight code ≤ p.eval S) ∧
      (CompanionPhaseTrialProgram.catalogue (trialInput z)).length ≤ p.eval S := by
  obtain ⟨p,hp⟩ := start_bound
  refine ⟨6*(p.comp (1+2*X))+1,?_⟩
  intro z S hprep hbits
  have harg : weight (z.1.1.1,z.2) ≤ 1+2*S := by simp only [weight_prod]; omega
  have hstart : weight (startCode z) ≤ p.eval (1+2*S) :=
    (hp z).trans (polynomial_eval_monotone p harg)
  have hsize : (startCode z).length ≤ p.eval (1+2*S) :=
    (list_length_le_weight _).trans hstart
  have hc := CompanionCodeBounds.trajectory_codes (trajectoryInput z) (6*p.eval (1+2*S)+1)
    (by change weight (startCode z) ≤ _; omega)
    (by change 6*(startCode z).length+1 ≤ _; omega)
  have hl := CompanionCodeBounds.trajectory_length (trajectoryInput z)
  have hlen : (trajectoryInput z).2.length ≤ S := by
    have h := list_length_le_weight z.2
    change ((z.2.drop _).take _).length ≤ S
    simp only [List.length_take,List.length_drop]
    omega
  refine ⟨by change (CompanionTrajectoryProgram.output (trajectoryInput z)).length ≤ _; omega,?_,?_⟩
  · change ∀ code∈CompanionTrajectoryProgram.output (trajectoryInput z),weight code ≤ _
    simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X] using hc
  · change (PairedCatalogProgram.catalog (startCode z)).length ≤ _
    simp only [PairedCatalogProgram.catalog,List.length_map,List.length_range,
      eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X]
    have hd := Nat.div_le_self (startCode z).length 2
    omega


lemma query_bound : ∃ q : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S → (history z).length ≤ S →
      weight (CompanionObservationQueriesProgram.output
        (CompanionObservedUpdateProgram.queryInput
          (CompanionPhaseTrialProgram.updateInput (trialInput z)))) ≤ q.eval S := by
  obtain ⟨p,hp⟩ := config_bound
  obtain ⟨r,hr⟩ := trajectory_bounds
  obtain ⟨q,hq⟩ := CompanionObservationQueriesProgram.polynomial_output
  refine ⟨q.comp (2*p+(X+1)*(r+1)+X+5),?_⟩
  intro z S hprep hbits hhist
  have hb : z.2.length ≤ S := (list_length_le_weight _).trans hbits
  have hc := hp z S hprep hb hhist
  have ht := hr z S hprep hbits
  have hcodes := list_weight_bound _ (r.eval S) ht.2.1
  have hcodeweight : weight (CompanionPhaseTrialProgram.trajectory (trialInput z)) ≤
      (S+1)*(r.eval S+1)+1 := hcodes.trans (by gcongr; exact ht.1)
  have htail : weight ((afterRestart z).drop (trajectoryWidth z)) ≤ S :=
    ((weight_sublist (List.drop_sublist _ _)).trans
      (weight_sublist (List.drop_sublist _ _))).trans hbits
  have hin : weight (CompanionObservedUpdateProgram.queryInput
      (CompanionPhaseTrialProgram.updateInput (trialInput z))) ≤
      2*p.eval S+(S+1)*(r.eval S+1)+S+5 := by
    change weight ((configAt 0 z,configAt 1 z),
      (CompanionPhaseTrialProgram.trajectory (trialInput z),
        (afterRestart z).drop (trajectoryWidth z))) ≤ _
    simp only [weight_prod]
    omega
  have hout := hq (CompanionObservedUpdateProgram.queryInput
    (CompanionPhaseTrialProgram.updateInput (trialInput z)))
  have hm := polynomial_eval_monotone q hin
  simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  exact (Nat.le_add_left _ _).trans (hout.trans hm)



open CompanionStoredSize

/-- A uniform additive increment and dimension bound for an entire phase.
The polynomial depends only on immutable data, word length and phase number. -/
lemma phase_bounds : ∃ p : Polynomial ℕ,∀ (z : Input) (S M R : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S → (history z).length ≤ S → 1 ≤ M →
    StoredHeight M (old z) → StoredShape R (old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (output z) ∧ StoredShape R (output z) := by
  obtain ⟨q,hq⟩ := query_bound
  obtain ⟨r,hr⟩ := trajectory_bounds
  let p := r+(X+1)*(2*(q+1)+3)+(X+1)+5
  refine ⟨p,?_⟩
  intro z S M R hprep hbits hhist hM hm hshape hR
  let d := CompanionObservedUpdateProgram.finishInput
    (CompanionPhaseTrialProgram.updateInput (trialInput z))
  have ht := hr z S hprep hbits
  have hq' := hq z S hprep hbits hhist
  have hv : ∀ x∈d.2,TreeFraction.height x.1 ≤ q.eval S+1 ∧
      TreeFraction.height x.2 ≤ q.eval S+1 := by
    intro x hx
    have hxw : weight x ≤ q.eval S := (weight_mem hx).trans hq'
    exact ⟨(TreeFraction.height_le_weight _).trans ((weight_fst x).trans (by omega)),
      (TreeFraction.height_le_weight _).trans ((weight_snd x).trans (by omega))⟩
  have hn := next_height d M (q.eval S+1) hM (by omega) hm.1 hm.2 hv
  have hlen : (CompanionPhaseFinishProgram.trajectory d).2.length ≤ S+1 := ht.1
  have hp : r.eval S+(S+1)*(2*(q.eval S+1)+3)+(S+1)+5=p.eval S := by
    simp only [p,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  have hmul := Nat.mul_le_mul_right (2*(q.eval S+1)+3) hlen
  have hn' : StoredHeight (M+p.eval S) (CompanionPhaseFinishProgram.next d) :=
    height_mono (by omega) hn
  have hns := next_shape d
  have hcat : (CompanionPhaseFinishProgram.trajectory d).1.length ≤ r.eval S := ht.2.2
  have hns' : StoredShape R (CompanionPhaseFinishProgram.next d) :=
    shape_mono (hcat.trans (by omega)) hns
  change StoredHeight (M+p.eval S) ((CompanionPhaseFinishProgram.output d).getD (old z)) ∧
    StoredShape R ((CompanionPhaseFinishProgram.output d).getD (old z))
  unfold CompanionPhaseFinishProgram.output
  split_ifs
  · exact ⟨hn',hns'⟩
  · exact ⟨height_mono (Nat.le_add_right M _) hm,hshape⟩

end ContingencyTables.CompanionPhaseSize

end OAI
