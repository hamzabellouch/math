import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposure
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformFibers
import OAI.Combinatorics.BalancedRyser.Probability.FreshTupleWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessConditional

namespace OAI

namespace Balanced.FreshCoordinate

noncomputable section
open scoped Classical

variable {D A : Type*} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]

theorem probability_two_prescriptions_on_subtype (d e : D) (hde : d ≠ e)
    (G E : (D → A) → Prop) [Nonempty {f : D → A // G f}]
    (b₁ b₂ : (D → A) → A)
    (hGd : ∀ f a, G (Function.update f d a) ↔ G f)
    (hGe : ∀ f a, G (Function.update f e a) ↔ G f)
    (hEd : ∀ f a, E (Function.update f d a) ↔ E f)
    (hEe : ∀ f a, E (Function.update f e a) ↔ E f)
    (hb₁d : ∀ f a, b₁ (Function.update f d a) = b₁ f)
    (hb₂d : ∀ f a, b₂ (Function.update f d a) = b₂ f)
    (hb₂e : ∀ f a, b₂ (Function.update f e a) = b₂ f) :
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1 ∧ f.1 d = b₁ f.1 ∧ f.1 e = b₂ f.1}).toReal =
    ((PMF.uniformOfFintype {f : D → A // G f}).toOuterMeasure
      {f | E f.1}).toReal / (Fintype.card A : ℝ)^2 := by
  have h := probability_prescription_on_subtype d G
    (fun f => E f ∧ f e = b₂ f) b₁ hGd
    (by
      intro f a
      rw [hEd, Function.update_of_ne hde.symm, hb₂d]) hb₁d
  rw [probability_prescription_on_subtype e G E b₂ hGe hEe hb₂e] at h
  simpa only [and_assoc, and_left_comm, and_comm, div_div, pow_two] using h

end
end Balanced.FreshCoordinate

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def orientedExternalPair (T : FourTuple F) (d e : Direction F)
    (w : Point F) (i j : Fin 4) (σ τ : Bool) (M : MergedPairs F) : Prop :=
  (OnLine w (constituent M d σ) ∧
    OnLine (tuplePoint M T i) (constituent M d (!σ))) ∧
  (OnLine w (constituent M e τ) ∧
    OnLine (tuplePoint M T j) (constituent M e (!τ)))

theorem oriented_external_pair_probability_on_event
    (T : FourTuple F) (d e : Direction F) (hde : d ≠ e)
    (hd : ∀ k, T.generator k ≠ d) (he : ∀ k, T.generator k ≠ e)
    (w : Point F) (i j : Fin 4) (σ τ : Bool)
    (G E : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M)
    (hEd : ∀ M v, E (Function.update M d v) ↔ E M)
    (hEe : ∀ M v, E (Function.update M e v) ↔ E M) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E M.1 ∧ orientedExternalPair T d e w i j σ τ M.1}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | E M.1}).toReal / (Fintype.card F : ℝ)^4 := by
  have h := FreshCoordinate.probability_two_prescriptions_on_subtype d e hde G E
    (fun M => pairPrescription d w (tuplePoint M T i) σ)
    (fun M => pairPrescription e w (tuplePoint M T j) τ)
    hGd hGe hEd hEe
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T d hd])
    (by intro M v; rw [tuplePoint_update_fresh T e he])
  simp_rw [pairPrescription_iff] at h
  have hcard : (Fintype.card (Bool → F) : ℝ)^2 = (Fintype.card F : ℝ)^4 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
    ring
  rw [hcard] at h
  exact h

def successWithPoint (g : Direction F) (T : FourTuple F) (w : Point F)
    (M : MergedPairs F) : Prop :=
  ((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
    Function.Injective (tuplePoint M T)) ∧
  OnLine w (lineThrough g (tuplePoint M T 0))

omit [Fintype F] in
theorem successWithPoint_update_fresh (g : Direction F) (T : FourTuple F)
    (w : Point F) (d : Direction F) (hd : ∀ k, T.generator k ≠ d)
    (M : MergedPairs F) (v : Bool → F) :
    successWithPoint g T w (Function.update M d v) ↔ successWithPoint g T w M := by
  unfold successWithPoint
  rw [tuplePoint_update_fresh T d hd]

theorem successful_external_pair_probability_on_event
    (g : Direction F) (T : FourTuple F) (d e : Direction F) (hde : d ≠ e)
    (hd : ∀ k, T.generator k ≠ d) (he : ∀ k, T.generator k ≠ e)
    (w : Point F) (i j : Fin 4) (σ τ : Bool)
    (G : MergedPairs F → Prop) [Nonempty {M : MergedPairs F // G M}]
    (hGd : ∀ M v, G (Function.update M d v) ↔ G M)
    (hGe : ∀ M v, G (Function.update M e v) ↔ G M) :
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | successWithPoint g T w M.1 ∧
        orientedExternalPair T d e w i j σ τ M.1}).toReal =
    ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
      {M | successWithPoint g T w M.1}).toReal / (Fintype.card F : ℝ)^4 := by
  exact oriented_external_pair_probability_on_event T d e hde hd he w i j σ τ
    G (successWithPoint g T w) hGd hGe
    (successWithPoint_update_fresh g T w d hd)
    (successWithPoint_update_fresh g T w e he)

theorem exposedLaw_eq_uniform_fiber (D : Finset (Direction F)) (a : MergedPairs F) :
    CandidateExposure.exposedLaw D a =
      (PMF.uniformOfFintype
        (ConditionalRestriction.FixedArray (fun d => d ∈ D) a)).map Subtype.val := by
  have hfilter : CandidateExposure.exposedLaw D a =
      (PMF.uniformOfFintype (MergedPairs F)).filter
        {M | ∀ d, d ∈ D → M d = a d}
        (ConditionalRestriction.fixed_supported (fun d => d ∈ D) a) := by
    ext M
    simp only [CandidateExposure.exposedLaw, PMF.filter_apply,
      PartialAlignment.offsetLaw_eq_uniform]
  rw [hfilter]
  exact @Balanced.uniform_filter_eq_subtype_map (MergedPairs F) inferInstance inferInstance
    {M | ∀ d, d ∈ D → M d = a d}
    (inferInstanceAs (Fintype (ConditionalRestriction.FixedArray (fun d => d ∈ D) a)))
    ⟨⟨a, by intro d hd; rfl⟩⟩ _

theorem successful_external_pair_probability_exposed
    (D : Finset (Direction F)) (a : MergedPairs F)
    (g : Direction F) (T : FourTuple F) (d e : Direction F) (hde : d ≠ e)
    (hdD : d ∉ D) (heD : e ∉ D)
    (hd : ∀ k, T.generator k ≠ d) (he : ∀ k, T.generator k ≠ e)
    (w : Point F) (i j : Fin 4) (σ τ : Bool) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure
      {M | successWithPoint g T w M ∧
        orientedExternalPair T d e w i j σ τ M}).toReal =
    ((CandidateExposure.exposedLaw D a).toOuterMeasure
      {M | successWithPoint g T w M}).toReal / (Fintype.card F : ℝ)^4 := by
  rw [exposedLaw_eq_uniform_fiber D a]
  simp only [PMF.toOuterMeasure_map_apply]
  have h := successful_external_pair_probability_on_event g T d e hde hd he w i j σ τ
    (fun M => ∀ t, t ∈ D → M t = a t)
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a d hdD)
    (fixed_coordinates_update_invariant (fun t => t ∈ D) a e heD)
  convert h using 1
  · apply FiniteUniformFibers.probability_fintype_congr
    rfl
  · apply congrArg (fun x : ℝ => x / (Fintype.card F : ℝ)^4)
    apply FiniteUniformFibers.probability_fintype_congr
    rfl

end
end Balanced.FreshTupleWitness

end OAI
