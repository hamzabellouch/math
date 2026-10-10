import OAI.Probability.DirectionalWalk.ContactJoins

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def relativeContinuationLaw {d : ℕ} (P : Measure (Path d)) (a : Word d) : Measure (Path d) :=
  (continuationLaw P a).map (shiftPath (-wordEnd a))

lemma relativeContinuationLaw_probability {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) : IsProbabilityMeasure (relativeContinuationLaw P a) := by
  let := continuationLaw_probability P a ha
  exact probabilityMeasure_map (measurable_shiftPath _).aemeasurable

lemma relativeContinuation_fresh_stopped {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a)) (N : ℕ) :
    (relativeContinuationLaw (annealed μ 0) a).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) =
      (annealed μ 0).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) := by
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  let K := axisLower e 0 ∪ axisUpper e N
  have hex : ∀ᵐ X ∂annealed μ 0, ∃ n, X n ∈ K := annealed_axis_exit μ hell e 0 0 N
  have he (b : Word d) (hb : firstHitWord K b) :
      relativeContinuationLaw (annealed μ 0) a (wordCylinder b) = annealed μ 0 (wordCylinder b) := by
    rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _) (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
      shiftPath_preimage_wordCylinder,continuationLaw_fresh_cylinder μ 0 a _ ha]
    · have hs := congrArg (fun M : Measure (Path d) => M (wordCylinder b))
        (annealed_shift μ (wordEnd a) (-wordEnd a))
      rw [add_neg_cancel,Measure.map_apply (measurable_shiftPath _) (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
        shiftPath_preimage_wordCylinder] at hs
      exact hs
    · apply Set.disjoint_left.mpr
      rintro y ⟨i,hi,rfl⟩ ⟨j,hj,heq⟩
      have hj' := hb.2 j hj
      have hnonneg : 0 ≤ axisHeight e (wordPath b j) := by
        by_contra h
        exact hj' (Or.inl (by exact lt_of_not_ge h))
      rw [wordPath_translate (wordEnd a) b j hj.le] at heq
      have ha' := hdep i hi
      have heq' := congrArg (axisHeight e) heq
      rw [axisHeight_add] at heq'
      omega
  exact firstVisitWord_map_eq _ _ K (firstHitWords_full_of_cylinder_eq _ _ K hex he) hex he

lemma posterior_old_prefix_contact_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI := relativeContinuationLaw_probability (annealed μ 0) a ha
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior (relativeContinuationLaw (annealed μ 0) a) E q b) *
        (annealed μ 0 (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  exact posterior_contact_raw_bound μ hell (relativeContinuationLaw (annealed μ 0) a) E hE hdis e
    start r N m hrN (relativeContinuation_fresh_stopped μ hell e a ha hdep N) hΔ

lemma binary_cross_entropy_bound (P Q : Measure Bool) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    P.real {true} * (-Real.log (Q.real {true})) ≤
      (InformationTheory.klDiv P Q).toReal + Real.log 2 := by
  have hi : Integrable (fun x => Real.log (P.real {x}) - Real.log (Q.real {x})) P := Integrable.of_finite
  have hkl := atom_klDiv_formula P Q hPQ hi
  have hnonneg := atom_logRatio_nonneg P Q hPQ hi
  rw [hkl,ENNReal.toReal_ofReal hnonneg]
  have hs : (∫ x, Real.log (P.real {x}) - Real.log (Q.real {x}) ∂P) =
      (∫ x, atomInfo Q x ∂P) - discreteEntropy P := by
    rw [discreteEntropy,← integral_sub Integrable.of_finite Integrable.of_finite]
    congr 1
    funext x
    simp only [atomInfo]
    ring
  rw [hs]
  have hent := (entropy_finite Bool P).2
  simp only [Fintype.card_bool,Nat.cast_ofNat] at hent
  have hcross : P.real {true} * (-Real.log (Q.real {true})) ≤ ∫ x, atomInfo Q x ∂P := by
    rw [integral_fintype Integrable.of_finite]
    simp only [Fintype.sum_bool,smul_eq_mul,atomInfo]
    have hpos : 0 ≤ P.real {false} * (-Real.log (Q.real {false})) :=
      mul_nonneg measureReal_nonneg (atomInfo_nonneg Q false)
    linarith
  linarith

lemma kl_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hfin : InformationTheory.klDiv P Q ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet E) :
    P.real E * (-Real.log (Q.real E)) ≤ (InformationTheory.klDiv P Q).toReal + Real.log 2 := by
  classical
  let f : Ω → Bool := fun x => decide (x ∈ E)
  have hf : Measurable f := by
    intro s hs
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
    · have he : f ⁻¹' s = Set.univ := by ext x;simp only [Set.mem_preimage,Set.mem_univ,iff_true];cases h : f x <;> simp_all
      rw [he];exact MeasurableSet.univ
    · have he : f ⁻¹' s = E := by ext x;simp only [Set.mem_preimage,f];by_cases hx : x ∈ E <;> simp_all
      rw [he];exact hE
    · have he : f ⁻¹' s = Eᶜ := by ext x;simp only [Set.mem_preimage,f,Set.mem_compl_iff];by_cases hx : x ∈ E <;> simp_all
      rw [he];exact hE.compl
    · have he : f ⁻¹' s = ∅ := by ext x;simp only [Set.mem_preimage,Set.mem_empty_iff_false,iff_false];cases h : f x <;> simp_all
      rw [he];exact MeasurableSet.empty
  let := probabilityMeasure_map hf.aemeasurable (μ := P)
  let := probabilityMeasure_map hf.aemeasurable (μ := Q)
  have hac := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hh := binary_cross_entropy_bound (P.map f) (Q.map f) (hac.map hf)
  have hmass (M : Measure Ω) : (M.map f).real {true} = M.real E := by
    rw [measureReal_def,Measure.map_apply hf (measurableSet_singleton _)]
    have he : f ⁻¹' {true} = E := by ext x;simp [f]
    rw [he]
    rfl
  rw [hmass P,hmass Q] at hh
  have hm := ENNReal.toReal_mono hfin (InformationTheory.klDiv_map_le P Q hf)
  linarith

lemma posterior_cylinder_mass {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (q : Fin ι) (b : Word d) :
    ENNReal.ofReal (wordPosterior P E q b) * P (wordCylinder b) = P (E q ∩ wordCylinder b) := by
  by_cases hb : P (wordCylinder b) = 0
  · have he : P (E q ∩ wordCylinder b) = 0 := measure_mono_null Set.inter_subset_right hb
    simp only [hb,mul_zero,he]
  · have hp : 0 < P.real (wordCylinder b) := ENNReal.toReal_pos hb (measure_ne_top _ _)
    rw [wordPosterior,ENNReal.ofReal_div_of_pos hp,measureReal_def,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.div_mul_cancel hb (measure_ne_top _ _)]

lemma relativeContinuation_fresh_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (a b : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (hb : ∀ j < b.1, 0 ≤ axisHeight e (wordPath b j)) :
    relativeContinuationLaw (annealed μ 0) a (wordCylinder b) = annealed μ 0 (wordCylinder b) := by
  rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _)
    (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
    shiftPath_preimage_wordCylinder,continuationLaw_fresh_cylinder μ 0 a _ ha]
  · have hs := congrArg (fun M : Measure (Path d) => M (wordCylinder b))
      (annealed_shift μ (wordEnd a) (-wordEnd a))
    rw [add_neg_cancel,Measure.map_apply (measurable_shiftPath _)
      (show MeasurableSet (wordCylinder b) from measurableSet_pathCylinder _ _),
      shiftPath_preimage_wordCylinder] at hs
    exact hs
  · apply Set.disjoint_left.mpr
    rintro y ⟨i,hi,rfl⟩ ⟨j,hj,heq⟩
    rw [wordPath_translate (wordEnd a) b j hj.le] at heq
    have heq' := congrArg (axisHeight e) heq
    rw [axisHeight_add] at heq'
    have := hdep i hi
    have := hb j hj
    omega

lemma prefix_relative_completion_mass {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) (E : Set (Path d)) (hE : MeasurableSet E) :
    P (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' E) =
      P (wordCylinder a) * relativeContinuationLaw P a E := by
  rw [relativeContinuationLaw,Measure.map_apply (measurable_shiftPath _) hE,
    continuationLaw,Measure.map_apply (measurable_tailPath _) (hE.preimage (measurable_shiftPath _)),
    ProbabilityTheory.cond_apply (show MeasurableSet (wordCylinder a) from measurableSet_pathCylinder _ _) _ _]
  rw [← mul_assoc,ENNReal.mul_inv_cancel ha (measure_ne_top _ _),one_mul]
  rfl

lemma posterior_old_prefix_weighted_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (a : Word d) (ha : annealed μ 0 (wordCylinder a) ≠ 0)
    (hdep : ∀ i < a.1, axisHeight e (wordPath a i) < axisHeight e (wordEnd a))
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' (E q ∩ wordCylinder b)) *
        annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ≤
      annealed μ 0 (wordCylinder a) *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let P := relativeContinuationLaw (annealed μ 0) a
  let := relativeContinuationLaw_probability (annealed μ 0) a ha
  have hmass (q : Fin ι) (b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}) :
      annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.1) ⁻¹' (E q ∩ wordCylinder b)) =
        annealed μ 0 (wordCylinder a) * (ENNReal.ofReal (wordPosterior P E q b) * annealed μ 0 (wordCylinder b)) := by
    rw [prefix_relative_completion_mass _ a ha _ ((hE q).inter (show MeasurableSet (wordCylinder (b : Word d)) from measurableSet_pathCylinder _ _)),
      ← posterior_cylinder_mass P E q b]
    rw [relativeContinuation_fresh_cylinder μ e a b ha hdep]
    intro j hj
    have hh := b.property.2.2 j hj.le
    exact le_of_not_gt (fun h => hh (Or.inl h))
  simp_rw [hmass,mul_assoc]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← Finset.mul_sum]
  simpa only [mul_assoc] using mul_le_mul_right (posterior_old_prefix_contact_bound μ hell e a ha hdep E hE hdis start r N m hrN hΔ) (annealed μ 0 (wordCylinder a))

end DirectionalZeroOne

end OAI
