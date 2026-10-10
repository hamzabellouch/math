import OAI.Probability.StrongRayleigh.FiniteFieldTilt
import OAI.Probability.StrongRayleigh.FiniteMarginalObservation
import OAI.Probability.StrongRayleigh.DensityBayes
import OAI.Probability.StrongRayleigh.TiltPartition
import OAI.Probability.StrongRayleigh.GaussianObservation
import OAI.Probability.StrongRayleigh.IndependentAtomObservation

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139

lemma finiteFieldWeight_congr_on {I : Type u_1} (S : Finset I) (h h' : I → ℝ)
    (heq : ∀ j ∈ S, h j = h' j) (x : I → Bool) :
    finiteFieldWeight S h x = finiteFieldWeight S h' x := by
  unfold finiteFieldWeight
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [heq j hj]

lemma finiteFieldMean_congr_on {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h h' : I → ℝ) (heq : ∀ j ∈ S, h j = h' j) (i : I) :
    finiteFieldMean μ S h i = finiteFieldMean μ S h' i := by
  unfold finiteFieldMean
  simp only [finiteFieldWeight_congr_on S h h' heq]

def endpointObservationField {I : Type u_3} [DecidableEq I]
    (S : Finset I) (t : ℝ) (y : S → ℝ) : I → ℝ :=
  fun j => if hj : j ∈ S then y ⟨j, hj⟩ - t / 2 else 0

def finiteEndpointMean {I : Type u_4} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : S → ℝ) : ℝ :=
  finiteFieldMean μ S (endpointObservationField S t y) i

lemma measurable_endpointObservationField {I : Type u_5} [DecidableEq I] (S : Finset I) :
    Measurable (fun p : ℝ × (S → ℝ) => endpointObservationField S p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j ∈ S
  · simp only [endpointObservationField, hj, dite_eq_left]
    exact ((measurable_pi_apply (⟨j, hj⟩ : S)).comp measurable_snd).sub
      (measurable_fst.div_const 2)
  · simp only [endpointObservationField, hj]
    exact measurable_const

lemma measurable_finiteEndpointMean {I : Type u_6} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    Measurable (fun p : ℝ × (S → ℝ) => finiteEndpointMean μ i S p.1 p.2) :=
  (measurable_finiteFieldMean μ S i).comp (measurable_endpointObservationField S)

lemma finiteEndpointMean_restrict {I : Type u_7} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) :
    finiteEndpointMean μ i S t (fun j : S => y j.1) =
      finiteFieldMean μ S (fun j => y j - t / 2) i := by
  apply finiteFieldMean_congr_on
  intro j hj
  simp [endpointObservationField, hj]

theorem finiteBinary_condExp_of_field_densities
    {Ω : Type u_8} {E : Type u_9} {F : Type u_10} [MeasurableSpace Ω] [mE : MeasurableSpace E] [Fintype F]
    (P : Measure Ω) [IsFiniteMeasure P] (ρ : Measure E) [SigmaFinite ρ]
    (μ : ProbabilityMeasure (F → Bool)) (X : Ω → (F → Bool)) (hX : Measurable X)
    (Y : Ω → E) (hY : Measurable Y) (h : E → F → ℝ) (hh : Measurable h)
    (hAtom : ∀ x, Measure.map Y (P.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => ENNReal.ofReal
        (Real.exp (∑ j, h y j * boolReal (x j)) *
          ((μ : Measure (F → Bool)) {x}).toReal))) (i : F) :
    P[(fun ω => boolReal (X ω i)) | mE.comap Y] =ᵐ[P]
      (fun ω => tiltMean μ (h (Y ω)) i) := by
  classical
  let w : (F → Bool) → E → ℝ := fun x y =>
    Real.exp (∑ j, h y j * boolReal (x j)) * ((μ : Measure (F → Bool)) {x}).toReal
  have hw : ∀ x, Measurable (w x) := by
    intro x
    apply Measurable.mul_const
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp hh).mul_const _)
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y =>
    mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  have hpos : ∀ y, 0 < ∑ x, w x y := fun y => tiltPartition_pos μ (h y)
  have hb := DensityBayes.finite_signal_condExp_indicator_real P ρ X hX Y hY
    w hw hw0 hpos hAtom {x | x i = true}
  have hind : (X ⁻¹' {x | x i = true}).indicator (fun _ => (1 : ℝ)) =
      fun ω => boolReal (X ω i) := by
    funext ω
    simp [boolReal, Set.indicator_apply]
  rw [hind] at hb
  filter_upwards [hb] with ω hω
  rw [hω]
  unfold tiltMean tiltPartition
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x i = true <;> simp [w, boolReal, hx]

private lemma endpoint_pi_dirac_zero {G : Type u_11} [Fintype G] :
    Measure.pi (fun _ : G => Measure.dirac (0 : ℝ)) =
      Measure.dirac (fun _ : G => (0 : ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  by_cases h : ∀ j, (0 : ℝ) ∈ s j
  · simp [Measure.dirac_apply', MeasurableSet.univ_pi hs, hs, Set.mem_pi, h]
  · have hp : (∏ j, (Measure.dirac (0 : ℝ)) (s j)) = 0 := by
      obtain ⟨j, hj⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Measure.dirac_apply', hs, hj]
    rw [hp]
    simp [Measure.dirac_apply', MeasurableSet.univ_pi hs, Set.mem_pi, h]

lemma gaussianEndpoint_shift_map {G : Type u_12} [Fintype G]
    (t : ℝ≥0) (x : G → Bool) :
    Measure.map (fun z : G → ℝ => fun j => (t : ℝ) * boolReal (x j) + z j)
      (Measure.pi (fun _ : G => gaussianReal 0 t)) =
      (Measure.pi (fun _ : G => gaussianReal 0 t)).withDensity
        (fun y => ENNReal.ofReal (GaussianObservation.likelihood t x y)) := by
  by_cases ht : t = 0
  · subst t
    simp only [NNReal.coe_zero, zero_mul, zero_add, gaussianReal_zero_var]
    rw [endpoint_pi_dirac_zero]
    change Measure.map id (Measure.dirac (fun _ : G => (0 : ℝ))) = _
    rw [Measure.map_id, dirac_withDensity]
    simp [GaussianObservation.likelihood]
  · rw [Measure.pi_map_pi (f := fun j z => (t : ℝ) * boolReal (x j) + z)
      (fun j => (measurable_const.add measurable_id).aemeasurable)]
    simp_rw [gaussianReal_map_const_add, zero_add]
    exact GaussianObservation.gaussianReal_pi_binary_shift t ht x

theorem finiteBinary_condExp_independentGaussian
    {Ω : Type u_13} {F : Type u_14} {G : Type u_15} [MeasurableSpace Ω] [Fintype F] [Fintype G]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (F → Bool))
    (X : Ω → (F → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (F → Bool)) P)
    (Z : Ω → (G → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw Z (Measure.pi (fun _ : G => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) (σ : G → F)
    (h : (G → ℝ) → F → ℝ) (hh : Measurable h)
    (hsum : ∀ (x : F → Bool) (y : G → ℝ),
      (∑ j, h y j * boolReal (x j)) =
        ∑ j, (y j - (t : ℝ) / 2) * boolReal (x (σ j))) (i : F) :
    let Y : Ω → (G → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω (σ j)) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (G → ℝ)).comap Y]
      =ᵐ[P] (fun ω => tiltMean μ (h (Y ω)) i) := by
  classical
  dsimp only
  let T : (F → Bool) → (G → ℝ) → (G → ℝ) :=
    fun x z j => (t : ℝ) * boolReal (x (σ j)) + z j
  have hT : ∀ x, Measurable (T x) := by
    intro x
    exact Measurable.of_eval (fun j => measurable_const.add (measurable_pi_apply j))
  have hY : Measurable (fun ω => T (X ω) (Z ω)) := by
    apply Measurable.of_eval
    intro j
    exact ((((measurable_of_countable boolReal).comp ((measurable_pi_apply (σ j)).comp hX)).const_mul
      (t : ℝ)).add ((measurable_pi_apply j).comp hZ))
  apply finiteBinary_condExp_of_field_densities P
    (Measure.pi (fun _ : G => gaussianReal 0 t)) μ X hX _ hY h hh ?_ i
  intro x
  have ha := IndependentAtomObservation.map_observation_restrict_atom_withDensity_ofReal
    hX hZ hind hZLaw T x (hT x)
    (Measure.pi (fun _ : G => gaussianReal 0 t))
    (GaussianObservation.likelihood t (fun j => x (σ j)))
    (GaussianObservation.measurable_likelihood t (fun j => x (σ j)))
    (gaussianEndpoint_shift_map t (fun j => x (σ j)))
  rw [ha]
  congr 1
  funext y
  have hmass : P (X ⁻¹' {x}) = (μ : Measure (F → Bool)) {x} := by
    rw [← Measure.map_apply hX (measurableSet_singleton x), hXLaw.map_eq]
  rw [hmass, hsum]
  unfold GaussianObservation.likelihood
  rw [mul_comm]

lemma endpointObservationField_sum {I : Type u_16} [DecidableEq I]
    (S J : Finset I) (hSJ : S ⊆ J) (t : ℝ) (y : S → ℝ) (x : J → Bool) :
    (∑ j : J, endpointObservationField S t y j.1 * boolReal (x j)) =
      ∑ j : S, (y j - t / 2) * boolReal (x ⟨j.1, hSJ j.2⟩) := by
  classical
  let f : I → ℝ := fun j => if hj : j ∈ S then
    (y ⟨j, hj⟩ - t / 2) * boolReal (x ⟨j, hSJ hj⟩) else 0
  calc
    _ = ∑ j : J, f j.1 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1 ∈ S <;> simp [endpointObservationField, f, hj]
    _ = ∑ j ∈ J, f j := Finset.sum_coe_sort J f
    _ = ∑ j ∈ S, f j := (Finset.sum_subset hSJ (fun j _ hj => by simp [f, hj])).symm
    _ = ∑ j : S, f j.1 := (Finset.sum_coe_sort S f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [f, j.2]

lemma finiteEndpointMean_eq_tiltMean {I : Type u_17} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (S J : Finset I) (hSJ : S ⊆ J)
    (i : J) (t : ℝ) (y : S → ℝ) :
    finiteEndpointMean μ i.1 S t y =
      tiltMean (finiteMarginal μ J) (fun j : J => endpointObservationField S t y j.1) i := by
  unfold finiteEndpointMean
  rw [finiteFieldMean_eq_tiltMean_finiteMarginal μ S J hSJ _ i]
  congr 1
  funext j
  by_cases hj : j.1 ∈ S <;> simp [endpointObservationField, hj]

theorem finiteEndpointMean_condExp
    {Ω : Type u_18} {I : Type u_19} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (i : I) (S : Finset I) (Z : Ω → (S → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw Z (Measure.pi (fun _ : S => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) :
    let Y : Ω → (S → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω j.1) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (S → ℝ)).comap Y]
      =ᵐ[P] (fun ω => finiteEndpointMean μ i S (t : ℝ) (Y ω)) := by
  classical
  let J := insert i S
  let R : (I → Bool) → (J → Bool) := fun x j => x j.1
  have hR : Measurable R := Measurable.of_eval (fun j => measurable_pi_apply j.1)
  have hRJ : HasLaw R (finiteMarginal μ J : Measure (J → Bool))
      (μ : Measure (I → Bool)) := by
    refine ⟨hR.aemeasurable, ?_⟩
    rw [finiteMarginal, ProbabilityMeasure.toMeasure_map]
  have hRX : Measurable (R ∘ X) := hR.comp hX
  have hindR : IndepFun (R ∘ X) Z P := by
    simpa only [Function.id_comp] using hind.comp hR measurable_id
  have hSJ : S ⊆ J := Finset.subset_insert i S
  let σ : S → J := fun j => ⟨j.1, hSJ j.2⟩
  let h : (S → ℝ) → J → ℝ := fun y j => endpointObservationField S (t : ℝ) y j.1
  have hh : Measurable h := by
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j.1).comp
      ((measurable_endpointObservationField S).comp (measurable_const.prodMk measurable_id))
  have hsum : ∀ (x : J → Bool) (y : S → ℝ),
      (∑ j, h y j * boolReal (x j)) =
        ∑ j, (y j - (t : ℝ) / 2) * boolReal (x (σ j)) :=
    fun x y => endpointObservationField_sum S J hSJ (t : ℝ) y x
  have hp := finiteBinary_condExp_independentGaussian P (finiteMarginal μ J)
    (R ∘ X) hRX (hRJ.comp hXLaw) Z hZ t hZLaw hindR σ h hh hsum
    ⟨i, Finset.mem_insert_self i S⟩
  change P[(fun ω => boolReal (X ω i)) |
      (inferInstance : MeasurableSpace (S → ℝ)).comap
        (fun ω j => (t : ℝ) * boolReal (X ω j.1) + Z ω j)] =ᵐ[P] _ at hp
  refine hp.trans (Filter.Eventually.of_forall (fun ω => ?_))
  exact (finiteEndpointMean_eq_tiltMean μ S J hSJ
    ⟨i, Finset.mem_insert_self i S⟩ (t : ℝ) _).symm

theorem finiteObservationDrift_condExp
    {Ω : Type u_20} {I : Type u_21} [MeasurableSpace Ω] [DecidableEq I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (hX : Measurable X)
    (hXLaw : HasLaw X (μ : Measure (I → Bool)) P)
    (i : I) (S : Finset I) (Z : Ω → (I → ℝ)) (hZ : Measurable Z)
    (t : ℝ≥0)
    (hZLaw : HasLaw (fun ω => fun j : S => Z ω j.1)
      (Measure.pi (fun _ : S => gaussianReal 0 t)) P)
    (hind : IndepFun X Z P) :
    let Y : Ω → (I → ℝ) := fun ω j => (t : ℝ) * boolReal (X ω j) + Z ω j
    P[(fun ω => boolReal (X ω i)) | (inferInstance : MeasurableSpace (S → ℝ)).comap
        (fun ω => fun j : S => Y ω j.1)] =ᵐ[P]
      (fun ω => finiteObservationDrift μ i S (t : ℝ) (Y ω)) := by
  let R : (I → ℝ) → (S → ℝ) := fun z j => z j.1
  have hR : Measurable R := Measurable.of_eval (fun j => measurable_pi_apply j.1)
  have hindR : IndepFun X (R ∘ Z) P := by
    simpa only [Function.id_comp] using hind.comp measurable_id hR
  have hp := finiteEndpointMean_condExp P μ X hX hXLaw i S (R ∘ Z)
    (hR.comp hZ) t hZLaw hindR
  refine hp.trans (Filter.Eventually.of_forall (fun ω => ?_))
  exact (finiteEndpointMean_restrict μ i S (t : ℝ)
    (fun j => (t : ℝ) * boolReal (X ω j) + Z ω j)).trans
    (finiteObservationDrift_eq_finiteFieldMean μ i S (t : ℝ)
      (fun j => (t : ℝ) * boolReal (X ω j) + Z ω j)).symm

end Problem336AdditiveD139

end

end OAI
