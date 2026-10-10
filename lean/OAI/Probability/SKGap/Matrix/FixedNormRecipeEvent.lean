import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRecipeEvent

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

def physicalNormBound (j : ℝ) : ℝ := 2*Real.sqrt j+1+1

lemma physicalNormBound_pos (j : ℝ) : 0<physicalNormBound j := by
  unfold physicalNormBound
  positivity

theorem gaussian_fixed_norm_recipe_probability {j A : ℝ} (hj : 0<j) (hj1 : j<1)
    (hA : 1≤A) (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>(Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ¬RecipeMatrixEvent j (physicalNormBound j) A B W C M Nmax
          (removeDiagonal (goeMatrix (j/n) g))}) atTop (𝓝 0) := by
  obtain ⟨R,B,W,C,hR,hB,hW,hC,hprob⟩:=gaussian_recipe_event_probability hj hj1 hA M Nmax
  refine ⟨B,W,C,hB,hW,hC,?_⟩
  have hup := hprob.add (recipeNormTail_limit hj)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hup)
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ:=Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let E : Set (MatrixCoordinates (Fin n)→ℝ):={g | ¬RecipeMatrixEvent j R A B W C M Nmax
    (removeDiagonal (goeMatrix (j/n) g))}
  let F : Set (MatrixCoordinates (Fin n)→ℝ):={g | physicalNormBound j<SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))}
  have hF : μ F≤recipeNormTail j n:=zeroDiagGOE_norm_tail hj hn
  apply (measure_mono (t:=E∪F) ?_).trans ((measure_union_le E F).trans (add_le_add_right hF _))
  intro g hg
  by_contra hh
  have ho : SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))≤physicalNormBound j:=
    le_of_not_gt fun hbad=>hh (.inr hbad)
  have he : RecipeMatrixEvent j R A B W C M Nmax (removeDiagonal (goeMatrix (j/n) g)):= by
    by_contra hbad;exact hh (.inl hbad)
  exact hg ⟨ho,he.2⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGapCutoff
namespace GapBridge

def restrictUpper {n : ℕ} (g : GaussianCoordinates n) : SKGap.Disorder n :=
  fun e => g e.val

lemma measurable_restrictUpper (n : ℕ) : Measurable (restrictUpper (n := n)) := by
  exact Measurable.of_eval (fun edge => measurable_pi_apply edge.val)

lemma coupling_restrictUpper {n : ℕ} (g : GaussianCoordinates n) :
    SKGap.coupling (restrictUpper g) = sampledInteraction g := by
  funext i k
  rcases lt_trichotomy i k with h | rfl | h
  · simp [SKGap.coupling, restrictUpper, sampledInteraction, h, ne_of_lt h,
      min_eq_left h.le, max_eq_right h.le]
  · simp [SKGap.coupling, sampledInteraction]
  · simp [SKGap.coupling, restrictUpper, sampledInteraction, h, ne_of_gt h,
      not_lt_of_gt h, min_eq_right h.le, max_eq_left h.le]

def edgeInteraction {n : ℕ} (g : SKGap.Disorder n) : Interaction n := Matrix.of (SKGap.coupling g)

lemma edgeInteraction_restrictUpper {n : ℕ} (g : GaussianCoordinates n) :
    edgeInteraction (restrictUpper g) = sampledInteraction g := coupling_restrictUpper g

lemma coupling_symmetric {n : ℕ} (g : SKGap.Disorder n) (i k : Fin n) :
    SKGap.coupling g i k = SKGap.coupling g k i := by
  rcases lt_trichotomy i k with h | rfl | h
  · simp [SKGap.coupling, h, not_lt_of_gt h]
  · rfl
  · simp [SKGap.coupling, h, not_lt_of_gt h]

lemma coupling_diagonal {n : ℕ} (g : SKGap.Disorder n) (i : Fin n) :
    SKGap.coupling g i i = 0 := by simp [SKGap.coupling]

lemma hamiltonian_zero {n : ℕ} (g : SKGap.Disorder n) (x : Spin n) :
    SKGap.hamiltonian g 0 x = energy (edgeInteraction g) x := by
  simp only [SKGap.hamiltonian, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, SKGap.spinValue, energy, spin, edgeInteraction, Matrix.of_apply]
  ring

lemma weight_zero {n : ℕ} (g : SKGap.Disorder n) (x : Spin n) :
    SKGap.weight g 0 x = Real.exp (energy (edgeInteraction g) x) := by
  rw [SKGap.weight, hamiltonian_zero]

lemma partition_zero {n : ℕ} (g : SKGap.Disorder n) :
    SKGap.partition g 0 = partition (edgeInteraction g) := by
  simp only [SKGap.partition, partition, weight_zero]

lemma mass_zero {n : ℕ} (g : SKGap.Disorder n) (x : Spin n) :
    SKGap.mass g 0 x = gibbs (edgeInteraction g) x := by
  simp only [SKGap.mass, weight_zero, partition_zero]
  rfl

lemma expectation_zero {n : ℕ} (g : SKGap.Disorder n) (f : Observables n) :
    SKGap.expectation g 0 f = gibbsExpectation (edgeInteraction g) f := by
  simp only [SKGap.expectation, gibbsExpectation, mass_zero]

lemma variance_zero {n : ℕ} (g : SKGap.Disorder n) (f : Observables n) :
    SKGap.variance g 0 f = gibbsVariance (edgeInteraction g) f := by
  simp only [SKGap.variance, gibbsVariance, expectation_zero]

lemma flip_eq {n : ℕ} (i : Fin n) (x : Spin n) : SKGap.flip i x = flip x i := rfl

def pairConditional {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (x : Spin n) : ℝ :=
  (gibbs J x * f x + gibbs J (flip x i) * f (flip x i)) /
    (gibbs J x + gibbs J (flip x i))

lemma conditionalExpectation_zero {n : ℕ} (g : SKGap.Disorder n) (i : Fin n)
    (f : Observables n) (x : Spin n) :
    SKGap.conditionalExpectation g 0 i f x = pairConditional (edgeInteraction g) i f x := by
  simp only [SKGap.conditionalExpectation, weight_zero, flip_eq, pairConditional, gibbs]
  field_simp [ne_of_gt (partition_pos (edgeInteraction g))]

lemma pairConditional_flip {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (x : Spin n) :
    pairConditional J i f (flip x i) = pairConditional J i f x := by
  simp only [pairConditional, flip_flip, add_comm]

lemma flipRate_complement {n : ℕ} (J : Interaction n) (hd : ∀ i, J i i = 0)
    (i : Fin n) (x : Spin n) : flipRate J (flip x i) i = 1 - flipRate J x i := by
  simp only [flipRate, spin_flip_self, mean_flip J hd]
  ring

lemma flipRate_eq_mass {n : ℕ} (J : Interaction n)
    (hJ : ∀ i k, J i k = J k i) (hd : ∀ i, J i i = 0)
    (i : Fin n) (x : Spin n) :
    flipRate J x i = gibbs J (flip x i) / (gibbs J x + gibbs J (flip x i)) := by
  apply (eq_div_iff (ne_of_gt (add_pos (gibbs_pos J x) (gibbs_pos J (flip x i))))).2
  have hb := gibbs_detailed_balance J hJ hd x i
  rw [flipRate_complement J hd] at hb
  nlinarith only [hb]

lemma pairConditional_residual {n : ℕ} (J : Interaction n)
    (hJ : ∀ i k, J i k = J k i) (hd : ∀ i, J i i = 0)
    (i : Fin n) (f : Observables n) (x : Spin n) :
    f x - pairConditional J i f x = flipRate J x i * (f x - f (flip x i)) := by
  rw [flipRate_eq_mass J hJ hd]
  unfold pairConditional
  field_simp [ne_of_gt (add_pos (gibbs_pos J x) (gibbs_pos J (flip x i)))]
  ring

lemma conditional_variance_projection {n : ℕ} (J : Interaction n)
    (i : Fin n) (f : Observables n) :
    (∑ x, gibbs J x * (f x - pairConditional J i f x) ^ 2) =
      ∑ x, gibbs J x * f x * (f x - pairConditional J i f x) := by
  let l : Observables n := fun x => gibbs J x * (f x - pairConditional J i f x) ^ 2
  let r : Observables n := fun x => gibbs J x * f x * (f x - pairConditional J i f x)
  have hp (x : Spin n) : l x + l (flip x i) = r x + r (flip x i) := by
    dsimp only [l, r]
    rw [pairConditional_flip]
    simp only [pairConditional]
    field_simp [ne_of_gt (add_pos (gibbs_pos J x) (gibbs_pos J (flip x i)))]
    ring
  have hh := congrArg (fun u : Observables n => ∑ x, u x) (funext hp)
  simp only [Finset.sum_add_distrib, sum_flip] at hh
  change (∑ x, l x) = ∑ x, r x
  linarith

theorem dirichlet_zero {n : ℕ} (g : SKGap.Disorder n) (f : Observables n) :
    SKGap.dirichlet g 0 f = dirichlet (edgeInteraction g) f f := by
  simp only [SKGap.dirichlet, expectation_zero, conditionalExpectation_zero, gibbsExpectation]
  simp_rw [conditional_variance_projection,
    pairConditional_residual (edgeInteraction g) (coupling_symmetric g) (coupling_diagonal g)]
  simp_rw [gibbs_edge_dirichlet (edgeInteraction g) (coupling_symmetric g) (coupling_diagonal g)]
  simp only [dirichlet, gibbsExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measurePreserving_restrictUpper (β : ℝ) (n : ℕ) :
    MeasurePreserving (restrictUpper (n := n)) (disorderLaw β n) (SKGap.disorderLaw β n) := by
  let μ : (Fin n × Fin n) → Measure ℝ := fun _ =>
    gaussianReal 0 (Real.toNNReal (β ^ 2 / (n : ℝ)))
  have h := measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd μ (fun e : Fin n × Fin n => e.1 < e.2))
  change MeasurePreserving (fun g : Fin n × Fin n → ℝ => fun e : SKGap.Edge n => g e.val)
    (Measure.pi μ) (Measure.pi (fun e : SKGap.Edge n => μ e.val))
  simpa only [MeasurableEquiv.piEquivPiSubtypeProd_apply, Function.comp_def] using h

lemma continuous_coupling (n : ℕ) : Continuous (edgeInteraction (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  change Continuous (fun g : SKGap.Disorder n => SKGap.coupling g i k)
  by_cases hik : i < k
  · simp only [SKGap.coupling, dite_eq_left hik]
    exact continuous_apply _
  · simp only [SKGap.coupling, dite_eq_right hik]
    by_cases hki : k < i
    · simp only [dite_eq_left hki]
      exact continuous_apply _
    · simp only [dite_eq_right hki]
      exact continuous_const

lemma poincare_iff_hasGap {n : ℕ} (g : SKGap.Disorder n) {C : ℝ} (hC : 0 < C) :
    g ∈ SKGap.poincareEvent n C ↔ HasGap (edgeInteraction g) (1 / C) := by
  simp only [SKGap.poincareEvent, Set.mem_ofPred_eq, HasGap, variance_zero, dirichlet_zero]
  apply forall_congr'
  intro f
  rw [show (1 / C) * gibbsVariance (edgeInteraction g) f =
    gibbsVariance (edgeInteraction g) f / C by ring, div_le_iff₀ hC, mul_comm]

lemma measurableSet_poincareEvent (n : ℕ) {C : ℝ} (hC : 0 < C) :
    MeasurableSet (SKGap.poincareEvent n C) := by
  have he : SKGap.poincareEvent n C =
      edgeInteraction ⁻¹' {J : Interaction n | HasGap J (1/C)} := by
    ext g
    exact poincare_iff_hasGap g hC
  rw [he]
  exact ((isClosed_hasGap (1/C)).preimage (continuous_coupling n)).measurableSet

theorem probability_poincare_eq (β : ℝ) (n : ℕ) {C : ℝ} (hC : 0 < C) :
    (SKGap.disorderLaw β n) (SKGap.poincareEvent n C) =
      (disorderLaw β n) {g | HasGap (sampledInteraction g) (1/C)} := by
  rw [← (measurePreserving_restrictUpper β n).measure_preimage
    (measurableSet_poincareEvent n hC).nullMeasurableSet]
  congr 1
  ext g
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, edgeInteraction_restrictUpper] using
    poincare_iff_hasGap (restrictUpper g) hC

theorem quenchedGap_iff_edgePoincare (β : ℝ) : QuenchedGap β ↔
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n => SKGap.disorderLaw β n (SKGap.poincareEvent n C))
      atTop (nhds 1) := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨1/γ, one_div_pos.mpr hγ, ?_⟩
    have he (n : ℕ) : SKGap.disorderLaw β n (SKGap.poincareEvent n (1/γ)) =
        disorderLaw β n {g | HasGap (sampledInteraction g) γ} := by
      simpa only [one_div_one_div] using probability_poincare_eq β n (one_div_pos.mpr hγ)
    simpa only [he] using h
  · rintro ⟨C, hC, h⟩
    refine ⟨1/C, one_div_pos.mpr hC, ?_⟩
    simpa only [probability_poincare_eq β _ hC] using h

end GapBridge
end SKGapCutoff
end
end

end OAI
