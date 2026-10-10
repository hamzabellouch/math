import OAI.Probability.DilutedSpin.ClippedModelFacts
import OAI.Probability.DilutedSpin.FinitePoissonSplit
import OAI.Probability.DilutedSpin.InsertionStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E X A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace X] [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]

lemma finite_poisson_deletion (r : ℝ≥0) (good : A → Prop) [DecidablePred good]
    (V : X×A → E) (hV : Measurable V) {D : ℝ} (hD : 0≤D) (hbound : ∀ z,‖V z‖≤D)
    {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r (Measure.map V (μ.prod (finiteUniform A))))-
      (∫ x, f x ∂compoundPoisson r (Measure.map (fun z : X×A => if good z.2 then V z else 0)
        (μ.prod (finiteUniform A))))| ≤
      C*r*(D/(Fintype.card A)*(∑ a : A,if good a then (0:ℝ) else 1)) := by
  let W : X×A → E := fun z => if good z.2 then V z else 0
  have hW : Measurable W := hV.ite
    ((Set.to_countable {a | good a}).measurableSet.preimage measurable_snd) measurable_const
  let J : X×A → E×E := fun z => (V z,W z)
  have hJ : Measurable J := hV.prodMk hW
  have hWb (z : X×A) : ‖W z‖≤D := by dsimp [W]; split <;> simp_all
  have hJb (z : X×A) : ‖J z‖≤D := by
    change max ‖V z‖ ‖W z‖ ≤ D
    exact max_le (hbound z) (hWb z)
  let ξ := Measure.map J (μ.prod (finiteUniform A))
  let : IsProbabilityMeasure ξ :=
    (Measure.isProbabilityMeasure_map_iff hJ.aemeasurable).mpr inferInstance
  have hJi : Integrable id ξ := by
    rw [integrable_map_measure aestronglyMeasurable_id hJ.aemeasurable]
    exact Integrable.of_bound hJ.aestronglyMeasurable D (Filter.Eventually.of_forall hJb)
  have hh := compoundPoisson_lipschitz_coupling r ξ hJi hf
  have h1 : Measure.map Prod.fst ξ = Measure.map V (μ.prod (finiteUniform A)) := by
    rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,Measure.map_map measurable_fst hJ]
    rfl
  have h2 : Measure.map Prod.snd ξ = Measure.map W (μ.prod (finiteUniform A)) := by
    rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,Measure.map_map measurable_snd hJ]
    rfl
  rw [h1,h2] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show ξ=Measure.map J (μ.prod (finiteUniform A)) from rfl,
    integral_map hJ.aemeasurable (by fun_prop)]
  have hdif : Integrable (fun z : X×A => ‖V z-W z‖) (μ.prod (finiteUniform A)) := by
    apply Integrable.of_bound ((hV.sub hW).norm.aestronglyMeasurable) D
    apply Filter.Eventually.of_forall
    intro z
    change ‖‖V z-W z‖‖≤D
    rw [norm_norm]
    dsimp [W]
    split <;> simp_all
  have hg : Integrable (fun z : X×A => D*(if good z.2 then 0 else 1))
      (μ.prod (finiteUniform A)) := by
    apply Integrable.of_bound ((measurable_of_countable (fun a : A => D*(if good a then (0:ℝ) else 1))).comp measurable_snd).aestronglyMeasurable D
    apply Filter.Eventually.of_forall
    intro z
    change ‖D*(if good z.2 then (0:ℝ) else 1)‖≤D
    split_ifs <;> simp [abs_of_nonneg hD,hD]
  calc
    _ ≤ ∫ z : X×A, D*(if good z.2 then 0 else 1) ∂μ.prod (finiteUniform A) := by
      apply integral_mono hdif hg
      intro z
      dsimp [J,W]
      split_ifs <;> simp_all
    _ = _ := by
      rw [integral_prod_symm _ hg]
      change (∫ a : A, (∫ _x : X, D*(if good a then (0:ℝ) else 1) ∂μ) ∂finiteUniform A) = _
      simp only [integral_const,probReal_univ,one_smul]
      rw [integral_finiteUniform]
      simp only [smul_eq_mul,Finset.mul_sum]
      ring_nf

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def rawReplicaMoment {p n : ℕ} (M : Model p)
    (P : Fin p → FiniteLaw (Fin n → Spin)) : ℝ :=
  ∫ z : InteractionSample p, (FiniteLaw.pi P).expect
    (fun s => ∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,z.2.2.2 l (s l a)) ∂M.disorder.toMeasure

lemma replicaInsertionMoment_eq {p n : ℕ} (M : Model p) (R : ℝ)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    replicaInsertionMoment M R P =
      ∫ z : InteractionSample p,(FiniteLaw.pi P).expect
        (fun s => ∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) ∂M.disorder.toMeasure := by
  unfold replicaInsertionMoment
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro s
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma factorCut_eventually (f : Spin → ℝ) :
    ∀ᶠ R : ℕ in atTop,factorCut (R:ℝ) f=f := by
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually (eventually_ge_atTop ‖f‖)] with R hR
  simp [factorCut,hR]

lemma rawReplicaMoment_limit {p n : ℕ} (M : Model p) (hM : Admissible M)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    Tendsto (fun R : ℕ => replicaInsertionMoment M (R:ℝ) P) atTop (𝓝 (rawReplicaMoment M P)) := by
  simp_rw [replicaInsertionMoment_eq]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · intro R
    apply Measurable.aestronglyMeasurable
    unfold FiniteLaw.expect
    apply Finset.measurable_sum
    intro s _
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro a _
    apply Measurable.mul (by fun_prop)
    exact Finset.measurable_prod _ (fun l _ => (measurable_pi_apply (s l a)).comp
      ((measurable_factorCut (R:ℝ)).comp (by fun_prop)))
  · exact integrable_const _
  · intro R
    filter_upwards [hM.factorization] with z hz
    rw [Real.norm_eq_abs]
    apply FiniteLaw.abs_expect_le
    intro s
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro a _
    rw [show (-z.2.2.1)*(∏ l,factorCut (R:ℝ) (z.2.2.2 l) (s l a)) =
      -(z.2.2.1*(∏ l,factorCut (R:ℝ) (z.2.2.2 l) (s l a))) by ring,abs_neg]
    exact (factorCut_product_lt_one (R:ℝ) z.2.2.1 z.2.2.2 (fun s => (hz.2 s).2) _).le
  · exact ae_of_all _ (fun z => by
      have he : ∀ᶠ R : ℕ in atTop,∀ l : Fin p,factorCut (R:ℝ) (z.2.2.2 l)=z.2.2.2 l :=
        Filter.eventually_all.mpr (fun l => factorCut_eventually (z.2.2.2 l))
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with R hR
      simp only [hR])

/-- Removing the coordinate cutoff uses only the original uniform product
bound. No additional moments of individual factors are assumed. -/
lemma rawReplica_combination_nonneg {p n : ℕ} (M : Model p) (hM : Admissible M)
    (hn : 1≤n) (j : Fin p) (P B : FiniteLaw (Fin n → Spin)) :
    0 ≤ rawReplicaMoment M (fun _ : Fin p => P) -
      (p:ℝ)*rawReplicaMoment M (fun l : Fin p => if l=j then P else B) +
      ((p-1:ℕ):ℝ)*rawReplicaMoment M (fun _ : Fin p => B) := by
  have hlim := ((rawReplicaMoment_limit M hM (fun _ : Fin p => P)).sub
    ((rawReplicaMoment_limit M hM (fun l : Fin p => if l=j then P else B)).const_mul (p:ℝ))).add
    ((rawReplicaMoment_limit M hM (fun _ : Fin p => B)).const_mul ((p-1:ℕ):ℝ))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun R => by
    rw [replicaInsertion_combination M hM j]
    exact mul_nonneg (hM.positivity n hn) (even_cavity_remainder_nonneg hM.even (by have := hM.arity; omega) _ _))

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma compoundPoisson_dirac_one (r : ℝ≥0) :
    compoundPoisson r (Measure.dirac (1:ℝ)) = Measure.map (fun n : ℕ => (n:ℝ)) (poissonMeasure r) := by
  rw [compoundPoisson,poissonMeasure,Measure.map_sum (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => Measure.dirac (1:ℝ)),∀ i,x i=1 :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => Measure.dirac (1:ℝ)) (i := i)).eventually (show ∀ᵐ x ∂Measure.dirac (1:ℝ),x=1 from by simp))
  rw [Measure.map_congr (ha.mono (fun x hx => show (∑ i,x i)=(n:ℝ) by simp [hx]))]
  simp

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator (r : ℝ≥0) (p : ℕ) [NeZero p] :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  let : IsProbabilityMeasure (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=0 then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
      split_ifs <;> simp
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hpn : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
    rw [hpn]; ring
  rw [hs]
  simp only [Fintype.card_fin,NNReal.coe_div,NNReal.coe_natCast,Complex.ofReal_div,Complex.ofReal_natCast,Complex.real_smul,Complex.ofReal_inv]
  rw [show ((p-1:ℕ):ℂ)=(p:ℂ)-1 by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]]
  field_simp
  ring

noncomputable def successCount {p k : ℕ} [NeZero p] (a : Fin k → Fin p) : ℕ :=
  ∑ i,if a i=0 then 1 else 0

lemma map_poisson_successCount (r : ℝ≥0) (p : ℕ) [NeZero p] :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCount z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator r p]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCount a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=0 then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCount]

end DilutedSpinGlass

end

end OAI
