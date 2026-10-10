import Mathlib
import OAI.Probability.Perceptron.Variational.LabelValue
import OAI.Probability.Perceptron.Variational.LabelRestorationMoments
import OAI.Probability.Perceptron.Variational.BoundedLeafRestoration
import OAI.Probability.Perceptron.Interpolation.TripleGaussianReplica

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev labelGaussianStep {k : ℕ} (q : Fin (k+1)→ℝ) :=
  fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j)
abbrev labelGaussianRoot {k : ℕ} (q : Fin (k+1)→ℝ) :=
  diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l))
def labelEvaluation (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) x

def labelResidualObservable (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) : EuclideanSpace ℝ (Fin 1)→ℝ :=
  fun x => residualResponse s f v (labelEvaluation x)

lemma labelProfileField_leaf {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    labelProfileField q g x=labelEvaluation (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) g x.2) :=
  labelProfileField_marked_state q g x

lemma labelResidualObservable_measurable (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) :
    Measurable (labelResidualObservable s f v) :=
  (residualResponse_continuous s f v).measurable.comp (by unfold labelEvaluation; fun_prop)

lemma labelResidualObservable_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    |labelResidualObservable s f v x|≤‖v‖ := residualResponse_bound s f v _

variable {S K : Type} [MeasurableSpace S] [Fintype K]

lemma labelRestorationPair_eq_terminal (μ : Measure S) [IsProbabilityMeasure μ]
    (k : ℕ) (b : IndexedCascadeBase k) (J : S×IndexedLeaf k→ℝ) (hJ : Measurable J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) (F : EuclideanSpace ℝ K→ℝ)
    (hF : Measurable F) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun x => Real.exp (J x)) (μ.prod (indexedLeafProbability k b)))
    (hp : ∀ l, (∫ x, Real.exp (J (x,l)) ∂μ)=Real.exp (F (gaussianLeafValue k C T t.2 l)))
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    gibbsReplicaMean (μ.prod (indexedLeafProbability k b)) J 2
      (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
        (fun xs => if indexedCommonDepth k (xs 0).2 (xs 1).2=d then 1 else 0) t.1) /
      (tiltMean (μ.prod (indexedLeafProbability k b)) J (labelRestorationWeight q s g.f t.1) 1)^2 =
    tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) C
      (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F d
      (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k b t) := by
  let G : IndexedLeaf k→ℝ := fun l => F (gaussianLeafValue k C T t.2 l)
  let W : IndexedLeaf k→ℝ := fun l =>
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)+
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l)
  let O : (Fin 2→IndexedLeaf k)→ℝ := fun l => if indexedCommonDepth k (l 0) (l 1)=d then
    (labelResidualObservable s g.f v (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 (l 0))*
      labelResidualObservable s g.f w (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 (l 0)))*
    (labelResidualObservable s g.f v (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 (l 1))*
      labelResidualObservable s g.f w (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 (l 1))) else 0
  have hW (l) : W l≤2*‖g.f‖ := by
    dsimp only [W]
    linarith [(le_abs_self _).trans (labelProfileTerminal_bound g s
      (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)),
      (le_abs_self _).trans (labelProfileTerminal_bound g s
      (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l))]
  have hiG : Integrable (fun l => Real.exp (G l)) (indexedLeafProbability k b) := by
    simpa only [hp,G] using hi.integral_prod_right
  have hiGW := exp_add_integrable_of_bound _ hiG (measurable_of_countable W) hW
  have hie : Integrable (fun l => Real.exp (
    (labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)+
      labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l))+
      F (gaussianLeafValue k C T t.2 l))) (indexedLeafProbability k b) := by
    convert hiGW using 1
    funext l
    congr 1
    exact add_comm _ _
  rw [←labelRestoration_ratio q s g.f (fun _ : Fin 2 => v) (fun _ => w)
    (μ.prod (indexedLeafProbability k b)) J hJ hi _ t.1]
  have he := product_leaf_restore μ (indexedLeafProbability k b) J G W hJ
    (measurable_of_countable G) (measurable_of_countable W) hi hp hW 2 O (measurable_of_countable O)
  have hr := tripleGaussianPair_replica k (labelGaussianStep q) (labelGaussianStep q) C
    (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F
    (labelProfileTerminal_lipschitz g s).continuous.measurable
    (labelProfileTerminal_lipschitz g s).continuous.measurable hF d
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w) b t hie
  rw [hr]
  refine (gibbsReplicaMean_congr _ _ _ ?_ 2 _ _ ?_).trans (he.trans ?_)
  · intro x
    simp only [labelProfileField_leaf,W,labelProfileTerminal,labelEvaluation]
  · intro xs
    simp only [Fin.prod_univ_two,labelProfileField_leaf,O,labelResidualObservable]
    split_ifs <;> ring
  · apply gibbsReplicaMean_congr
    · intro l; exact add_comm _ _
    · intro l; rfl

def labelPairCoefficient (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) (d : Fin (k+1)) : ℝ :=
  rootPathCorrelation (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k
    (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
      (gaussianLinearMarkStep (labelGaussianStep q)) (z i)
      (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
        (gaussianLinearMarkStep (labelGaussianStep q)) k z (fun x => labelProfileTerminal g s (x 0)) i))
    (fun x => labelResidualObservable s g.f v (x 0)) d

def sourceLabelPairRatio (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (enrichedIndexedBaseMeasure n k t.1)
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) 2
    (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
      (fun xs => if indexedCommonDepth k (xs 0).2 (xs 1).2=d then 1 else 0) t.2.1) /
    (tiltMean (enrichedIndexedBaseMeasure n k t.1)
      (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) (labelRestorationWeight q s g.f t.2.1) 1)^2

lemma enrichedIndexedHamiltonian_joint_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p e : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (Function.uncurry (enrichedIndexedHamiltonian n M k f a p e h u)) := by
  unfold enrichedIndexedHamiltonian
  exact countableGaussianHamiltonian_measurable (enrichedIndexedBoundedEnergy_measurable n M k f a h)
    (sourceGaussianRow_measurable p e h u) (indexedGaussianRowLength_measurable (I:=EnrichedIndex (n+1) (n+1) p) k)

lemma sourceLabelPair_exp_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) :
    ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
      Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p e h u t.2.2 x))
        (enrichedIndexedBaseMeasure n k t.1) := by
  let D := IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
  let κ : Kernel D (NormalizedSpin (n+1)×IndexedLeaf k) :=
    (Kernel.const D (unitSphereLaw (n+1))).prod ((indexedLeafKernel k).comap Prod.fst measurable_fst)
  have hκ (t : D) : κ t=enrichedIndexedBaseMeasure n k t.1 := by
    rw [Kernel.prod_apply]; rfl
  let H : D→NormalizedSpin (n+1)×IndexedLeaf k→ℝ :=
    fun t => enrichedIndexedHamiltonian n M k f a p e h u t.2.2
  have hbase := enrichedIndexedHamiltonian_joint_measurable n M k f a p e h u
  have ht : Measurable (fun p : D×(NormalizedSpin (n+1)×IndexedLeaf k) => (p.1.2.2,p.2)) :=
    measurable_fst.snd.snd.prodMk measurable_snd
  have hc := hbase.comp ht
  have hH : Measurable (Function.uncurry H) := hc
  have hm : MeasurableSet {t : D | Integrable (fun x => Real.exp (H t x)) (κ t)} :=
    measurableSet_kernel_integrable (κ:=κ) (f:=fun t x => Real.exp (H t x)) hH.exp.stronglyMeasurable
  have hi : ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
      Integrable (fun x => Real.exp (H t x)) (κ t) := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    refine ae_of_all _ fun b => ?_
    have hi := (measurePreserving_snd (μ:=countableGaussianLaw.prod countableGaussianLaw)
      (ν:=countableGaussianLaw)).quasiMeasurePreserving.ae
      (enrichedIndexedHamiltonian_exp_ae n M k f a p e h hh0 hh u b)
    simpa only [hκ,H] using hi
  simpa only [hκ,H] using hi

lemma sourceLabelPairRatio_eq_triple (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)))
    (hi : Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p e h u t.2.2 x))
      (enrichedIndexedBaseMeasure n k t.1)) :
    sourceLabelPairRatio n M k f a p e h u q g s d v w t =
      tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k))) d
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  have hbase := enrichedIndexedHamiltonian_joint_measurable n M k f a p e h u
  have hmJ : Measurable (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) :=
    hbase.of_uncurry_left
  have he := labelRestorationPair_eq_terminal (unitSphereLaw (n+1)) k t.1
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) hmJ
    (enrichedIncrementMap p e h) (enrichedRootMap p e h) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))).continuous.measurable t.2 hi
    (enrichedIndexedHamiltonian_leaf_partition n M k f a p e h u t.2.2) q g s d v w
  exact he

lemma sourceLabelPairRatio_eq_triple_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (_hz : StrictMono z) (_hz0 : ∀ i, 0<z i) (_hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
    sourceLabelPairRatio n M k f a p e h u q g s d v w t =
      tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k))) d
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  filter_upwards [sourceLabelPair_exp_ae n M k f a p e h hh0 hh u z] with t ht
  exact sourceLabelPairRatio_eq_triple n M k f a p e h u q g s d v w t ht

lemma sourceLabelPairRatio_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    (∫ t, sourceLabelPairRatio n M k f a p e h u q g s d v w t
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal * (labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
  have he := countable_three_terminal_pair_value k z hz hz0 hz1
    (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
    (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
    (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (labelProfileTerminal_lipschitz g s) (labelProfileTerminal_lipschitz g s)
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))) d
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
    (labelResidualObservable_measurable s g.f v) (labelResidualObservable_measurable s g.f w)
    ‖v‖ ‖w‖ (norm_nonneg _) (norm_nonneg _)
    (labelResidualObservable_bound s g.f v) (labelResidualObservable_bound s g.f w)
  exact (integral_congr_ae (sourceLabelPairRatio_eq_triple_ae n M k f a p e h hh0 hh u z hz hz0 hz1 q g s d v w)).trans he

end SphericalPerceptronFreeEnergy
end

end OAI
