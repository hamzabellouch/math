import Mathlib
import OAI.Probability.Perceptron.Variational.CompactRestorationWitness
import OAI.Probability.Perceptron.Variational.CountableSingleRestoration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S K : Type} [MeasurableSpace S] [Fintype K]

lemma labelRestorationSingle_eq_terminal (μ : Measure S) [IsProbabilityMeasure μ]
    (k : ℕ) (b : IndexedCascadeBase k) (J : S×IndexedLeaf k→ℝ) (hJ : Measurable J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) (F : EuclideanSpace ℝ K→ℝ)
    (hF : Measurable F) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun x => Real.exp (J x)) (μ.prod (indexedLeafProbability k b)))
    (hp : ∀ l, (∫ x, Real.exp (J (x,l)) ∂μ)=Real.exp (F (gaussianLeafValue k C T t.2 l)))
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) :
    gibbsReplicaMean (μ.prod (indexedLeafProbability k b)) J 1
      (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
        (fun _ => 1) t.1) /
      (tiltMean (μ.prod (indexedLeafProbability k b)) J (labelRestorationWeight q s g.f t.1) 1)^1 =
    tripleGaussianMean k (labelGaussianStep q) (labelGaussianStep q) C
      (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F
      (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k b t) := by
  let G : IndexedLeaf k→ℝ := fun l => F (gaussianLeafValue k C T t.2 l)
  let W : IndexedLeaf k→ℝ := fun l =>
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)+
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l)
  let O : (Fin 1→IndexedLeaf k)→ℝ := fun l =>
    labelResidualObservable s g.f v (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 (l 0))*
      labelResidualObservable s g.f w (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 (l 0))
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
  rw [←labelRestoration_ratio q s g.f (fun _ : Fin 1 => v) (fun _ => w)
    (μ.prod (indexedLeafProbability k b)) J hJ hi _ t.1]
  have he := product_leaf_restore μ (indexedLeafProbability k b) J G W hJ
    (measurable_of_countable G) (measurable_of_countable W) hi hp hW 1 O (measurable_of_countable O)
  have hr := tripleGaussianMean_replica k (labelGaussianStep q) (labelGaussianStep q) C
    (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F
    (labelProfileTerminal_lipschitz g s).continuous.measurable
    (labelProfileTerminal_lipschitz g s).continuous.measurable hF
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w) b t hie
  rw [hr]
  refine (gibbsReplicaMean_congr _ _ _ ?_ 1 _ _ ?_).trans (he.trans ?_)
  · intro x
    simp only [labelProfileField_leaf,W,labelProfileTerminal,labelEvaluation]
  · intro xs
    simp only [Fin.prod_univ_one,labelProfileField_leaf,O,labelResidualObservable]
    ring
  · apply gibbsReplicaMean_congr
    · intro l; exact add_comm _ _
    · intro l; rfl

def sourceLabelSingleRatio (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (enrichedIndexedBaseMeasure n k t.1)
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) 1
    (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
      (fun _ => 1) t.2.1) /
    (tiltMean (enrichedIndexedBaseMeasure n k t.1)
      (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) (labelRestorationWeight q s g.f t.2.1) 1)^1

lemma sourceLabelSingleRatio_eq_triple (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)))
    (hi : Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p e h u t.2.2 x))
      (enrichedIndexedBaseMeasure n k t.1)) :
    sourceLabelSingleRatio n M k f a p e h u q g s v w t =
      tripleGaussianMean k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k)))
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  have hbase := enrichedIndexedHamiltonian_joint_measurable n M k f a p e h u
  have hmJ : Measurable (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) :=
    hbase.of_uncurry_left
  have he := labelRestorationSingle_eq_terminal (unitSphereLaw (n+1)) k t.1
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) hmJ
    (enrichedIncrementMap p e h) (enrichedRootMap p e h) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))).continuous.measurable t.2 hi
    (enrichedIndexedHamiltonian_leaf_partition n M k f a p e h u t.2.2) q g s v w
  exact he

lemma sourceLabelSingleRatio_eq_triple_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (_hz : StrictMono z) (_hz0 : ∀ i, 0<z i) (_hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) :
    ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
    sourceLabelSingleRatio n M k f a p e h u q g s v w t =
      tripleGaussianMean k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k)))
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  filter_upwards [sourceLabelPair_exp_ae n M k f a p e h hh0 hh u z] with t ht
  exact sourceLabelSingleRatio_eq_triple n M k f a p e h u q g s v w t ht

lemma sourceLabelSingleRatio_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) :
    (∫ t, sourceLabelSingleRatio n M k f a p e h u q g s v w t
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      labelSingleCoefficient k z q g s v*labelSingleCoefficient k z q g s w := by
  have he := countable_three_terminal_single_value k z hz hz0 hz1
    (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
    (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
    (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (labelProfileTerminal_lipschitz g s) (labelProfileTerminal_lipschitz g s)
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k)))
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
    (labelResidualObservable_measurable s g.f v) (labelResidualObservable_measurable s g.f w)
    ‖v‖ ‖w‖ (norm_nonneg _) (norm_nonneg _)
    (labelResidualObservable_bound s g.f v) (labelResidualObservable_bound s g.f w)
  exact (integral_congr_ae (sourceLabelSingleRatio_eq_triple_ae n M k f a p e h hh0 hh u z hz hz0 hz1 q g s v w)).trans he

end SphericalPerceptronFreeEnergy
end

end OAI
