import OAI.Probability.DilutedSpin.CavityProxy
import OAI.Probability.DilutedSpin.CenteredTrialLocal
import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.TrialPhysical

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal

lemma cavityProxy_envelope {p : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) :
    |cavityProxy M C H N L u-Real.log 2| ≤ H+C*(M.alpha*p:ℝ≥0)+C*(M.alpha*(p-1:ℕ):ℝ≥0) := by
  have hs : |insertionPoisson M C H N L u
      (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
      (fun _ z => cavitySiteEnergy z.1 z.2) (M.alpha*p)| ≤ H+C*(M.alpha*p:ℝ≥0) := by
    apply poisson_average_bound
    intro k
    exact abs_integral_le_bound_ae _ ((cavitySiteEnergy_ae_bound (k := k) M hθ hh).mono
      (fun z hz => reservoirInsertionOn_bound M C H N L u _ hz))
  have hb : |insertionPoisson M C H N L u
      (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (fun _ θ => cavityBondEnergy θ) (M.alpha*(p-1:ℕ))| ≤ 0+C*(M.alpha*(p-1:ℕ):ℝ≥0) := by
    apply poisson_average_bound
    intro k
    exact abs_integral_le_bound_ae _ ((cavityBondEnergy_ae_bound (k := k) M hθ).mono
      (fun z hz => reservoirInsertionOn_bound M C H N L u _ hz))
  have hx := (abs_sub _ _).trans (add_le_add hs hb)
  convert hx using 1 <;> first | rfl | (dsimp [cavityProxy]; congr 1; ring)

lemma cavityProxy_functional_bound {p : ℕ} (M : Model p) {C H : ℝ}
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure,‖z.1‖≤C) (hh : ∀ᵐ h ∂M.field.toMeasure,|h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (N L : ℕ) (u : Spec L×ℕ → ℝ) :
    |cavityProxy M C H N L u-functional M L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc)| ≤
      (H+C*(M.alpha*p:ℝ≥0)+C*(M.alpha*(p-1:ℕ):ℝ≥0))+functionalEnvelope M := by
  simpa only [sub_sub_sub_cancel_right] using
    (abs_sub (cavityProxy M C H N L u-Real.log 2)
      (functional M L (reservoirTrialLaw M C H N L u) (fun i => gridExponents L i.castSucc)-Real.log 2)).trans
      (add_le_add (cavityProxy_envelope M hθ hh N L u)
        (functional_envelope M hθi hhi _ _ (fun i => gridExponents_pos L i.castSucc)))

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma trialSiteField_center {p r k : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    trialSiteField (centeredModel M) m ζ (fun j => centerSample (θ j))=
      trialSiteField M m ζ θ-∑ j,referenceEnergy (θ j) := by
  rw [centeredModel,trialSiteField_map_eq M m hm]
  simp only [id_eq,trial_site_center θ _ m hm]
  rw [integral_sub (integrable_trial_site_field M m hm hh ζ θ) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,trialSiteField]

lemma trialSiteDisorder_center {p r : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    trialSiteDisorder (centeredModel M) m ζ k= trialSiteDisorder M m ζ k-
      (k:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  rw [centeredModel,trialSiteDisorder_map_eq M m hm]
  change (∫ θ : Fin k → InteractionSample p,trialSiteField (centeredModel M) m ζ (fun j => centerSample (θ j))
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=_
  simp_rw [trialSiteField_center M m hm ζ hh]
  rw [integral_sub (integrable_trialSiteField M m hm hθ hh ζ k)
    (integrable_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)),
    integral_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)]
  simp only [Fintype.card_fin,trialSiteDisorder]

lemma trialEdge_center {p r : ℕ} (M : Model p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(centeredModel M).disorder.toMeasure)=
      (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure)-
      ∫ z,referenceEnergy z ∂M.disorder.toMeasure := by
  change (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map centerSample M.disorder.toMeasure)=_
  have heq : (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map centerSample M.disorder.toMeasure)=
      ∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge (centerSample z).1 x)) ∂M.disorder.toMeasure :=
    integral_map (measurable_centerSample p).aemeasurable
      (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  rw [heq]
  simp_rw [trial_edge_center _ m hm ζ]
  apply integral_sub _ (referenceEnergy_integrable M hθ)
  apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ z.1)

lemma functional_center {p r : ℕ} (M : Model p) (hp : 1 ≤ p) (m : Fin r → ℝ)
    (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1))
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    functional (centeredModel M) r ζ m=functional M r ζ m-
      (M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  have hsi : Integrable (trialSiteDisorder M m ζ) (poissonMeasure (M.alpha*p)) := by
    apply ((integrable_const _).add ((poisson_integrable_count _).mul_const _)).mono'
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_def,Pi.mul_def] using trialSiteDisorder_bound M m hm hθ hh ζ k)
  change Real.log 2+(∫ k,trialSiteDisorder (centeredModel M) m ζ k ∂poissonMeasure (M.alpha*p))-
    (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(centeredModel M).disorder.toMeasure)=_
  simp_rw [trialSiteDisorder_center M m hm ζ hθ hh]
  rw [integral_sub hsi ((poisson_integrable_count _).mul_const _),integral_mul_const,poisson_mean,
    trialEdge_center M m hm ζ hθ]
  simp only [NNReal.coe_mul,NNReal.coe_natCast,Nat.cast_sub hp,Nat.cast_one,functional,trialSiteDisorder,trialSiteField]
  ring
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
local instance upperTrialMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance upperTrialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
namespace KernelTower
variable {Ω : Type} [Fintype Ω]
omit [Fintype Ω] in
lemma pathMap_pathPrefix {Λ : Type} (g : Ω → Λ) (n : ℕ) (y : FinitePath Ω (n+1)) :
    pathMap g n (pathPrefix n y)=pathPrefix n (pathMap g (n+1) y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (g y.1,pathMap g n (pathPrefix n y.2))=(g y.1,pathPrefix n (pathMap g (n+1) y.2))
      rw [ih]

lemma piTower_eq_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) : piTower n T=pi n T := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (_,fun (x : ι → Ω) => piTower n (fun i => (T i).2 (x i)))=(_,fun (x : ι → Ω) => pi n (fun i => (T i).2 (x i)))
      congr 1
      funext x
      exact ih _

lemma piTower_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    piTower (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (piTower n T) := by
  induction n with
  | zero =>
      change (FiniteLaw.pi (fun _ : ι => FiniteLaw.point a),fun _ => ())=(FiniteLaw.point (fun _ : ι => a),fun _ => ())
      rw [FiniteLaw.pi_point]
  | succ n ih =>
      change (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => piTower (n+1) (fun i => pad a n ((T i).2 (x i))))=
        (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => pad (fun _ : ι => a) n (piTower n (fun i => (T i).2 (x i))))
      congr 1
      funext x
      exact ih _

omit [Fintype Ω] in
lemma proj_eq_pathMap {ι : Type} (n : ℕ) (y : FinitePath (ι → Ω) n) (i : ι) :
    FinitePath.proj n y i=pathMap (fun a : ι → Ω => a i) n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (y.1 i,FinitePath.proj n y.2 i)=(y.1 i,pathMap (fun a : ι → Ω => a i) n y.2)
      rw [ih]
end KernelTower

namespace PrescribedTree
variable {Λ R : Type} [Fintype Λ] [Fintype R]
noncomputable def finiteTrialLaw (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) : Hierarchy (r+1) :=
  Q.asProbability (fun a => KernelTower.realEncode r (U a) (x a))

lemma finite_trialLog {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (F : (ι → ℝ) → ℝ) :
    trialLog r (finiteTrialLaw r Q U x) m F =
      (FiniteLaw.pi (fun _ : ι => Q)).expect (fun a =>
        KernelTower.backwardLog r (KernelTower.piTower r (fun i => U (a i))) m
          (fun y => F (fun i => x (a i) (KernelTower.pathMap (fun b : ι → Λ => b i) r y)))) := by
  unfold trialLog finiteTrialLaw
  rw [FiniteLaw.integral_pi_asProbability]
  apply FiniteLaw.expect_congr
  intro a
  rw [KernelTower.piTower_eq_pi]
  exact (KernelTower.backwardLog_realEncode r (fun i => U (a i)) (fun i => x (a i)) F m).symm.trans
    (by congr 1; funext y; simp only [KernelTower.proj_eq_pathMap])

lemma edgeRoot_pad (r : ℕ) (a : Λ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)≠0)
    {p : ℕ} (z : InteractionSample p) :
    edgeRoot (Λ := Λ) (R := R) (n := r+1) (p := p) Q (fun b : R => KernelTower.pad a r (U b))
      (fun (b : R) (y : FinitePath Λ (r+1)) => x b (KernelTower.pathPrefix r y)) m z =
      trialLog (ι := Fin p) r (finiteTrialLaw r Q U x) (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y)) := by
  refine Eq.trans ?_ (finite_trialLog r Q U x (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y))).symm
  change (FiniteLaw.pi (fun _ : Fin p => Q)).expect _ =
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect _
  apply FiniteLaw.expect_congr
  intro b
  rw [KernelTower.piTower_pad a r (fun i : Fin p => U (b i))]
  have he (y : FinitePath (Fin p → Λ) (r+1)) :
      (fun j => x (b j) (KernelTower.pathPrefix r (KernelTower.pathMap (fun a : Fin p → Λ => a j) (r+1) y)))=
      (fun j => x (b j) (KernelTower.pathMap (fun a : Fin p → Λ => a j) r (KernelTower.pathPrefix r y))) := by
    funext j
    rw [KernelTower.pathMap_pathPrefix]
  simp only [he]
  exact KernelTower.backwardLog_pad (fun _ : Fin p => a) r
    (KernelTower.piTower r (fun i : Fin p => U (b i))) m hend
    (fun y : FinitePath (Fin p → Λ) r => Real.log (edge z.1
      (fun j => x (b j) (KernelTower.pathMap (fun c : Fin p → Λ => c j) r y))))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
