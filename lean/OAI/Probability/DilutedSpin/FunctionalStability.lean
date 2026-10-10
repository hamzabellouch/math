import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.DilutedSpin.IntegralError
import OAI.Probability.DilutedSpin.MixedPatterns

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
local instance functionalStabilityRootMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance functionalStabilityRootBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
lemma integral_independentInsertion_trialLog (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : ∀ i, 0 < m i) (hend : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i)) :
    (∫ z, independentInsertion T Q m base old V a F z
      ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))) =
      trialLog L (rootEncodingLaw T Q m base old (fun w j => spin (V w j)) hb μ)
        (fun i => m i.castSucc) (FiniteLaw.spinLog F) := by
  let enc := fun z : FullRootState Y X I M × Site N =>
    rootEncoding T Q m base old (fun w j => spin (V w j)) z.1 z.2
  have he : Measurable enc := measurable_rootEncoding_joint T Q m base old _ hb
  have hf : ∀ s, |F s|≤∑ t, |F t| := fun s =>
    Finset.single_le_sum (fun t _ => abs_nonneg (F t)) (Finset.mem_univ s)
  have hc := (logMean_continuous_bound L _ (FiniteLaw.spinLog_continuous F)
    (FiniteLaw.spinLog_bound F hf) (fun i => m i.castSucc) (fun i => hm i.castSucc)).1
  change _ = ∫ η, logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc) η
    ∂Measure.pi (fun _ : Fin a => Measure.map enc (μ.prod (siteLaw N)))
  have hme : Measurable (fun z : Fin a → FullRootState Y X I M × Site N => fun i => enc (z i)) :=
    Measurable.of_eval (fun index => he.comp (measurable_pi_apply index))
  rw [← Measure.pi_map_pi (fun _ : Fin a => he.aemeasurable)]
  rw [integral_map hme.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  exact independentInsertion_encode T Q m base old V a F hend hV z
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma fieldAverage_map_stability {p N k : ℕ} (M : Model p) (hN : 0<N)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    |fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))-fieldAverage (N := N) M θ|≤
      (∑ j,‖(T (θ j)).1-(θ j).1‖)+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
  rw [indexAverage_mapModel]
  let C := ∑ j,‖(T (θ j)).1-(θ j).1‖
  have hfm : Measurable (fun h : Fin N → ℝ => indexAverage (fun j => T (θ j)) (fun i => g (h i))) :=
    ((continuous_indexAverage (p := p) (N := N) (k := k)).comp (continuous_const.prodMk continuous_id)).measurable.comp (Measurable.of_eval (fun index => hg.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hfm.aestronglyMeasurable
    (indexAverage_integrable_and_fieldAverage_bound M hh hN θ).1
    ((integrable_const C).add (integrable_pi_sum M.field.toMeasure hd))
    (ae_of_all _ (fun h => indexAverage_stability hN (fun j => T (θ j)) θ (fun i => g (h i)) h))
  have heq : (∫ h : Fin N → ℝ,C+∑ i,|g (h i)-h i| ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
      C+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
    rw [integral_add (integrable_const C) (integrable_pi_sum M.field.toMeasure hd),integral_pi_sum M.field.toMeasure hd]
    simp
  simpa only [Pi.add_def,heq,fieldAverage] using he.2

lemma disorderAverage_map_eq {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (N k : ℕ) :
    disorderAverage (mapModel M T g hT hg) N k=
      ∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  change (∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure))=_
  exact integral_pi_map _ T hT _ (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable

lemma disorderAverage_map_stability {p N : ℕ} (M : Model p) (hN : 0<N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (k : ℕ) :
    |disorderAverage (mapModel M T g hT hg) N k-disorderAverage M N k|≤
      (k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+(N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure) := by
  rw [disorderAverage_map_eq]
  let d := (N:ℝ)*(∫ h,|g h-h| ∂M.field.toMeasure)
  have hfm : Measurable (fun θ : Fin k → InteractionSample p =>
      fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))) :=
    (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable.comp
      (Measurable.of_eval (fun index => hT.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) hfm.aestronglyMeasurable
    (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).1
    ((integrable_pi_sum M.disorder.toMeasure hD).add (integrable_const d))
    (ae_of_all _ (fieldAverage_map_stability M hN hh T g hT hg hd))
  have heq : (∫ θ : Fin k → InteractionSample p,(∑ j,‖(T (θ j)).1-(θ j).1‖)+d
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=
      (k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+d := by
    rw [integral_add (integrable_pi_sum M.disorder.toMeasure hD) (integrable_const d),integral_pi_sum M.disorder.toMeasure hD]
    simp
  simpa only [Pi.add_def,heq,disorderAverage] using he.2

/-- Uniform first-moment stability of the exact pinned physical pressure. -/
lemma pressure_map_stability {p N : ℕ} (M : Model p) (hN : 0<N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) :
    |pressure (mapModel M T g hT hg) N-pressure M N|≤
      (M.alpha:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+(∫ h,|g h-h| ∂M.field.toMeasure) := by
  let D := ∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have he := integrate_error (poissonMeasure (M.alpha*N)) StronglyMeasurable.of_discrete.aestronglyMeasurable
    (disorderAverage_integrable_and_pressure_bound M hθ hh hN).1
    (((poisson_integrable_count _).mul_const D).add (integrable_const ((N:ℝ)*d)))
    (ae_of_all _ (disorderAverage_map_stability M hN hθ hh T g hT hg hD hd))
  have heq : (∫ k : ℕ,(k:ℝ)*D+(N:ℝ)*d ∂poissonMeasure (M.alpha*N))=(M.alpha:ℝ)*N*D+N*d := by
    rw [integral_add ((poisson_integrable_count _).mul_const D) (integrable_const _),integral_mul_const,poisson_mean]
    simp
  have hb : |(∫ k,disorderAverage (mapModel M T g hT hg) N k ∂poissonMeasure (M.alpha*N))-
      (∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))|≤(M.alpha:ℝ)*N*D+N*d := by
    simpa only [Pi.add_def,Pi.mul_def,heq] using he.2
  change |((∫ k,disorderAverage (mapModel M T g hT hg) N k ∂poissonMeasure (M.alpha*N))/N)-
      ((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))/N)|≤_
  rw [← sub_div,abs_div,abs_of_pos (show (0:ℝ)<N from Nat.cast_pos.mpr hN),div_le_iff₀ (show (0:ℝ)<N from Nat.cast_pos.mpr hN)]
  dsimp [D,d] at hb
  nlinarith

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance functionalStabilityTrialMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance functionalStabilityTrialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma trialSiteField_map_eq {p r k : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (θ : Fin k → InteractionSample p) :
    trialSiteField (mapModel M T g hT hg) m ζ θ =
      ∫ h,trialLog r ζ m (siteLog θ (g h)) ∂M.field.toMeasure := by
  change (∫ h,trialLog r ζ m (siteLog θ h) ∂Measure.map g M.field.toMeasure)=_
  exact integral_map hg.aemeasurable
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)

lemma trialSiteField_map_stability {p r k : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    |trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))-trialSiteField M m ζ θ|≤
      (∫ h,|g h-h| ∂M.field.toMeasure)+∑ j,‖(T (θ j)).1-(θ j).1‖ := by
  rw [trialSiteField_map_eq M m hm]
  have hfm : Measurable (fun h => trialLog r ζ m (siteLog (fun j => T (θ j)) (g h))) :=
    ((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).measurable.comp hg
  have he := integrate_error M.field.toMeasure hfm.aestronglyMeasurable
    (integrable_trial_site_field M m hm hh ζ θ)
    (hd.add (integrable_const (∑ j,‖(T (θ j)).1-(θ j).1‖)))
    (ae_of_all _ (fun h => trial_site_stability r (fun j => T (θ j)) θ (g h) h m hm ζ))
  simpa only [trialSiteField,Pi.add_def,integral_add hd (integrable_const _),integral_const,
    probReal_univ,one_smul] using he.2

lemma trialSiteDisorder_map_eq {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (k : ℕ) :
    trialSiteDisorder (mapModel M T g hT hg) m ζ k =
      ∫ θ : Fin k → InteractionSample p,trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  change (∫ θ : Fin k → InteractionSample p,trialSiteField (mapModel M T g hT hg) m ζ θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure))=_
  exact integral_pi_map _ T hT _ (stronglyMeasurable_trialSiteField (mapModel M T g hT hg) m hm ζ k).measurable

lemma trialSiteDisorder_map_stability {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) (k : ℕ) :
    |trialSiteDisorder (mapModel M T g hT hg) m ζ k-trialSiteDisorder M m ζ k|≤
      (∫ h,|g h-h| ∂M.field.toMeasure)+(k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure) := by
  rw [trialSiteDisorder_map_eq M m hm]
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have hfm : Measurable (fun θ : Fin k → InteractionSample p =>
      trialSiteField (mapModel M T g hT hg) m ζ (fun j => T (θ j))) :=
    (stronglyMeasurable_trialSiteField (mapModel M T g hT hg) m hm ζ k).measurable.comp
      (Measurable.of_eval (fun index => hT.comp (measurable_pi_apply index)))
  have he := integrate_error (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) hfm.aestronglyMeasurable
    (integrable_trialSiteField M m hm hθ hh ζ k)
    ((integrable_const d).add (integrable_pi_sum M.disorder.toMeasure hD))
    (ae_of_all _ (trialSiteField_map_stability M m hm ζ hh T g hT hg hd))
  have heq : (∫ θ : Fin k → InteractionSample p,d+∑ j,‖(T (θ j)).1-(θ j).1‖
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=
      d+(k:ℝ)*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure) := by
    rw [integral_add (integrable_const d) (integrable_pi_sum M.disorder.toMeasure hD),integral_pi_sum M.disorder.toMeasure hD]
    simp
  simpa only [Pi.add_def,heq,trialSiteDisorder] using he.2

lemma functional_map_stability {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hD : Integrable (fun z => ‖(T z).1-z.1‖) M.disorder.toMeasure)
    (hd : Integrable (fun h => |g h-h|) M.field.toMeasure) :
    |functional (mapModel M T g hT hg) r ζ m-functional M r ζ m|≤
      (M.alpha:ℝ)*((p:ℝ)+((p-1:ℕ):ℝ))*(∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure)+
      (∫ h,|g h-h| ∂M.field.toMeasure) := by
  let D := ∫ z,‖(T z).1-z.1‖ ∂M.disorder.toMeasure
  let d := ∫ h,|g h-h| ∂M.field.toMeasure
  have hsi : Integrable (trialSiteDisorder M m ζ) (poissonMeasure (M.alpha*p)) := by
    apply ((integrable_const _).add ((poisson_integrable_count _).mul_const _)).mono'
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_def,Pi.mul_def] using (trialSiteDisorder_bound M m hm hθ hh ζ k))
  have hs := integrate_error (poissonMeasure (M.alpha*p)) StronglyMeasurable.of_discrete.aestronglyMeasurable
    hsi ((integrable_const d).add ((poisson_integrable_count _).mul_const D))
    (ae_of_all _ (trialSiteDisorder_map_stability M m hm ζ hθ hh T g hT hg hD hd))
  have hsbound : |(∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p))-
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p))|≤d+(M.alpha:ℝ)*p*D := by
    simpa only [Pi.add_def,Pi.mul_def,integral_add (integrable_const d) ((poisson_integrable_count _).mul_const D),
      integral_const,probReal_univ,one_smul,integral_mul_const,poisson_mean,NNReal.coe_mul,NNReal.coe_natCast] using hs.2
  have hei : Integrable (fun z : InteractionSample p => trialLog r ζ m (fun x => Real.log (edge z.1 x))) M.disorder.toMeasure := by
    apply hθ.mono' (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using trial_edge_bound r m hm ζ z.1)
  have he := integrate_error M.disorder.toMeasure
    (((trial_edge_lipschitz r m hm ζ).continuous.measurable.comp (measurable_fst.comp hT)).aestronglyMeasurable)
    hei hD (ae_of_all _ (fun z => trial_edge_stability r (T z).1 z.1 m hm ζ))
  have heq : (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x))
      ∂(mapModel M T g hT hg).disorder.toMeasure)=
      ∫ z,trialLog r ζ m (fun x => Real.log (edge (T z).1 x)) ∂M.disorder.toMeasure := by
    change (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂Measure.map T M.disorder.toMeasure)=_
    exact integral_map hT.aemeasurable (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
  unfold functional
  change |(Real.log 2 + (∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p)) -
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂(mapModel M T g hT hg).disorder.toMeasure)) -
      (Real.log 2 + (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) -
      (M.alpha:ℝ)*(p-1:ℕ)*(∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure))|≤_
  rw [heq]
  have hc : 0≤(M.alpha:ℝ)*(p-1:ℕ) := mul_nonneg M.alpha.coe_nonneg (Nat.cast_nonneg _)
  have h := he.2
  dsimp [D,d] at hsbound
  have hhbound := abs_sub
    ((∫ k,trialSiteDisorder (mapModel M T g hT hg) m ζ k ∂poissonMeasure (M.alpha*p))-
      (∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)))
    ((M.alpha:ℝ)*(p-1:ℕ)*((∫ z,trialLog r ζ m (fun x => Real.log (edge (T z).1 x)) ∂M.disorder.toMeasure)-
      (∫ z : InteractionSample p,trialLog r ζ m (fun x => Real.log (edge z.1 x)) ∂M.disorder.toMeasure)))
  rw [abs_mul,abs_of_nonneg hc] at hhbound
  simp only [Function.comp_apply] at h
  convert hhbound.trans (add_le_add hsbound (mul_le_mul_of_nonneg_left h hc)) using 1
  all_goals try ring_nf

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
local instance functionalStabilityOrderMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance functionalStabilityOrderBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ d,0 < m d) (ζ : Hierarchy (r+1))

noncomputable def trialDisorderAt (k : ℕ) (h : ℝ) : ℝ :=
  ∫ z : Fin k → InteractionSample p,trialLog r ζ m (siteLog z h)
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

include hm

lemma trialDisorderAt_measurable (k : ℕ) : Measurable (trialDisorderAt M m ζ k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact (trial_site_lipschitz r m hm ζ).continuous.stronglyMeasurable.integral_prod_left.measurable

lemma trialDisorderAt_bound
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : ℝ) : |trialDisorderAt M m ζ k h|≤|h|+k*interactionMoment M := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p => trialLog r ζ m (siteLog z h))
    ((integrable_const |h|).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z h)))
  simpa only [trialDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

lemma trialSite_integrable_prod
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×ℝ => trialLog r ζ m (siteLog z.1 z.2))
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply ((hh.comp_snd _).add ((interaction_sum_integrable M hθ k).comp_fst _)).mono'
    (trial_site_lipschitz r m hm ζ).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trial_site_bound r m hm ζ z.1 z.2))

lemma trialDisorderAt_integral
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h,trialDisorderAt M m ζ k h ∂M.field.toMeasure)=trialSiteDisorder M m ζ k :=
  (integral_integral_swap (trialSite_integrable_prod M m hm ζ hθ hh k)).symm

lemma trialDisorderAt_joint_integrable
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    Integrable (fun z : ℕ×ℝ => trialDisorderAt M m ζ z.1 z.2)
      ((poissonMeasure t).prod M.field.toMeasure) := by
  apply ((hh.comp_snd _).add (((poisson_integrable_count t).mul_const (interactionMoment M)).comp_fst _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => trialDisorderAt_measurable M m hm ζ k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (trialDisorderAt_bound M m hm ζ hθ z.1 z.2))

lemma trialPoisson_field_order
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (t : ℝ≥0) :
    (∫ h,∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure t ∂M.field.toMeasure)=
      ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure t := by
  rw [← integral_integral_swap (trialDisorderAt_joint_integrable M m hm ζ hθ hh t)]
  simp_rw [trialDisorderAt_integral M m hm ζ hθ hh]

end DilutedSpinGlass

end

end OAI
