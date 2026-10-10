import OAI.Probability.DilutedSpin.CavityMaskEnergy
import OAI.Probability.DilutedSpin.CavitySiteMean
import OAI.Probability.DilutedSpin.EnergyInsertionMean
import OAI.Probability.DilutedSpin.FirstMomentUpper
import OAI.Probability.DilutedSpin.PhysicalCavitySplit

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

noncomputable def energyCavityIncrement
    (μ : Measure X) (ξ : Measure Y) (ν : Measure I) (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ) : ℝ :=
  let F := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
    (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  Real.log 2+
    (∫ E,cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E-F E
      ∂compoundPoisson (reservoirRate α q N) μo)-
    (∫ E,∫ v,F (E+v)-F E ∂compoundPoisson (α*N-reservoirRate α q N) μo
      ∂compoundPoisson (reservoirRate α q N) μo)

/-- The actual finite-size physical increment at a common score intensity has
its reservoir/cavity representation, with only the repeated-new-site and
mark-location displacement errors. -/
lemma perturbedMean_reservoir_increment
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x σ => (theta x).1 (fun i => σ (e i))) μ μ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ (α*N) s)-
      energyCavityIncrement (N := N) μ ξ ν α s theta field Q m ψ|≤
      C*cavityBadRate α q N+2*D*s/(N+1) := by
  let F := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
    (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
  let G := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  let ρ := compoundPoisson (reservoirRate α q N) μo
  let : IsProbabilityMeasure μo :=
    (Measure.isProbabilityMeasure_map_iff (measurable_indexedPotential theta hθm).aemeasurable).mpr inferInstance
  have hθb : ∀ x σ,|(theta x).1 σ|≤C := fun x σ =>
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta x).1 σ : |(theta x).1 σ|≤‖(theta x).1‖).trans (hθ x)
  have hio : Integrable id μo := integrable_indexedPotential μ theta hθm hC hθb
  have hiρ : Integrable id ρ := compoundPoisson_integrable_id _ μo hio
  have hFl : LipschitzWith 1 F := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
    (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a)
  have hGl : LipschitzWith 1 G := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
    (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a)
  have hs := perturbedMean_cavity_split (N := N) μ ξ ν α s theta field hθm hhm Q m hm ψ hC hD hθb hh hf
  rw [cavityLaw_mean_eq μ theta hθm hsym hC hθ _ _ hGl] at hs
  have hn := averagedEnergyRoot_old_new_compare μ ξ ν ρ hiρ (oneNewRate α q N) s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  have ho := perturbedMean_averagedEnergyRoot (N := N) μ ξ ν (α*N) s theta field hθm hhm Q m hm ψ hC hD hθb hh hf
  have hb := compoundPoisson_increment (reservoirRate α q N) (α*N-reservoirRate α q N) μo hio hFl
  rw [add_tsub_cancel_of_le (reservoirRate_le α q N)] at hb
  have hFi : Integrable F ρ := integrable_lipschitz_of_id ρ hiρ hFl
  have hFb : ∀ E,|F E|≤‖E‖+(H*N+D*s) := by
    intro E
    simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
      (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i _ a => hf i.1 _ a) E
  have hCb : ∀ E,|cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E|≤
      ‖E‖+(H+C*(oneNewRate α q N)+(H*N+D*s)) := by
    intro E
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ theta field hH hC hθ hh hFb
      (oneNewRate α q N) E
  have hCi : Integrable (cavityPoissonValue μ ξ theta field F (oneNewRate α q N)) ρ :=
    (hiρ.norm.add (integrable_const _)).mono'
      (measurable_cavityPoissonValue μ ξ theta field hθm hhm hFl.continuous _).aestronglyMeasurable
      (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hCb E))
  change |(_-_)-(Real.log 2+(∫ E,cavityPoissonValue μ ξ theta field F (oneNewRate α q N) E-F E ∂ρ)-
    (∫ E,∫ v,F (E+v)-F E ∂compoundPoisson (α*N-reservoirRate α q N) μo ∂ρ))|≤_
  rw [integral_sub hCi hFi,← hb,ho]
  have hhabs := (abs_add_le _ _).trans (add_le_add hs hn)
  dsimp only [F,G,ρ,μo] at *
  convert hhabs using 1
  simp only [Nat.cast_add,Nat.cast_one]
  congr 1
  ring

end DilutedSpinGlass.SizeCoupling

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma rootMap_selectRoot {X Y : Type} (f : X → Y) (l : ℕ) (b : RootPath Bool l) (z : RootPath X l) :
    rootMap f (selectedCount l b) (selectRoot l b z)=selectRoot l b (rootMap f l z) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · exact ih b z.2
    · exact Prod.ext rfl (ih b z.2)

namespace PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma measurable_activeEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => activeEnergy V x j l r (z a) f y) := by
  induction l with
  | zero => exact measurable_const
  | succ l ih =>
    apply (ih r.2 (fun a => (z a).2) (measurable_snd.comp hz) (pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |activeEnergy V x j l r z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [activeEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have h := add_le_add (ih r.2 z.2 (pathFst n y))
      (mixedEnergy_bound z.1 (fun a => decide (a=j))
        (fun _ => V (pathMap (cavityProject l) n (pathFst n y)))
        (fun a => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n (pathSnd n y))))
    simpa only [singleBlockEnergy,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

noncomputable def activeDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ)
    (z : RootPath (InteractionSample p × (Fin p → R)) l) : ℝ :=
  backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
    (activeEnergy V x j l (rootMap Prod.snd l z) (rootMap Prod.fst l z) f)

lemma measurable_activeDatumRoot [MeasurableSpace R] [MeasurableSingletonClass R]
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (activeDatumRoot T U V x m j f l) := by
  let F := fun z : RootPath (InteractionSample p) l × RootPath (Fin p → R) l =>
    backwardLog n (cavityTower T U l z.2) m (activeEnergy V x j l z.2 z.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog n _ m (measurable_activeEnergy V x j l b id measurable_id f)
  exact hF.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
    (measurable_rootMap Prod.snd measurable_snd l))

omit [NeZero N] in
lemma allocatedMean_selected [MeasurableSpace R] [MeasurableSingletonClass R]
    (M : Model p) (Q : FiniteLaw R) (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (s : Fin N) (l : ℕ)
    (c : RootPath (Fin N) l) :
    (∫ z : RootPath (InteractionSample p × (Fin p → R)) l,
      backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
        (allocatedEnergy V x j s l (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f)
      ∂rootLaw l (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))=
    ∫ z,activeDatumRoot T U V x m j f (selectedCount l (rootMap (fun a => decide (a=s)) l c)) z
      ∂rootLaw (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) := by
  simp_rw [allocatedRoot_selected,←rootMap_selectRoot]
  exact integral_selectRoot _ l _ _ (measurable_activeDatumRoot T U V x m j f _)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
