import OAI.Probability.DilutedSpin.CavityAllocatedMean
import OAI.Probability.DilutedSpin.CavitySeparable
import OAI.Probability.DilutedSpin.FirstMomentCount
import OAI.Probability.DilutedSpin.PoissonReplacement

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperAllocated_integrable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))
      (rootLaw l (fun _ => upperDatumLaw M Q)) := by
  have h := ((measurePreserving_rootSplit _ _ l).comp
    (measurePreserving_rootMap (upperDatum_site_projection M Q j) l)).integrable_comp_of_integrable
      (allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)
  simpa only [Function.comp_def,allocatedDatumRoot,rootMap_comp] using h

omit [MeasurableSingletonClass R] in
lemma upperCountMean_cavity (M : Model p) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M T Q U V x m j f 0 l=
      ∫ z : RootPath (UpperDatum p N R) l,
        cavityRoot T U V x m j l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1) l z) (rootMap Prod.fst l z) f
        ∂rootLaw l (fun _ => upperDatumLaw M Q) := by
  unfold upperCountMean datumRoot realCountEnergy
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change (∫ _ : Unit, _ ∂Measure.dirac ())=_
  simp only [integral_dirac]

lemma upperCountMean_separable (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l=
      ∑ s : Fin N,∫ c,activeCountMean M Q (T s) U (V s) x m j (f s)
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  rw [upperCountMean_cavity]
  simp_rw [cavityRoot_separable,rootMap_comp,Function.comp_def]
  rw [integral_finsetSum _ (fun s _ => upperAllocated_integrable M hM Q (T s) U (V s) x m hm j s (f s) l)]
  exact Finset.sum_congr rfl (fun s _ => upperAllocatedMean M hM Q (T s) U (V s) x m hm j s (f s) l)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p : ℕ}

lemma activeCountMean_bound (M : Model p) (hM : Admissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |activeCountMean M Q T U V x m j f l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  let ν := M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖) ν :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  have hs := integrable_rootArray_sum ν (fun z => ‖z.1.1‖) hi l
  have hB (z : RootPath (InteractionSample p × (Fin p → R)) l) :
      |activeDatumRoot T U V x m j f l z|≤B+∑ i,‖(rootArray l z i).1.1‖ := by
    apply backwardLog_bound n _ m hm
    intro y
    simpa only [rootArray_rootMap] using activeEnergy_bound V x j l
      (rootMap Prod.snd l z) (rootMap Prod.fst l z) f hf y
  have hF : Integrable (activeDatumRoot T U V x m j f l) (rootLaw l (fun _ => ν)) :=
    ((integrable_const B).add hs).mono'
      (measurable_activeDatumRoot T U V x m j f l).aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hF.abs ((integrable_const B).add hs) hB).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const B) hs,integral_rootArray_sum ν _ hi l]
  have he : (∫ a : InteractionSample p × (Fin p → R),‖a.1.1‖ ∂ν)=
      ∫ a : InteractionSample p,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [ν,probReal_univ,one_smul] using
      (integral_fun_fst (μ := M.disorder.toMeasure)
        (ν := ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)
        (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul,mul_comm]

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma upperPoissonCount_bound_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (r : ℝ≥0)
    :
    (∫ k,upperCountMean M T Q U V x (fun d => m d.succ) j f k 0 ∂poissonMeasure (r/p))+
      (r:ℝ)*(((p-1:ℕ):ℝ)/p)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) ≤
    ∫ l,upperCountMean M T Q U V x (fun d => m d.succ) j f 0 l ∂poissonMeasure r := by
  have hp : 0 < p := by have := hM.arity; omega
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hpR : (p:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  let e := ∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure
  have hh := poisson_count_replacement r p
    (upperCountMean M T Q U V x (fun d => m d.succ) j f)
    ((((p-1:ℕ):ℝ)/p)*e) (show 0 ≤ ∫ a : InteractionSample p, ‖a.1‖ ∂M.disorder.toMeasure from
      integral_nonneg (fun a => norm_nonneg a.1))
    (fun k l => upperCountMean_bound_firstMoment M hM T Q U V x _ hstrict j f k l
      (fun y => norm_le_pi_norm f y))
    (fun k l => ?_)
  · simpa only [mul_assoc] using hh
  · have h := upperCountMean_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l
    convert h using 1
    dsimp only [e]
    field_simp

end DilutedSpinGlass.PrescribedTree

end

end OAI
