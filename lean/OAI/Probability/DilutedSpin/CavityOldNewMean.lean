import OAI.Probability.DilutedSpin.CavityPack
import OAI.Probability.DilutedSpin.InsertionPoint
import OAI.Probability.DilutedSpin.OldEnergyEmbedding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]
lemma cavityLaw_mean_eq (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun x => (theta x).1)
      (fun x s => (theta x).1 (fun l => s (e l))) μ μ)
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (r s : ℝ≥0) {F : ((Fin (N+1) → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F) :
    (∫ E,F E ∂(compoundPoisson r
      (Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
        indexedPotential theta (z.1,fun i => (z.2 i).succ))
        (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
      compoundPoisson s (Measure.map (fun z : X×(Fin (q+1)×(Fin q → Fin N)) =>
        indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
        (μ.prod (finiteUniform (Fin (q+1)×(Fin q → Fin N)))))))=
    ∫ E,∫ v,F (liftOldEnergy E+v)
      ∂compoundPoisson s (Measure.map (newPotential (N := N) theta)
        (μ.prod (finiteUniform (Fin q → Fin N))))
      ∂compoundPoisson r (Measure.map (indexedPotential theta)
        (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) := by
  let μo := Measure.map (indexedPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin (q+1) → Fin N)))
  let μn := Measure.map (newPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin q → Fin N)))
  let : IsProbabilityMeasure μo := inferInstance
  let : IsProbabilityMeasure μn := inferInstance
  have hio : Integrable id μo := integrable_indexedPotential μ theta hθm hC (fun x σ =>
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta x).1 σ : |(theta x).1 σ|≤‖(theta x).1‖).trans (hθ x))
  have hin : Integrable id μn := by
    apply (integrable_map_measure aestronglyMeasurable_id (measurable_newPotential theta hθm).aemeasurable).mpr
    apply Integrable.of_bound (measurable_newPotential theta hθm).aestronglyMeasurable C
    exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun _ =>
      (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1)))
  have hiO := compoundPoisson_integrable_id r μo hio
  have hiN := compoundPoisson_integrable_id s μn hin
  let ρo := Measure.map (liftOldEnergy (N := N)) (compoundPoisson r μo)
  let : IsProbabilityMeasure ρo := inferInstance
  have hiL : Integrable id ρo :=
    (integrable_map_measure aestronglyMeasurable_id (liftOldEnergy (N := N)).measurable.aemeasurable).mpr
      ((liftOldEnergy (N := N)).integrable_comp hiO)
  rw [old_compoundLaw μ theta hθm,oneNew_markLaw μ theta hθm hsym]
  change (∫ E,F E ∂(ρo ∗ compoundPoisson s μn))=_
  rw [integral_conv (integrable_lipschitz_of_id _ (integrable_id_conv _ _ hiL hiN) hF)]
  have hm : StronglyMeasurable (fun E : (Fin (N+1) → Spin) → ℝ =>
      ∫ v,F (E+v) ∂compoundPoisson s μn) :=
    (show StronglyMeasurable (Function.uncurry (fun E v : (Fin (N+1) → Spin) → ℝ => F (E+v))) from
      (hF.continuous.comp continuous_add).stronglyMeasurable).integral_prod_right
  exact integral_map (liftOldEnergy (N := N)).measurable.aemeasurable hm.aestronglyMeasurable

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_tail (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i : Fin l => z.2 i.succ)) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma singleBlockEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : Fin p → R) (z : InteractionSample p)
    (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    singleBlockEnergy V x j l r z (pathMap (cavityPack (l+1)) n y)=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => V (pathFst n y))
        (fun a => x (r a) (pathMap (fun b : Ω × (Fin (l+1) → Fin p → Λ) => b.2 0 a) n y)) := by
  unfold singleBlockEnergy
  rw [pathFst_pack,pathProject_pack,pathFst_tail,pathSnd_pack]
  simp only [← pathMap_comp,Function.comp_def]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    activeEnergy V x j l r z f (pathMap (cavityPack l) n y)=
      f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
        (fun _ => V (pathFst n y))
        (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y)) := by
  induction l with
  | zero =>
    change f (pathMap Prod.fst n y)=f (pathFst n y)+∑ i : Fin 0,_
    simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero,pathMap_fst]
  | succ l ih =>
    change activeEnergy V x j l r.2 z.2 f (pathFst n (pathMap (cavityPack (l+1)) n y))+
      singleBlockEnergy V x j l r.1 z.1 (pathMap (cavityPack (l+1)) n y)=_
    rw [pathFst_pack,ih,singleBlockEnergy_pack,pathFst_tail,Fin.sum_univ_succ]
    simp only [rootArray,Fin.cons_zero,Fin.cons_succ,←pathMap_comp,Function.comp_def]
    ring

omit [Fintype R] in
lemma activeRoot_flat (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (activeEnergy V x j l r z f)=
      backwardLog n (prod n T (pi n (fun i : Fin l => piTower n (fun a => U (rootArray l r i a))))) m
        (fun y => f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
          (fun _ => V (pathFst n y))
          (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y))) := by
  rw [←backwardLog_of_projects n (cavityPack_projects T U l r)]
  congr 1
  funext y
  exact activeEnergy_pack V x j l r z f y

end DilutedSpinGlass.PrescribedTree

end

end OAI
