import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FramePairing

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, MDifferentiable Model 𝓘(ℝ,ℝ) (f i)) :
    scalarDifferential (∑ i ∈ s, f i) = ∑ i ∈ s, scalarDifferential (f i) := by
  funext x
  have hh : HasMFDerivAt Model 𝓘(ℝ,ℝ) (∑ i ∈ s, f i) x
      (∑ i ∈ s, (show Space →L[ℝ] ℝ from mfderiv Model 𝓘(ℝ,ℝ) (f i) x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using! (hasMFDerivAt_const (I := Model) (I' := 𝓘(ℝ,ℝ)) (0 : ℝ) x)
    | insert i s hi IH =>
      erw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact ((hf i (Finset.mem_insert_self i s) x).hasMFDerivAt).add
        (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
  unfold scalarDifferential
  rw [hh.mfderiv]
  change (ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1))
    (∑ i ∈ s, mfderiv Model 𝓘(ℝ,ℝ) (f i) x) = _
  erw [_root_.map_sum]
  change ∑ i ∈ s, scalarDifferential (f i) x = (∑ i ∈ s, scalarDifferential (f i)) x
  exact (Finset.sum_apply x s (fun i => scalarDifferential (f i))).symm

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_comp {f : X → ℝ} (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f)
    {g : ℝ → ℝ} {g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' (f x)) (f x)) :
    scalarDifferential (g ∘ f) = fun x => g' (f x) • scalarDifferential f x := by
  funext x
  unfold scalarDifferential
  rw [mfderiv_comp x ((hg x).differentiableAt.mdifferentiableAt) (hf x),mfderiv_eq_fderiv,
    (hg x).hasFDerivAt.fderiv]
  erw [←map_smul]
  congr 1
  ext v
  let L : Space →L[ℝ] ℝ := mfderiv Model 𝓘(ℝ,ℝ) f x
  change L v * g' (f x) = g' (f x) * L v
  ring

omit [IsManifold Model ∞ X] in
lemma wedgeOne_sum_left {ι : Type*} (s : Finset ι) (a : ι → Form X 1) (b : Form X 1) :
    wedgeOne (∑ i ∈ s, a i) b = ∑ i ∈ s, wedgeOne (a i) b := by
  funext x
  simp only [wedgeOne,Finset.sum_apply, ExteriorForms.oneLinear]
  erw [_root_.map_sum]
  exact _root_.map_sum (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _

omit [IsManifold Model ∞ X] in
lemma wedgeOne_fun_smul_left (f : X → ℝ) (a b : Form X 1) :
    wedgeOne (fun x => f x • a x) b = fun x => f x • wedgeOne a b x := by
  funext x
  change ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (f x • a x)) (b x) = _
  dsimp only [ExteriorForms.oneLinear]
  erw [_root_.map_smul]
  exact _root_.map_smul (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _
end TamingCompatibility.ManifoldForms

end
end

end OAI
