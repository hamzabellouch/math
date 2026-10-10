import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.IntegrableIntegralAeTendsto
import OAI.Analysis.CoulombRadii.FieldAnalysis.DeterminantWave

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma complex_smooth_compact_ibp {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hC : HasCompactSupport f)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφC : HasCompactSupport φ) (v : Configuration n) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : Configuration n → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp hφ
  have hgC : HasCompactSupport g := hφC.comp_left Complex.ofReal_zero
  have hd (x : Configuration n) : fderiv ℝ g x v = (fderiv ℝ φ x v : ℂ) := by
    exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L v)
      ((Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) volume := (hf'.mul hg.continuous).integrable_of_hasCompactSupport
    (hgC.mul_left (f := fun x => fderiv ℝ f x v))
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) volume := (hf.continuous.mul hg').integrable_of_hasCompactSupport
    (hC.mul_right (f' := fun x => fderiv ℝ g x v))
  have hi3 : Integrable (fun x => f x * g x) volume := (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
    (hC.mul_right (f' := g))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)
  simpa only [hd] using h

noncomputable def H1Vector.ofSmoothCompact {n : ℕ} (f : Spins n → Configuration n → ℂ)
    (hf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hC : ∀ s, HasCompactSupport (f s)) : H1Vector n where
  value := f
  gradient s a x := fderiv ℝ (f s) x (EuclideanSpace.single a 1)
  value_L2 s := (hf s).continuous.memLp_of_hasCompactSupport (hC s)
  partial_L2 s a :=
    (((hf s).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hC s).fderiv_apply ℝ (EuclideanSpace.single a 1))
  weak_partial s a φ hφ hφC := complex_smooth_compact_ibp (f s) (hf s) (hC s) φ hφ hφC _

lemma tensor_compact_support {A : Type*} [TopologicalSpace A] [T2Space A]
    {n : ℕ} (f : Fin n → A → ℂ) (hC : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x : Fin n → A => ∏ i, f i (x i)) := by
  apply HasCompactSupport.intro (isCompact_univ_pi (fun i => (hC i).isCompact))
  intro x hx
  have hn : ¬ ∀ i, x i ∈ tsupport (f i) := by simpa only [mem_univ_pi] using hx
  obtain ⟨i,hi⟩ := not_forall.mp hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

noncomputable def configurationHomeomorph (n : ℕ) : Configuration n ≃ₜ (Fin n → Space) :=
  ((PiLp.homeomorph 2 (fun _ : Fin n × Fin 3 => ℝ)).trans
    (Homeomorph.piCurry (X := Fin n) (Y := Fin 3) (Z := ℝ))).trans
    (Homeomorph.piCongrRight fun _ => (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm)

lemma tensorOrbital_compact_support {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (b : Fin n → α) (s : Spins n) : HasCompactSupport (tensorOrbital v b s) := by
  exact (tensor_compact_support (fun i x => v (b i) x (s i)) (fun i => hC (b i) (s i))).comp_homeomorph
    (configurationHomeomorph n)

noncomputable def positionCLM {n : ℕ} (i : Fin n) : Configuration n →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun b : Fin 3 =>
      (EuclideanSpace.proj (i,b) : Configuration n →L[ℝ] ℝ))

lemma positionCLM_apply {n : ℕ} (i : Fin n) (x : Configuration n) :
    positionCLM i x = position x i := rfl

lemma tensorOrbital_contDiff {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (b : Fin n → α) (s : Spins n) : ContDiff ℝ (⊤ : ℕ∞) (tensorOrbital v b s) := by
  unfold tensorOrbital
  apply contDiff_prod
  intro i _
  exact (hv (b i) (s i)).comp (positionCLM i).contDiff

noncomputable def slaterConfiguration {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (s : Spins n) (x : Configuration n) : ℂ :=
  slaterWave (fun i (a : Fin 2 × Space) => v i a.2 a.1) (fun i => (s i, position x i))

lemma slaterConfiguration_expansion {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (s : Spins n) : slaterConfiguration v s =
      fun x => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x := by
  funext x
  simp only [slaterConfiguration, slaterWave, determinantWave_expansion, tensorOrbital]

lemma slaterConfiguration_contDiff {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s)) (s : Spins n) :
    ContDiff ℝ (⊤ : ℕ∞) (slaterConfiguration v s) := by
  rw [slaterConfiguration_expansion]
  apply contDiff_const.mul
  exact ContDiff.sum (fun p _ => contDiff_const.mul (tensorOrbital_contDiff v hv p s))

lemma slaterConfiguration_compact_support {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) (s : Spins n) :
    HasCompactSupport (slaterConfiguration v s) := by
  have ht (p : Equiv.Perm (Fin n)) : HasCompactSupport
      (fun x => (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) :=
    (tensorOrbital_compact_support v hC p s).mul_left
  have hs : HasCompactSupport (fun x => ∑ p : Equiv.Perm (Fin n),
      (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) :=
    by
      convert (HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun (p : Equiv.Perm (Fin n)) x => (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) (fun p _ => ht p)) using 1
      first | rfl | (funext x; simp only [Finset.sum_apply])
  rw [slaterConfiguration_expansion]
  exact hs.mul_left (f := fun _ => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ))

noncomputable def slaterState {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) : H1Vector n :=
  H1Vector.ofSmoothCompact (slaterConfiguration v)
    (slaterConfiguration_contDiff v hv) (slaterConfiguration_compact_support v hC)

lemma slaterState_antisymmetric {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) :
    Antisymmetric (slaterState v hv hC) := by
  intro p s
  filter_upwards [] with x
  change slaterConfiguration v (s ∘ p) (permute p x) = _ * slaterConfiguration v s x
  have he : (fun i => ((s ∘ p) i, position (permute p x) i)) =
      (fun i => (s i, position x i)) ∘ p := by
    funext i
    simp only [Function.comp_apply, position_permute]
  simp only [slaterConfiguration, slaterWave, he, determinantWave_permute]
  ring

noncomputable def flatSpinOrbital (v : Space → Fin 2 → ℂ) : Fin 2 × (Fin 3 → ℝ) → ℂ :=
  fun sx => v (WithLp.toLp 2 sx.2) sx.1

lemma flatSpinOrbital_memLp (v : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume) :
    MemLp (flatSpinOrbital v) 2 spinSpaceMeasure := by
  change MemLp (flatSpinOrbital v) 2 (Measure.count.prod volume)
  have hi (s : Fin 2) : MemLp (fun t : Fin 2 => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Fin 2) _ => tensorPair_memLp (hi s)
    ((hv s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  funext sx
  simp [flatSpinOrbital, ite_mul]

lemma flatSpinOrbital_inner (v u : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume)
    (hu : ∀ s, MemLp (fun x => u x s) 2 volume) :
    (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂spinSpaceMeasure) =
      ∑ s : Fin 2, ∫ x : Space, star (v x s) * u x s := by
  have hI := (flatSpinOrbital_memLp v hv).star.integrable_mul (flatSpinOrbital_memLp u hu)
  change Integrable (fun a => star (flatSpinOrbital v a) * flatSpinOrbital u a)
    (Measure.count.prod volume) at hI
  change (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hI, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => star (v x s) * u x s)

lemma slaterState_cubeState {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) :
    cubeState (slaterState v hv hC) = slaterWave (fun i => flatSpinOrbital (v i)) := by
  funext x
  rfl

lemma slaterState_normalized {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s))
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Space, star (v i x s) * v j x s) =
      if i = j then (1:ℂ) else 0) : mass (slaterState v hv hC) = 1 := by
  have hV (i : Fin n) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  rw [← cubeState_full_mass, slaterState_cubeState]
  apply slaterWave_normalized (fun i => flatSpinOrbital (v i))
    (fun i => flatSpinOrbital_memLp (v i) (hV i))
  intro i j
  rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
  by_cases h : i = j
  · simpa only [ite_eq_left h] using ho i j
  · simpa only [ite_eq_right h] using ho i j

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
