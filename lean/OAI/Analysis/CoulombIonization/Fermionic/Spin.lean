import Mathlib
import OAI.Analysis.CoulombIonization.Variational.L2
import OAI.Analysis.CoulombIonization.Fermionic.Pauli
import OAI.Analysis.CoulombIonization.FormDomain.L2

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPauli
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [Fintype S] [MeasurableSingletonClass S] {μ : Measure A} [SigmaFinite μ]

omit [SigmaFinite μ] in
lemma memLp_spin (v : S → A → ℂ) (hv : ∀ s, MemLp (v s) 2 μ) :
    MemLp (fun p : A × S => v p.2 p.1) 2 (μ.prod Measure.count) := by
  classical
  have ht (s : S) : MemLp (({p : A × S | p.2 = s} : Set (A × S)).indicator
      (fun p => v s p.1)) 2 (μ.prod Measure.count) :=
    ((hv s).comp_fst Measure.count).indicator (measurable_snd (measurableSet_singleton s))
  have hf : (fun p : A × S => v p.2 p.1) =
      ∑ s : S, ({p : A × S | p.2 = s} : Set (A × S)).indicator (fun p => v s p.1) := by
    funext p
    simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    simp
  rw [hf]
  exact memLp_finsetSum' _ (fun s _ => ht s)

lemma prod_spin_norm_sq (v : S → A → ℂ) (hv : ∀ s, MemLp (v s) 2 μ) :
    (∫ p : A × S, ‖v p.2 p.1‖^2 ∂μ.prod Measure.count) = ∑ s : S, ∫ x, ‖v s x‖^2 ∂μ := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (memLp_spin v hv).aestronglyMeasurable).1 (memLp_spin v hv)
  rw [integral_prod_symm _ hi, integral_count]

lemma pi_count_eq {I S : Type*} [Fintype I] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] :
    Measure.pi (fun _ : I => (Measure.count : Measure S)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro f
  simp
end CoulombPauli

namespace CoulombAtom
namespace Pauli
open CoulombPauli
abbrev OneParticle := Space × Fin 2
abbrev oneMeasure : Measure OneParticle := volume.prod Measure.count
abbrev Many (N : ℕ) := CoulombPauli.sectorL2 N oneMeasure

def splitSpin (N : ℕ) : (Fin N → OneParticle) ≃ᵐ (Configuration N × Spins N) :=
  MeasurableEquiv.arrowProdEquivProdArrow Space (Fin 2) (Fin N)

lemma splitSpin_apply {N : ℕ} (x : Fin N → OneParticle) :
    splitSpin N x = (fun i => (x i).1, fun i => (x i).2) := rfl

lemma splitSpin_preserving (N : ℕ) :
    MeasurePreserving (splitSpin N) (configMeasure N oneMeasure)
      ((volume : Measure (Configuration N)).prod (Measure.count : Measure (Spins N))) := by
  have he := measurePreserving_arrowProdEquivProdArrow Space (Fin 2) (Fin N)
    (fun _ => (volume : Measure Space)) (fun _ => (Measure.count : Measure (Fin 2)))
  simpa only [splitSpin, pi_count_eq, ← volume_pi] using he

lemma memLp_value {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    MemLp (fun x : Fin N → OneParticle =>
      ψ.value (fun i => (x i).2) (fun i => (x i).1)) 2 (configMeasure N oneMeasure) := by
  exact (memLp_spin ψ.value hψ).comp_measurePreserving (splitSpin_preserving N)

def toMany {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) : Many N :=
  (memLp_value ψ hψ).toLp _

lemma toMany_ae {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    toMany ψ hψ =ᵐ[configMeasure N oneMeasure] (fun x : Fin N → OneParticle =>
      ψ.value (fun i => (x i).2) (fun i => (x i).1)) := MemLp.coeFn_toLp _

lemma toMany_norm_sq {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    ‖toMany ψ hψ‖^2 = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖^2 := by
  rw [l2_norm_sq]
  calc
    _ = ∫ x : Fin N → OneParticle,
        ‖ψ.value (fun i => (x i).2) (fun i => (x i).1)‖^2 ∂configMeasure N oneMeasure :=
      integral_congr_ae ((toMany_ae ψ hψ).fun_comp (fun z : ℂ => ‖z‖^2))
    _ = ∫ p : Configuration N × Spins N, ‖ψ.value p.2 p.1‖^2 ∂volume.prod Measure.count :=
      (splitSpin_preserving N).integral_comp (splitSpin N).measurableEmbedding
        (fun p : Configuration N × Spins N => ‖ψ.value p.2 p.1‖^2)
    _ = _ := prod_spin_norm_sq ψ.value hψ

lemma toMany_permute {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2)
    (π : Equiv.Perm (Fin N))
    (ha : ∀ s, ∀ᵐ x, ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)) :
    permute π (toMany ψ hψ) = (((Equiv.Perm.sign π : ℤ) : ℂ)) • toMany ψ hψ := by
  have hax : ∀ᵐ x, ∀ s, ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x) := ae_all_iff.2 ha
  have hab : ∀ᵐ p : Configuration N × Spins N ∂volume.prod Measure.count,
      ψ.value (p.2 ∘ π) (p.1 ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value p.2 p.1) :=
    (Measure.quasiMeasurePreserving_fst.ae hax).mono (fun p hp => hp p.2)
  have hat := (splitSpin_preserving N).quasiMeasurePreserving.ae hab
  apply Lp.ext
  filter_upwards [pull_ae (permCoords π) (permCoords_preserving π) (toMany ψ hψ),
    (permCoords_preserving π).quasiMeasurePreserving.ae (toMany_ae ψ hψ),
    toMany_ae ψ hψ, Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ)) (toMany ψ hψ), hat]
    with x h1 h2 h3 h4 h5
  change pull (permCoords π) (permCoords_preserving π) (toMany ψ hψ) x = _
  rw [h1,h2,h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]
  simpa only [splitSpin_apply, permCoords_apply, Function.comp_def, smul_eq_mul] using h5

theorem form_occupation_le_one {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ)
    (i : Fin (N+1)) (u : Lp ℂ 2 oneMeasure) (hu : ‖u‖ = 1) :
    (N+1 : ℝ) * ‖(CoulombPauli.insertOrbital i u).adjoint (toMany ψ hψ.1)‖^2 ≤ 1 := by
  have ha (i j : Fin (N+1)) (hij : i ≠ j) :
      permute (Equiv.swap i j) (toMany ψ hψ.1) = -toMany ψ hψ.1 := by
    rw [toMany_permute ψ hψ.1 (Equiv.swap i j) (hψ.2.2.2.1 _)]
    simp [Equiv.Perm.sign_swap hij]
  have hb := occupation_le_one i u hu (toMany ψ hψ.1) ha
  exact hb.trans_eq ((toMany_norm_sq ψ hψ.1).trans hψ.2.2.2.2.1)
end Pauli
end CoulombAtom

namespace CoulombPauli
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
local instance : DecidableEq S := Classical.decEq S

def countVector (s : S) : Lp ℂ 2 (Measure.count : Measure S) :=
  indicatorConstLp 2 (measurableSet_singleton s) (by simp) 1

omit [Fintype S] in
lemma countVector_inner (s : S) (u : Lp ℂ 2 (Measure.count : Measure S)) :
    inner ℂ (countVector s) u = u s := by
  rw [countVector, L2.inner_indicatorConstLp_one]
  simp

omit [Fintype S] in
lemma countVector_ae (s : S) :
    countVector s =ᵐ[Measure.count] (fun t : S => if t = s then (1 : ℂ) else 0) := by
  unfold countVector
  filter_upwards [(indicatorConstLp_coeFn (p := 2) (hs := measurableSet_singleton s)
    (hμs := by simp) (c := (1 : ℂ)))] with t ht
  rw [ht]
  by_cases h : t = s <;> simp [h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
open CoulombSobolev

lemma spin_test_total (f : Lp ℂ 2 ((volume : Measure E).prod (Measure.count : Measure S)))
    (hf : ∀ (φ : Test E) (s : S), inner ℂ (tensor φ.toL2 (countVector s)) f = 0) : f = 0 := by
  have hx (φ : Test E) : (tensorLeft φ.toL2).adjoint f = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℂ 2 (Measure.count : Measure S)] with s hs
    rw [← countVector_inner, ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply,
      hf, hs, Pi.zero_apply]
  apply eq_zero_of_tensor_orthogonal
  intro u v
  have hh : (tensorRight v).adjoint f = 0 := by
    apply test_total
    intro φ
    rw [← tensor_adjoint_exchange, hx, inner_zero_right]
  rw [← tensorRight_apply, ← ContinuousLinearMap.adjoint_inner_right, hh, inner_zero_right]

lemma spin_test_inner (v : S → E → ℂ) (hv : ∀ s, MemLp (v s) 2)
    (φ : Test E) (s : S) :
    inner ℂ (tensor φ.toL2 (countVector s)) ((memLp_spin v hv).toLp _) =
      ∫ x, v s x * (φ.fn x : ℂ) := by
  classical
  have he : (fun p : E × S => inner ℂ (tensor φ.toL2 (countVector s) p)
      ((memLp_spin v hv).toLp _ p)) =ᵐ[volume.prod Measure.count]
      (fun p : E × S => (v p.2 p.1 * (φ.fn p.1 : ℂ)) * (if p.2 = s then 1 else 0)) := by
    filter_upwards [tensor_ae φ.toL2 (countVector s),
      (memLp_spin v hv).coeFn_toLp,
      Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
      Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with p h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    split_ifs <;> simp [RCLike.inner_apply, mul_comm]
  have hi : Integrable (fun p : E × S => (v p.2 p.1 * (φ.fn p.1 : ℂ)) *
      (if p.2 = s then 1 else 0)) (volume.prod Measure.count) :=
    (L2.integrable_inner (tensor φ.toL2 (countVector s)) ((memLp_spin v hv).toLp _)).congr he
  rw [MeasureTheory.L2.inner_def, integral_congr_ae he, integral_prod_symm _ hi, integral_count]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · simp
end CoulombPauli

end

end OAI
