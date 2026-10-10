import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Multiplier
import OAI.Analysis.CoulombIonization.FormDomain.LipschitzWeak

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι : Type*} [Fintype ι]

structure LipschitzMultiplier (v : ι → E) where
  value : E → ℝ
  constant : NNReal
  lipschitz : LipschitzWith constant value
  bound : ∃ C : ℝ, ∀ x, |value x| ≤ C

omit [Fintype ι] in
lemma LipschitzMultiplier.value_memLp {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) : MemLp (fun x => (p.value x : ℂ) * F.val none x) 2 :=
  memLp_bounded_mul p.lipschitz.continuous p.bound (Lp.memLp _)

omit [Fintype ι] in
lemma LipschitzMultiplier.gradient_memLp {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) (i : ι) :
    MemLp (fun x => (p.value x : ℂ) * F.val (some i) x +
      Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x) 2 := by
  have hd : MemLp (fun x => Complex.ofReal (lineDeriv ℝ p.value x (v i))) ⊤ :=
    memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_lineDeriv p.lipschitz.continuous volume))
      (p.constant * ‖v i‖) (Eventually.of_forall fun x => by
        simpa using (norm_lineDeriv_le_of_lipschitz ℝ p.lipschitz (x₀ := x) (v := v i)))
  exact (memLp_bounded_mul p.lipschitz.continuous p.bound (Lp.memLp _)).add
    (hd.fun_mul (Lp.memLp (F.val none)))

def LipschitzMultiplier.apply {v : ι → E} (p : LipschitzMultiplier v) (F : weakGraph v) :
    weakGraph v := by
  let G : WeakGraphAmbient E ι := WithLp.toLp 2 fun k => match k with
    | none => (p.value_memLp F).toLp _
    | some i => (p.gradient_memLp F i).toLp _
  refine ⟨G, (mem_weakGraph v G).mpr ?_⟩
  intro i
  exact (((mem_weakGraph v F.val).mp F.property i).mul_lipschitz
    (Lp.memLp _) (Lp.memLp _) p.lipschitz p.bound).congr_ae
      (p.value_memLp F).coeFn_toLp.symm (p.gradient_memLp F i).coeFn_toLp.symm

omit [Fintype ι] in
lemma LipschitzMultiplier.apply_value {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) :
    ((p.apply F).val none : E → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ) * F.val none x :=
  (p.value_memLp F).coeFn_toLp

omit [Fintype ι] in
lemma LipschitzMultiplier.apply_gradient {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) (i : ι) :
    ((p.apply F).val (some i) : E → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * F.val (some i) x +
        Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x :=
  (p.gradient_memLp F i).coeFn_toLp

end Multiplier

structure FermionLipschitzMultiplier (N : ℕ) extends LipschitzMultiplier (sectorDirections N) where
  symmetric : ∀ (π : Equiv.Perm (Fin N)) (x : Configuration N), value (x ∘ π) = value x

def FermionLipschitzMultiplier.apply {N : ℕ} (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    fermionGraph N := by
  let G : SectorGraph N := WithLp.toLp 2 fun s => p.toLipschitzMultiplier.apply (F.val s)
  refine ⟨G, (mem_fermionSpace_ae (sectorGraphValue N G)).mpr ?_⟩
  intro π s
  have hl := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    (p.toLipschitzMultiplier.apply_value (F.val (s ∘ π)))
  filter_upwards [hl, p.toLipschitzMultiplier.apply_value (F.val s),
    (mem_fermionSpace_ae (sectorGraphValue N F.val)).mp F.property π s] with x hx hy hz
  change (p.toLipschitzMultiplier.apply (F.val (s ∘ π))).val none (x ∘ π) =
    (((Equiv.Perm.sign π : ℤ) : ℂ)) * (p.toLipschitzMultiplier.apply (F.val s)).val none x
  simp only [sectorGraphValue_apply] at hz
  simp only [permuteConfiguration_apply] at hx
  rw [hx, hy, p.symmetric, hz]
  ring

lemma FermionLipschitzMultiplier.apply_value {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toLipschitzMultiplier.apply_value (F.val s)

lemma FermionLipschitzMultiplier.apply_gradient {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphComponent s (some (i, a)) (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s (some (i, a)) F x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * graphComponent s none F x :=
  p.toLipschitzMultiplier.apply_gradient (F.val s) (i, a)

attribute [local irreducible] graphNuclear graphPair graphComponent FermionLipschitzMultiplier.apply

lemma FermionLipschitzMultiplier.apply_nuclear {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (graphNuclear s i (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphNuclear s i F x := by
  filter_upwards [graphNuclear_ae s i (p.apply F), graphNuclear_ae s i F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionLipschitzMultiplier.apply_pair {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (graphPair s i j hij (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphPair s i j hij F x := by
  filter_upwards [graphPair_ae s i j hij (p.apply F), graphPair_ae s i j hij F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionLipschitzMultiplier.gradient_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    ‖graphComponent s (some (i, a)) (p.apply F)‖ ^ 2 -
      (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
        graphComponent s (some (i, a)) F⟫_ℂ).re =
      ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
        ‖graphComponent s none F x‖ ^ 2 := by
  apply l2_ims_identity p.value (fun x => lineDeriv ℝ p.value x (direction i a))
    (graphComponent s (some (i, a)) F) (graphComponent s none F)
  · exact p.apply_gradient F s i a
  · filter_upwards [p.apply_gradient (p.apply F) s i a, p.apply_value F s] with x hx hy
    exact hx.trans (congrArg (fun z : ℂ =>
      (p.value x : ℂ) * graphComponent s (some (i, a)) (p.apply F) x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * z) hy)

lemma FermionLipschitzMultiplier.value_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) :
    (⟪fermionGraphValue N (p.apply (p.apply F)), fermionGraphValue N F⟫_ℂ).re =
      ‖fermionGraphValue N (p.apply F)‖ ^ 2 := by
  rw [graphValue_pairing, graphValue_norm_sq]
  apply Finset.sum_congr rfl
  intro s _
  exact l2_multiplier_pairing p.value (graphComponent s none F)
    (graphComponent s none (p.apply F)) (graphComponent s none (p.apply (p.apply F)))
    (p.apply_value F s) (p.apply_value (p.apply F) s)

attribute [local irreducible] formEnergy graphFormVector fermionGraphValue coulombFormOperator

lemma FermionLipschitzMultiplier.nuclear_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply (p.apply F)), graphNuclear s i F⟫_ℂ).re =
      ‖graphNuclear s i (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_nuclear F s i)
    (p.apply_nuclear (p.apply F) s i)

lemma FermionLipschitzMultiplier.pair_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply (p.apply F)), graphPair s i j hij F⟫_ℂ).re =
      ‖graphPair s i j hij (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_pair F s i j hij)
    (p.apply_pair (p.apply F) s i j hij)

lemma FermionLipschitzMultiplier.kinetic_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) (p.apply F)‖ ^ 2) -
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
        graphComponent s (some (i, a)) F⟫_ℂ).re) =
    ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
        ‖graphComponent s none F x‖ ^ 2 := by
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun a _ => p.gradient_ims F s i a

lemma FermionLipschitzMultiplier.operator_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (Z : ℝ) (F : fermionGraph N) :
    (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
          graphComponent s (some (i, a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i (p.apply F)‖ ^ 2) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then ‖graphPair s i j (ne_of_lt hij) (p.apply F)‖ ^ 2 else 0) := by
  calc
    _ = _ := coulombFormOperator_pairing Z N F (p.apply (p.apply F))
    _ = _ := by simp only [p.nuclear_pairing, p.pair_pairing]

private lemma lipschitz_ims_arithmetic (K L A B R : ℝ) (h : K - L = R) :
    (1 / 2 * K - A + B) - (1 / 2 * L - A + B) = 1 / 2 * R := by
  rw [← h]
  ring

lemma FermionLipschitzMultiplier.form_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (Z : ℝ) (F : fermionGraph N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
          ‖graphComponent s none F x‖ ^ 2) := by
  calc
    _ = _ := congrArg (fun t : ℝ => t -
      (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re)
        (coulombFormOperator_inner Z N (p.apply F)).symm
    _ = _ := congrArg₂ (fun a b : ℝ => a - b)
      (coulombFormOperator_diagonal Z N (p.apply F)) (p.operator_pairing Z F)
    _ = _ := lipschitz_ims_arithmetic _ _ _ _ _ (p.kinetic_ims F)

theorem quantum_ground_multiplier_lipschitz {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N) (p : FermionLipschitzMultiplier N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      energy Z N * ‖fermionGraphValue N (p.apply F)‖ ^ 2 =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
          ‖graphComponent s none F x‖ ^ 2) := by
  have he := congrArg Complex.re (quantum_ground_form_equation hZ F hn hF
    (p.apply (p.apply F)))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    p.value_pairing] at he
  rw [← he]
  exact p.form_ims Z F

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal

end

end OAI
