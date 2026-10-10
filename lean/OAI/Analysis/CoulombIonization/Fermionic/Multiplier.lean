import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakProduct
import OAI.Analysis.CoulombIonization.FormDomain.CoulombCoercivity
import OAI.Analysis.CoulombIonization.FormDomain.FormBottom
import OAI.Analysis.CoulombIonization.Variational.L2

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
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

structure SmoothMultiplier (v : ι → E) where
  value : E → ℝ
  regular : ContDiff ℝ ∞ value
  bound : ∃ C : ℝ, ∀ x, |value x| ≤ C
  gradient_bound : ∀ i, ∃ C : ℝ, ∀ x, |lineDeriv ℝ value x (v i)| ≤ C

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma memLp_bounded_mul {p : E → ℝ} (hp : Continuous p)
    (hb : ∃ C : ℝ, ∀ x, |p x| ≤ C) {f : E → ℂ} (hf : MemLp f 2) :
    MemLp (fun x => (p x : ℂ) * f x) 2 := by
  obtain ⟨C, hC⟩ := hb
  have ht : MemLp (fun x => (p x : ℂ)) ⊤ := memLp_top_of_bound
    (Complex.continuous_ofReal.comp hp).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa using hC x)
  exact ht.fun_mul hf

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [Fintype ι] in
lemma SmoothMultiplier.derivative_continuous {v : ι → E}
    (p : SmoothMultiplier v) (i : ι) :
    Continuous (fun x => lineDeriv ℝ p.value x (v i)) := by
  have he : (fun x => lineDeriv ℝ p.value x (v i)) =
      fun x => fderiv ℝ p.value x (v i) := by
    funext x
    exact (p.regular.differentiable (by simp) x).lineDeriv_eq_fderiv
  rw [he]
  exact (p.regular.continuous_fderiv (by simp)).clm_apply continuous_const

omit [Fintype ι] in
lemma SmoothMultiplier.value_memLp {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) : MemLp (fun x => (p.value x : ℂ) * F.val none x) 2 :=
  memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp _)

omit [Fintype ι] in
lemma SmoothMultiplier.gradient_memLp {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) (i : ι) :
    MemLp (fun x => (p.value x : ℂ) * F.val (some i) x +
      Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x) 2 :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp _)).add
    (memLp_bounded_mul (p.derivative_continuous i) (p.gradient_bound i) (Lp.memLp _))

def SmoothMultiplier.apply {v : ι → E} (p : SmoothMultiplier v) (F : weakGraph v) :
    weakGraph v := by
  let G : WeakGraphAmbient E ι := WithLp.toLp 2 fun k => match k with
    | none => (p.value_memLp F).toLp _
    | some i => (p.gradient_memLp F i).toLp _
  refine ⟨G, (mem_weakGraph v G).mpr ?_⟩
  intro i
  exact (((mem_weakGraph v F.val).mp F.property i).mul_smooth
    (Lp.memLp _) (Lp.memLp _) p.regular).congr_ae
      (p.value_memLp F).coeFn_toLp.symm (p.gradient_memLp F i).coeFn_toLp.symm

omit [Fintype ι] in
lemma SmoothMultiplier.apply_value {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) :
    ((p.apply F).val none : E → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ) * F.val none x :=
  (p.value_memLp F).coeFn_toLp

omit [Fintype ι] in
lemma SmoothMultiplier.apply_gradient {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) (i : ι) :
    ((p.apply F).val (some i) : E → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * F.val (some i) x +
        Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x :=
  (p.gradient_memLp F i).coeFn_toLp

end Multiplier

structure FermionMultiplier (N : ℕ) extends SmoothMultiplier (sectorDirections N) where
  symmetric : ∀ (π : Equiv.Perm (Fin N)) (x : Configuration N), value (x ∘ π) = value x

def FermionMultiplier.apply {N : ℕ} (p : FermionMultiplier N) (F : fermionGraph N) :
    fermionGraph N := by
  let G : SectorGraph N := WithLp.toLp 2 fun s => p.toSmoothMultiplier.apply (F.val s)
  refine ⟨G, (mem_fermionSpace_ae (sectorGraphValue N G)).mpr ?_⟩
  intro π s
  have hl := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    (p.toSmoothMultiplier.apply_value (F.val (s ∘ π)))
  filter_upwards [hl, p.toSmoothMultiplier.apply_value (F.val s),
    (mem_fermionSpace_ae (sectorGraphValue N F.val)).mp F.property π s] with x hx hy hz
  change (p.toSmoothMultiplier.apply (F.val (s ∘ π))).val none (x ∘ π) =
    (((Equiv.Perm.sign π : ℤ) : ℂ)) * (p.toSmoothMultiplier.apply (F.val s)).val none x
  simp only [sectorGraphValue_apply] at hz
  simp only [permuteConfiguration_apply] at hx
  rw [hx, hy, p.symmetric, hz]
  ring

lemma FermionMultiplier.apply_value {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_value (F.val s)

lemma FermionMultiplier.apply_gradient {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphComponent s (some (i, a)) (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s (some (i, a)) F x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_gradient (F.val s) (i, a)

lemma graphNuclear_ae {N : ℕ} (s : Spins N) (i : Fin N) (F : fermionGraph N) :
    (graphNuclear s i F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (ContinuousLinearMap.proj i)
    (fun a => (i, a)) (by intro a; simp [sectorDirections, direction]) (F.val s)).coeFn_toLp

lemma graphPair_ae {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j)
    (F : fermionGraph N) :
    (graphPair s i j hij F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i - x j‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij]) (F.val s)).coeFn_toLp

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.apply_nuclear {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (graphNuclear s i (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphNuclear s i F x := by
  filter_upwards [graphNuclear_ae s i (p.apply F), graphNuclear_ae s i F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionMultiplier.apply_pair {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (graphPair s i j hij (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphPair s i j hij F x := by
  filter_upwards [graphPair_ae s i j hij (p.apply F), graphPair_ae s i j hij F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma coulombFormOperator_pairing (Z : ℝ) (N : ℕ) (F G : fermionGraph N) :
    (⟪G, coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i, a)) G, graphComponent s (some (i, a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        (⟪graphNuclear s i G, graphNuclear s i F⟫_ℂ).re) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then (⟪graphPair s i j (ne_of_lt hij) G,
          graphPair s i j (ne_of_lt hij) F⟫_ℂ).re else 0) := by
  have ht : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold coulombFormOperator
  simp only [ht, add_apply, sub_apply, smul_apply, sum_apply, inner_add_right, inner_sub_right,
    inner_smul_right, inner_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [ContinuousLinearMap.adjoint_inner_right]

lemma energy_le_graphForm {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hF : ‖fermionGraphValue N F‖ ^ 2 = 1) :
    energy Z N ≤ (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  rw [coulombFormOperator_inner]
  unfold energy
  split_ifs with hN
  · subst N
    simp [formEnergy]
  · exact csInf_le (sector_energies_bddBelow Z hZ N)
      ⟨graphFormVector F, graphFormVector_admissible F hF, rfl⟩

attribute [local irreducible] fermionGraphValue coulombFormOperator

theorem quantum_ground_form_equation {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N) (G : fermionGraph N) :
    ⟪G, coulombFormOperator Z N F⟫_ℂ =
      (energy Z N : ℂ) * ⟪fermionGraphValue N G, fermionGraphValue N F⟫_ℂ := by
  have hlow : ∀ U : fermionGraph N,
      energy Z N * ‖fermionGraphValue N U‖ ^ 2 ≤ (⟪U, coulombFormOperator Z N U⟫_ℂ).re :=
    form_lower_of_unit (fermionGraphValue N) (fermionGraphValue_injective N)
      (coulombFormOperator Z N) (fun U hU => energy_le_graphForm hZ U hU)
  have he : (⟪F, coulombFormOperator Z N F⟫_ℂ).re =
      energy Z N * ‖fermionGraphValue N F‖ ^ 2 := by
    rw [coulombFormOperator_inner, hF, hn, mul_one]
  exact ground_form_equation (V := fermionGraph N) (H := fermionSpace N)
    (fermionGraphValue N) (coulombFormOperator Z N)
    (coulombFormOperator_selfAdjoint Z N) hlow he G

lemma FermionMultiplier.gradient_ims {N : ℕ} (p : FermionMultiplier N)
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

lemma graphValue_pairing {N : ℕ} (F G : fermionGraph N) :
    (⟪fermionGraphValue N G, fermionGraphValue N F⟫_ℂ).re =
      ∑ s : Spins N, (⟪graphComponent s none G, graphComponent s none F⟫_ℂ).re := by
  change (⟪(fermionGraphValue N G).val, (fermionGraphValue N F).val⟫_ℂ).re = _
  have hi := PiLp.inner_apply (𝕜 := ℂ)
    (x := (fermionGraphValue N G).val) (y := (fermionGraphValue N F).val)
  have he := congrArg Complex.re hi
  rw [Complex.re_sum] at he
  have hc (U : fermionGraph N) (s : Spins N) :
      (fermionGraphValue N U).val s = graphComponent s none U := by
    unfold fermionGraphValue graphComponent
    rfl
  simpa only [hc] using he

lemma FermionMultiplier.value_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪fermionGraphValue N (p.apply (p.apply F)), fermionGraphValue N F⟫_ℂ).re =
      ‖fermionGraphValue N (p.apply F)‖ ^ 2 := by
  rw [graphValue_pairing, graphValue_norm_sq]
  apply Finset.sum_congr rfl
  intro s _
  exact l2_multiplier_pairing p.value (graphComponent s none F)
    (graphComponent s none (p.apply F)) (graphComponent s none (p.apply (p.apply F)))
    (p.apply_value F s) (p.apply_value (p.apply F) s)

attribute [local irreducible] formEnergy graphFormVector

lemma FermionMultiplier.nuclear_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply (p.apply F)), graphNuclear s i F⟫_ℂ).re =
      ‖graphNuclear s i (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_nuclear F s i)
    (p.apply_nuclear (p.apply F) s i)

lemma FermionMultiplier.pair_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply (p.apply F)), graphPair s i j hij F⟫_ℂ).re =
      ‖graphPair s i j hij (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_pair F s i j hij)
    (p.apply_pair (p.apply F) s i j hij)

lemma FermionMultiplier.kinetic_ims {N : ℕ} (p : FermionMultiplier N)
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

lemma coulombFormOperator_diagonal (Z : ℝ) (N : ℕ) (G : fermionGraph N) :
    (⟪G, coulombFormOperator Z N G⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ‖graphComponent s (some (i, a)) G‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i G‖ ^ 2) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then ‖graphPair s i j (ne_of_lt hij) G‖ ^ 2 else 0) := by
  rw [coulombFormOperator_pairing Z N G G]
  have hs (u : Lp ℂ 2 (volume : Measure (Configuration N))) :
      (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simp only [hs]

lemma FermionMultiplier.operator_pairing {N : ℕ} (p : FermionMultiplier N)
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

private lemma ims_arithmetic (K L A B R : ℝ) (h : K - L = R) :
    (1 / 2 * K - A + B) - (1 / 2 * L - A + B) = 1 / 2 * R := by
  rw [← h]
  ring

lemma FermionMultiplier.form_ims {N : ℕ} (p : FermionMultiplier N)
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
    _ = _ := ims_arithmetic _ _ _ _ _ (p.kinetic_ims F)

theorem quantum_ground_multiplier_smooth {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N) (p : FermionMultiplier N) :
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
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

end

end OAI
