import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureBlockInformation
import OAI.NumberTheory.DukePrimeDegree.Geometry.KernelTransport
import OAI.NumberTheory.PrimePackets.LeafSupport

namespace OAI

/-! # Covariance of the actual normalized future measures -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_after_normalize_map
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (e : Y ≃ᵐ Z) (A B : Set Z)
    (hB₀ : (ν.map e) B ≠ 0) (hBtop : (ν.map e) B ≠ ∞) :
    (anchorNormalize (anchorNormalize (ν.map e) B) A).restrict A =
      ((anchorNormalize ν (e ⁻¹' A)).restrict (e ⁻¹' A)).map e := by
  change (anchorNormalize (((ν.map e) B)⁻¹ • ν.map e) A).restrict A = _
  rw [anchorNormalize_smul _ _ _ (ENNReal.inv_ne_zero.mpr hBtop)
    (ENNReal.inv_ne_top.mpr hB₀)]
  have he := anchorNormalize_map_equiv ν e (e ⁻¹' A)
  rw [e.surjective.image_preimage A] at he
  rw [he,e.restrict_map]

namespace EliminationChain

theorem ae_normalizedFuture_diagonal
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (m : ℕ) :
    ∀ᵐ x ∂μ,
      (anchorNormalize
        (c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell (-1))))
        (c.remainingFutureAtom ell hell Q m (rightAction x (diagonalOneParameter ell hell (-1))))).restrict
        (c.remainingFutureAtom ell hell Q m (rightAction x (diagonalOneParameter ell hell (-1)))) =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q (m+1) x)).restrict
        (c.remainingFutureAtom ell hell Q (m+1) x)).map (c.rootDilation ell 1) := by
  filter_upwards [c.ae_remainingTimeProduct_diagonal d hP hf μ hA ell hell (-1),
    c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA] with x hx hc
  rw [hx]
  simp only [neg_neg]
  have hmass : ((c.remainingTimeProduct hP hf μ x).map (c.rootDilation ell 1))
      (c.cube 1)=c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) :=
    Measure.map_apply (c.rootDilation ell 1).measurable (c.cube_open 1).measurableSet
  have H := normalized_restriction_after_normalize_map (c.remainingTimeProduct hP hf μ x)
    (c.rootDilation ell 1).toMeasurableEquiv
    (c.remainingFutureAtom ell hell Q m (rightAction x (diagonalOneParameter ell hell (-1))))
    (c.cube 1)
    (by simpa only [Homeomorph.toMeasurableEquiv_coe,hmass] using hc.1.ne')
    (by simpa only [Homeomorph.toMeasurableEquiv_coe,hmass] using hc.2)
  simpa only [Homeomorph.toMeasurableEquiv_coe,c.remainingFutureAtom_shift_index ell hell Q m x] using H

def ambientFutureMeasure
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0)
    (Q : X n → ℕ) (m : ℕ) (x : X n) : Measure (X n) :=
  ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
    (c.remainingFutureAtom ell hell Q m x)).restrict
    (c.remainingFutureAtom ell hell Q m x)).map (fun u => rightAction x (c.word u))

theorem ae_ambientFuture_diagonal
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (m : ℕ) :
    ∀ᵐ x ∂μ, c.ambientFutureMeasure hP hf μ ell hell Q m
        (rightAction x (diagonalOneParameter ell hell (-1))) =
      (c.ambientFutureMeasure hP hf μ ell hell Q (m+1) x).map
        (fun y => rightAction y (diagonalOneParameter ell hell (-1))) := by
  filter_upwards [c.ae_normalizedFuture_diagonal d hP hf μ hA ell hell Q m] with x hx
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  have hF (z : X (d+1)) : Measurable (fun u => rightAction z (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hT : Measurable T := (continuous_rightAction _).measurable
  unfold ambientFutureMeasure
  rw [hx,Measure.map_map (hF _) (c.rootDilation ell 1).measurable,
    Measure.map_map hT (hF _)]
  congr 1
  funext u
  exact c.remaining_orbit_diagonal ell hell x u

end EliminationChain

def delayedFutureKernel {n : ℕ} (κ : Kernel (X n) (X n)) (a : G n) :
    ℕ → Kernel (X n) (X n)
  | 0 => κ
  | N+1 => transportKernel (rightActionHomeomorph a⁻¹).toMeasurableEquiv
      (delayedFutureKernel κ a N)

instance delayedFutureKernel_markov {n : ℕ} (κ : Kernel (X n) (X n))
    [IsMarkovKernel κ] (a : G n) (N : ℕ) : IsMarkovKernel (delayedFutureKernel κ a N) := by
  induction N with
  | zero => exact inferInstanceAs (IsMarkovKernel κ)
  | succ N ih =>
    let _ := ih
    change IsMarkovKernel (transportKernel (rightActionHomeomorph a⁻¹).toMeasurableEquiv _)
    infer_instance

theorem delayedFutureKernel_spec
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (N : ℕ) :
    let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
    μ.bind K=μ ∧ (∀ᵐ x ∂μ, ∀ᵐ y ∂K x, K y=K x) ∧
      ∀ᵐ x ∂μ, K x=c.ambientFutureMeasure hP hf μ ell hell Q (N+1) x := by
  let a := diagonalOneParameter ell hell (-1)
  let e := (rightActionHomeomorph a⁻¹).toMeasurableEquiv
  have he : μ.map e=μ := by
    change μ.map (fun x => rightAction x a⁻¹)=μ
    have ha : a⁻¹=diagonalOneParameter ell hell 1 := by
      dsimp only [a]
      rw [←diagonalOneParameter_neg]
      norm_num
    rw [ha,diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  induction N with
  | zero => exact ⟨hstat,hself,hversion⟩
  | succ N ih =>
    refine ⟨transportKernel_stationary e μ he _ ih.1,
      transportKernel_self_constant e μ he _ ih.1 ih.2.1,?_⟩
    filter_upwards [hT.quasiMeasurePreserving.ae ih.2.2,
      c.ae_ambientFuture_diagonal d hP hf μ hA ell hell Q (N+1)] with x hx hc
    rw [delayedFutureKernel,transportKernel_apply]
    simp only [Homeomorph.toMeasurableEquiv_coe,Homeomorph.toMeasurableEquiv_symm_coe]
    change (delayedFutureKernel κ a N (rightAction x (a⁻¹)⁻¹)).map
      (fun y => rightAction y a⁻¹)=_
    rw [inv_inv]
    rw [hx,hc,Measure.map_map (continuous_rightAction a⁻¹).measurable
      (continuous_rightAction a).measurable]
    simp only [Function.comp_def,rightAction_mul,mul_inv_cancel,rightAction_one,Measure.map_id']

end DukePrimeDegree

end

end OAI
