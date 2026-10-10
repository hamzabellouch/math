import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.ConfigurationMeasurableEquiv
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeakDirectionalUnique

namespace OAI

noncomputable section

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
lemma H1Vector.gradient_congr_ae {n : ℕ} (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) (s : Spins n) (a : Fin n × Fin 3) :
    u.gradient s a =ᵐ[volume] v.gradient s a := by
  apply weak_directional_unique (f := u.value s) (EuclideanSpace.single a 1)
    ((u.partial_L2 s a).locallyIntegrable (by norm_num))
    ((v.partial_L2 s a).locallyIntegrable (by norm_num))
  · intro φ hφ hc
    simpa only [mul_comm] using u.weak_partial s a φ hφ hc
  · intro φ hφ hc
    rw [show (∫ x, (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)*u.value s x) =
      (∫ x, (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)*v.value s x) from
      integral_congr_ae ((he s).mono (fun x hx => by dsimp only; rw [hx]))]
    simpa only [mul_comm] using v.weak_partial s a φ hφ hc

def ConfigSupported {n : ℕ} (u : H1Vector n) (A : Set (Configuration n)) : Prop :=
  ∀ s, ∀ᵐ x ∂volume, x ∉ A → u.value s x = 0

lemma ConfigSupported.gradient {n : ℕ} {u : H1Vector n} {A : Set (Configuration n)}
    (hu : ConfigSupported u A) (hA : IsClosed A) (s : Spins n) (a : Fin n × Fin 3) :
    ∀ᵐ x ∂volume, x ∉ A → u.gradient s a x = 0 := by
  apply weak_directional_zero_on_open (EuclideanSpace.single a 1)
    ((u.partial_L2 s a).locallyIntegrable (by norm_num))
    (fun φ hφ hc => by simpa only [mul_comm] using u.weak_partial s a φ hφ hc)
    Aᶜ hA.isOpen_compl (hu s)

lemma continuous_position {n : ℕ} (i : Fin n) :
    Continuous (fun x : Configuration n => position x i) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun b => (EuclideanSpace.proj (i,b)).continuous)

def allPositions {n : ℕ} (A : Set Space) : Set (Configuration n) :=
  {x | ∀ i, position x i ∈ A}

lemma isClosed_allPositions {n : ℕ} {A : Set Space} (hA : IsClosed A) :
    IsClosed (allPositions (n := n) A) := by
  have he : allPositions (n := n) A = ⋂ i, (fun x : Configuration n => position x i) ⁻¹' A := by
    ext x
    simp [allPositions]
  rw [he]
  exact isClosed_iInter (fun i => hA.preimage (continuous_position i))

def SpatiallySupported {n : ℕ} (u : H1Vector n) (A : Set Space) : Prop :=
  ConfigSupported u (allPositions A)

lemma spatialSupport_gradient {n : ℕ} {u : H1Vector n} {A : Set Space}
    (hu : SpatiallySupported u A) (hA : IsClosed A) (s : Spins n) (a : Fin n × Fin 3) :
    ∀ᵐ x ∂volume, (∃ i, position x i ∉ A) → u.gradient s a x = 0 := by
  simpa only [allPositions, Set.mem_ofPred_eq, not_forall] using
    ConfigSupported.gradient hu (isClosed_allPositions hA) s a
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compactSupport_slice_right {φ : E × F → ℝ} (hC : HasCompactSupport φ) (x : E) :
    HasCompactSupport (fun y => φ (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hC.image continuous_snd)
  intro y hy
  exact ⟨(x,y), subset_tsupport φ hy, rfl⟩

lemma tensor_weak_right {u : E → ℂ} {v d : F → ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hd : MemLp d 2 volume)
    (a : F)
    (hvd : ∀ φ : F → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, (fderiv ℝ φ y a : ℂ)*v y) = -(∫ y, (φ y : ℂ)*d y))
    (φ : E × F → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ z, (fderiv ℝ φ z (0,a) : ℂ)*(u z.1*v z.2) ∂(volume.prod volume)) =
      -(∫ z, (φ z : ℂ)*(u z.1*d z.2) ∂(volume.prod volume)) := by
  have hT : MemLp (fun z => (φ z : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hC.comp_left Complex.ofReal_zero)
  have hD : MemLp (fun z => (fderiv ℝ φ z (0,a) : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hC.fderiv_apply ℝ (0,a)).comp_left Complex.ofReal_zero)
  rw [integral_prod (fun z => (fderiv ℝ φ z (0,a) : ℂ)*(u z.1*v z.2))
      (hD.integrable_mul (tensorPair_memLp hu hv)),
    integral_prod (fun z => (φ z : ℂ)*(u z.1*d z.2))
      (hT.integrable_mul (tensorPair_memLp hu hd)), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  have hφx : ContDiff ℝ ∞ (fun y => φ (x,y)) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hdφ (y : F) : fderiv ℝ (fun y => φ (x,y)) y a = fderiv ℝ φ (x,y) (0,a) := by
    change fderiv ℝ (φ ∘ Prod.mk x) y a = _
    rw [(hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)) |>.fderiv]
    simp
  have H := hvd (fun y => φ (x,y)) hφx (compactSupport_slice_right hC x)
  simp_rw [hdφ] at H
  simp_rw [mul_left_comm _ (u x), integral_const_mul]
  rw [H]
  ring
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compactSupport_slice_left {φ : E × F → ℝ} (hC : HasCompactSupport φ) (y : F) :
    HasCompactSupport (fun x => φ (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hC.image continuous_fst)
  intro x hx
  exact ⟨(x,y), subset_tsupport φ hx, rfl⟩

lemma tensor_weak_left {u d : E → ℂ} {v : F → ℂ}
    (hu : MemLp u 2 volume) (hd : MemLp d 2 volume) (hv : MemLp v 2 volume)
    (a : E)
    (hud : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x))
    (φ : E × F → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ z, (fderiv ℝ φ z (a,0) : ℂ)*(u z.1*v z.2) ∂(volume.prod volume)) =
      -(∫ z, (φ z : ℂ)*(d z.1*v z.2) ∂(volume.prod volume)) := by
  have hT : MemLp (fun z => (φ z : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hC.comp_left Complex.ofReal_zero)
  have hD : MemLp (fun z => (fderiv ℝ φ z (a,0) : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hC.fderiv_apply ℝ (a,0)).comp_left Complex.ofReal_zero)
  rw [integral_prod_symm (fun z => (fderiv ℝ φ z (a,0) : ℂ)*(u z.1*v z.2))
      (hD.integrable_mul (tensorPair_memLp hu hv)),
    integral_prod_symm (fun z => (φ z : ℂ)*(d z.1*v z.2))
      (hT.integrable_mul (tensorPair_memLp hd hv)), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  have hφy : ContDiff ℝ ∞ (fun x => φ (x,y)) := hφ.comp (contDiff_id.prodMk contDiff_const)
  have hdφ (x : E) : fderiv ℝ (fun x => φ (x,y)) x a = fderiv ℝ φ (x,y) (a,0) := by
    exact congrArg (fun A : E →L[ℝ] ℝ => A a)
      (((hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))).fderiv)
  have H := hud (fun x => φ (x,y)) hφy (compactSupport_slice_left hC y)
  simp_rw [hdφ] at H
  simp_rw [← mul_assoc, integral_mul_const]
  rw [H]
  ring
end Coulomb

end

end OAI
