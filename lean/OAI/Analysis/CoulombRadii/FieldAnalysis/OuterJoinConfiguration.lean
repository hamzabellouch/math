import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RetainedFinePower

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def outerJoinConfiguration (m k : ℕ) :
    (Configuration m × Configuration k) ≃L[ℝ] Configuration (k+m) :=
  (ContinuousLinearEquiv.prodComm ℝ (Configuration m) (Configuration k)).trans
    (joinConfiguration k m)
lemma outerJoinConfiguration_apply (m k : ℕ) (x : Configuration m) (y : Configuration k) :
    outerJoinConfiguration m k (x,y) = joinConfiguration k m (y,x) := rfl
lemma outerJoinConfiguration_measurePreserving (m k : ℕ) :
    MeasurePreserving (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv
      (volume.prod volume) volume :=
  (joinConfiguration_measurePreserving k m).comp Measure.measurePreserving_swap
lemma outerJoinConfiguration_right_single (m k : ℕ) (a : Fin k × Fin 3) :
    outerJoinConfiguration m k (0, EuclideanSpace.single a 1) =
      EuclideanSpace.single (Fin.castAdd m a.1,a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [outerJoinConfiguration_apply, joinConfiguration_left]
    simp [PiLp.single_apply, Prod.ext_iff]
  · intro j
    rw [outerJoinConfiguration_apply, joinConfiguration_right]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (k+m) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
abbrev outerAppend {m k : ℕ} (s : Spins m) (t : Spins k) : Spins (k+m) := Fin.append t s
noncomputable def outerAppendEquiv (m k : ℕ) : Spins m × Spins k ≃ Spins (k+m) :=
  (Equiv.prodComm _ _).trans (Fin.appendEquiv k m)
noncomputable def outerPerm (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k+m)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr p (Equiv.refl (Fin m)))
lemma outerPerm_left (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    outerPerm m p (Fin.castAdd m i) = Fin.castAdd m (p i) := by simp [outerPerm]
lemma outerPerm_right (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin m) :
    outerPerm m p (Fin.natAdd k i) = Fin.natAdd k i := by simp [outerPerm]
lemma outerPerm_sign (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    (outerPerm m p).sign = p.sign := by simp [outerPerm, Equiv.Perm.sign_sumCongr]
lemma append_outerPerm {m k : ℕ} (s : Spins m) (t : Spins k) (p : Equiv.Perm (Fin k)) :
    outerAppend s t ∘ outerPerm m p = outerAppend s (t ∘ p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [outerAppend, outerPerm_left]
  · intro j; simp [outerAppend, outerPerm_right]
lemma permute_outer_join {m k : ℕ} (p : Equiv.Perm (Fin k)) (x : Configuration m)
    (y : Configuration k) :
    permute (outerPerm m p) (outerJoinConfiguration m k (x,y)) =
      outerJoinConfiguration m k (x, permute p y) := by
  rw [outerJoinConfiguration_apply, outerJoinConfiguration_apply]
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration k m (y,x) (outerPerm m p (Fin.castAdd m j),b) = _
    rw [outerPerm_left, joinConfiguration_left, joinConfiguration_left]
    rfl
  · intro j
    change joinConfiguration k m (y,x) (outerPerm m p (Fin.natAdd k j),b) = _
    rw [outerPerm_right, joinConfiguration_right, joinConfiguration_right]
lemma H1Vector.weak_partial_outerJoin {m k : ℕ} (ψ : H1Vector (k+m))
    (s : Spins (k+m)) (a : Fin k × Fin 3) :
    ∀ (η : Configuration m × Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η →
      (∫ z, ψ.value s (outerJoinConfiguration m k z) *
        (fderiv ℝ η z (0, EuclideanSpace.single a 1) : ℂ) ∂(volume.prod volume)) =
      -(∫ z, ψ.gradient s (Fin.castAdd m a.1, a.2) (outerJoinConfiguration m k z) *
        (η z : ℂ) ∂(volume.prod volume)) := by
  apply weak_directional_change (outerJoinConfiguration m k) (outerJoinConfiguration_measurePreserving m k)
    (0, EuclideanSpace.single a 1)
  rw [outerJoinConfiguration_right_single]
  exact ψ.weak_partial s (Fin.castAdd m a.1, a.2)

lemma H1Vector.outer_slices_H1 {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    ∀ᵐ x ∂(volume : Measure (Configuration m)),
      (∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y)) * (φ y : ℂ))) := by
  have hV (t : Spins k) := (ψ.value_L2 (outerAppend s t)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)
  have hG (t : Spins k) (a : Fin k × Fin 3) :=
    (ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
      (outerJoinConfiguration_measurePreserving m k)
  have hval : ∀ᵐ x ∂(volume : Measure (Configuration m)),
      ∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume :=
    ae_all_iff.mpr (fun t => memLp_fiber_ae
      (f := fun z : Configuration m × Configuration k =>
        ψ.value (outerAppend s t) (outerJoinConfiguration m k z)) (hV t))
  have hgrad := fun (t : Spins k) (a : Fin k × Fin 3) =>
    weak_slice (hV t) (hG t a) (EuclideanSpace.single a 1)
      (ψ.weak_partial_outerJoin (outerAppend s t) a)
  have hall := ae_all_iff.mpr (fun t => ae_all_iff.mpr (hgrad t))
  filter_upwards [hval, hall] with x hx hall
  exact ⟨hx, fun t a => (hall t a).2⟩

def H1Vector.OuterSliceRegular {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (x : Configuration m) : Prop :=
      (∀ t : Spins k, MemLp (fun y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))) 2 volume) ∧
      (∀ (t : Spins k) (a : Fin k × Fin 3),
        MemLp (fun y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))) 2 volume ∧
        ∀ (φ : Configuration k → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y, ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) *
          (fderiv ℝ φ y (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ y, ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y)) * (φ y : ℂ)))

lemma H1Vector.outerSliceRegular_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    ∀ᵐ x ∂volume, ψ.OuterSliceRegular s x := ψ.outer_slices_H1 s

noncomputable def H1Vector.outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (x : Configuration m) : H1Vector k := by
  classical
  exact if h : ψ.OuterSliceRegular s x then
    { value := fun t y => ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))
      gradient := fun t a y => ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
        (outerJoinConfiguration m k (x,y))
      value_L2 := h.1
      partial_L2 := fun t a => (h.2 t a).1
      weak_partial := fun t a => (h.2 t a).2 }
  else H1Vector.zero k

lemma H1Vector.outerSlice_value {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    {x : Configuration m} (hx : ψ.OuterSliceRegular s x) (t : Spins k) (y : Configuration k) :
    (ψ.outerSlice s x).value t y = ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y)) := by
  simp [H1Vector.outerSlice, hx]

lemma H1Vector.outerSlice_gradient {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    {x : Configuration m} (hx : ψ.OuterSliceRegular s x) (t : Spins k) (a : Fin k × Fin 3)
    (y : Configuration k) :
    (ψ.outerSlice s x).gradient t a y =
      ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) (outerJoinConfiguration m k (x,y)) := by
  simp [H1Vector.outerSlice, hx]

lemma mass_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    (fun x => mass (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [mass, ψ.outerSlice_value s hx]

lemma mass_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    Integrable (fun x => mass (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (mass_outerSlice_ae ψ s).symm
  apply integrable_finsetSum
  intro t _
  have h := ((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
  exact h.integral_prod_left

lemma integral_mass_outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) :
    (∑ s : Spins m, ∫ x, mass (ψ.outerSlice s x)) = mass ψ := by
  calc
    _ = ∑ s : Spins m, ∑ t : Spins k, ∫ z, ‖ψ.value (outerAppend s t) z‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_congr_ae (mass_outerSlice_ae ψ s), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        have h := ((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
          (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
        change Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at h
        rw [← integral_prod _ h]
        exact (outerJoinConfiguration_measurePreserving m k).integral_comp'
          (fun z => ‖ψ.value (outerAppend s t) z‖^2)
      · intro t _
        exact (((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
          (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow
            (p := 2) (by decide)).integral_prod_left
    _ = mass ψ := by
      rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
        ∫ z, ‖ψ.value (outerAppend st.1 st.2) z‖^2)]
      exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

lemma H1Vector.outerSlice_antisymmetric {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (hψ : ∀ (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z) :
    ∀ᵐ x ∂volume, Antisymmetric (ψ.outerSlice s x) := by
  have h (p : Equiv.Perm (Fin k)) (t : Spins k) :=
    Measure.ae_ae_of_ae_prod ((outerJoinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hψ p t))
  have hall := ae_all_iff.mpr (fun p => ae_all_iff.mpr (h p))
  filter_upwards [ψ.outerSliceRegular_ae s, hall] with x hx hxA
  intro p t
  filter_upwards [hxA p t] with y hy
  change ψ.value (outerAppend s t ∘ outerPerm m p)
      (permute (outerPerm m p) (outerJoinConfiguration m k (x,y))) =
    (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t)
      (outerJoinConfiguration m k (x,y)) at hy
  simpa only [ψ.outerSlice_value s hx, append_outerPerm, outerPerm_sign, permute_outer_join] using hy

lemma Antisymmetric.outerSlice {m k : ℕ} {ψ : H1Vector (k+m)} (hψ : Antisymmetric ψ)
    (s : Spins m) : ∀ᵐ x ∂volume, Antisymmetric (ψ.outerSlice s x) :=
  ψ.outerSlice_antisymmetric s (fun p t => hψ (outerPerm m p) (outerAppend s t))

lemma kinetic_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    (fun x => kinetic (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ y, ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [kinetic, ψ.outerSlice_gradient s hx]

lemma kinetic_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    Integrable (fun x => kinetic (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (kinetic_outerSlice_ae ψ s).symm
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro a _
  exact (((ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)).integral_prod_left

lemma integral_kinetic_outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) :
    (∑ s : Spins m, ∫ x, kinetic (ψ.outerSlice s x)) =
      (1/2 : ℝ) * ∑ st : Spins (k+m), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.castAdd m a.1,a.2) z‖^2 := by
  have hs (s : Spins m) : (∫ x, kinetic (ψ.outerSlice s x)) =
      (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) z‖^2 := by
    rw [integral_congr_ae (kinetic_outerSlice_ae ψ s), integral_const_mul]
    congr 1
    have hi (t : Spins k) (a : Fin k × Fin 3) :
        Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) (outerJoinConfiguration m k z)‖^2)
          (volume.prod volume) :=
      ((ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
        (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun a _ => (hi t a).integral_prod_left))]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum _ (fun a _ => (hi t a).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_prod _ (hi t a)]
    exact (outerJoinConfiguration_measurePreserving m k).integral_comp'
      (fun z => ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) z‖^2)
  simp_rw [hs]
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∑ a : Fin k × Fin 3, ∫ z, ‖ψ.gradient (outerAppend st.1 st.2) (Fin.castAdd m a.1,a.2) z‖^2)]
  congr 1
  exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

lemma potentialForm_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (V : Configuration k → ℝ) :
    (fun x => potentialForm V (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V y * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.outerSlice_value s hx]

lemma potentialForm_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (V : Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z => V ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value (outerAppend s t) z‖^2)) :
    Integrable (fun x => potentialForm V (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (potentialForm_outerSlice_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((outerJoinConfiguration_measurePreserving m k).integrable_comp_emb
    (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  have H' : Integrable (fun z : Configuration m × Configuration k =>
      V z.2 * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) := by
    change Integrable (fun z : Configuration m × Configuration k =>
      V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
        ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  exact H'.integral_prod_left

lemma integral_potentialForm_outerSlice {m k : ℕ} (ψ : H1Vector (k+m))
    (V : Configuration k → ℝ)
    (hV : ∀ st : Spins (k+m), Integrable (fun z => V ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm V (ψ.outerSlice s x)) =
      ∑ st : Spins (k+m), ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm V (ψ.outerSlice s x)) =
      ∑ t : Spins k, ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_outerSlice_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.2 * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((outerJoinConfiguration_measurePreserving m k).integrable_comp_emb
        (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (outerAppend s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (outerJoinConfiguration_measurePreserving m k).integral_comp'
        (fun z => V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

lemma outerJoinConfiguration_symm_snd (m k : ℕ) (z : Configuration (k+m)) :
    ((outerJoinConfiguration m k).symm z).2 = ((joinConfiguration k m).symm z).1 := rfl
lemma outer_finePower_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (k+m)) (st : Spins (k+m)) :
    Integrable (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply (hw.const_mul (((k:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*k)).mono'
  · exact ((retainedFinePower_measurable b r hr).comp
      (measurable_snd.comp (outerJoinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (retainedFinePower_nonneg ..) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (retainedFinePower_bound hb r _) (sq_nonneg _)

theorem outer_block_retained_fine_kinetic_lower {m k : ℕ} (ψ : H1Vector (k+m))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2) ψ -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) * mass ψ ≤ outerKinetic (m:=k) (k:=m) ψ := by
  let C := (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)
  have hs (s : Spins m) :
      thomasFermiCoefficient * (∫ x, potentialForm (retainedFinePower b r) (ψ.outerSlice s x)) -
        C * (∫ x, mass (ψ.outerSlice s x)) ≤ ∫ x, kinetic (ψ.outerSlice s x) := by
    rw [←integral_const_mul, ←integral_const_mul,
      ←integral_sub ((potentialForm_outerSlice_integrable ψ s _ (fun t => outer_finePower_integrable hb r hr ψ (outerAppend s t))).const_mul _)
        ((mass_outerSlice_integrable ψ s).const_mul C)]
    apply integral_mono_ae
      (((potentialForm_outerSlice_integrable ψ s _ (fun t => outer_finePower_integrable hb r hr ψ (outerAppend s t))).const_mul _).sub
        ((mass_outerSlice_integrable ψ s).const_mul C)) (kinetic_outerSlice_integrable ψ s)
    exact (ψ.outerSlice_antisymmetric s (hψ s)).mono fun x hx =>
      retained_fine_kinetic_lower_all (ψ.outerSlice s x) hx hb r hr
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simp only [Finset.sum_sub_distrib, ←Finset.mul_sum] at H
  rw [integral_potentialForm_outerSlice ψ _ (outer_finePower_integrable hb r hr ψ),
    integral_mass_outerSlice, integral_kinetic_outerSlice] at H
  exact H
lemma ae_outer_block_position_injective (m k : ℕ) :
    ∀ᵐ z : Configuration (k+m), Function.Injective (position ((outerJoinConfiguration m k).symm z).2) := by
  filter_upwards [ae_position_injective (k+m)] with z hz
  intro i j hij
  have h : Fin.castAdd m i = Fin.castAdd m j := hz (by simpa only [outerJoinConfiguration_symm_snd, position_split_left] using hij)
  exact Fin.ext (congrArg (fun z : Fin (k+m) => z.val) h)

lemma ae_outer_fine_pair_bound {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) :
    ∀ᵐ z : Configuration (k+m),
      retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 ≤
        pairPotential ((outerJoinConfiguration m k).symm z).2 + ((2*Real.pi+1)/(2*b))*k := by
  filter_upwards [ae_outer_block_position_injective m k] with z hz
  have h := retained_fine_pair_lower hb (r ((outerJoinConfiguration m k).symm z).2)
    (position ((outerJoinConfiguration m k).symm z).2) hz
  have hc : ((r ((outerJoinConfiguration m k).symm z).2).card : ℝ) ≤ k := by
    exact_mod_cast (show (r ((outerJoinConfiguration m k).symm z).2).card ≤ k by simpa using Finset.card_le_univ (r ((outerJoinConfiguration m k).symm z).2))
  have hC : 0 ≤ (2*Real.pi+1)/(2*b) := by positivity
  have hh := mul_le_mul_of_nonneg_left hc hC
  change retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 -
    ((2*Real.pi+1)/(2*b))*(r ((outerJoinConfiguration m k).symm z).2).card ≤
      pairPotential ((outerJoinConfiguration m k).symm z).2 at h
  linarith

lemma outer_fineCoulomb_integrable {m k : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration k → Finset (Fin k)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (ψ : H1Vector (k+m)) (st : Spins (k+m)) :
    Integrable (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2) := by
  have hw : Integrable (fun z => ‖ψ.value st z‖^2) :=
    (ψ.value_L2 st).integrable_norm_pow (p:=2) (by decide)
  apply ((ψ.outer_pair_integrable st).add (hw.const_mul (((2*Real.pi+1)/(2*b))*k))).mono'
  · exact ((retainedFineCoulomb_measurable b r hr).comp
      (measurable_snd.comp (outerJoinConfiguration m k).symm.continuous.measurable)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · filter_upwards [ae_outer_fine_pair_bound (m:=m) hb r] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (retainedFineCoulomb_nonneg ..) (sq_nonneg _))]
    simpa only [add_mul, Pi.add_apply, outerJoinConfiguration_symm_snd] using mul_le_mul_of_nonneg_right hz (sq_nonneg ‖ψ.value st z‖)

theorem outer_block_retained_fine_pair_lower {m k : ℕ} (ψ : H1Vector (k+m))
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    potentialForm (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2) ψ -
      (((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
    potentialForm (fun z => pairPotential ((outerJoinConfiguration m k).symm z).2) ψ :=
  sub_le_iff_le_add.mpr (potentialForm_le_add_const ψ (outer_fineCoulomb_integrable hb r hr ψ)
    ψ.outer_pair_integrable (ae_outer_fine_pair_bound hb r))

theorem outer_block_retained_fine_energy_lower {m k : ℕ} (ψ : H1Vector (k+m))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2) ψ +
    potentialForm (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2) ψ -
      (((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) +
        ((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
      outerKinetic (m:=k) (k:=m) ψ + potentialForm (fun z => pairPotential ((outerJoinConfiguration m k).symm z).2) ψ := by
  have h1 := outer_block_retained_fine_kinetic_lower ψ hψ hb r hr
  have h2 := outer_block_retained_fine_pair_lower ψ hb r hr
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
