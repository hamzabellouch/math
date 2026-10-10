import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorOperatorResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinTensorResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreTensorFiber

namespace OAI

/-! The polynomial tensor residual is the actual differential residual of
finite tensor synthesis in the full physical spin space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def finiteTensorResidualValue {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (x : Configuration n) : ℂ :=
  ∑ b, c b*tensorOrbitalResidual v r b s x

theorem tensorOrbitalResidual_memLp {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (b : Fin n → α) (s : SpinConfiguration n) :
    MemLp (tensorOrbitalResidual v r b s) 2 := by
  apply memLp_finsetSum Finset.univ
  intro i _
  have h := (Coulomb.slotTensor_memLp (fun j y => v (b j) y (s j))
    (fun j y => r (b j) y (s j)) (fun j => hv (b j) (s j)) (fun j => hr (b j) (s j)) 1 i).comp_measurePreserving
    (Coulomb.configurationMeasurableEquiv_measurePreserving n)
  convert h using 1
  funext x
  simp only [Function.comp_apply,Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorResidualValue_memLp {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    MemLp (finiteTensorResidualValue v r c s) 2 :=
  memLp_finsetSum Finset.univ (fun b _ => (tensorOrbitalResidual_memLp v r hv hr b s).const_mul (c b))

theorem finiteTensorResidualValue_eq_flat {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (x : Configuration n) :
    finiteTensorResidualValue v r c s x =
      tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
        (fun a => Coulomb.flatSpinOrbital (r a)) c (spinConfigurationPoint s x) := by
  unfold finiteTensorResidualValue tensorOrbitalResidual tensorTotalReplacement tensorSlotReplacement
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  change c b*(r (b i) (Coulomb.position x i) (s i)*
    ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      c b*Coulomb.slotTensor (fun j y => v (b j) y (s j))
        (fun j y => r (b j) y (s j)) 1 i (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem finiteTensorResidualValue_norm {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2) (c : (Fin n → α) → ℂ) :
    (∑ s, ∫ x, ‖finiteTensorResidualValue v r c s x‖^2) =
      ∫ z, ‖tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
        (fun a => Coulomb.flatSpinOrbital (r a)) c z‖^2
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  have h := Coulomb.spinConfiguration_integral (fun s x => ‖finiteTensorResidualValue v r c s x‖^2)
    (fun s => (finiteTensorResidualValue_memLp v r hv hr c s).norm.integrable_sq)
  simp only [finiteTensorResidualValue_eq_flat,spinConfigurationPoint_coordinates] at h
  simpa only [finiteTensorResidualValue_eq_flat] using h.symm

theorem finiteTensorState_value_C2 {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) :
    ContDiff ℝ 2 ((finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c).value s) := by
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul (coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i)))

theorem finiteTensorState_gradient_classical {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2) (c : (Fin n → α) → ℂ)
    (s : SpinConfiguration n) (a : Fin n × Fin 3) (x : Configuration n) :
    (finiteTensorState v hv hL2 hpartial c).gradient s a x =
      configurationComplexPartial ((finiteTensorState v hv hL2 hpartial c).value s) a x := by
  have h := configurationComplexPartial_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => tensorOrbital_C1 v hv b s) a x
  exact h.symm

theorem finiteTensorState_operator_residual {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : (Fin n → α) → ℂ) (s : SpinConfiguration n) (x : Configuration n) :
    let p := finiteTensorState v (fun a t => (hv a t).of_le (by norm_num)) hL2 hpartial c
    finiteTensorResidualValue v r c s x =
      (-1/2:ℂ)*configurationComplexLaplacian (p.value s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*p.value s x-((n:ℝ)*E:ℝ)*p.value s x := by
  dsimp only
  change (∑ b, c b*tensorOrbitalResidual v r b s x) =
    (-1/2:ℂ)*configurationComplexLaplacian (fun y => ∑ b, c b*Coulomb.tensorOrbital v b s y) x+
    ((∑ i, V (Coulomb.position x i)):ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)-
    ((n:ℝ)*E:ℝ)*(∑ b, c b*Coulomb.tensorOrbital v b s x)
  rw [configurationComplexLaplacian_sum c (fun b => Coulomb.tensorOrbital v b s)
    (fun b => coordinateProduct_C2 (fun i y => v (b i) y (s i)) (fun i => hv (b i) (s i))) x]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← tensorOrbital_operator_residual v r hv V E heq b s x]
  ring

end ContinuumCoulomb

end

end OAI
