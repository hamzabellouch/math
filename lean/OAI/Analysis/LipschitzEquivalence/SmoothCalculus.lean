import OAI.Analysis.LipschitzEquivalence.FiniteRows

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def smoothSubmodule (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Submodule ℝ (H → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (fun _ : H => (0:ℝ)))
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ ∞ f from hf).const_smul c

abbrev Smooth (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type _ := ↥(smoothSubmodule H)

namespace Smooth

def eval (p : H) : Smooth H →ₗ[ℝ] ℝ where
  toFun f := (f : H → ℝ) p
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem contDiff {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : Smooth H) : ContDiff ℝ ∞ (f : H → ℝ) := f.property

theorem differentiable (f : Smooth H) : Differentiable ℝ (f : H → ℝ) :=
  f.contDiff.differentiable (by simp)

def grad (p : H) : Smooth H →ₗ[ℝ] H where
  toFun f := gradient (f : H → ℝ) p
  map_add' f g := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ ((f : H → ℝ)+(g : H → ℝ)) p) = _
    rw [fderiv_add (f.differentiable p) (g.differentiable p),map_add]
    rfl
  map_smul' c f := by
    change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (c • (f : H → ℝ)) p) = _
    rw [fderiv_const_smul (f.differentiable p) c,map_smul]
    rfl

theorem grad_eq (f : Smooth H) (p : H) : grad p f = gradient (f : H → ℝ) p := rfl

theorem norm_grad (f : Smooth H) (p : H) : ‖grad p f‖ = ‖fderiv ℝ (f : H → ℝ) p‖ :=
  (InnerProductSpace.toDual ℝ H).symm.norm_map _

theorem grad_contDiff (f : Smooth H) : ContDiff ℝ ∞ (fun p => grad p f) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (f.contDiff.fderiv_right (by simp))

theorem grad_continuous (f : Smooth H) : Continuous (fun p => grad p f) :=
  f.grad_contDiff.continuous

theorem grad_norm_le {C : ℝ≥0} (f : Smooth H) (h : LipschitzWith C (f : H → ℝ)) (p : H) :
    ‖grad p f‖ ≤ C := by
  rw [norm_grad]
  exact norm_fderiv_le_of_lipschitz ℝ h

def mul (f g : Smooth H) : Smooth H := ⟨fun p => (f : H → ℝ) p*(g : H → ℝ) p,
  f.contDiff.mul g.contDiff⟩

@[simp] theorem mul_apply (f g : Smooth H) (p : H) : (f.mul g : H → ℝ) p = f.val p*g.val p := rfl

theorem grad_mul (f g : Smooth H) (p : H) :
    grad p (f.mul g) = f.val p • grad p g + g.val p • grad p f := by
  apply (InnerProductSpace.toDual ℝ H).injective
  simp only [grad_eq,toDual_gradient,map_add,map_smul]
  exact fderiv_mul (f.differentiable p) (g.differentiable p)

end Smooth

def edge (p q : H) (t : ℝ) : H := q+t • (p-q)

theorem edge_continuous {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) : Continuous (edge p q) := by
  unfold edge
  fun_prop

theorem edge_mem {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : Set H} (hK : Convex ℝ K) {p q : H} (hp : p ∈ K) (hq : q ∈ K)
    {t : ℝ} (ht : t ∈ Icc 0 1) : edge p q t ∈ K := by
  have he : edge p q t = (1-t) • q+t • p := by simp [edge,sub_smul,smul_sub]; module
  rw [he]
  exact hK hq hp (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem edge_hasDerivAt {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) (t : ℝ) : HasDerivAt (edge p q) (p-q) t := by
  unfold edge
  simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (p-q)).const_add q

theorem smooth_edge_integral (f : Smooth H) (p q : H) :
    (∫ t in (0:ℝ)..1, fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) = f.val p-f.val q := by
  have hint : IntervalIntegrable (fun t => fderiv ℝ (f : H → ℝ) (edge p q t) (p-q)) volume 0 1 :=
    ((f.contDiff.continuous_fderiv (by simp)).comp (edge_continuous p q)).clm_apply continuous_const
      |>.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) 1) => (f.differentiable _).hasFDerivAt.comp_hasDerivAt t (edge_hasDerivAt p q t)) hint
  simpa [edge] using h

open FreeSpace

def gradEnergy (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2

def gradMass (a : MolecularData H) (f : Smooth H) : ℝ :=
  ∑ i, (|a.coeff i| *dist (a.p i) (a.q i)) *
    ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖

theorem gradEnergy_nonneg (a : MolecularData H) (f : Smooth H) : 0 ≤ gradEnergy a f := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)

theorem gradMass_nonneg (a : MolecularData H) (f : Smooth H) : 0 ≤ gradMass a f := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)

theorem gradEnergy_midpoint (a : MolecularData H) (f g : Smooth H) :
    gradEnergy a ((1/2:ℝ) • (f+g)) =
      (gradEnergy a f+gradEnergy a g)/2-gradEnergy a (f-g)/4 := by
  have he (p q : H) :
      (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) ((1/2:ℝ) • (f+g))‖^2) =
      ((∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) f‖^2)+
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) g‖^2))/2-
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) (f-g)‖^2)/4 := by
    have hf : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 := ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) g‖^2) volume 0 1 := ((g.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hfg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) (f-g)‖^2) volume 0 1 := (((f-g).grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    simp only [map_smul,map_add,hilbert_midpoint_energy,← map_sub]
    rw [intervalIntegral.integral_sub ((hf.add hg).div_const 2) (hfg.div_const 4),
      intervalIntegral.integral_div,intervalIntegral.integral_add hf hg,intervalIntegral.integral_div]
  simp only [gradEnergy,he,mul_sub,← mul_div_assoc,mul_add,Finset.sum_sub_distrib,
    ← Finset.sum_div,Finset.sum_add_distrib]

end LipschitzCounterexample.CompactWSC
end

end OAI
