import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePointMeasurable
import OAI.Analysis.CoulombRadii.SpectralTheory.AmbientEigen
import OAI.Analysis.CoulombRadii.FormDomain.RegularizedKinetic

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma potentialForm_smoothMul {n:ℕ} (u:H1Vector n) (f:SmoothBoundedCoefficient) (i:Fin n)
    (V:Configuration n → ℝ):
    potentialForm V (u.smoothMul (fun x => f.value (position x i)) (f.lift_smooth i)
      f.bound f.derivBound (fun x => f.value_le (position x i)) (f.lift_deriv_le i))=
    potentialForm (fun x => V x*(f.value (position x i))^2) u := by
  unfold potentialForm
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
lemma regularized_weighted_core (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (l e:ℝ) (hl:l≠0) (he:0<e):
    potentialForm (fun x => (∑ j:Fin k,coulombKernel (position x 0-position x (Fin.natAdd 1 j)))*
      (regularizedU l e (position x 0))⁻¹) u ≤
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x 0)*
      (regularizedU l e (position x 0))⁻¹) u := by
  let f:=rootReciprocalCoefficient l e hl he
  let w:=reciprocalCoefficient l e hl he
  let z:=u.smoothMul (fun x => f.value (position x 0)) (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let v:=z.smoothMul (fun x => f.value (position x 0)) (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let v':=u.smoothMul (fun x => w.value (position x 0)) (w.lift_smooth 0) w.bound w.derivBound
    (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0)
  have hv:∀ s,v.value s =ᵐ[volume] v'.value s := by
    intro s
    filter_upwards [] with x
    change (f.value (position x 0):ℂ)*((f.value (position x 0):ℂ)*u.value s x)=
      (w.value (position x 0):ℂ)*u.value s x
    rw [←mul_assoc,←sq,←Complex.ofReal_pow,rootReciprocalCoefficient_sq]
  have hk:0≤∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x) := by
    apply Finset.sum_nonneg
    intro s _
    have H:=regularized_weight_kinetic u s l e hl he
    change 0≤∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v'.gradient s (0,a) x) at H
    have Heq:(∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x))=
        ∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v'.gradient s (0,a) x) := by
      apply Finset.sum_congr rfl
      intro a _
      exact integral_congr_ae ((v.gradient_congr_ae v' hv s (0,a)).mono (fun x hx => by dsimp only; rw [hx]))
    rw [Heq]
    exact H
  have hc:∀ (a:Fin k × Fin 3) x,fderiv ℝ (fun y => f.value (position y 0)) x
      (EuclideanSpace.single (Fin.natAdd 1 a.1,a.2) 1)=0 := by
    intro a x
    rw [oneBody_derivative f.value f.smooth]
    exact ite_eq_right (by intro H; have hh:=congrArg Fin.val H; simp only [Fin.val_zero,Fin.val_natAdd] at hh; omega)
  have hp:∀ (p:Equiv.Perm (Fin k)) x,f.value (position (permute (corePerm 1 p) x) 0)=f.value (position x 0) := by
    intro p x
    rw [position_permute]
    have H:=corePerm_left 1 p (0:Fin 1)
    change corePerm 1 p 0=0 at H
    rw [H]
  have H:=weighted_core_inequality Z hZ u ha hm hmin _ (f.lift_smooth 0)
    f.bound f.derivBound (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0) hc hp hk
  dsimp only at H
  rw [potentialForm_smoothMul,potentialForm_smoothMul] at H
  simp only [f,rootReciprocalCoefficient_sq,reciprocalCoefficient,crossPotential,
    Fin.sum_univ_one,position_split_left,position_split_right,nuclearPotential,attraction,atom,
    show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl,sub_zero] at H
  exact H
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
def atomicCross {k:ℕ} (x:Configuration (1+k)):ℝ:=
  ∑ j:Fin k,coulombKernel (position x 0-position x (Fin.natAdd 1 j))
lemma atomicCross_integrable {k:ℕ} (u:H1Vector (1+k)) (s:Spins (1+k)):
    Integrable (fun x => atomicCross x*‖u.value s x‖^2) := by
  simpa only [crossPotential,Fin.sum_univ_one,position_split_left,position_split_right,
    show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl,atomicCross] using u.cross_integrable (m:=1) (k:=k) s
lemma potentialForm_bdd_mul_integrable {n:ℕ} (u:H1Vector n) (V f:Configuration n → ℝ)
    (hV:∀ s,Integrable (fun x => V x*‖u.value s x‖^2))
    (hf:AEStronglyMeasurable f volume) {C:ℝ} (hC:∀ᵐ x,‖f x‖≤C) (s:Spins n):
    Integrable (fun x => V x*f x*‖u.value s x‖^2) := by
  exact ((hV s).mul_bdd hf hC).congr (Eventually.of_forall (fun x => by dsimp only; ring))
lemma potentialForm_tendsto_bdd {n:ℕ} (u:H1Vector n) (V:Configuration n → ℝ)
    (hV:∀ s,Integrable (fun x => V x*‖u.value s x‖^2))
    (f:ℕ → Configuration n → ℝ) (g:Configuration n → ℝ) (C:ℝ)
    (hf:∀ j,AEStronglyMeasurable (f j) volume) (hC:∀ j,∀ᵐ x,‖f j x‖≤C)
    (ht:∀ᵐ x,Tendsto (fun j => f j x) atTop (𝓝 (g x))):
    Tendsto (fun j => potentialForm (fun x => V x*f j x) u) atTop
      (𝓝 (potentialForm (fun x => V x*g x) u)) := by
  unfold potentialForm
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => ‖V x*‖u.value s x‖^2‖*C)
  · intro j
    exact (potentialForm_bdd_mul_integrable u V (f j) hV (hf j) (hC j) s).aestronglyMeasurable
  · exact (hV s).norm.mul_const C
  · intro j
    filter_upwards [hC j] with x hx
    rw [show V x*f j x*‖u.value s x‖^2=(V x*‖u.value s x‖^2)*f j x by ring,norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [ht] with x hx
    exact (tendsto_const_nhds.mul hx).mul_const _

def atomicWeight (e:ℝ) (x:Space):ℝ:=(coulombKernel x+e)⁻¹
lemma atomicWeight_bound {e:ℝ} (he:0<e) (x:Space):‖atomicWeight e x‖≤e⁻¹ := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold atomicWeight coulombKernel; positivity)]
  exact inv_anti₀ he (by change e≤‖x‖⁻¹+e; exact le_add_of_nonneg_left (inv_nonneg.mpr (norm_nonneg x)))
lemma atomicWeight_measurable (e:ℝ):Measurable (atomicWeight e) :=
  (coulombKernel_measurable.add_const e).inv
lemma regularized_weighted_core_limit (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (e:ℝ) (he:0<e):
    potentialForm (fun x => atomicCross x*atomicWeight e (position x 0)) u ≤
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x 0)*atomicWeight e (position x 0)) u := by
  let l:ℕ → ℝ:=fun j => ((j:ℝ)+1)⁻¹
  have hl:∀ j,l j≠0:=fun j => ne_of_gt (by dsimp [l]; positivity)
  have ht:Tendsto l atTop (𝓝 0):=by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  let f:ℕ → Configuration (1+k) → ℝ:=fun j x => (regularizedU (l j) e (position x 0))⁻¹
  have hf:∀ j,AEStronglyMeasurable (f j) volume:=fun j =>
    ((reciprocalCoefficient (l j) e (hl j) he).lift_smooth (0:Fin (1+k))).continuous.aestronglyMeasurable
  have hb:∀ j,∀ᵐ x,‖f j x‖≤e⁻¹ := by
    intro j
    exact Eventually.of_forall (fun x => by simpa only [f,reciprocalCoefficient,Real.norm_eq_abs] using
      (reciprocalCoefficient (l j) e (hl j) he).value_le (position x 0))
  have hft:∀ᵐ x:Configuration (1+k),Tendsto (fun j => f j x) atTop (𝓝 (atomicWeight e (position x 0))) := by
    filter_upwards [ae_position_ne (1+k) 0] with x hx
    exact ((NeutralAtom.regularizedKernel_tendsto ht (hx 0)).add_const e).inv₀
      (by change (‖position x 0‖⁻¹+e)≠0; positivity)
  have hleft:=potentialForm_tendsto_bdd u atomicCross (atomicCross_integrable u) f _ _ hf hb hft
  have hv:∀ s,Integrable (fun x:Configuration (1+k) => (Z:ℝ)*coulombKernel (position x 0)*‖u.value s x‖^2) := by
    intro s
    simpa only [sub_zero,mul_assoc] using
      ((u.nuclear_coulomb_integrable_bound s 0 (0:Space) (by norm_num : (0:ℝ)<1)).1.const_mul (Z:ℝ))
  have hright:=potentialForm_tendsto_bdd u (fun x => (Z:ℝ)*coulombKernel (position x 0)) hv f _ _ hf hb hft
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun j =>
    regularized_weighted_core Z hZ u ha hm hmin (l j) e (hl j) he)
end Coulomb
end

end

end OAI
