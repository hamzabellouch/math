import Mathlib
import OAI.Analysis.HardSphere.Geometry.HeadLift
import OAI.Analysis.HardSphere.Geometry.InnerClmRealRight
import OAI.Analysis.HardSphere.Geometry.LabelLift
import OAI.Analysis.HardSphere.Geometry.FinsetProd
import OAI.Analysis.HardSphere.Geometry.CoeScalar

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma scalar_partition_ims {S : Type*} [Fintype S] (w d : S → ℂ) (u v : ℂ)
    (hp : ∑ s, ‖w s‖^2=1) (hc : ∑ s, w s*conj (d s)=0) :
    (∑ s, ‖w s*v+d s*u‖^2)=‖v‖^2+∑ s, ‖d s*u‖^2 := by
  have hc' : (∑ s, (w s*v*conj (d s*u)).re)=0 := by
    rw [← Complex.re_sum]
    have hs : (∑ s, w s*v*conj (d s*u))=(v*conj u)*(∑ s, w s*conj (d s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [map_mul]
      ring
    rw [hs,hc,mul_zero,Complex.zero_re]
  simp_rw [← Complex.normSq_eq_norm_sq,Complex.normSq_add]
  simp_rw [Complex.normSq_mul,Complex.normSq_eq_norm_sq]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul,
    ← Finset.mul_sum,hc',mul_zero,add_zero]

lemma real_norm_sq (z : ℂ) (hz : conj z=z) : ‖z‖^2=(z*z).re := by
  have he := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z:=z))
  simpa only [hz,Complex.ofReal_re,Complex.normSq_eq_norm_sq] using he

lemma SmoothMultiplier.partition_derivative {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1)
    (p : Direction n) (X : Configuration n L) :
    (∑ s, (w s).toFun X*coordDerivative n L (w s).toFun p X)=0 := by
  let f := SmoothMultiplier.sum (fun s ↦ (w s).mul (w s))
  have hf : f.toFun=fun _ ↦ 1 := funext hp
  have hd : coordDerivative n L f.toFun p X=0 := by
    rw [hf]
    simp [coordDerivative]
  rw [SmoothMultiplier.partial_sum] at hd
  have he (s : S) : coordDerivative n L ((w s).mul (w s)).toFun p X=
      2*((w s).toFun X*coordDerivative n L (w s).toFun p X) := by
    change coordDerivative n L ((w s).toFun*(w s).toFun) p X=_
    rw [coordDerivative_mul ((w s).smooth.differentiable (by simp))
      ((w s).smooth.differentiable (by simp))]
    change (w s).toFun X*_+_*_= _
    ring
  simp_rw [he] at hd
  rw [← Finset.mul_sum] at hd
  exact (mul_eq_zero.mp hd).resolve_left (by norm_num)

lemma SmoothMultiplier.partition_norm {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (X : Configuration n L) :
    (∑ s, ‖(w s).toFun X‖^2)=1 := by
  simp_rw [real_norm_sq _ (hr _ _)]
  rw [← Complex.re_sum,hp,Complex.one_re]

lemma SmoothMultiplier.partition_scalar_norm {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : ScalarL2 n L) :
    (∑ s, ‖(w s).onScalar u‖^2)=‖u‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun s _ ↦
    (Lp.memLp ((w s).onScalar u)).integrable_norm_pow (by norm_num))]
  apply integral_congr_ae
  have hc : ∀ᵐ X ∂volume, ∀ s, ((w s).onScalar u) X=(w s).toFun X*u X :=
    ae_all_iff.mpr (fun s ↦ (w s).coe_onScalar u)
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow]
  rw [← Finset.sum_mul,SmoothMultiplier.partition_norm w hr hp,one_mul]

lemma SmoothMultiplier.partition_direction_ims {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : Jet n L) (p : Direction n) :
    (∑ s, ‖((w s).onJet u).2 p‖^2)=‖u.2 p‖^2+∑ s, ‖(w s).derivativeScalar p u.1‖^2 := by
  have hi (s : S) : Integrable (fun X ↦ ‖((w s).derivativeScalar p u.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun s _ ↦
    (Lp.memLp (((w s).onJet u).2 p)).integrable_norm_pow (by norm_num)),
    ← integral_finsetSum Finset.univ (fun s _ ↦ hi s),
    ← integral_add ((Lp.memLp (u.2 p)).integrable_norm_pow (by norm_num)) (integrable_finsetSum _ (fun s _ ↦ hi s))]
  apply integral_congr_ae
  have hc (s : S) : ∀ᵐ X ∂volume,
      (((w s).onJet u).2 p) X=(w s).toFun X*(u.2 p) X+coordDerivative n L (w s).toFun p X*u.1 X := by
    filter_upwards [(w s).coe_onScalar (u.2 p),(w s).coe_derivativeScalar p u.1,
      Lp.coeFn_add ((w s).onScalar (u.2 p)) ((w s).derivativeScalar p u.1)] with X h1 h2 h3
    change (((w s).onScalar (u.2 p)+(w s).derivativeScalar p u.1) : ScalarL2 n L) X=_
    rw [h3,Pi.add_apply,h1,h2]
  have hd : ∀ᵐ X ∂volume, ∀ s, ((w s).derivativeScalar p u.1) X=coordDerivative n L (w s).toFun p X*u.1 X :=
    ae_all_iff.mpr (fun s ↦ (w s).coe_derivativeScalar p u.1)
  filter_upwards [ae_all_iff.mpr hc,hd] with X hX hY
  simp_rw [hX,hY]
  apply scalar_partition_ims _ _ _ _ (SmoothMultiplier.partition_norm w hr hp X)
  simp_rw [(w _).partial_real (hr _) p X]
  exact SmoothMultiplier.partition_derivative w hp p X

theorem SmoothMultiplier.partition_ims {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : Jet n L) :
    (∑ s, energy ((w s).onJet u))=energy u+∑ p : Direction n, ∑ s, ‖(w s).derivativeScalar p u.1‖^2 := by
  change (∑ s, ∑ p, ‖((w s).onJet u).2 p‖^2)=_
  rw [Finset.sum_comm]
  simp_rw [SmoothMultiplier.partition_direction_ims w hr hp u]
  rw [Finset.sum_add_distrib]
  rfl

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def productPartition (n : ℕ) (L : Length) (a c : SmoothMultiplier 1 L) (σ : Fin n → Bool) :
    SmoothMultiplier n L :=
  SmoothMultiplier.finsetProd Finset.univ (fun i ↦ (cond (σ i) a c).liftLabel n i)

lemma productPartition_apply (n : ℕ) (L : Length) (a c : SmoothMultiplier 1 L)
    (σ : Fin n → Bool) (X : Configuration n L) :
    (productPartition n L a c σ).toFun X=∏ i, (cond (σ i) a c).orbital (X i) := rfl

lemma productPartition_real {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (σ : Fin n → Bool) (X : Configuration n L) :
    conj ((productPartition n L a c σ).toFun X)=(productPartition n L a c σ).toFun X := by
  simp only [productPartition_apply,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp only [Bool.cond_false,Bool.cond_true,SmoothMultiplier.orbital,ha,hc]

lemma productPartition_unity {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) :
    (∑ σ : Fin n → Bool, (productPartition n L a c σ).toFun X*(productPartition n L a c σ).toFun X)=1 := by
  simp_rw [productPartition_apply,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) ↦
    (cond b a c).orbital (X i)*(cond b a c).orbital (X i))]
  simp only [Fintype.sum_bool,Bool.cond_true,Bool.cond_false,hp,Finset.prod_const_one]

lemma productPartition_partial {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (σ : Fin n → Bool) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (productPartition n L a c σ).toFun p X=
      (∏ i∈Finset.univ.erase p.1, (cond (σ i) a c).orbital (X i))*
      coordDerivative 1 L (cond (σ p.1) a c).toFun (0,p.2) (fun _ ↦ X p.1) := by
  classical
  rw [productPartition,SmoothMultiplier.partial_finsetProd]
  simp_rw [SmoothMultiplier.partial_liftLabel]
  rw [Finset.sum_eq_single p.1]
  · rw [ite_eq_left rfl]
    rfl
  · intro i _ hi
    rw [ite_eq_right (Ne.symm hi),mul_zero]
  · simp

lemma binary_product_sum {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool → ℝ) (d : Bool → ℝ) (j : I)
    (hf : ∀ i, f i true+f i false=1) :
    (∑ σ : I → Bool, (∏ i∈Finset.univ.erase j, f i (σ i))*d (σ j))=d true+d false := by
  let g (i : I) (b : Bool) := if i=j then d b else f i b
  have he (σ : I → Bool) : (∏ i∈Finset.univ.erase j, f i (σ i))*d (σ j)=∏ i, g i (σ i) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun i ↦ g i (σ i)) (Finset.mem_univ j)]
    dsimp only [g]
    rw [ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1]
  simp_rw [he]
  rw [← Fintype.prod_sum,Finset.prod_eq_single j]
  · simp [g]
  · intro i _ hi
    simpa only [g,ite_eq_right hi,Fintype.sum_bool] using hf i
  · simp

lemma productPartition_gradient_partition {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (p : Direction n) (X : Configuration n L) :
    (∑ σ : Fin n → Bool, ‖coordDerivative n L (productPartition n L a c σ).toFun p X‖^2)=
      ‖coordDerivative 1 L a.toFun (0,p.2) (fun _ ↦ X p.1)‖^2+
      ‖coordDerivative 1 L c.toFun (0,p.2) (fun _ ↦ X p.1)‖^2 := by
  have hnorm (i : Fin n) : ‖a.orbital (X i)‖^2+‖c.orbital (X i)‖^2=1 := by
    rw [real_norm_sq (a.orbital (X i)) (ha (fun _ ↦ X i)),
      real_norm_sq (c.orbital (X i)) (hc (fun _ ↦ X i)),← Complex.add_re,hp,Complex.one_re]
  simp_rw [productPartition_partial,norm_mul,mul_pow,norm_prod,← Finset.prod_pow]
  exact binary_product_sum (fun i b ↦ ‖(cond b a c).orbital (X i)‖^2)
    (fun b ↦ ‖coordDerivative 1 L (cond b a c).toFun (0,p.2) (fun _ ↦ X p.1)‖^2) p.1 hnorm

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
