import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorDifferential

namespace OAI

/-! The differential one-body residual of a product is the sum of the
one-orbital residuals in its electron slots. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorOrbitalResidual {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ) (b : Fin n → α)
    (s : SpinConfiguration n) (x : Configuration n) : ℂ :=
  ∑ i, r (b i) (Coulomb.position x i) (s i)*
    ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)

theorem tensorOrbital_operator_residual {n : ℕ} {α : Type*}
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (V : Position → ℝ) (E : ℝ)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (b : Fin n → α) (s : SpinConfiguration n) (x : Configuration n) :
    (-1/2:ℂ)*configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x+
      ((∑ i, V (Coulomb.position x i)):ℝ)*Coulomb.tensorOrbital v b s x-
      ((n:ℝ)*E:ℝ)*Coulomb.tensorOrbital v b s x = tensorOrbitalResidual v r b s x := by
  have hL := coordinateProduct_laplacian (fun i y => v (b i) y (s i))
    (fun i => hv (b i) (s i)) x
  change configurationComplexLaplacian (Coulomb.tensorOrbital v b s) x = _ at hL
  have hf (i : Fin n) : v (b i) (Coulomb.position x i) (s i)*
      (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      Coulomb.tensorOrbital v b s x :=
    Finset.mul_prod_erase Finset.univ
      (fun j => v (b j) (Coulomb.position x j) (s j)) (Finset.mem_univ i)
  have hR : tensorOrbitalResidual v r b s x =
      ∑ i, ((-1/2:ℂ)*
        (positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
          ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
        (V (Coulomb.position x i):ℂ)*Coulomb.tensorOrbital v b s x-
        (E:ℂ)*Coulomb.tensorOrbital v b s x) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [heq]
    rw [show ((-1/2:ℂ)*positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)+
        (V (Coulomb.position x i):ℂ)*v (b i) (Coulomb.position x i) (s i)-
        (E:ℂ)*v (b i) (Coulomb.position x i) (s i))*
        (∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) =
      (-1/2:ℂ)*(positionComplexLaplacian (fun y => v (b i) y (s i)) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))+
      (V (Coulomb.position x i):ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j))-
      (E:ℂ)*(v (b i) (Coulomb.position x i) (s i)*
        ∏ j ∈ Finset.univ.erase i, v (b j) (Coulomb.position x j) (s j)) by ring]
    rw [hf]
  rw [hR,hL]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
  ring

theorem configurationComplexPartial_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (a : Fin n × Fin 3) (x : Configuration n) :
    configurationComplexPartial (fun y => ∑ j, c j*f j y) a x =
      ∑ j, c j*configurationComplexPartial (f j) a x := by
  unfold configurationComplexPartial
  have hd (j : α) := (hf j).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (c j))]
  simp only [sum_apply,fderiv_const_mul (hd _),smul_apply,smul_eq_mul]

theorem configurationComplexLaplacian_sum {n : ℕ} {α : Type*} [Fintype α]
    (c : α → ℂ) (f : α → Configuration n → ℂ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration n) :
    configurationComplexLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationComplexLaplacian (f j) x := by
  have hfirst (a : Fin n × Fin 3) :
      configurationComplexPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationComplexPartial (f j) a y) :=
    funext (configurationComplexPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationComplexLaplacian
  simp_rw [hfirst,configurationComplexPartial_sum c _
    (fun j => configurationComplexPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
