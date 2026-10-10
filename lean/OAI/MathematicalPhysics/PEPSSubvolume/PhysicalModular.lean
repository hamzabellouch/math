import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Crossing
import OAI.MathematicalPhysics.PEPSSubvolume.BipartiteEnergy

namespace OAI

/-! Physical tensor products and symmetric modular discrepancies. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.PhysicalModular
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.BipartiteEnergy PolynomialPEPS.Subvolume.ModularMatrix
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
variable {L q : ℕ}

def tensorAcross (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) : Operator L q :=
  Matrix.reindex (joinEquiv X) (joinEquiv X) (Matrix.kronecker A B)

@[simp] theorem tensorAcross_join (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ)
    (x y : RegionConfiguration q X) (z w : RegionConfiguration q Xᶜ) :
    tensorAcross X A B (joinConfigurations X x z) (joinConfigurations X y w) = A x y * B z w := by
  classical
  change tensorAcross X A B (joinEquiv X (x,z)) (joinEquiv X (y,w)) = _
  simp [tensorAcross,Matrix.reindex_apply,Matrix.kronecker,Matrix.kroneckerMap]

@[simp] theorem asMap_tensorAcross_join (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ)
    (v : State L q) (x : RegionConfiguration q X) (z : RegionConfiguration q Xᶜ) :
    asMap (tensorAcross X A B) v (joinConfigurations X x z) =
      ∑ y, ∑ w, A x y * B z w * v (joinConfigurations X y w) := by
  classical
  change (∑ t, tensorAcross X A B (joinConfigurations X x z) t * v t) = _
  rw [← Equiv.sum_comp (joinEquiv X)]
  simp only [Fintype.sum_prod_type,joinEquiv_apply,tensorAcross_join]

theorem inner_tensorAcross (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ)
    (v : State L q) :
    inner ℂ v (asMap (tensorAcross X A B) v) = expectation (coefficientMatrix v X) A B := by
  classical
  rw [PiLp.inner_apply,← Equiv.sum_comp (joinEquiv X)]
  simp only [Fintype.sum_prod_type,joinEquiv_apply,asMap_tensorAcross_join,RCLike.inner_apply,
    Finset.sum_mul,expectation,bilinearExpectation,Matrix.mul_apply,conjugateEntries,
    Matrix.conjTranspose_apply,Matrix.map_apply,coefficientMatrix,starRingEnd_apply,
    star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem tensorAcross_mul (X : Finset (Vertex L))
    (A C : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B D : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X (A*C) (B*D) = tensorAcross X A B * tensorAcross X C D := by
  classical
  unfold tensorAcross
  rw [Matrix.kronecker,Matrix.mul_kronecker_mul]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (joinEquiv X)).map_mul _ _

@[simp] theorem tensorAcross_one (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) :
    tensorAcross X A 1 = liftLocal X A := (liftLocal_eq_reindex X A).symm

theorem tensorAcross_smul (X : Finset (Vertex L)) (c : ℂ)
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X (c • A) B = c • tensorAcross X A B := by
  classical
  ext x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (joinEquiv (q := q) X).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (joinEquiv (q := q) X).surjective y
  simp only [joinEquiv_apply,tensorAcross_join,Matrix.smul_apply,smul_eq_mul]
  ring

theorem tensorAcross_add (X : Finset (Vertex L))
    (A C : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X (A+C) B = tensorAcross X A B + tensorAcross X C B := by
  classical
  ext x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (joinEquiv (q := q) X).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (joinEquiv (q := q) X).surjective y
  simp only [joinEquiv_apply,tensorAcross_join,Matrix.add_apply]
  ring

theorem tensorAcross_sub (X : Finset (Vertex L))
    (A C : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X (A-C) B = tensorAcross X A B - tensorAcross X C B := by
  classical
  ext x y
  obtain ⟨⟨u,z⟩,rfl⟩ := (joinEquiv (q := q) X).surjective x
  obtain ⟨⟨v,w⟩,rfl⟩ := (joinEquiv (q := q) X).surjective y
  simp only [joinEquiv_apply,tensorAcross_join,Matrix.sub_apply]
  ring

theorem rpow_filter_recovery {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) :
    (s^(2/a))^(a/2) = s := by
  rw [← Real.rpow_mul hs]
  have h : (2/a)*(a/2) = 1 := by field_simp
  rw [h,Real.rpow_one]

end PolynomialPEPS.Subvolume.PhysicalModular

namespace PolynomialPEPS.Subvolume.PhysicalModular
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.BipartiteEnergy PolynomialPEPS.Subvolume.ModularMatrix
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
variable {L q : ℕ}

theorem tensorAcross_sandwich (X : Finset (Vertex L))
    (C A E : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    tensorAcross X (C*A*E) B = liftLocal X C * tensorAcross X A B * liftLocal X E := by
  classical
  calc
    _ = tensorAcross X (C*A*E) ((1*B)*1) := by simp
    _ = _ := by rw [tensorAcross_mul,tensorAcross_mul,tensorAcross_one,tensorAcross_one]

theorem physical_product_error_le (X : Finset (Vertex L)) (v : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (e : RegionConfiguration q X → ℝ) (he : ∀ i, 0 ≤ e i)
    (a : ℝ) (ha : 0<a) (ha' : a ≤ 1/2) (hs : ∑ i, (e i)^(2/a)=1)
    (hρ : reducedDensity v X = (‖v‖^2:ℂ) • spectralHom U (fun i => (((e i)^(2/a):ℝ):ℂ)))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    let F := liftLocal X (spectralHom U (fun i => (e i:ℂ)))
    let D := liftLocal X (inverseOnSupport U e)
    let H := tensorAcross X A B
    ‖inner ℂ v (asMap ((1/2:ℂ) • (F*H*D+D*H*F)-H) v)‖ ≤
      8*a^2*‖v‖^2*(‖A‖*‖B‖) := by
  classical
  dsimp only
  let p := fun i => (e i)^(2/a)
  have hrecovery : weightPower p (a/2) = diagonal (fun i => (e i:ℂ)) := by
    ext i j
    simp only [weightPower,diagonal_apply,p]
    split_ifs <;> simp only [rpow_filter_recovery (he _) ha]
  have hinverse : weightInverse p (a/2) = diagonal (fun i => ((e i)⁻¹:ℂ)) := by
    ext i j
    simp only [weightInverse,diagonal_apply,p]
    split_ifs <;> simp only [rpow_filter_recovery (he _) ha]
  have hd : tensorAcross X (distortionInBasis U A p (a/2)) B =
      (1/2:ℂ) • (liftLocal X (spectralHom U (fun i => (e i:ℂ))) *
        tensorAcross X A B * liftLocal X (inverseOnSupport U e) +
        liftLocal X (inverseOnSupport U e) * tensorAcross X A B *
          liftLocal X (spectralHom U (fun i => (e i:ℂ)))) - tensorAcross X A B := by
    rw [distortionInBasis_eq,hrecovery,hinverse,tensorAcross_sub,tensorAcross_smul,tensorAcross_add]
    simp only [tensorAcross_sandwich]
    simp only [inverseOnSupport, spectralHom_apply, Unitary.conjStarAlgAut_apply]
  rw [← hd,inner_tensorAcross]
  have hh := basis_product_error_le (coefficientMatrix v X) U p
    (fun i => Real.rpow_nonneg (he i) _) ‖v‖ (norm_nonneg _) hρ A B (a/2)
      (by rw [abs_of_nonneg (by positivity)]; linarith)
  change _ ≤ 32*(a/2)^2*‖v‖^2*(∑ i, (e i)^(2/a))*(‖A‖*‖B‖) at hh
  rw [hs,mul_one] at hh
  convert hh using 1
  ring

theorem inner_star_re (H : Operator L q) (v : State L q) :
    (inner ℂ v (asMap (star H) v)).re = (inner ℂ v (asMap H v)).re := by
  classical
  unfold asMap
  rw [map_star]
  change (inner ℂ v ((ContinuousLinearMap.adjoint _) v)).re = _
  rw [ContinuousLinearMap.adjoint_inner_right,← inner_conj_symm v]
  exact Complex.conj_re _

theorem inner_symmetrize_re (H : Operator L q) (v : State L q) :
    (inner ℂ v (asMap ((1/2:ℂ) • (H+star H)) v)).re = (inner ℂ v (asMap H v)).re := by
  classical
  have h := inner_star_re H v
  simp only [asMap,map_smul,map_add,_root_.smul_apply,
    _root_.add_apply,inner_smul_right,inner_add_right] at *
  simp only [Complex.mul_re,Complex.add_re,Complex.add_im] 
  norm_num
  linarith

end PolynomialPEPS.Subvolume.PhysicalModular

namespace PolynomialPEPS.Subvolume.PhysicalModular
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.BipartiteEnergy PolynomialPEPS.Subvolume.ModularMatrix
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
variable {L q : ℕ}

def modularError (F D H : Operator L q) : Operator L q :=
  (1/2:ℂ) • (F*H*D+D*H*F)-H

theorem modularError_sum {ι : Type*} [Fintype ι] (F D : Operator L q) (H : ι → Operator L q) :
    modularError F D (∑ i, H i) = ∑ i, modularError F D (H i) := by
  classical
  simp only [modularError,Matrix.mul_sum,Matrix.sum_mul,Finset.sum_add_distrib,
    smul_add,Finset.smul_sum,Finset.sum_sub_distrib]

theorem physical_sum_error_le {ι : Type*} [Fintype ι]
    (X : Finset (Vertex L)) (v : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (e : RegionConfiguration q X → ℝ) (he : ∀ i, 0 ≤ e i)
    (a : ℝ) (ha : 0<a) (ha' : a ≤ 1/2) (hs : ∑ i, (e i)^(2/a)=1)
    (hρ : reducedDensity v X = (‖v‖^2:ℂ) • spectralHom U (fun i => (((e i)^(2/a):ℝ):ℂ)))
    (A : ι → Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : ι → Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    let F := liftLocal X (spectralHom U (fun i => (e i:ℂ)))
    let D := liftLocal X (inverseOnSupport U e)
    ‖inner ℂ v (asMap (modularError F D (∑ i, tensorAcross X (A i) (B i))) v)‖ ≤
      8*a^2*‖v‖^2*(∑ i, ‖A i‖*‖B i‖) := by
  classical
  dsimp only
  rw [modularError_sum]
  simp only [asMap,map_sum,_root_.sum_apply,inner_sum]
  calc
    _ ≤ ∑ i, ‖inner ℂ v (asMap (modularError
          (liftLocal X (spectralHom U (fun i => (e i:ℂ))))
          (liftLocal X (inverseOnSupport U e)) (tensorAcross X (A i) (B i))) v)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, 8*a^2*‖v‖^2*(‖A i‖*‖B i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact physical_product_error_le X v U e he a ha ha' hs hρ (A i) (B i)
    _ = _ := (Finset.mul_sum ..).symm

theorem modularError_real (F D H : Operator L q) (hF : F.IsHermitian)
    (hD : D.IsHermitian) (hH : H.IsHermitian) (v : State L q) :
    (inner ℂ v (asMap (modularError F D H) v)).re =
      (inner ℂ v (asMap (F*H*D) v)).re - (inner ℂ v (asMap H v)).re := by
  have hs : star (F*H*D)=D*H*F := by
    simp only [star_mul,hF.star_eq,hD.star_eq,hH.star_eq,Matrix.mul_assoc]
  unfold modularError
  rw [← hs]
  change (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) (_-_) v)).re = _
  rw [map_sub]
  simp only [_root_.sub_apply,inner_sub_right,Complex.sub_re]
  rw [show (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) ((1/2:ℂ) •
    (F*H*D+star (F*H*D))) v)).re = (inner ℂ v (asMap (F*H*D) v)).re from
      inner_symmetrize_re _ v]
  rfl

end PolynomialPEPS.Subvolume.PhysicalModular

end

end OAI
