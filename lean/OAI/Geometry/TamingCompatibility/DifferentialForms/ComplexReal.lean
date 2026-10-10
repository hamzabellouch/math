import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFrameTest
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexMatrix
import OAI.Geometry.TamingCompatibility.Charts.LocalFormalAdjoint

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
def retract (n : ℕ) : C n →L[ℝ] R n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => Complex.reCLM ∘L (EuclideanSpace.proj i).restrictScalars ℝ)

@[simp] lemma retract_apply (n : ℕ) (u : C n) (i : Fin n) : retract n u i = (u i).re := rfl
@[simp] lemma retract_embed (n : ℕ) (u : R n) : retract n (embed n u) = u := by
  ext i
  rfl

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

def entry {m n : ℕ} (i : Fin m) (j : Fin n) : (R n →L[ℝ] R m) →L[ℝ] ℝ :=
  EuclideanSpace.proj i ∘L ContinuousLinearMap.apply ℝ (R m) (EuclideanSpace.single j 1)

@[simp] lemma entry_apply {m n : ℕ} (i : Fin m) (j : Fin n) (L : R n →L[ℝ] R m) :
    entry i j L = L (EuclideanSpace.single j 1) i := rfl

def coefficient {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (i : Fin m) (j : Fin n) : 𝓢(D,ℂ) :=
  SchwartzMap.postcompCLM (Complex.ofRealCLM ∘L entry i j) a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma coefficient_apply {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m))
    (i : Fin m) (j : Fin n) (x : D) : coefficient a i j x = (entry i j (a x) : ℂ) := rfl

lemma real_sum_coord {ι : Type*} [Fintype ι] {n : ℕ} (f : ι → R n) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j :=
  map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) f Finset.univ
lemma complex_sum_coord {ι : Type*} [Fintype ι] {n : ℕ} (f : ι → C n) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j :=
  map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) f Finset.univ

lemma real_matrix_apply {m n : ℕ} (a : R n →L[ℝ] R m) (u : R n) (i : Fin m) :
    ∑ j, entry i j a * u j = a u i := by
  have hu : ∑ j : Fin n, u j • EuclideanSpace.single j 1 = u := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u
  have hh := congrArg (fun v : R n => a v i) hu
  simpa only [map_sum,map_smul,real_sum_coord,PiLp.smul_apply,smul_eq_mul,mul_comm,entry_apply] using hh

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma schwartz_matrix_embed {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    (∑ i, ∑ j, SchwartzMap.smulLeftCLM (C m) (coefficient a i j)
      (SchwartzMap.postcompCLM (unit m n i j) (SchwartzMap.postcompCLM (embed n) u))) =
    SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.multiply a a.hasTemperateGrowth u) := by
  ext x k
  simp only [sum_apply,complex_sum_coord,SchwartzMap.smulLeftCLM_apply
    (coefficient a _ _).hasTemperateGrowth,SchwartzMap.postcompCLM_apply,PiLp.smul_apply,
    coefficient_apply,unit_apply,embed_apply,smul_eq_mul]
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum,real_matrix_apply]
  rfl

lemma multiply_embed {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    multiply (coefficient a) (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.multiply a a.hasTemperateGrowth u) :
        𝓢'(D,C m)) := by
  rw [multiply_schwartz,schwartz_matrix_embed]

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open MeasureTheory LineDeriv TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m n : ℕ}

def firstOrder (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m)) :
    𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m) :=
  (∑ i, multiply (coefficient (a i)) ∘L lineDerivOpCLM ℂ 𝓢'(D,C n) (e i)) + multiply (coefficient b)

def formalAdjoint (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m)) :
    𝓢'(D,C m) →L[ℂ] 𝓢'(D,C n) :=
  -(∑ i, lineDerivOpCLM ℂ 𝓢'(D,C n) (e i) ∘L
    multiply (coefficient (LocalFormalAdjoint.adjointCoefficient (a i)))) +
    multiply (coefficient (LocalFormalAdjoint.adjointCoefficient b))

def square (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m))
    (ρ : 𝓢(D,ℝ)) : 𝓢'(D,C n) →L[ℂ] 𝓢'(D,C n) :=
  formalAdjoint e (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
    (LocalFormalAdjoint.weightedCoefficient ρ b) ∘L firstOrder e a b

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma lineDeriv_embed (v : D) (u : 𝓢(D,R n)) :
    ∂_{v} (SchwartzMap.postcompCLM (embed n) u) = SchwartzMap.postcompCLM (embed n) (∂_{v} u) := by
  ext1 x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hh := (embed n).hasFDerivAt.comp x u.differentiableAt.hasFDerivAt
  change fderiv ℝ ((embed n) ∘ u) x v = _
  rw [hh.fderiv]
  rfl

lemma distribution_lineDeriv_embed (v : D) (u : 𝓢(D,R n)) :
    ∂_{v} (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed n) (∂_{v} u) : 𝓢'(D,C n)) := by
  rw [TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,lineDeriv_embed]

lemma firstOrder_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    firstOrder e a b (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.firstOrder e a b u) : 𝓢'(D,C m)) := by
  simp only [firstOrder,LocalFormalAdjoint.firstOrder,_root_.add_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,distribution_lineDeriv_embed,
    multiply_embed,map_add,map_sum]

lemma formalAdjoint_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R m)) :
    formalAdjoint e a b (SchwartzMap.postcompCLM (embed m) u : 𝓢'(D,C m)) =
      (SchwartzMap.postcompCLM (embed n) (LocalFormalAdjoint.formalAdjoint e a b u) : 𝓢'(D,C n)) := by
  simp only [formalAdjoint,LocalFormalAdjoint.formalAdjoint,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,
    multiply_embed,distribution_lineDeriv_embed,map_add,map_neg,map_sum]

lemma square_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (u : 𝓢(D,R n)) :
    square e a b ρ (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed n)
        (LocalFormalAdjoint.formalAdjoint e (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
          (LocalFormalAdjoint.weightedCoefficient ρ b) (LocalFormalAdjoint.firstOrder e a b u)) : 𝓢'(D,C n)) := by
  rw [square,ContinuousLinearMap.comp_apply,firstOrder_embed,formalAdjoint_embed]
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {m n k : ℕ}

lemma multiply_apply_component (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n))
    (φ : 𝓢(D,ℂ)) (i : Fin m) :
    (multiply a u φ) i = ∑ j, (u (SchwartzMap.smulLeftCLM ℂ (a i j) φ)) j := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    smulLeftCLM_apply_apply,fiberMap_apply,complex_sum_coord,unit_apply]
  simp [Finset.sum_ite_irrel]

lemma multiply_derivative (a : Fin m → Fin n → 𝓢(D,ℂ)) (v : D) (u : 𝓢'(D,C n)) :
    ∂_{v} (multiply a u) = multiply (fun i j => ∂_{v} (a i j)) u + multiply a (∂_{v} u) := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    lineDerivOp_sum,distribution_derivative_product,← fiberMap_derivative,Finset.sum_add_distrib]

lemma multiply_add (a b : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => a i j + b i j) u = multiply a u + multiply b u := by
  ext φ i
  simp only [_root_.add_apply,multiply_apply_component,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : SchwartzMap.smulLeftCLM ℂ (a i j+b i j) φ =
      SchwartzMap.smulLeftCLM ℂ (a i j) φ + SchwartzMap.smulLeftCLM ℂ (b i j) φ := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (a i j+b i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (a i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (b i j).hasTemperateGrowth,_root_.add_apply,add_smul]
  rw [he,map_add]
  rfl

lemma multiply_sum {ι : Type*} [Fintype ι] (a : ι → Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => ∑ t, a t i j) u = ∑ t, multiply (a t) u := by
  classical
  let P (s : Finset ι) : Prop := multiply (fun i j => ∑ t ∈ s, a t i j) u = ∑ t ∈ s, multiply (a t) u
  have hp : ∀ s, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      dsimp only [P]
      simp only [Finset.sum_empty]
      ext φ i
      have h0 : SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(D,ℂ)) φ = 0 := by
        ext x
        rw [SchwartzMap.smulLeftCLM_apply_apply (0 : 𝓢(D,ℂ)).hasTemperateGrowth]
        simp only [_root_.zero_apply,zero_smul]
      simp only [multiply_apply_component,h0,map_zero,PiLp.zero_apply,Finset.sum_const_zero,
        _root_.zero_apply]
    | @insert t s ht ih =>
      dsimp only [P] at ih ⊢
      simp only [Finset.sum_insert ht,multiply_add,ih]
  exact hp Finset.univ

lemma coefficient_derivative (a : 𝓢(D,R n →L[ℝ] R m)) (v : D) (i : Fin m) (j : Fin n) :
    (∂_{v} (coefficient a i j) : 𝓢(D,ℂ)) = coefficient (∂_{v} a) i j :=
  ScalarPair.postcomp_derivative _ _ _

def entryProduct (f g : 𝓢(D,ℂ)) : 𝓢(D,ℂ) := SchwartzMap.smulLeftCLM ℂ f g

lemma entryProduct_apply (f g : 𝓢(D,ℂ)) (x : D) : entryProduct f g x = f x * g x :=
  SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x

lemma entryProduct_test (f g φ : 𝓢(D,ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (entryProduct f g) φ =
      SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.smulLeftCLM ℂ f φ) := by
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply (entryProduct f g).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,entryProduct_apply,smul_eq_mul]
  ring

def matProduct (b : Fin k → Fin m → 𝓢(D,ℂ)) (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    Fin k → Fin n → 𝓢(D,ℂ) := fun i l => ∑ j, entryProduct (b i j) (a j l)

lemma multiply_comp (b : Fin k → Fin m → 𝓢(D,ℂ)) (a : Fin m → Fin n → 𝓢(D,ℂ))
    (u : 𝓢'(D,C n)) : multiply b (multiply a u) = multiply (matProduct b a) u := by
  change multiply b (multiply a u) = multiply (fun i l => ∑ j, entryProduct (b i j) (a j l)) u
  rw [multiply_sum]
  ext φ i
  simp only [multiply_apply_component,_root_.sum_apply,complex_sum_coord,entryProduct_test]

end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
