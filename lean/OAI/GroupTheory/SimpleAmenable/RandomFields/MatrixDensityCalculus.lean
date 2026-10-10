import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AffineNoiseEnergy

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section MatrixDensityCalculus
open Classical Matrix

noncomputable def determinantMultilinear {ι : Type*} [Fintype ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

theorem determinantMultilinear_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    determinantMultilinear A=A.det := rfl

theorem matrix_hasDerivAt_det {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s).det) ((A t).det*Matrix.trace (A'*(A t)⁻¹)) t := by
  let M := A t
  let L := A'*M⁻¹
  have hmul : L*M=A' := by
    rw [mul_assoc,Matrix.nonsing_inv_mul _ hunit,mul_one]
  have hrow (i : ι) : A' i=∑j,L i j • M j := by
    ext k
    rw [← hmul]
    simp only [Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hd := (determinantMultilinear.hasFDerivAt (A t)).comp_hasDerivAt t hA
  have he : determinantMultilinear.linearDeriv (A t) A'=M.det*Matrix.trace L := by
    have hlin : determinantMultilinear.linearDeriv (A t) A'=
        ∑i,determinantMultilinear (Function.update (A t) i (A' i)) := by
      convert! ContinuousMultilinearMap.linearDeriv_apply determinantMultilinear
        (fun i j => A t i j) (fun i j => A' i j) using 1
    rw [hlin]
    calc
      _ = ∑i,(M.updateRow i (∑j,L i j • M j)).det := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hrow i]
        rfl
      _ = ∑i,L i i*M.det := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.det_updateRow_sum,smul_eq_mul]
      _ = M.det*Matrix.trace L := by
        simp only [Matrix.trace,Matrix.diag,Finset.mul_sum,mul_comm]
  rw [he] at hd
  convert! hd using 1

end MatrixDensityCalculus

section AffineNoiseIdentity
open Classical Matrix

noncomputable def noiseGradientCoordinate {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  deriv f (x i)*∏j∈Finset.univ.erase i,f (x j)

theorem singletonNoise_eq {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (q : NoiseFactor) (i : ι) (x : ι → ℝ) :
    singletonNoise f q i x=noiseFactor f q (x i)*∏j∈Finset.univ.erase i,f (x j) := by
  unfold singletonNoise centeredNoiseTensor noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (if j∈({i} : Finset ι) then
    (fun _ => noiseFactor f q) j else f) (x j)) (Finset.mem_univ i)]
  simp only [Finset.mem_singleton]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem singletonNoise_score {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) :
    singletonNoise f .score i x=noiseGradientCoordinate f i x := by
  rw [singletonNoise_eq]
  rfl

theorem singletonNoise_diagonal {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) :
    singletonNoise f .diagonal i x=
      x i*noiseGradientCoordinate f i x+noiseTensor (fun _ : ι => f) x/2 := by
  rw [singletonNoise_eq]
  unfold noiseFactor noiseGradientCoordinate noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ (fun j => f (x j)) (Finset.mem_univ i)]
  ring

theorem pairNoise_gradient {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (p : NoisePair ι) (x : ι → ℝ) :
    pairNoise f p x=x p.val.2*noiseGradientCoordinate f p.val.1 x := by
  rw [← singletonNoise_score]
  unfold pairNoise singletonNoise centeredNoiseTensor noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p.val.2),
    ← Finset.mul_prod_erase Finset.univ (fun i => (if i∈({p.val.1} : Finset ι) then
      (fun _ => noiseFactor f .score) i else f) (x i)) (Finset.mem_univ p.val.2)]
  simp only [Finset.mem_insert,Finset.mem_singleton,or_true,ite_true,
    ite_eq_right (Ne.symm p.property),noiseFactor]
  have hp : (∏i∈Finset.univ.erase p.val.2,
      (if i∈({p.val.1,p.val.2} : Finset ι) then
        (fun i => noiseFactor f (if i=p.val.1 then .score else .position)) i else f) (x i))=
      ∏i∈Finset.univ.erase p.val.2,(if i=p.val.1 then deriv f else f) (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    by_cases he : i=p.val.1
    · simp [he,noiseFactor]
    · simp [he,hne]
  simp only [Finset.mem_insert,Finset.mem_singleton,noiseFactor] at hp
  rw [hp]
  ring

theorem affineNoiseGenerator_eq {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (L : Matrix ι ι ℝ) (v x : ι → ℝ) :
    affineNoiseGenerator f L v x=
      (∑i,((L*ᵥx) i+v i)*noiseGradientCoordinate f i x)+
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 := by
  have hsplit : (∑i,L i i*x i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ∑i,∑j,L i j*x j*noiseGradientCoordinate f i x := by
    have ho : (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ∑i,∑j,if i≠j then L i j*x j*noiseGradientCoordinate f i x else 0 := by
      change (∑p : {p : ι×ι // p.1≠p.2},L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=_
      rw [← Finset.sum_subtype (Finset.univ.filter (fun p : ι×ι => p.1≠p.2)) (by simp)
        (fun p : ι×ι => L p.1 p.2*x p.2*noiseGradientCoordinate f p.1 x),Finset.sum_filter,
        Fintype.sum_prod_type]
    rw [ho,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (∑j,if i=j then L i j*x j*noiseGradientCoordinate f i x else 0)+
          (∑j,if i≠j then L i j*x j*noiseGradientCoordinate f i x else 0) := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp_all
  simp_rw [affineNoiseGenerator,singletonNoise_diagonal,singletonNoise_score,pairNoise_gradient]
  simp only [mul_add,Finset.sum_add_distrib]
  have ht : (∑i,L i i*(noiseTensor (fun _ : ι => f) x/2))=
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 := by
    rw [← Finset.sum_mul]
    simp only [Matrix.trace,Matrix.diag]
    ring
  rw [ht]
  have hh : (∑p : NoisePair ι,L p.val.1 p.val.2*(x p.val.2*noiseGradientCoordinate f p.val.1 x))=
      ∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x := by
    simp only [mul_assoc]
  rw [hh]
  simp only [← mul_assoc] at hsplit ⊢
  rw [show (∑i,L i i*x i*noiseGradientCoordinate f i x)+
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2+
      (∑i,v i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ((∑i,L i i*x i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x))+
      (∑i,v i*noiseGradientCoordinate f i x)+Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 by ring,
      hsplit]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,add_mul,Finset.sum_add_distrib]

theorem noiseTensor_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) {x : ℝ → ι → ℝ} {x' : ι → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => noiseTensor (fun _ : ι => f) (x s))
      (∑i,x' i*noiseGradientCoordinate f i (x t)) t := by
  have h (i : ι) := ((hf (x t i)).hasDerivAt).comp t ((hasDerivAt_pi.mp hx) i)
  convert! HasDerivAt.fun_finsetProd (fun i (_ : i∈Finset.univ) => h i) using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [noiseGradientCoordinate,smul_eq_mul,Function.comp_apply]
  ring

end AffineNoiseIdentity

end SimpleAmenable
end
end

end OAI
