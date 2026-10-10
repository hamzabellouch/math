import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixWhitening
import OAI.Probability.SKGap.Localization.BilinearUnion
import OAI.Probability.SKGap.Localization.GramUniformRobust

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*}

def conditionalColumns (X M G N : ι → ℝ) : Matrix ι ((Fin 3) ⊕ Unit) ℝ :=
  fun i k => Sum.elim (fun l => ![X i,M i,G i] l) (fun _ => N i) k

def conditionalCoupling (c : ℝ) : Matrix (Fin 3) Unit ℝ := fun k _ => ![0,c,0] k

def conditionalCoefficient (j cM cG cN : ℝ) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  fromBlocks !![j,0,0;0,cM,cG;0,cG,0] (conditionalCoupling cN)
    (conditionalCoupling cN)ᵀ 0

lemma conditionalCoefficient_hermitian (j cM cG cN : ℝ) :
    (conditionalCoefficient j cM cG cN).IsHermitian := by
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;> simp [conditionalCoefficient,Matrix.conjTranspose_apply]
    | inr k => simp [conditionalCoefficient,Matrix.conjTranspose_apply]
  | inr i => cases k <;> simp [conditionalCoefficient,Matrix.conjTranspose_apply]

lemma conditional_rank_expansion (X M G N : ι → ℝ) (j cM cG cN : ℝ) :
    conditionalColumns X M G N*conditionalCoefficient j cM cG cN*
      (conditionalColumns X M G N)ᵀ =
      j • vecMulVec X X+cM • vecMulVec M M+
      cG • (vecMulVec M G+vecMulVec G M)+cN • (vecMulVec M N+vecMulVec N M) := by
  ext i k
  simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,
    conditionalColumns,conditionalCoefficient,conditionalCoupling,vecMulVec_apply]
  ring

lemma conditional_schur_coefficient {j b s q κ : ℝ} (hb : 0 < b) (hj : 0 < j)
    (hs : 0 < s) (hq : 0 < q) (hk : κ^2=1-j*q/s) :
    (2*j*q+2*(j*b)*(κ-1))/q = j*(2-j*b/s)-((κ-1)*√(j*b)/√q)^2 := by
  have hB : 0 < j*b := mul_pos hj hb
  have hq0 : √q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  rw [div_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hq.le]
  field_simp
  have hk' : κ^2*s=s-j*q := by
    calc
      _ = (1-j*q/s)*s := by rw [hk]
      _ = _ := by field_simp
  nlinarith [hk']

lemma conditionalCoefficient_at_equality {j b s q κ : ℝ} (hb : 0 < b) (hj : 0 < j)
    (hs : 0 < s) (hq : 0 < q) (hk : κ^2=1-j*q/s) :
    conditionalCoefficient j ((2*j*q+2*(j*b)*(κ-1))/q) j ((κ-1)*√(j*b)/√q)=
      augmentedCoefficient (rankCoefficient j b s) (conditionalCoupling ((κ-1)*√(j*b)/√q)) := by
  have h := conditional_schur_coefficient hb hj hs hq hk
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp [conditionalCoefficient,augmentedCoefficient,rankCoefficient,conditionalCoupling,
          Matrix.mul_apply,h,pow_two]
    | inr k => simp [conditionalCoefficient,augmentedCoefficient]
  | inr i => cases k <;> simp [conditionalCoefficient,augmentedCoefficient]

theorem conditional_rank_change_basis (X U Z V : ι → ℝ) (j cU cZ cV : ℝ)
    {q s B : ℝ} (hq : 0 < q) (hs : 0 < s) (hB : 0 < B) :
    let Q := conditionalColumns X (√q • U) ((√s)⁻¹ • Z) ((√B)⁻¹ • (V-B • U))
    Q*conditionalCoefficient j ((cU+2*B*cV)/q) (cZ*√s/√q) (cV*√B/√q)*Qᵀ =
      j • vecMulVec X X+cU • vecMulVec U U+
      cZ • (vecMulVec U Z+vecMulVec Z U)+cV • (vecMulVec U V+vecMulVec V U) := by
  dsimp only
  rw [conditional_rank_expansion]
  have hq0 : √q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hs0 : √s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hB0 : √B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  ext i k
  simp only [Matrix.add_apply,Matrix.smul_apply,vecMulVec_apply,Pi.smul_apply,Pi.sub_apply,
    smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hq.le]; ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Set Real
open scoped MatrixOrder Matrix.Norms.Frobenius

theorem compact_conditional_rank_criterion {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {j : ℝ} (hj : 0 < j) (hj1 : j < 1) (b e s q κ : α → ℝ)
    (hb : Continuous b) (he : Continuous e) (hs : Continuous s)
    (hq : Continuous q) (hκ : Continuous κ)
    (hb0 : ∀ x, 0 < b x) (hb1 : ∀ x, b x ≤ 1) (he0 : ∀ x, 0 ≤ e x)
    (hs0 : ∀ x, 0 < s x) (hq0 : ∀ x, 0 < q x)
    (hκsq : ∀ x, κ x^2=1-j*q x/s x) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ x (ι : Type) [Fintype ι] [DecidableEq ι]
        (S D : Matrix ι ι ℝ) (V : Matrix ι ((Fin 3) ⊕ Unit) ℝ)
        (C : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ) (c : ℝ),
        S.PosDef → D.IsHermitian → C.IsHermitian →
        (S-c • (1 : Matrix ι ι ℝ)).PosSemidef →
        ‖Vᵀ*D*S⁻¹*D*V-augmentedGram (ν := Unit) (limitingGram (b x) (e x) (s x))‖ < ρ →
        ‖C-conditionalCoefficient j ((2*j*q x+2*(j*b x)*(κ x-1))/q x)
          j ((κ x-1)*√(j*b x)/√(q x))‖ < ρ →
        (S-D*V*C*Vᵀ*D-(δ*c) • (1 : Matrix ι ι ℝ)).PosDef := by
  let coupling := fun x => conditionalCoupling ((κ x-1)*√(j*b x)/√(q x))
  have hcoupling : Continuous coupling := by
    unfold coupling conditionalCoupling
    fun_prop (disch := intro x; exact ne_of_gt (Real.sqrt_pos.2 (hq0 x)))
  obtain ⟨δ,ρ,hδ,hδ1,hρ,hcrit⟩ := compact_limiting_augmented_gram_robust hj hj1
    b e s coupling hb he hs hcoupling hb1 he0 (fun x => (hs0 x).ne')
  refine ⟨δ,ρ,hδ,hδ1,hρ,?_⟩
  intro x ι _ _ S D V C c hS hD hC hc hg hcc
  obtain ⟨R,hR,hRR,hu,hgram⟩ := positive_whitening_gram hS D hD V
  have hcc' : ‖C-augmentedCoefficient (rankCoefficient j (b x) (s x)) (coupling x)‖ < ρ := by
    rw [conditionalCoefficient_at_equality (hb0 x) hj (hs0 x) (hq0 x) (hκsq x)] at hcc
    exact hcc
  have hh := hcrit x ι (R⁻¹*D*V) C hC (by rw [hgram]; exact hg) hcc'
  have hp := positive_unwhitening hR hD hRR hu V C δ hh
  have hp' := hp.add_posSemidef (hc.smul hδ.le)
  convert hp' using 1
  rw [smul_sub,smul_smul,sub_smul,one_smul]
  abel
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_lift_real (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    ComplexSpectral.quadratic (RealComplex.liftMatrix M) (RealComplex.liftVec v)=rayleigh M v := by
  simp [ComplexSpectral.quadratic,RealComplex.liftMatrix,RealComplex.liftVec,
    rayleigh,dotProduct,mulVec]

lemma complex_lowerRayleigh_margin {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {c : ℝ} (hc : c < ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix M)) :
    (M-c • (1 : Matrix ι ι ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hM.sub
    (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial c))))
  intro x hx
  apply rayleigh_pos_of_unit (M := M-c • (1 : Matrix ι ι ℝ)) (fun v hv => ?_)
    (v := WithLp.toLp 2 x) (fun hz => hx (congrArg WithLp.ofLp hz))
  have hv' : ‖v‖=1 := hv
  have hh := ComplexSpectral.lowerRayleigh_le (RealComplex.liftMatrix M)
    (x := RealComplex.liftVec v) (by
      simp only [ComplexSpectral.unitSphere,Metric.mem_sphere,dist_zero_right,
        RealComplex.norm_liftVec,hv'])
  rw [quadratic_lift_real] at hh
  have hsq : v.ofLp⬝ᵥv.ofLp=1 := by
    have hn := EuclideanSpace.real_norm_sq_eq v
    rw [hv'] at hn
    simpa only [dotProduct,pow_two,one_mul] using hn.symm
  change 0 < v.ofLp⬝ᵥ((M-c • (1 : Matrix ι ι ℝ))*ᵥv.ofLp)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,hsq,mul_one]
  exact sub_pos.mpr (lt_of_lt_of_le hc hh)

theorem bilinearPathGood_margin {n : ℕ} {j A : ℝ} (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) (hg : bilinearPathGood j A a g) :
    ((1-pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-
      ((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1)-
      ((1-sqrt j*A)^2/4) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hh := hg 1 ⟨by norm_num,le_rfl⟩
  change _ ∧ _ ∧ _ at hh
  have he : pathShift 1 ((j/(n:ℝ))*∑ i,a i)=((j/(n:ℝ))*∑ i,a i) •
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i k
    simp [pathShift,Matrix.diagonal,Matrix.one_apply]
  rw [he] at hh
  apply complex_lowerRayleigh_margin ?_ hh.2.1
  apply Matrix.isHermitian_one.sub
  have hD : (pathDiagonal a 1).IsHermitian := by
    exact isHermitian_diagonal_iff.mpr (fun i => isSelfAdjoint_iff.mpr (star_trivial _))
  have hW : (goeMatrix (j/(n:ℝ)) g).IsHermitian := by
    change (goeMatrix (j/(n:ℝ)) g)ᴴ=goeMatrix (j/(n:ℝ)) g
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using goeMatrix_transpose (j/(n:ℝ)) g
  change (pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1).IsHermitian
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,hD.eq,hW.eq,star_trivial,Matrix.mul_assoc]
end SKGap
end
end

end OAI
