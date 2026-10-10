import OAI.Combinatorics.EuclideanRamsey.SignedRows

namespace OAI

universe uIndex uRow uColor

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma trace_gram_complement {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (η : ℝ) (hη : B.trace ≤ η) :
    (η • (1 : Matrix ι ι ℝ)-B).PosSemidef := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.1.eigenvectorUnitary
  have he (i : ι) : hB.1.eigenvalues i ≤ η := by
    apply le_trans _ hη
    rw [hB.1.trace_eq_sum_eigenvalues]
    simpa using (Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i))
  have hD : (diagonal (fun i => η-hB.1.eigenvalues i)).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (he i))
  have hd : e (diagonal (fun i => η-hB.1.eigenvalues i)) = η • 1-B := by
    have hr : diagonal (fun i => η-hB.1.eigenvalues i) =
        η • (1 : Matrix ι ι ℝ)-diagonal hB.1.eigenvalues := by
      ext i j
      by_cases h : i=j <;> simp [h]
    rw [hr,map_sub,map_smul,map_one]
    congr 1
    exact hB.1.spectral_theorem.symm
  rw [← hd]
  exact hD.mul_mul_conjTranspose_same _

lemma exists_gram_sqrt {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    ∃ R : Matrix ι ι ℝ,R*R.transpose=P := by
  let R := CFC.sqrt P
  have hr : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  refine ⟨R,?_⟩
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hr.1.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.nonneg

lemma gram_fromCols {ι : Type uIndex} {τ : Type uRow} {κ : Type uColor} [Fintype τ] [Fintype κ]
    (U : Matrix ι τ ℝ) (R : Matrix ι κ ℝ) :
    (U.fromCols R)*(U.fromCols R).transpose = U*U.transpose+R*R.transpose := by
  ext i j
  simp [Matrix.mul_apply,Matrix.fromCols,Matrix.transpose_apply,Fintype.sum_sum_type]

theorem complete_gram_pair {d : ℕ} {τ : Type uRow} [Fintype τ]
    (U V : Matrix (Fin d) τ ℝ) (η : ℝ) (hη : 0 < η)
    (hdiff : U*U.transpose-V*V.transpose=1)
    (htrace : (V*V.transpose).trace < η) :
    ∃ R : Matrix (Fin d) (Fin d) ℝ,
      let c := (Real.sqrt (1+η))⁻¹
      (c • (U.fromCols R))*(c • (U.fromCols R)).transpose=1 ∧
      (c • (V.fromCols R))*(c • (V.fromCols R)).transpose=
        (η/(1+η)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hB : (V*V.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose V
  obtain ⟨R,hR⟩ := exists_gram_sqrt _ (trace_gram_complement _ hB η htrace.le)
  refine ⟨R,?_⟩
  dsimp only
  have he (A : Matrix (Fin d) τ ℝ) :
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R)*
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R).transpose =
      (1/(1+η)) • (A*A.transpose+R*R.transpose) := by
    rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,gram_fromCols]
    congr 1
    rw [← _root_.mul_inv_rev,← sq,Real.sq_sqrt (by linarith)]
    simp
  rw [he,he,hR]
  have hU : U*U.transpose+(η • 1-V*V.transpose)=(1+η) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [add_smul,one_smul,← hdiff]
    abel
  rw [hU,smul_smul,one_div_mul_cancel (by linarith : 1+η ≠ 0),one_smul]
  constructor
  · rfl
  · have hv : V*V.transpose+(η • 1-V*V.transpose)=η • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    rw [hv,smul_smul]
    congr 1
    ring
end EuclideanRamsey

namespace EuclideanRamsey
open Matrix
lemma row_gram_distance {d : ℕ} {τ : Type uRow} [Fintype τ]
    (v : τ → ℝ) (U : Matrix (Fin d) τ ℝ) (q : ℝ)
    (hU : U*U.transpose=q • (1 : Matrix (Fin d) (Fin d) ℝ))
    (a b : Fin d → ℝ) :
    (∑ x,((v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x))^2) =
      q*(∑ j,(a j-b j)^2) := by
  have he (x : τ) : (v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x) =
      (U.transpose *ᵥ (a-b)) x := by
    simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Pi.sub_apply,
      mul_sub,Finset.sum_sub_distrib]
    simp only [mul_comm]
    ring
  simp only [he,pow_two]
  change (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) = _
  have hquad : (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) =
      (a-b) ⬝ᵥ ((U*U.transpose) *ᵥ (a-b)) := by
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec (a-b) U]
    congr 1
    exact (Matrix.vecMul_transpose U.transpose (a-b)).symm
  rw [hquad,hU,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,dotProduct,Pi.sub_apply]

theorem two_scale_of_signed_rows {α : Type} [DecidableEq α] {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (a : Fin s → EuclideanSpace ℝ (Fin d))
    (v : α → ℝ) (g : α → Fin d → ℝ) (f : α →₀ ℚ)
    (ζ η : ℝ) (hζ : 0 < ζ) (hη : 0 < η)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f' g' : Fin s → EuclideanSpace ℝ (Fin ℓ)),
      (∀ i j,‖f' i-f' j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g' i-g' j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g' i (σ x)=f' i x := by
  classical
  obtain ⟨τ,hτ,vp,vn,U,V,hdiff,htrace,hperm⟩ :=
    normalized_signed_rows hs (fun i j => a i j) v g f ζ η hζ heval hmom hneg
  let := hτ
  obtain ⟨R,hR1,hR2⟩ := complete_gram_pair U V η hη hdiff htrace
  let c := (Real.sqrt (1+η))⁻¹
  let Up := c • U.fromCols R
  let Un := c • V.fromCols R
  let cp : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vp (fun _ => 0) x
  let cn : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vn (fun _ => 0) x
  let ip (i : Fin s) (x : τ ⊕ Fin d) := cp x+∑ j,a i j*Up j x
  let ineg (i : Fin s) (x : τ ⊕ Fin d) := cn x+∑ j,a i j*Un j x
  have hperm' (i : Fin s) : ∃ σ : Equiv.Perm (τ ⊕ Fin d),∀ x,ineg i (σ x)=ip i x := by
    obtain ⟨σ,hσ⟩ := hperm i
    refine ⟨Equiv.sumCongr σ (Equiv.refl _),?_⟩
    intro x
    cases x with
    | inl x =>
      have h := congrArg (fun r : ℝ => c*r) (hσ x)
      simpa [ineg,ip,cn,cp,Up,Un,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using h
    | inr x => simp [ineg,ip,cn,cp,Up,Un]
  let ℓ := Fintype.card (τ ⊕ Fin d)
  let e := Fintype.equivFin (τ ⊕ Fin d)
  let fp (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ip i (e.symm x))
  let fn (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ineg i (e.symm x))
  have hd' : Nonempty (τ ⊕ Fin d) := ⟨Sum.inr ⟨0,hd⟩⟩
  refine ⟨ℓ,Fintype.card_pos_iff.mpr hd',fp,fn,?_,?_,?_⟩
  · intro i j
    have h := row_gram_distance cp Up 1 (by simpa only [one_smul] using hR1) (a i) (a j)
    rw [one_mul] at h
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fp,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ip i x-ip j x)^2)]
    exact h
  · intro i j
    have h := row_gram_distance cn Un (η/(1+η)) hR2 (a i) (a j)
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fn,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ineg i x-ineg j x)^2)]
    exact h
  · intro i
    obtain ⟨σ,hσ⟩ := hperm' i
    refine ⟨e.symm.trans (σ.trans e),?_⟩
    intro x
    simpa [fp,fn,Equiv.trans_apply] using hσ (e.symm x)
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators
lemma evaluation_coset_pushforward {k : ℕ} (φ : Lattice k →+ ℝ)
    (μ : LatticeRing k) (hμ : cosetPushforward φ.ker μ=0) (n : ℝ) :
    μ.coeff.mapDomain (fun x => φ x/n)=0 := by
  let f := QuotientAddGroup.lift φ.ker φ le_rfl
  have he : (fun x => φ x/n) = (fun y => f y/n) ∘ QuotientAddGroup.mk' φ.ker := by
    funext x
    rfl
  rw [he,Finsupp.mapDomain_comp]
  change Finsupp.mapDomain _ (cosetPushforward φ.ker μ) = 0
  rw [hμ,Finsupp.mapDomain_zero]

lemma lattice_affine_evaluation {k d s : ℕ} (a : Fin s → Space d)
    (w : Fin k → AffineVector d) (i : Fin s) (γ : Lattice k) (n : ℝ) :
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)) (rationalize γ)/n =
      (∑ j,(γ j:ℝ)/n*w j none)+
        ∑ α,a i α*(∑ j,(γ j:ℝ)/n*w j (some α)) := by
  simp only [LinearMap.comp_apply,Fintype.linearCombination_apply,map_sum,map_smul,
    rationalize,AddMonoidHom.coe_mk,Rat.smul_def,rowEvaluation,LinearMap.coe_mk,
    AddHom.coe_mk,Fintype.sum_option,realAugmented,one_mul]
  change (∑ j,(γ j:ℝ)*(w j none+∑ α,a i α*w j (some α)))/n = _
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma scaled_second_moment {k d : ℕ} (μ : LatticeRing k) (n : ℕ)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (ζ : ℚ) (hsecond : ∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l)
    (α β : Fin d) :
    μ.coeff.sum (fun γ q => (q:ℝ)*(∑ j,U α j*latticeSample n γ j)*
      (∑ l,U β l*latticeSample n γ l)) =
      (ζ:ℝ)*(U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose) α β := by
  have hm (j l : Fin k) : ∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*latticeSample n γ j*latticeSample n γ l = (ζ:ℝ)*(C j l:ℝ) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (hsecond j l)
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul,secondMoment,
      Finsupp.sum,Rat.cast_sum,Rat.cast_intCast] at h
    rw [← h,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp only [latticeSample]
    ring
  simp only [Finsupp.sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  have hr (j l : Fin k) : (∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*(U α j*latticeSample n γ j)*(U β l*latticeSample n γ l)) =
      U α j*U β l*((ζ:ℝ)*(C j l:ℝ)) := by
    rw [← hm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    ring
  simp only [hr]
  change _ = (ζ:ℝ)*(∑ l,(∑ j,U α j*(C j l:ℝ))*U β l)
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f g : Fin s → Space ℓ),
      (∀ i j,‖f i-f j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x := by
  classical
  obtain ⟨k,w,C,hk,hC,hU,hquot⟩ := realCriterion_lattice a hd h
  let U : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
  let φ (i : Fin s) : Lattice k →+ ℝ :=
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
  let Λ (i : Fin s) := (φ i).ker
  obtain ⟨ν,hcos,hzero,hfirst,hsecond⟩ :=
    finite_lattice_identity k s hk hs Λ C hC hquot
  obtain ⟨n,μ,ζ,hn,hζ,hcos,_,_,hmom,hneg⟩ :=
    rational_smoothing hd Λ ν C U hC hU hcos hzero hfirst hsecond η hη
  let v (γ : Lattice k) : ℝ := ∑ j,(γ j:ℝ)/(n:ℝ)*w j none
  let g (γ : Lattice k) (α : Fin d) : ℝ := ∑ j,U α j*latticeSample n γ j
  have heval (i : Fin s) : μ.coeff.mapDomain (fun γ => v γ+∑ α,a i α*g γ α)=0 := by
    have he := evaluation_coset_pushforward (φ i) μ (hcos i) (n:ℝ)
    have heq : (fun γ => φ i γ/(n:ℝ)) = (fun γ => v γ+∑ α,a i α*g γ α) := by
      funext γ
      simpa only [φ,v,g,U,latticeSample,mul_comm,AddMonoidHom.comp_apply,LinearMap.toAddMonoidHom_coe] using lattice_affine_evaluation a w i γ (n:ℝ)
    rwa [heq] at he
  have hmoment (α β : Fin d) : μ.coeff.sum (fun γ q => (q:ℝ)*g γ α*g γ β) =
      (ζ:ℝ)*(if α=β then 1 else 0) := by
    have he := scaled_second_moment μ n C U ζ hmom α β
    rw [hU] at he
    exact he
  have hnegative : μ.coeff.sum (fun γ q => max (-(q:ℝ)) 0*(∑ α,(g γ α)^2)) < η*(ζ:ℝ) := by
    rw [tsum_eq_sum (s := μ.coeff.support)] at hneg
    · exact hneg
    · intro γ hγ
      have hz := Finsupp.notMem_support_iff.mp hγ
      simp [hz]
  exact two_scale_of_signed_rows hd hs a v g μ.coeff (ζ:ℝ) η
    (by exact_mod_cast hζ) hη heval hmoment hnegative

end EuclideanRamsey

end

end OAI
