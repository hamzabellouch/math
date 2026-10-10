import OAI.GroupTheory.Kervaire.UnitaryHomotopy

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The ambient projection onto the skew-Hermitian tangent at the identity. -/
def skewPart {I : Type*} [Fintype I] [DecidableEq I] :
    Mat I →ₗ[ℝ] skewAdjoint.submodule ℝ (Mat I) where
  toFun A := ⟨(1/2 : ℝ) • (A-star A), by
    change star ((1/2 : ℝ) • (A-star A)) = -((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_sub,star_star,star_trivial]
    rw [← neg_sub A (star A),smul_neg]⟩
  map_add' A B := by
    apply Subtype.ext
    change (1/2 : ℝ) • ((A+B)-star (A+B)) =
      (1/2 : ℝ) • (A-star A)+(1/2 : ℝ) • (B-star B)
    rw [star_add]
    module
  map_smul' c A := by
    apply Subtype.ext
    change (1/2 : ℝ) • (c • A-star (c • A)) = c • ((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_trivial]
    module

@[simp] lemma skewPart_coe {I : Type*} [Fintype I] [DecidableEq I]
    (A : skewAdjoint.submodule ℝ (Mat I)) : skewPart (A : Mat I) = A := by
  apply Subtype.ext
  change (1/2 : ℝ) • ((A : Mat I)-star (A : Mat I)) = A
  rw [A.property]
  module

/-- A constant ambient form restricting to the determinant volume on the unitary tangent. -/
def tangentVolume {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (skewAdjoint.submodule ℝ (Mat I))) : Mat I [⋀^J]→L[ℝ] ℝ where
  toAlternatingMap := b.det.compLinearMap skewPart
  cont := by
    change Continuous (fun v : J → Mat I ↦ b.det (fun j ↦ skewPart (v j)))
    simp only [Basis.det_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun v : J → Mat I ↦ (b.coord i) (skewPart (v j)))
    exact (b.coord i).continuous_of_finiteDimensional.comp
      (skewPart.continuous_of_finiteDimensional.comp (continuous_apply j))

lemma tangentVolume_equiv_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (L : Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R))) :
    tangentVolume c (fun j ↦ (L (b j) : Mat (K ⊕ R))) ≠ 0 := by
  change c.det (fun j ↦ skewPart (L (b j) : Mat (K ⊕ R))) ≠ 0
  simp only [skewPart_coe]
  exact (c.isUnit_det (b.map L)).ne_zero

lemma model_jacobian_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R)) :
    tangentVolume c (fun j ↦ fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction (b j) : Alg K R))) ≠ 0 := by
  simp only [fderiv_model_gauge]
  exact tangentVolume_equiv_ne_zero b c (modelHorizontalEquiv U V)

/-- The only incidence fiber over the identity is the connected gauge orbit. -/
lemma model_fiber_blocks (X A : Mat K) (B : Matrix K R ℂ) (C : Matrix R K ℂ)
    (D T : Mat R) (hQ : fromBlocks A B C D ∈ unitary (Mat (K ⊕ R)))
    (heq : diag X (-1) * fromBlocks A B C D = fromBlocks A B C D * diag 1 T) :
    X = 1 ∧ B = 0 ∧ C = 0 ∧ T = -1 ∧ A ∈ unitary (Mat K) ∧ D ∈ unitary (Mat R) := by
  have hh : X*A = A ∧ X*B = B*T ∧ -C = C ∧ -D = D*T := by
    simpa [diag, fromBlocks_multiply] using heq
  have hC : C = 0 := by
    ext i j
    have hc := congrFun (congrFun hh.2.2.1 i) j
    change -C i j = C i j at hc
    change C i j = 0
    linear_combination -(1/2 : ℂ) * hc
  subst C
  have hu := Unitary.mem_iff.mp hQ
  have hu₁ : star A*A = 1 ∧ star A*B = 0 ∧ Bᴴ*A = 0 ∧ Bᴴ*B+star D*D = 1 := by
    simpa only [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← fromBlocks_one, fromBlocks_inj] using hu.1
  have hA' : A*star A = 1 := mul_eq_one_comm.mp hu₁.1
  have hB : B = 0 := by
    have h := congrArg (fun B : Matrix K R ℂ ↦ A * B) hu₁.2.1
    simpa only [← Matrix.mul_assoc, hA', Matrix.one_mul, Matrix.mul_zero] using h
  subst B
  have hD : star D*D = 1 := by simpa using hu₁.2.2.2
  have hT : T = -1 := by
    have h := congrArg (star D * ·) hh.2.2.2
    simpa only [mul_neg, ← Matrix.mul_assoc, hD, one_mul] using h.symm
  have hX : X = 1 := by
    have h := congrArg (· * star A) hh.1
    simpa only [Matrix.mul_assoc, hA', mul_one] using h
  exact ⟨hX,rfl,rfl,hT,⟨hu₁.1,hA'⟩,⟨hD,mul_eq_one_comm.mp hD⟩⟩

lemma model_fiber_iff (X : Mat K) (Q : unitary (Mat (K ⊕ R))) (T : unitary (Mat R)) :
    diag X (-1) * (Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R)) * diag 1 (T : Mat R) ↔
      X = 1 ∧ (T : Mat R) = -1 ∧ ∃ (U : unitary (Mat K)) (V : unitary (Mat R)),
        (Q : Mat (K ⊕ R)) = diag (U : Mat K) (V : Mat R) := by
  constructor
  · intro h
    have hQ := Q.property
    rw [← fromBlocks_toBlocks (Q : Mat (K ⊕ R))] at h hQ
    obtain ⟨hX,hB,hC,hT,hA,hD⟩ := model_fiber_blocks _ _ _ _ _ _ hQ h
    refine ⟨hX,hT,⟨_,hA⟩,⟨_,hD⟩,?_⟩
    change (Q : Mat (K ⊕ R)) = diag (Q : Mat (K ⊕ R)).toBlocks₁₁ (Q : Mat (K ⊕ R)).toBlocks₂₂
    calc
      _ = fromBlocks (Q : Mat (K ⊕ R)).toBlocks₁₁ (Q : Mat (K ⊕ R)).toBlocks₁₂
          (Q : Mat (K ⊕ R)).toBlocks₂₁ (Q : Mat (K ⊕ R)).toBlocks₂₂ := (fromBlocks_toBlocks _).symm
      _ = _ := by rw [hB,hC]; rfl
  · rintro ⟨rfl,hT,U,V,hQ⟩
    rw [hQ,hT,diag_mul,diag_mul]
    simp

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

/-- A finite-spectrum unitary has a skew logarithm, including the cut point -1. -/
lemma exists_skew_log (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ a : A, star a = -a ∧ exp a = (u : A) := by
  let f : ℂ → ℂ := fun z ↦ (z.arg : ℂ) * I
  have hf : ContinuousOn f (spectrum ℂ (u : A)) := hfin.continuousOn f
  have hnorm : IsStarNormal (u : A) := inferInstance
  refine ⟨cfc f (u : A), ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    apply cfc_congr
    intro z _
    simp [f, mul_neg]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp' Complex.exp f (u : A)
      Complex.continuous_exp.continuousOn hf hnorm]
    conv_rhs => rw [← cfc_id' ℂ (u : A)]
    apply cfc_congr
    intro z hz
    have hn := spectrum.norm_eq_one_of_unitary u.property hz
    simpa only [f, hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z

/-- A smooth ambient path from the identity to any finite-spectrum unitary. -/
lemma exists_smooth_path (u : unitary A) (hfin : (spectrum ℂ (u : A)).Finite) :
    ∃ p : ℝ → A, ContDiff ℝ ∞ p ∧ p 0 = 1 ∧ p 1 = (u : A) ∧
      ∀ t, p t ∈ unitary A := by
  obtain ⟨a, ha, hua⟩ := exists_skew_log u hfin
  let p : ℝ → A := fun t ↦ exp (t • a)
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · exact (show AnalyticOnNhd ℝ (exp : A → A) Set.univ from
      fun x _ ↦ exp_analytic x).contDiff.comp (contDiff_id.smul contDiff_const)
  · simp [p]
  · simpa [p] using hua
  · intro t
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star (t • a) = -(t • a)
    simp [ha]

lemma matrix_exists_smooth_path {I : Type*} [Fintype I] [DecidableEq I]
    (u : unitary (Matrix I I ℂ)) :
    ∃ p : ℝ → Matrix I I ℂ, ContDiff ℝ ∞ p ∧ p 0 = 1 ∧ p 1 = (u : Matrix I I ℂ) ∧
      ∀ t, p t ∈ unitary (Matrix I I ℂ) :=
  exists_smooth_path u (Matrix.finite_spectrum _)

end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

def jacobian (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) : ℝ :=
  tangentVolume c (fun j ↦ fderiv ℝ (incidence f) (t,p) (0,p*(direction (b j) : Alg K R)))

lemma continuous_jacobian (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Continuous (jacobian b c f t) := by
  apply (tangentVolume c).toContinuousMultilinearMap.cont.comp
  apply continuous_pi
  intro j
  exact (((contDiff_incidence hf).continuous_fderiv (by simp)).comp
    (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_const.prodMk (continuous_id.mul continuous_const))

lemma model_fiber_gauge (t : ℝ) (p : unitary (Alg K R))
    (hp : incidence model (t,(p : Alg K R)) = 1) :
    ∃ (U : unitary (Mat K)) (V : unitary (Mat R)), p = gaugePoint U V := by
  let Q : unitary (Mat (K ⊕ R)) := ⟨p.val.2.1,(unitary_alg_parts p).2.1⟩
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  have hQ (D : Mat (K ⊕ R)) : star (Q : Mat (K ⊕ R))*((Q : Mat (K ⊕ R))*D) = D := by
    rw [← mul_assoc,Q.property.1,one_mul]
  have hdiag : diag (1 : Mat K) (star (T : Mat R))*diag 1 (T : Mat R) = 1 := by
    rw [diag_mul,one_mul,T.property.1,diag_one]
  have heq : diag p.val.1 (-1)*(Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) := by
    have hh := congrArg (fun M : Mat (K ⊕ R) ↦ M*(Q : Mat (K ⊕ R))*diag 1 (T : Mat R)) hp
    change diag p.val.1 (-1)*(Q : Mat (K ⊕ R))*diag 1 (star (T : Mat R))*star (Q : Mat (K ⊕ R)) *
      (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) = _ at hh
    simpa only [mul_assoc,hQ,hdiag,mul_one,one_mul] using hh
  obtain ⟨hX,hT,U,V,hUV⟩ := (model_fiber_iff p.val.1 Q T).mp heq
  refine ⟨U,V,Subtype.ext ?_⟩
  exact Prod.ext hX (Prod.ext hUV hT)

/-- The determinant volume is normalized by the base point's horizontal frame. -/
def modelVolumeBasis (b : Basis J ℝ (Horizontal K R)) :
    Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) :=
  b.map (modelHorizontalEquiv 1 1)

lemma model_jacobian_base (b : Basis J ℝ (Horizontal K R)) (t : ℝ) :
    jacobian b (modelVolumeBasis b) model t (gaugePoint (1 : unitary (Mat K)) (1 : unitary (Mat R)) : Alg K R) = 1 := by
  unfold jacobian
  simp only [fderiv_model_gauge]
  change (modelVolumeBasis b).det
    (fun j ↦ skewPart (modelHorizontalEquiv 1 1 (b j) : Mat (K ⊕ R))) = 1
  simp only [skewPart_coe]
  exact (modelVolumeBasis b).det_self

lemma model_jacobian_pos_gauge (b : Basis J ℝ (Horizontal K R)) (t : ℝ)
    (U : unitary (Mat K)) (V : unitary (Mat R)) :
    0 < jacobian b (modelVolumeBasis b) model t (gaugePoint U V : Alg K R) := by
  obtain ⟨u,hu,hu0,hu1,huU⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path U
  obtain ⟨v,hv,hv0,hv1,hvU⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path V
  let p : ℝ → Alg K R := fun s ↦ (1,diag (u s) (v s),-1)
  let j : ℝ → ℝ := fun s ↦ jacobian b (modelVolumeBasis b) model t (p s)
  have hp : Continuous p := by
    apply continuous_const.prodMk
    apply Continuous.prodMk _ continuous_const
    simp only [diag_eq_corner]
    exact ((in11 (K := K) (R := R)).continuous.comp hu.continuous).add
      ((in22 (K := K) (R := R)).continuous.comp hv.continuous)
  have hj : Continuous j := (continuous_jacobian b (modelVolumeBasis b) contDiff_model t).comp hp
  have hj0 : j 0 = 1 := by
    change jacobian b (modelVolumeBasis b) model t (1,diag (u 0) (v 0),-1) = 1
    rw [hu0,hv0]
    exact model_jacobian_base b t
  have hj1 : j 1 = jacobian b (modelVolumeBasis b) model t (gaugePoint U V : Alg K R) := by
    change jacobian _ _ _ _ (1,diag (u 1) (v 1),-1) = _
    rw [hu1,hv1]
    rfl
  have hne (s : ℝ) : j s ≠ 0 :=
    model_jacobian_ne_zero b (modelVolumeBasis b) t ⟨u s,huU s⟩ ⟨v s,hvU s⟩
  by_contra hn
  have hn' : j 1 ≤ 0 := by rw [hj1]; exact le_of_not_gt hn
  obtain ⟨s,_,hs⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 from zero_le_one)
    hj.continuousOn (show (0 : ℝ) ∈ Set.Icc (j 1) (j 0) from ⟨hn',by rw [hj0]; norm_num⟩)
  exact hne s hs

lemma model_jacobian_pos_fiber (b : Basis J ℝ (Horizontal K R)) (t : ℝ)
    (p : unitary (Alg K R)) (hp : incidence model (t,(p : Alg K R)) = 1) :
    0 < jacobian b (modelVolumeBasis b) model t (p : Alg K R) := by
  obtain ⟨U,V,rfl⟩ := model_fiber_gauge t p hp
  exact model_jacobian_pos_gauge b t U V

end KervaireIncidenceCurrent

end

end OAI
