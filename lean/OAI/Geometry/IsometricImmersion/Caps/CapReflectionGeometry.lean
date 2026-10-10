import OAI.Geometry.IsometricImmersion.Calculus.AffineCovariantHessian
import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature
import OAI.Geometry.IsometricImmersion.Coordinates.AffinePushforward
import OAI.Geometry.IsometricImmersion.Caps.C8ActualCapEstimate
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Model

def reflectionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,-1]

def reflectPoint (p : Coord) : Coord := fun i => if i = 0 then p 0 else -p 1

@[simp] theorem reflectPoint_zero (p : Coord) : reflectPoint p 0 = p 0 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_one (p : Coord) : reflectPoint p 1 = -p 1 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_twice (p : Coord) : reflectPoint (reflectPoint p) = p := by
  ext i
  fin_cases i <;> simp

theorem reflectPoint_eq_affine : reflectPoint = affineCoordinates 0 reflectionMatrix := by
  funext p
  ext i
  fin_cases i <;> simp [reflectPoint,affineCoordinates,reflectionMatrix,
    dotProduct,Fin.sum_univ_two]

theorem reflectionMatrix_square : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem reflectionMatrix_det : reflectionMatrix.det = -1 := by
  norm_num [reflectionMatrix,Matrix.det_fin_two]

theorem reflectionMatrix_isUnit : IsUnit reflectionMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  rw [reflectionMatrix_det]
  norm_num

@[simp] theorem reflectionMatrix_inv : reflectionMatrix⁻¹ = reflectionMatrix :=
  Matrix.inv_eq_left_inv reflectionMatrix_square

theorem reflectPoint_contDiff : ContDiff ℝ ∞ reflectPoint := by
  rw [reflectPoint_eq_affine]
  exact affineCoordinates_contDiff 0 reflectionMatrix

def reflectionIsometry : Coord ≃ₗᵢ[ℝ] Coord where
  toFun := reflectPoint
  invFun := reflectPoint
  left_inv := reflectPoint_twice
  right_inv := reflectPoint_twice
  map_add' p q := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.add_apply,add_comm]
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.smul_apply,smul_eq_mul]
  norm_map' p := by
    change ‖reflectPoint p‖ = ‖p‖
    rw [Pi.norm_def,Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro index _
    fin_cases index <;> simp

def reflectedScalar {V : Type*} (f : Coord → V) : Coord → V := f ∘ reflectPoint

def reflectedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 reflectionMatrix

theorem reflectedScalar_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (reflectedScalar f) (reflectPoint ⁻¹' U) :=
  hf.comp reflectPoint_contDiff.contDiffOn (fun _ hp => hp)

theorem reflectedDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (reflectPoint ⁻¹' U) := hU.preimage reflectPoint_contDiff.continuous

theorem reflectedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (reflectedMetric g) (reflectPoint ⁻¹' U) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 reflectionMatrix
      (Matrix.mulVec_injective_of_isUnit reflectionMatrix_isUnit)

theorem reflectedMetric_add (g eta : MetricField) :
    reflectedMetric (g+eta) = reflectedMetric g + reflectedMetric eta :=
  affinePullbackMetric_add g eta 0 reflectionMatrix

theorem reflectedMetric_entry (g : MetricField) (p : Coord) (i j : Fin 2) :
    reflectedMetric g p i j =
      if i=j then g (reflectPoint p) i j else -g (reflectPoint p) i j := by
  rw [reflectPoint_eq_affine]
  fin_cases i <;> fin_cases j <;>
    simp [reflectedMetric,affinePullbackMetric,reflectionMatrix,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_det (g : MetricField) (p : Coord) :
    (reflectedMetric g p).det = (g (reflectPoint p)).det := by
  simpa only [reflectedMetric,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using det_affinePullbackMetric g 0 reflectionMatrix p

theorem reflectedMetric_curvature {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : reflectPoint p ∈ U) :
    gaussianCurvature (reflectedMetric g) p = gaussianCurvature g (reflectPoint p) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    covHessian (reflectedMetric g) (reflectedScalar z) p =
      reflectionMatrixᵀ * covHessian g z (reflectPoint p) * reflectionMatrix := by
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine] using
    covHessian_affinePullback hg hz hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian_entry {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) (i j : Fin 2) :
    covHessian (reflectedMetric g) (reflectedScalar z) p i j =
      if i=j then covHessian g z (reflectPoint p) i j
      else -covHessian g z (reflectPoint p) i j := by
  rw [reflectedMetric_hessian hg hz hU hp]
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_hessian_det {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    (covHessian (reflectedMetric g) (reflectedScalar z) p).det =
      (covHessian g z (reflectPoint p)).det := by
  rw [reflectedMetric_hessian hg hz hU hp]
  simp [Matrix.det_mul,Matrix.det_transpose]

theorem reflectedMetric_energy {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    heightEnergy (reflectedMetric g) (reflectedScalar z) p = heightEnergy g z (reflectPoint p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using
    heightEnergy_affinePullback (g := g) 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hd)

theorem reflectedMetric_quotient {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    hessianQuotient (reflectedMetric g) (reflectedScalar z) p =
      -hessianQuotient g z (reflectPoint p) := by
  simp only [hessianQuotient,reflectedMetric_hessian_entry hg hz hU hp,
    show (0 : Fin 2) ≠ 1 by decide,ite_false,ite_true,neg_div]

theorem reflectPoint_mem_symmetricSquare (r : ℝ) (p : Coord) :
    reflectPoint p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) ↔
      p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) := by
  simp only [mem_Icc,Pi.le_def,Fin.forall_fin_two,reflectPoint_zero,reflectPoint_one]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

theorem reflectPoint_mem_modelSquare (p : Coord) :
    reflectPoint p ∈ modelSquare ↔ p ∈ modelSquare := reflectPoint_mem_symmetricSquare 3 p

theorem reflectedDomain_contains_modelSquare {U : Set Coord} (hS : modelSquare ⊆ U) :
    modelSquare ⊆ reflectPoint ⁻¹' U := by
  intro p hp
  exact hS ((reflectPoint_mem_modelSquare p).mpr hp)

theorem modelCurvature_reflect (kappa : ℝ) (p : Coord) :
    modelCurvature kappa (reflectPoint p) = modelCurvature kappa p := by
  simp only [modelCurvature,reflectPoint_zero,reflectPoint_one]
  rw [modelProfile_even (p 1)]

theorem reflectedMetric_model {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∀ p ∈ reflectPoint ⁻¹' U,
      gaussianCurvature (reflectedMetric g0) p = modelCurvature kappa p := by
  intro p hp
  rw [reflectedMetric_curvature hg0 hU hp,hmodel _ hp,modelCurvature_reflect]

theorem reflectedMetric_eq_pushforward (g : MetricField) :
    reflectedMetric g = affinePushforwardMetric g 0 reflectionMatrix := by
  funext p
  simp only [reflectedMetric,affinePullbackMetric,affinePushforwardMetric,
    affineInverseCoordinates,affineCoordinates,reflectionMatrix_inv,sub_zero,zero_add]

theorem reflectedMetric_tsupport (g : MetricField) :
    tsupport (reflectedMetric g) = reflectPoint '' tsupport g := by
  rw [reflectedMetric_eq_pushforward,reflectPoint_eq_affine]
  exact affinePushforwardMetric_tsupport g 0 reflectionMatrix reflectionMatrix_isUnit

theorem reflectedMetric_support_patch {eta : MetricField} (h : tsupport eta ⊆ patchBox) :
    tsupport (reflectedMetric eta) ⊆ patchBox := by
  rw [reflectedMetric_tsupport]
  rintro p ⟨q,hq,rfl⟩
  exact (reflectPoint_mem_symmetricSquare (1/10) q).mpr (h hq)

theorem reflectedScalar_jet_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) (p : Coord) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (reflectedScalar f) p‖ =
      ‖iteratedFDeriv ℝ k f (reflectPoint p)‖ :=
  reflectionIsometry.norm_iteratedFDeriv_comp_right f p k

theorem reflectedMetric_entry_jet_norm (g : MetricField) (p : Coord)
    (i j : Fin 2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ =
      ‖iteratedFDeriv ℝ k (fun q => g q i j) (reflectPoint p)‖ := by
  have he : (fun q => reflectedMetric g q i j) =
      if i=j then reflectedScalar (fun q => g q i j)
      else -reflectedScalar (fun q => g q i j) := by
    funext q
    rw [reflectedMetric_entry]
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · exact reflectedScalar_jet_norm _ p k
  · rw [iteratedFDeriv_neg_apply,norm_neg]
    exact reflectedScalar_jet_norm _ p k

theorem reflectedScalar_C8 {z : Coord → ℝ} {Z : ℝ}
    (hZ : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (reflectedScalar z) p‖ ≤ Z := by
  intro k hk p hp
  rw [reflectedScalar_jet_norm]
  exact hZ k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem reflectedMetric_C8 {g : MetricField} {G : ℝ}
    (hG : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) :
    ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ ≤ G := by
  intro i j k hk p hp
  rw [reflectedMetric_entry_jet_norm]
  exact hG i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

end SmoothLocal.Flow.Reflection

end

end OAI
