import Mathlib
import OAI.MathematicalPhysics.BFSS.TaylorBounds

namespace OAI

/-! Gauge conjugation, exponential curves and nearest normal points. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

def colorExtract : ColorMatrix N →ₗ[ℝ] ColorVector N where
  toFun X := WithLp.toLp 2 (fun A => (Matrix.trace (M.color A * X)).re)
  map_add' _ _ := by
    ext A
    simp [Matrix.mul_add,Matrix.trace_add]
  map_smul' _ _ := by
    ext A
    simp [Matrix.trace_smul]

lemma colorExtract_embed (a : ColorVector N) : M.colorExtract (M.colorEmbed a) = a := by
  ext A
  exact M.colorCombination_coeff a A

lemma colorEmbed_extract (X : ColorMatrix N) (hX : X.IsHermitian) (ht : Matrix.trace X = 0) :
    M.colorEmbed (M.colorExtract X) = X := M.colorCombination_reconstruct X hX ht

def colorConjugate (U : ColorMatrix N) : ColorVector N →ₗ[ℝ] ColorVector N where
  toFun a := M.colorExtract (U * M.colorEmbed a * Uᴴ)
  map_add' _ _ := by simp only [map_add,mul_add,add_mul]
  map_smul' _ _ := by simp only [map_smul,mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

lemma colorEmbed_conjugate (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (a : ColorVector N) :
    M.colorEmbed (M.colorConjugate U a) = U * M.colorEmbed a * Uᴴ := by
  apply M.colorEmbed_extract
  · exact Matrix.isHermitian_mul_mul_conjTranspose U (M.colorCombination_hermitian a)
  · have hu : Uᴴ * U = 1 := (Unitary.mem_iff.mp hU).1
    rw [Matrix.trace_mul_cycle,hu,one_mul]
    exact M.colorCombination_traceless a

lemma bracket_conjugate (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (X Y : ColorMatrix N) :
    AlgebraData.bracket (U*X*Uᴴ) (U*Y*Uᴴ) = U * AlgebraData.bracket X Y * Uᴴ := by
  have hu : Uᴴ * U = 1 := (Unitary.mem_iff.mp hU).1
  have hp (X Y : ColorMatrix N) : (U*X*Uᴴ)*(U*Y*Uᴴ) = U*(X*Y)*Uᴴ := by
    calc
      _ = U*X*(Uᴴ*U)*Y*Uᴴ := by simp only [mul_assoc]
      _ = _ := by rw [hu]; simp only [mul_one,mul_assoc]
  unfold bracket
  rw [hp,hp]
  simp only [mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul]

lemma colorConjugate_lie (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (a b : ColorVector N) :
    M.colorLie (M.colorConjugate U a) (M.colorConjugate U b) =
      M.colorConjugate U (M.colorLie a b) := by
  apply M.colorEmbed_injective
  rw [M.colorEmbed_lie,M.colorEmbed_conjugate U hU,M.colorEmbed_conjugate U hU,
    M.colorEmbed_conjugate U hU,M.colorEmbed_lie]
  exact bracket_conjugate U hU _ _

def gaugeConjugate (U : ColorMatrix N) (q : Boson N) : Boson N :=
  WithLp.toLp 2 (fun p => M.colorConjugate U (spatialColor q p.1) p.2)

lemma spatialColor_gaugeConjugate (U : ColorMatrix N) (q : Boson N) (i : SpaceIndex) :
    spatialColor (M.gaugeConjugate U q) i = M.colorConjugate U (spatialColor q i) := rfl

lemma gaugeConjugate_zeroRelations (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (q : Boson N) (hq : M.ZeroRelations q) : M.ZeroRelations (M.gaugeConjugate U q) := by
  rcases hq with ⟨h01,h12,h20,hd⟩
  unfold ZeroRelations
  simp only [spatialColor_gaugeConjugate,M.colorConjugate_lie U hU,
    h01,h12,h20,map_smul]
  refine ⟨trivial,trivial,trivial,?_⟩
  intro i hi
  rw [hd i hi,map_zero]

lemma gaugeConjugate_mem_massiveZeros (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (q : Boson N) (hq : q ∈ M.massiveZeros) : M.gaugeConjugate U q ∈ M.massiveZeros := by
  apply M.potential_zero_of_relations
  exact M.gaugeConjugate_zeroRelations U hU q (M.potential_zero_relations q hq)
end
end BFSSQuantum.AlgebraData
namespace BFSSGaugeFlow
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exp_skew (X : Matrix n n ℂ) (hX : X.IsHermitian) (t : ℝ) :
    NormedSpace.exp (t • ((-Complex.I) • X)) ∈ unitary (Matrix n n ℂ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ (Matrix n n ℂ)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  change (t • ((-Complex.I) • X))ᴴ = -(t • ((-Complex.I) • X))
  simp [Matrix.conjTranspose_smul,hX.eq]

lemma exp_conj_deriv_zero (W X : Matrix n n ℂ) :
  HasDerivAt (fun t : ℝ => NormedSpace.exp (t • W) * X * NormedSpace.exp (t • (-W)))
    (W*X-X*W) 0 := by
  have hd := ((hasDerivAt_exp_smul_const W (0:ℝ)).mul_const X).mul
    (hasDerivAt_exp_smul_const (-W) (0:ℝ))
  convert! hd using 1
  simp [sub_eq_add_neg]

lemma exp_conj_reverse (X : Matrix n n ℂ) (hX : X.IsHermitian) (t : ℝ) :
  (NormedSpace.exp (t • ((-Complex.I) • X)))ᴴ =
    NormedSpace.exp (t • (-((-Complex.I) • X))) := by
  rw [←Matrix.exp_conjTranspose]
  congr 1
  simp [Matrix.conjTranspose_smul,hX.eq]
end
end BFSSGaugeFlow

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : BFSSQuantum.AlgebraData N)

lemma colorExtract_bracket (a b : ColorVector N) :
    M.colorExtract (AlgebraData.bracket (M.colorEmbed a) (M.colorEmbed b)) = M.colorLie a b := by
  rw [←M.colorEmbed_lie,M.colorExtract_embed]

def gaugeCurve (q : Boson N) (w : ColorVector N) (t : ℝ) : Boson N :=
  M.gaugeConjugate (NormedSpace.exp (t • ((-Complex.I) • M.colorEmbed w))) q

lemma gaugeCurve_mem_massiveZeros (q : Boson N) (hq : q ∈ M.massiveZeros)
    (w : ColorVector N) (t : ℝ) : M.gaugeCurve q w t ∈ M.massiveZeros :=
  M.gaugeConjugate_mem_massiveZeros _
    (BFSSGaugeFlow.exp_skew _ (M.colorCombination_hermitian w) t) q hq

lemma gaugeCurve_zero (q : Boson N) (w : ColorVector N) : M.gaugeCurve q w 0 = q := by
  ext p
  change M.colorExtract ((NormedSpace.exp (0 • ((-Complex.I) • M.colorEmbed w))) *
    M.colorEmbed (spatialColor q p.1) *
    (NormedSpace.exp (0 • ((-Complex.I) • M.colorEmbed w)))ᴴ) p.2 = q p
  simp only [zero_smul,NormedSpace.exp_zero,Matrix.conjTranspose_one,one_mul,mul_one,
    M.colorExtract_embed]
  rfl

lemma colorConjugate_curve_deriv (a w : ColorVector N) :
    HasDerivAt (fun t : ℝ => M.colorConjugate
      (NormedSpace.exp (t • ((-Complex.I) • M.colorEmbed w))) a) (M.colorLie w a) 0 := by
  have hd := (M.colorExtract.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (BFSSGaugeFlow.exp_conj_deriv_zero ((-Complex.I) • M.colorEmbed w) (M.colorEmbed a))
  have he : (((-Complex.I) • M.colorEmbed w)*M.colorEmbed a -
      M.colorEmbed a*((-Complex.I) • M.colorEmbed w)) =
      AlgebraData.bracket (M.colorEmbed w) (M.colorEmbed a) := by
    simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
  change HasDerivAt (fun t : ℝ => M.colorExtract
    (NormedSpace.exp (t • ((-Complex.I) • M.colorEmbed w)) * M.colorEmbed a *
    (NormedSpace.exp (t • ((-Complex.I) • M.colorEmbed w)))ᴴ)) _ 0
  simp_rw [BFSSGaugeFlow.exp_conj_reverse (M.colorEmbed w) (M.colorCombination_hermitian w)]
  convert! hd using 1
  simp only [LinearMap.coe_toContinuousLinearMap',he,M.colorExtract_bracket]

def bosonAssemble : (SpaceIndex → ColorVector N) →ₗ[ℝ] Boson N where
  toFun a := WithLp.toLp 2 (fun p => a p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma gaugeCurve_deriv_zero (q : Boson N) (w : ColorVector N) :
    HasDerivAt (M.gaugeCurve q w) (M.gaugeTangent q w) 0 := by
  have hd : HasDerivAt (fun t : ℝ => fun i : SpaceIndex => M.colorConjugate
      (NormedSpace.exp (t • ((-Complex.I) • M.colorEmbed w))) (spatialColor q i))
      (fun i : SpaceIndex => M.colorLie w (spatialColor q i)) 0 :=
    hasDerivAt_pi.mpr (fun i => M.colorConjugate_curve_deriv (spatialColor q i) w)
  exact ((bosonAssemble (N := N)).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hd

theorem nearest_zero_normal (x q : Boson N) (hq : q ∈ M.massiveZeros)
    (hmin : ∀ p ∈ M.massiveZeros, ‖x-q‖ ≤ ‖x-p‖) : x-q ∈ M.normalSlice q := by
  rw [normalSlice,Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨w,rfl⟩ := hu
  have hd := ((hasDerivAt_const (0:ℝ) x).sub (M.gaugeCurve_deriv_zero q w)).norm_sq
  have hm : IsLocalMin (fun t : ℝ => ‖x-M.gaugeCurve q w t‖^2) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change ‖x-M.gaugeCurve q w 0‖^2 ≤ ‖x-M.gaugeCurve q w t‖^2
    rw [M.gaugeCurve_zero]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
      (hmin _ (M.gaugeCurve_mem_massiveZeros q hq w t))
  have he := hm.hasDerivAt_eq_zero hd
  simp only [Pi.sub_apply,M.gaugeCurve_zero,zero_sub,inner_neg_right] at he
  linarith
end
end BFSSQuantum.AlgebraData

end OAI
