import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabOriginQuadrature

namespace OAI

/-! Actual rational cubature of the scalar slab shift. -/

noncomputable section
namespace ContinuumCoulomb.SlabOriginValue
open ExactQuantumFactoring.BitStackProgram

abbrev Parameters := (ℕ × ℚ) × (ℚ × ℚ)
abbrev Input := RationalTripleQuadrature.Input Parameters

def parameterCode : Parameters → List Bool :=
  prodCode (prodCode unaryCode ratCode) (prodCode ratCode ratCode)

def sample (e : Parameters) (x y z : ℚ) : ℚ :=
  CappedKernelProgram.approximate (e.1,(e.2.1*x,(e.2.1*y,e.2.2*z)))

def value (rho : ℚ) (x : Input) : ℚ :=
  -rho*x.2.1.2.1^2*x.2.1.2.2*RationalTripleQuadrature.value sample x

noncomputable opaque sampleInputProgram :
    Procedure (prodCode (prodCode (prodCode parameterCode ratCode) ratCode) ratCode)
      CappedKernelProgram.inputCode
      (fun q => (q.1.1.1.1,(q.1.1.1.2.1*q.1.1.2,
        (q.1.1.1.2.1*q.1.2,q.1.1.1.2.2*q.2)))) := by
  let xyz := Procedure.first (prodCode (prodCode parameterCode ratCode) ratCode) ratCode
  let ex := (Procedure.first (prodCode parameterCode ratCode) ratCode).comp xyz
  let e := (Procedure.first parameterCode ratCode).comp ex
  let x := (Procedure.second parameterCode ratCode).comp ex
  let y := (Procedure.second (prodCode parameterCode ratCode) ratCode).comp xyz
  let z := Procedure.second (prodCode (prodCode parameterCode ratCode) ratCode) ratCode
  let head := (Procedure.first (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp e
  let shape := (Procedure.second (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp e
  let H := (Procedure.first ratCode ratCode).comp shape
  let S := (Procedure.second ratCode ratCode).comp shape
  let hx := Procedure.ratMul.comp (H.pair x)
  let hy := Procedure.ratMul.comp (H.pair y)
  let sz := Procedure.ratMul.comp (S.pair z)
  exact head.pair (hx.pair (hy.pair sz))

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode (prodCode parameterCode ratCode) ratCode) ratCode)
      ratCode (fun q => sample q.1.1.1 q.1.1.2 q.1.2 q.2) :=
  CappedKernelProgram.program.comp sampleInputProgram

noncomputable opaque program (rho : ℚ) :
    Procedure (RationalQuadratureProgram.inputCode parameterCode) ratCode (value rho) := by
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode parameterCode)
  let params := (Procedure.first parameterCode (prodCode ratCode ratCode)).comp env
  let shape := (Procedure.second (prodCode unaryCode ratCode) (prodCode ratCode ratCode)).comp params
  let H := (Procedure.first ratCode ratCode).comp shape
  let S := (Procedure.second ratCode ratCode).comp shape
  let hsq := Procedure.ratMul.comp (H.pair H)
  let c := Procedure.constant (RationalQuadratureProgram.inputCode parameterCode) ratCode (-rho)
  let factor := Procedure.ratMul.comp ((Procedure.ratMul.comp (c.pair hsq)).pair S)
  let quad := RationalTripleQuadrature.program parameterCode sample sampleProgram
  exact (Procedure.ratMul.comp (factor.pair quad)).congrFun (by intro x; simp [value,pow_two])

noncomputable def certificate (rho : ℚ) :
    Turing.TM2ComputableInPolyTime (RationalQuadratureProgram.inputCode parameterCode)
      ratCode (value rho) := (program rho).toTM2

theorem sample_error (e : Parameters) (hε : 0 < e.1.2) (x y z : ℚ) :
    |(sample e x y z:ℝ)-SlabOriginQuadrature.integrand (e.1.2:ℝ)
      (e.2.1:ℝ) (e.2.2:ℝ) ![(x:ℝ),(y:ℝ),(z:ℝ)]| ≤
      (e.1.2:ℝ)⁻¹^2 * (2:ℝ)⁻¹^e.1.1 := by
  have h := CappedKernelProgram.approximation_error
    (e.1,(e.2.1*x,(e.2.1*y,e.2.2*z))) hε
  simpa only [sample,SlabOriginQuadrature.integrand,SlabOriginQuadrature.point,
    CappedKernelProgram.position,Rat.cast_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one] using h

theorem error (rho : ℚ) (x : Input) (hrho : 0 ≤ rho) (hε : 0 < x.2.1.1.2)
    (hH : 0 ≤ x.2.1.2.1) (hS : 0 ≤ x.2.1.2.2) (hh : 0 ≤ x.2.2.2)
    (ha : x.2.2.1 = -1) (hend : (x.1:ℚ)*x.2.2.2=2) :
    |(value rho x:ℝ)-slabPotential (rho:ℝ) (x.2.1.2.1:ℝ) (x.2.1.2.2:ℝ) 0| ≤
      (rho:ℝ)*(x.2.1.2.1:ℝ)^2*(x.2.1.2.2:ℝ)*8*
        (3*((x.2.1.1.2:ℝ)⁻¹^2*((x.2.1.2.1:ℝ)+(x.2.1.2.2:ℝ)))*(x.2.2.2:ℝ)+
          (x.2.1.1.2:ℝ)⁻¹^2*(2:ℝ)⁻¹^x.2.1.1.1)+
      (rho:ℝ)*(2*Real.pi*(x.2.1.1.2:ℝ)^2) := by
  have hv (w : Fin 3 → ℕ) (_hw : ∀ i, w i < x.1) :
      |(sample x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 0))
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 1))
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 2)):ℝ)-
        SlabOriginQuadrature.integrand (x.2.1.1.2:ℝ) (x.2.1.2.1:ℝ) (x.2.1.2.2:ℝ)
          (fun i => UniformQuadrature.node (-1) (x.2.2.2:ℝ) (w i))| ≤
          (x.2.1.1.2:ℝ)⁻¹^2*(2:ℝ)⁻¹^x.2.1.1.1 := by
    have heq : (fun i : Fin 3 => UniformQuadrature.node (-1) (x.2.2.2:ℝ) (w i)) =
        ![(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 0):ℝ),
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 1):ℝ),
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (w 2):ℝ)] := by
      funext i
      fin_cases i <;> simp [RationalQuadratureProgram.node,UniformQuadrature.node,ha]
    rw [heq]
    exact sample_error _ hε _ _ _
  have h := SlabOriginQuadrature.sampling_error
    (show 0 < (x.2.1.1.2:ℝ) by exact_mod_cast hε)
    (show 0 ≤ (rho:ℝ) by exact_mod_cast hrho)
    (show 0 ≤ (x.2.1.2.1:ℝ) by exact_mod_cast hH)
    (show 0 ≤ (x.2.1.2.2:ℝ) by exact_mod_cast hS)
    (show 0 ≤ (x.2.2.2:ℝ) by exact_mod_cast hh) (by positivity)
    (show (x.1:ℝ)*(x.2.2.2:ℝ)=2 by exact_mod_cast hend) _ hv
  simpa only [value,Rat.cast_mul,Rat.cast_neg,Rat.cast_pow,
    RationalTripleQuadrature.value_cast] using h

end ContinuumCoulomb.SlabOriginValue

end

end OAI
