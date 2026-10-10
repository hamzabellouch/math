import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixUnitsHom

namespace OAI


noncomputable section



namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

local instance (priority := 2000) functionSemiring (p q : ℕ) :
    Semiring C(Interval,TensorMat p q) := (inferInstance : Ring C(Interval,TensorMat p q)).toSemiring
variable {p q : ℕ}

def scalarMatrix (g : C(Interval,ℝ)) (x : TensorMat p q) : C(Interval,TensorMat p q) :=
  ⟨fun t => g t • x,by fun_prop⟩

lemma scalarMatrix_mem (g : C(Interval,ℝ)) (x : TensorMat p q)
    (hg0 : g leftEndpoint=0) (hg1 : g rightEndpoint=0) :
    scalarMatrix g x ∈ dimensionDrop p q := by
  constructor
  · change ∃ y,(leftAmplification p q) y=(scalarMatrix g x) leftEndpoint
    exact ⟨0,by simp [scalarMatrix,hg0]⟩
  · change ∃ y,(rightAmplification p q) y=(scalarMatrix g x) rightEndpoint
    exact ⟨0,by simp [scalarMatrix,hg1]⟩

def interiorMatrix (g : C(Interval,ℝ)) (hg0 : g leftEndpoint=0)
    (hg1 : g rightEndpoint=0) (x : TensorMat p q) : DimensionDrop p q :=
  ⟨scalarMatrix g x,scalarMatrix_mem g x hg0 hg1⟩

lemma interiorMatrix_norm_le (g : C(Interval,ℝ)) (hg0 : g leftEndpoint=0)
    (hg1 : g rightEndpoint=0) (x : TensorMat p q) (hg : ∀ t,|g t|≤1) :
    ‖interiorMatrix g hg0 hg1 x‖≤‖x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
  intro t
  change ‖g t • x‖≤‖x‖
  have he : g t • x=(g t:ℂ) • x := by
    ext i j
    exact (Complex.coe_smul (g t) (x i j)).symm
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg x) (hg t)

lemma interiorMatrix_norm_eq (g : C(Interval,ℝ)) (hg0 : g leftEndpoint=0)
    (hg1 : g rightEndpoint=0) (x : TensorMat p q) (hg : ∀ t,|g t|≤1)
    (t : Interval) (hgt : g t=1) : ‖interiorMatrix g hg0 hg1 x‖=‖x‖ := by
  apply le_antisymm (interiorMatrix_norm_le g hg0 hg1 x hg)
  change ‖x‖ ≤ ‖scalarMatrix g x‖
  calc
    ‖x‖ = ‖scalarMatrix g x t‖ := by
      change ‖x‖ = ‖g t • x‖
      rw [hgt, one_smul]
    _ ≤ ‖scalarMatrix g x‖ := ContinuousMap.norm_coe_le_norm _ t

end JiangSuConstruction

end


noncomputable section
namespace JiangSuConstruction
open ConcreteMatrixUnits
open scoped CStarAlgebra ComplexOrder

variable {p q : ℕ}
local notation "I" => Fin p × Fin q
local instance (priority := 2000) localizationFunctionSemiring (p q : ℕ) :
    Semiring C(Interval,TensorMat p q) := (inferInstance : Ring C(Interval,TensorMat p q)).toSemiring

lemma matrix_unit_norm (i j : I) : ‖unit i j‖=1 := by
  apply le_antisymm (unit_norm_le_one i j)
  have hn := CStarMatrix.norm_entry_le_norm (M := unit i j) (i := i) (j := j)
  simpa [unit,Matrix.single_apply] using hn

lemma matrix_unit_compress (o i j : I) (x : TensorMat p q) :
    unit o i*x*unit j o = x i j • unit o o := by
  change CStarMatrix.ofMatrix (Matrix.single o i (1:ℂ)*
    CStarMatrix.ofMatrix.symm x*Matrix.single j o 1) = _
  rw [Matrix.single_mul_mul_single]
  ext a b
  by_cases ha : o=a <;> by_cases hb : o=b <;>
    simp [Matrix.single_apply,unit,ha,hb]

lemma exists_interior_bump (t : Interval) (ht0 : t≠leftEndpoint) (ht1 : t≠rightEndpoint)
    (V : Set Interval) (hV : IsOpen V) (ht : t∈V) :
    ∃ g : C(Interval,ℝ), g t=1 ∧ g leftEndpoint=0 ∧ g rightEndpoint=0 ∧
      (∀ x,0≤g x ∧ g x≤1) ∧ ∀ x,g x≠0 → x∈V := by
  let W := V ∩ ({leftEndpoint,rightEndpoint} : Set Interval)ᶜ
  have hW : IsOpen W := hV.inter ((isClosed_singleton.union isClosed_singleton).isOpen_compl)
  have htW : t∈W := ⟨ht,by simpa using And.intro ht0 ht1⟩
  have hd : Disjoint Wᶜ {t} := Set.disjoint_singleton_right.mpr (by simpa using htW)
  obtain ⟨g,hg0,hg1,hg⟩ := exists_continuous_zero_one_of_isClosed hW.isClosed_compl isClosed_singleton hd
  refine ⟨g,hg1 (by simp),hg0 ?_,hg0 ?_,fun x => hg x,?_⟩
  · simp [W]
  · simp [W]
  · intro x hx
    by_contra h
    exact hx (hg0 (fun hW => h hW.1))

lemma complex_smul_real (r : ℝ) (x : TensorMat p q) : (r:ℂ) • x=r • x := by
  ext i j
  exact Complex.coe_smul r (x i j)

lemma scalarMatrix_apply_complex (g : C(Interval,ℝ)) (x : TensorMat p q) (t : Interval) :
    scalarMatrix g x t=(g t:ℂ) • x := (complex_smul_real _ _).symm

lemma interior_compression_error (g : C(Interval,ℝ)) (hg0 : g leftEndpoint=0)
    (hg1 : g rightEndpoint=0) (hg : ∀ x, |g x|≤1) (t : Interval)
    (o i j : I) (f : DimensionDrop p q) {ε : ℝ} (hε : 0≤ε)
    (hf : ∀ x,g x≠0 → ‖f.val x-f.val t‖≤ε) :
    ‖interiorMatrix g hg0 hg1 (unit o i) * f * interiorMatrix g hg0 hg1 (unit j o) -
      (f.val t i j) • interiorMatrix (g*g) (by simp [hg0]) (by simp [hg1]) (unit o o)‖ ≤ ε := by
  apply (ContinuousMap.norm_le _ hε).mpr
  intro x
  change ‖scalarMatrix g (unit o i) x*f.val x*scalarMatrix g (unit j o) x -
    (f.val t i j) • scalarMatrix (g*g) (unit o o) x‖ ≤ ε
  simp only [scalarMatrix_apply_complex,ContinuousMap.mul_apply,Complex.ofReal_mul]
  have he : ((g x:ℂ) • unit o i)*f.val x*((g x:ℂ) • unit j o) -
      f.val t i j • (((g x:ℂ)*(g x:ℂ)) • unit o o) =
      ((g x:ℂ) • unit o i)*(f.val x-f.val t)*((g x:ℂ) • unit j o) := by
    rw [mul_sub,sub_mul]
    congr 1
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [matrix_unit_compress,smul_smul]
    congr 1
    ring
  rw [he]
  by_cases hx : g x=0
  · simp [hx,hε]
  · have ha : ‖(g x:ℂ) • unit o i‖≤1 := by
      simpa [norm_smul,matrix_unit_norm,Complex.norm_real,Real.norm_eq_abs] using hg x
    have hb : ‖(g x:ℂ) • unit j o‖≤1 := by
      simpa [norm_smul,matrix_unit_norm,Complex.norm_real,Real.norm_eq_abs] using hg x
    calc
      _ ≤ (‖(g x:ℂ) • unit o i‖*‖f.val x-f.val t‖)*‖(g x:ℂ) • unit j o‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*ε)*1 := by gcongr; exact hf x hx
      _ = ε := by ring

end JiangSuConstruction

end

end OAI
