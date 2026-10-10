import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockGauss
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-!
# The open two-block Gauss chart

The cell with invertible principal block is homeomorphic to lower-cross
coordinates times the actual neutral subgroup times upper-cross
coordinates. This is a concrete parabolic chart, independent of the
lexicographic initial-segment root coordinates.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree

def twoBlockGaussCell (a b : ℕ) : Set (TwoBlockSL a b) :=
  {g | IsUnit g.val.toBlocks₁₁}

abbrev TwoBlockGaussCoordinates (a b : ℕ) :=
  Matrix (Fin b) (Fin a) ℝ × twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ

def twoBlockGaussEquiv (a b : ℕ) :
    twoBlockGaussCell a b ≃ TwoBlockGaussCoordinates a b where
  toFun g := ⟨twoBlockLowerCoordinate g.val,
    ⟨twoBlockCore g.val, twoBlockCore_mem_neutral g.val g.property⟩,
    twoBlockUpperCoordinate g.val⟩
  invFun p := ⟨twoBlockLower p.1 * p.2.1.val * twoBlockUpper p.2.2,
    twoBlock_product_principal_isUnit p.1 p.2.1 p.2.2⟩
  left_inv g := Subtype.ext (twoBlockGauss_factorization g.val).symm
  right_inv p := by
    obtain ⟨L, C, U⟩ := p
    have hc := twoBlockGauss_coordinates_product L C U
    apply Prod.ext hc.1
    apply Prod.ext _ hc.2
    exact Subtype.ext (twoBlockCore_product L C U)

lemma isOpen_twoBlockGaussCell (a b : ℕ) : IsOpen (twoBlockGaussCell a b) := by
  have hc : Continuous (fun g : TwoBlockSL a b => g.val.toBlocks₁₁.det) := by
    change Continuous (fun g : TwoBlockSL a b =>
      Matrix.det (fun i j => g.val (Sum.inl i) (Sum.inl j)))
    fun_prop
  simpa only [twoBlockGaussCell, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using
    isOpen_ne_fun hc continuous_const

lemma one_mem_twoBlockGaussCell (a b : ℕ) : (1 : TwoBlockSL a b) ∈ twoBlockGaussCell a b := by
  change IsUnit ((1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ).toBlocks₁₁)
  simpa only [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁] using
    (isUnit_one : IsUnit (1 : Matrix (Fin a) (Fin a) ℝ))

lemma continuous_twoBlockUpper (a b : ℕ) :
    Continuous (twoBlockUpper : Matrix (Fin a) (Fin b) ℝ → TwoBlockSL a b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> fun_prop

lemma continuous_twoBlockLower (a b : ℕ) :
    Continuous (twoBlockLower : Matrix (Fin b) (Fin a) ℝ → TwoBlockSL a b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> fun_prop

lemma continuous_twoBlockPrincipalInverse (a b : ℕ) :
    Continuous (fun g : twoBlockGaussCell a b => g.val.val.toBlocks₁₁⁻¹) := by
  have hp : Continuous (fun g : twoBlockGaussCell a b => g.val.val.toBlocks₁₁) := by
    change Continuous (fun g : twoBlockGaussCell a b =>
      fun i j => g.val.val (Sum.inl i) (Sum.inl j))
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro g
  have hdet : IsUnit g.val.val.toBlocks₁₁.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.property
  have hr : ContinuousAt Ring.inverse g.val.val.toBlocks₁₁.det := by
    simpa only [hdet.unit_spec] using NormedRing.inverse_continuousAt hdet.unit
  exact (continuousAt_matrix_inv g.val.val.toBlocks₁₁ hr).comp (x := g) hp.continuousAt

lemma continuous_twoBlockGaussEquiv (a b : ℕ) : Continuous (twoBlockGaussEquiv a b) := by
  have h12 : Continuous (fun g : twoBlockGaussCell a b => g.val.val.toBlocks₁₂) := by
    change Continuous (fun g : twoBlockGaussCell a b =>
      fun i j => g.val.val (Sum.inl i) (Sum.inr j))
    fun_prop
  have h21 : Continuous (fun g : twoBlockGaussCell a b => g.val.val.toBlocks₂₁) := by
    change Continuous (fun g : twoBlockGaussCell a b =>
      fun i j => g.val.val (Sum.inr i) (Sum.inl j))
    fun_prop
  have hl : Continuous (fun g : twoBlockGaussCell a b => twoBlockLowerCoordinate g.val) :=
    h21.matrix_mul (continuous_twoBlockPrincipalInverse a b)
  have hu : Continuous (fun g : twoBlockGaussCell a b => twoBlockUpperCoordinate g.val) :=
    (continuous_twoBlockPrincipalInverse a b).matrix_mul h12
  have hc : Continuous (fun g : twoBlockGaussCell a b => twoBlockCore g.val) :=
    (((continuous_twoBlockLower a b).comp hl.neg).mul continuous_subtype_val).mul
      ((continuous_twoBlockUpper a b).comp hu.neg)
  exact hl.prodMk ((hc.subtype_mk _).prodMk hu)

lemma continuous_twoBlockGaussEquiv_symm (a b : ℕ) :
    Continuous (twoBlockGaussEquiv a b).symm := by
  apply Continuous.subtype_mk
  exact (((continuous_twoBlockLower a b).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd.fst)).mul
      ((continuous_twoBlockUpper a b).comp continuous_snd.snd)

def twoBlockGaussHomeomorph (a b : ℕ) :
    twoBlockGaussCell a b ≃ₜ TwoBlockGaussCoordinates a b where
  toEquiv := twoBlockGaussEquiv a b
  continuous_toFun := continuous_twoBlockGaussEquiv a b
  continuous_invFun := continuous_twoBlockGaussEquiv_symm a b

end DukePrimeDegree

end

end OAI
