import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ShuffleFiltration
import OAI.Combinatorics.Chromatic.Walls.TensorAssociatedGrade

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

def UnitalSourceGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) :=
  Grade (unitalSourceFiltration a c η hc θ d W) (unitalSourceFiltration a c η hc θ d (W+1))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : AddCommGroup (UnitalSourceGrade a c η hc θ d W) :=
  inferInstanceAs (AddCommGroup (Grade _ _))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Module ℚ (UnitalSourceGrade a c η hc θ d W) :=
  inferInstanceAs (Module ℚ (Grade _ _))

def UnitalSourceTensorGrade (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  Grade (unitalSourceTensorFiltration a c η hc θ d e W)
    (unitalSourceTensorFiltration a c η hc θ d e (W+1))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : AddCommGroup (UnitalSourceTensorGrade a c η hc θ d e W) :=
  inferInstanceAs (AddCommGroup (Grade _ _))
noncomputable instance (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : Module ℚ (UnitalSourceTensorGrade a c η hc θ d e W) :=
  inferInstanceAs (Module ℚ (Grade _ _))

noncomputable def unitalGradeShuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V : ℤ) :
    UnitalSourceGrade a c η hc θ d U →ₗ[ℚ] UnitalSourceGrade a c η hc θ e V →ₗ[ℚ]
      UnitalSourceGrade a c η hc θ (d+e) (U+V) :=
  LinearFiltration.bilinear (unitalSourceFiltration a c η hc θ d U)
    (unitalSourceFiltration a c η hc θ d (U+1))
    (unitalSourceFiltration a c η hc θ e V) (unitalSourceFiltration a c η hc θ e (V+1))
    (unitalSourceFiltration a c η hc θ (d+e) (U+V))
    (unitalSourceFiltration a c η hc θ (d+e) (U+V+1))
    (shuffleBUnit a c η hc d e (hd.compatible he))
    (fun f hf g hg=>shuffleBUnit_filtered a c η hc θ hχ d e hd he U V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc,add_comm (1:ℤ) V] using
        shuffleBUnit_filtered a c η hc θ hχ d e hd he (U+1) V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc] using
        shuffleBUnit_filtered a c η hc θ hχ d e hd he U (V+1) f g hf hg)

lemma unitalGradeShuffle_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (U V : ℤ)
    (f : unitalSourceFiltration a c η hc θ d U) (g : unitalSourceFiltration a c η hc θ e V) :
    unitalGradeShuffle a c η hc θ hχ d e hd he U V
      (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)=
      (Submodule.Quotient.mk ⟨shuffleBUnit a c η hc d e (hd.compatible he) f.val g.val,
        shuffleBUnit_filtered a c η hc θ hχ d e hd he U V f.val g.val f.property g.property⟩ :
        UnitalSourceGrade a c η hc θ (d+e) (U+V)) := rfl

noncomputable def unitalSeparationConstant (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₗ[ℚ] B a (slope c η) d⊗[ℚ]B a (slope c η) e where
  toFun f := (unitalSeparationSeries a c η hc hs f).coeff 0
  map_add' f g := by rw [map_add,HahnSeries.coeff_add]
  map_smul' r f := by rw [map_smul,HahnSeries.coeff_smul]; rfl

noncomputable def unitalGradeCoproduct (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ) :
    UnitalSourceGrade a c η hc θ (d+e) W →ₗ[ℚ] UnitalSourceTensorGrade a c η hc θ d e W :=
  LinearFiltration.map (unitalSourceFiltration a c η hc θ (d+e) W)
    (unitalSourceFiltration a c η hc θ (d+e) (W+1))
    (unitalSourceTensorFiltration a c η hc θ d e W)
    (unitalSourceTensorFiltration a c η hc θ d e (W+1))
    (unitalSeparationConstant a c η hc d e hs)
    (fun f hf=>unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 f hf)
    (fun f hf=>unitalSeparationSeries_coeff_filtration a c η hc θ d e hs (W+1) 0 f hf)

lemma unitalGradeCoproduct_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ)
    (f : unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalGradeCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨(unitalSeparationSeries a c η hc hs f.val).coeff 0,
        unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 f.val f.property⟩ :
        UnitalSourceTensorGrade a c η hc θ d e W) := rfl

noncomputable def unitalSourceTensorGradeEquiv (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    (⨁ u : ℤ,UnitalSourceGrade a c η hc θ d u ⊗[ℚ]
      UnitalSourceGrade a c η hc θ e (W-u)) ≃ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ d e W :=
  tensorGradeEquiv (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e)
    (unitalSourceFiltration_antitone a c η hc θ d) (unitalSourceFiltration_antitone a c η hc θ e) W

end ElementaryPositivity.RawShuffle

end

end OAI
