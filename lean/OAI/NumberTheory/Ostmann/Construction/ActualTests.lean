import OAI.NumberTheory.Ostmann.Construction.GiantPhase
import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def residueTest (d : Decomposition) (p : ℕ) : ZMod p → ℂ :=
  if hp : p=0 then fun _ => 0 else letI : NeZero p := ⟨hp⟩
    fun x => (Supply.normalizedIndicator (d.residueSupport p) x:ℂ)

def residueTransform (d : Decomposition) (p : ℕ) : ZMod p → ℂ :=
  if hp : p=0 then fun _ => 0 else letI : NeZero p := ⟨hp⟩
    Supply.additiveTransform (d.residueSupport p)

def giantResidueTest (d : Decomposition) (p : ℕ) : ZMod p → ℂ :=
  if hp : p=0 then fun _ => 0 else letI : NeZero p := ⟨hp⟩
    giantTest (d.residueSupport p)

def giantResidueTransform (d : Decomposition) (p : ℕ) (v : ZMod p) : ℂ :=
  phase (residueTransform d p v)

@[simp] theorem residueTest_eq (d : Decomposition) (p : ℕ) [NeZero p] (x : ZMod p) :
    residueTest d p x=(Supply.normalizedIndicator (d.residueSupport p) x:ℂ) := by
  simp only [residueTest,NeZero.ne p,dite_false]

@[simp] theorem residueTransform_eq (d : Decomposition) (p : ℕ) [NeZero p] (v : ZMod p) :
    residueTransform d p v=Supply.additiveTransform (d.residueSupport p) v := by
  simp only [residueTransform,NeZero.ne p,dite_false]

@[simp] theorem giantResidueTest_eq (d : Decomposition) (p : ℕ) [NeZero p] (x : ZMod p) :
    giantResidueTest d p x=giantTest (d.residueSupport p) x := by
  simp only [giantResidueTest,NeZero.ne p,dite_false]

theorem residueTest_fourier (d : Decomposition) (p : ℕ) [NeZero p] (v : ZMod p) :
    Supply.unitaryDFT (residueTest d p) v=residueTransform d p v := by
  simp only [residueTest,residueTransform,NeZero.ne p,dite_false]
  rfl

theorem giantResidueTest_fourier (d : Decomposition) (p : ℕ) [NeZero p] (v : ZMod p) :
    Supply.unitaryDFT (giantResidueTest d p) v=giantResidueTransform d p v := by
  simp only [giantResidueTest,giantResidueTransform,residueTransform,NeZero.ne p,dite_false]
  exact giantTest_fourier _ _

theorem residueTest_sum_zero (d : Decomposition) (p : ℕ) [NeZero p] :
    ∑ x,residueTest d p x=0 := by
  simp only [residueTest_eq,← Complex.ofReal_sum,Supply.sum_normalizedIndicator,Complex.ofReal_zero]

theorem giantResidueTransform_norm_le (d : Decomposition) (p : ℕ) (v : ZMod p) :
    ‖giantResidueTransform d p v‖≤1 := phase_norm_le _

theorem residueTransform_neg (d : Decomposition) (p : ℕ) (v : ZMod p) :
    residueTransform d p (-v)=conj (residueTransform d p v) := by
  by_cases hp : p=0
  · simp only [residueTransform,hp,dite_true, map_zero]
  · let : NeZero p := ⟨hp⟩
    simp only [residueTransform_eq,Supply.additiveTransform_neg]

theorem giantResidueTransform_neg (d : Decomposition) (p : ℕ) (v : ZMod p) :
    giantResidueTransform d p (-v)=conj (giantResidueTransform d p v) := by
  simp only [giantResidueTransform,residueTransform_neg,phase_conj]

end Ostmann.Construction

end

end OAI
