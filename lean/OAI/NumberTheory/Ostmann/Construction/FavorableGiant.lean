import OAI.NumberTheory.Ostmann.Construction.ActualTests
import OAI.NumberTheory.Ostmann.Construction.GiantEmpirical

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def favorableGiantResidueTest (d : Decomposition) (P : Finset ℕ) (p : ℕ) (x : ZMod p) : ℂ :=
  if p∈P then giantResidueTest d p x else 0

def favorableGiantResidueTransform (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) (v : ZMod p) : ℂ :=
  if p∈P then giantResidueTransform d p v else 0

theorem favorableGiantResidueTest_fourier (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) [NeZero p] (v : ZMod p) :
    Supply.unitaryDFT (favorableGiantResidueTest d P p) v=
      favorableGiantResidueTransform d P p v := by
  by_cases hp : p∈P
  · have he : favorableGiantResidueTest d P p=giantResidueTest d p := by
      funext x; simp [favorableGiantResidueTest,hp]
    rw [he]
    simpa only [favorableGiantResidueTransform,hp,ite_true] using giantResidueTest_fourier d p v
  · have he : favorableGiantResidueTest d P p=0 := by
      funext x; simp [favorableGiantResidueTest,hp]
    rw [he]
    simp [favorableGiantResidueTransform,hp,Supply.unitaryDFT]

theorem favorableGiantResidueTransform_norm_le (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) (v : ZMod p) : ‖favorableGiantResidueTransform d P p v‖≤1 := by
  by_cases hp : p∈P
  · simpa only [favorableGiantResidueTransform,hp,ite_true] using giantResidueTransform_norm_le d p v
  · simp [favorableGiantResidueTransform,hp]

theorem favorableGiantResidueTransform_neg (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) (v : ZMod p) :
    favorableGiantResidueTransform d P p (-v)=conj (favorableGiantResidueTransform d P p v) := by
  by_cases hp : p∈P
  · simpa only [favorableGiantResidueTransform,hp,ite_true] using giantResidueTransform_neg d p v
  · simp [favorableGiantResidueTransform,hp]

theorem favorableGiantResidueTest_nat (d : Decomposition) (P : Finset ℕ)
    (p n : ℕ) [NeZero p] :
    favorableGiantResidueTest d P p (n:ZMod p)=
      ((if p∈P then giantNatTest d p n else 0 : ℝ):ℂ) := by
  by_cases hp : p∈P
  · simp only [favorableGiantResidueTest,hp,ite_true,giantResidueTest_eq,giantNatTest_eq]
    apply Complex.ext <;> simp [giantTestReal,giantTest_real]
  · simp [favorableGiantResidueTest,hp]

theorem favorableGiantResidueTest_nat_re (d : Decomposition) (P : Finset ℕ)
    (p n : ℕ) [NeZero p] :
    (favorableGiantResidueTest d P p (n:ZMod p)).re=
      if p∈P then giantNatTest d p n else 0 := by
  rw [favorableGiantResidueTest_nat,Complex.ofReal_re]

end Ostmann.Construction

end

end OAI
