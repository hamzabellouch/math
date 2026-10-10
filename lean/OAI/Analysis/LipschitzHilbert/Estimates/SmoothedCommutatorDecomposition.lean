import OAI.Analysis.LipschitzHilbert.Fourier.LineDyadicTelescoping
import OAI.Analysis.LipschitzHilbert.Geometry.DyadicNearbyInputs
import OAI.Analysis.LipschitzHilbert.Fourier.LineLowHighSum
import OAI.Analysis.LipschitzHilbert.Fourier.LineHighLowSum

namespace OAI

/-! Exact decomposition of a smoothed coefficient against finitely many
input bands into the three already bounded commutator interactions. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineSchwartzCommutator_zero_right (m b : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b 0=0 := by
  have hh := lineSchwartzCommutator_sum_right (∅ : Finset Unit) m b (fun _ => 0)
  simpa only [Finset.sum_empty] using hh

theorem schwartzDerivative_sum {ι : Type*} (I : Finset ι) (f : ι → SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (∑ i∈I, f i)=∑ i∈I, schwartzDerivative 1 (f i) :=
  map_sum (SchwartzMap.derivCLM ℂ ℂ) f I

theorem schwartzDerivative_zero : schwartzDerivative 1 (0 : SchwartzMap ℝ ℂ)=0 :=
  map_zero (SchwartzMap.derivCLM ℂ ℂ)

theorem scale_add_four (j : ℤ) : scale (j+4)=16*scale j := by
  simp only [scale,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  norm_num
  ring

theorem lineCommutator_nearbyInput (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) :
    lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (nearbyInput J h i))=
      ∑ j∈J, if i-4≤j ∧ j≤ i+4 then
        lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (lineDyadic h j)) else 0 := by
  classical
  rw [nearbyInput,schwartzDerivative_sum,lineSchwartzCommutator_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i-4≤j ∧ j≤ i+4
  · simp only [nearbyInputPiece,ite_eq_left hij,lineDyadic]
  · simp only [nearbyInputPiece,ite_eq_right hij,schwartzDerivative_zero,lineSchwartzCommutator_zero_right]

theorem split_dyadic_interaction {E : Type*} [AddCommMonoid E] (i j : ℤ) (x : E) :
    (if i≤j+4 then x else 0)=
      (if i+5≤j then x else 0)+(if i-4≤j ∧ j≤ i+4 then x else 0) := by
  by_cases hlow : i+5≤j
  · have h1 : i≤j+4 := by omega
    have h2 : ¬(i-4≤j ∧ j≤ i+4) := by omega
    simp only [ite_eq_left h1,ite_eq_left hlow,ite_eq_right h2,add_zero]
  · by_cases hnear : i-4≤j ∧ j≤ i+4
    · have h1 : i≤j+4 := by omega
      simp only [ite_eq_left h1,ite_eq_right hlow,ite_eq_left hnear,zero_add]
    · have h1 : ¬i≤j+4 := by omega
      simp only [ite_eq_right h1,ite_eq_right hlow,ite_eq_right hnear,add_zero]

theorem smoothedCommutator_decomposition (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (l v : ℤ) (hl : ∀ j∈J, l≤j+4) (hv : ∀ j∈J, j+4≤v) :
    lineSchwartzCommutator m (lineLowpass b l) (schwartzDerivative 1 (∑ j∈J, lineDyadic h j))=
      (∑ j∈J, lowHighPiece m b h j)+
      (∑ i∈Finset.Icc (l+1) v, highLowRow J m b h i)+
      (∑ i∈Finset.Icc (l+1) v, lineSchwartzCommutator m (lineDyadic b i)
        (schwartzDerivative 1 (nearbyInput J h i))) := by
  classical
  let I := Finset.Icc (l+1) v
  let F := fun i j => lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (lineDyadic h j))
  have hj (j : ℤ) (hj : j∈J) :
      lineSchwartzCommutator m (lineLowpass b l) (schwartzDerivative 1 (lineDyadic h j))=
        lowHighPiece m b h j+∑ i∈I, if i≤j+4 then F i j else 0 := by
    rw [lineLowpass_telescope_filtered b l (j+4) v (hl j hj) (hv j hj),
      lineSchwartzCommutator_add_left,lineSchwartzCommutator_sum_left]
    have he : lineSchwartzCommutator m (lineLowpass b (j+4))
        (schwartzDerivative 1 (lineDyadic h j))=lowHighPiece m b h j := by
      simp only [lineLowpass,lineDyadic,lowHighPiece,scale_add_four]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i≤j+4
    · simp only [ite_eq_left hij]
      rfl
    · simp only [ite_eq_right hij,lineSchwartzCommutator_zero_left]
  rw [schwartzDerivative_sum,lineSchwartzCommutator_sum_right]
  calc
    _ = ∑ j∈J, (lowHighPiece m b h j+∑ i∈I, if i≤j+4 then F i j else 0) :=
      Finset.sum_congr rfl hj
    _ = (∑ j∈J, lowHighPiece m b h j)+(∑ i∈I, ∑ j∈J, if i≤j+4 then F i j else 0) := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
    _ = (∑ j∈J, lowHighPiece m b h j)+(∑ i∈I, (highLowRow J m b h i+
        lineSchwartzCommutator m (lineDyadic b i) (schwartzDerivative 1 (nearbyInput J h i)))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [split_dyadic_interaction]
      rw [Finset.sum_add_distrib,lineCommutator_nearbyInput]
      rfl
    _ = _ := by rw [Finset.sum_add_distrib]; exact (add_assoc _ _ _).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
