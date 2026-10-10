import OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import OAI.NumberTheory.DirichletL.Hecke.Conjugation

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.HeckeDetectorFamilyInclusion
open HeckeFamily HeckeDetectorZeros Complex

theorem maximum_le_of_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ)
    (hinclude : ∀ i,∃ j, ∀ s : ℂ, LFunction (χ i) s=LFunction (ψ j) s) :
    zeroMaximum χ hχ T≤zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j,hj⟩ := hinclude i
    rw [←hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · rw [←hj s]
      exact hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

theorem maximum_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hχ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inl i,fun _ => rfl⟩

theorem maximum_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum ψ hψ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inr i,fun _ => rfl⟩

theorem inverse_nonprincipal (χ : Character) (hχ : χ.residue≠1) : χ.inverse.residue≠1 := by
  change χ.residue⁻¹≠1
  simpa only [ne_eq,inv_eq_one] using hχ

theorem maximum_inverse {ι : Type*} [Fintype ι] (χ : ι→Character)
    (hχ : ∀ i,(χ i).residue≠1) (T : ℝ) :
    zeroMaximum (fun i => (χ i).inverse) (fun i => inverse_nonprincipal (χ i) (hχ i)) T=
      zeroMaximum χ hχ T := by
  let ψ := fun i => (χ i).inverse
  have hψ := fun i => inverse_nonprincipal (χ i) (hχ i)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T hm
      rw [LFunction_inverse_conj (χ i) (hχ i),map_eq_zero] at hz
      have hh := zero_re_le_maximum χ hχ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
      have hz' : LFunction (ψ i) (conj s)=0 := by
        rw [LFunction_inverse_conj (χ i) (hχ i),conj_conj,hz,map_zero]
      have hh := zero_re_le_maximum ψ hψ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz'
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

end SevenEighths.HeckeDetectorFamilyInclusion

end

end OAI
