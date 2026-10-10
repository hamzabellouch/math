import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.ProjectiveTail
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ)

abbrev cyclesSequence (i : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles (i+1)) (K.toCycles (i+1) i) (by
    rw [← cancel_mono (K.iCycles i), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

def cyclesSequenceKernel (i : ℕ) :
    IsLimit (KernelFork.ofι (cyclesSequence K i).f (cyclesSequence K i).zero) := by
  refine isLimitAux _ (fun s => K.liftCycles s.ι i (by simp) ?_) ?_ ?_
  · calc
      s.ι ≫ K.d (i+1) i = (s.ι ≫ K.toCycles (i+1) i) ≫ K.iCycles i := by simp only [Category.assoc, K.toCycles_i]
      _ = 0 := by rw [show s.ι ≫ K.toCycles (i+1) i = 0 from s.condition]; simp
  · intro s
    exact K.liftCycles_i _ _ _ _
  · intro s m hm
    apply (cancel_mono (K.iCycles (i+1))).mp
    exact hm.trans (K.liftCycles_i _ _ _ _).symm

theorem cyclesSequence_exact (i : ℕ) : (cyclesSequence K i).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (cyclesSequenceKernel K i)

theorem cyclesSequence_shortExact (i : ℕ) (h : K.ExactAt i) :
    (cyclesSequence K i).ShortExact := by
  have : Epi (K.toCycles (i+1) i) := by
    have hs : (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).Exact :=
      (K.exactAt_iff' (i+1) i _ (by simp) rfl).mp h
    have hf : K.toCycles (i+1) i ≫
        (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom =
        (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).toCycles := by
      exact K.toCycles_cyclesIsoSc'_hom _ _ _ _ _
    apply (epi_comp_iff_of_isIso (K.toCycles (i+1) i)
      (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom).mp
    rw [hf]
    exact hs.epi_toCycles
  have : Mono (cyclesSequence K i).f := inferInstanceAs (Mono (K.iCycles (i+1)))
  have : Epi (cyclesSequence K i).g := inferInstanceAs (Epi (K.toCycles (i+1) i))
  exact ⟨cyclesSequence_exact K i⟩

/-- In an exact tail of projective terms, projective dimension drops by one
at each successive cycle. This does not identify free terms with finite length. -/
theorem cycles_projective (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hd : HasProjectiveDimensionLE (K.cycles a) g) :
    Projective (K.cycles (a+g)) := by
  induction g generalizing a with
  | zero => simpa using (projective_iff_hasProjectiveDimensionLE_zero _).mpr hd
  | succ g ih =>
    have hs := cyclesSequence_shortExact K a (he a le_rfl)
    have : Projective (cyclesSequence K a).X₂ := hp (a+1)
    have hnext : HasProjectiveDimensionLE (K.cycles (a+1)) g :=
      (hs.hasProjectiveDimensionLT_X₃_iff g inferInstance).mp hd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1) (fun i hi => he i (by omega)) hnext
end DerivedBar.ProjectiveTail

end

end OAI
