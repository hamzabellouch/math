import OAI.Analysis.Triangular.Energy.LatticePoisson

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma inputComplex_spectral_atoms (a : InputCoefficients) (x : Plane) :
    inputComplex a x=tailSpectral a (atomFunction h x)+finiteSpectral a (atomFunction H x) := by
  simp only [inputComplex_spectral,atomFunction,map_smul,smul_eq_mul]
lemma outputComplex_spectral_atoms (a : InputCoefficients) (x : Plane) :
    outputComplex a x=tailSpectral a (dualAtomFunction 0 x)+finiteSpectral a (dualAtomFunction 1 x) := by
  simp only [dualAtomFunction,map_smul,smul_eq_mul,outputComplex,transformedInput,mul_add]
  rfl
lemma inputComplex_lattice_summable (a : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => inputComplex a (AtomicTriangular.triangularPoint v)) := by
  simp_rw [inputComplex_spectral_atoms]
  exact ((tailSpectral a).summable (atom_lattice_summable h_pos)).add
    ((finiteSpectral a).summable (atom_lattice_summable H_pos))
lemma outputComplex_lattice_summable (a : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => outputComplex a (AtomicTriangular.triangularPoint v)) := by
  simp_rw [outputComplex_spectral_atoms]
  exact ((tailSpectral a).summable (dualAtom_lattice_summable 0)).add
    ((finiteSpectral a).summable (dualAtom_lattice_summable 1))
lemma input_output_lattice_poisson (a : InputCoefficients) :
    (∑' v : ℤ × ℤ, inputComplex a (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, outputComplex a (AtomicTriangular.triangularPoint v) := by
  simp_rw [inputComplex_spectral_atoms,outputComplex_spectral_atoms]
  rw [((tailSpectral a).summable (atom_lattice_summable h_pos)).tsum_add
    ((finiteSpectral a).summable (atom_lattice_summable H_pos)),
    ((tailSpectral a).summable (dualAtom_lattice_summable 0)).tsum_add
    ((finiteSpectral a).summable (dualAtom_lattice_summable 1)),
    ←(tailSpectral a).map_tsum (atom_lattice_summable h_pos),
    ←(finiteSpectral a).map_tsum (atom_lattice_summable H_pos),
    ←(tailSpectral a).map_tsum (dualAtom_lattice_summable 0),
    ←(finiteSpectral a).map_tsum (dualAtom_lattice_summable 1)]
  change tailSpectral a (∑' v : ℤ × ℤ, atomFunction (damping 0) (AtomicTriangular.triangularPoint v))+
    finiteSpectral a (∑' v : ℤ × ℤ, atomFunction (damping 1) (AtomicTriangular.triangularPoint v))=_
  rw [atom_lattice_poisson,atom_lattice_poisson]
lemma pairComplex_lattice_summable (a₁ a₂ : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v)) :=
  (inputComplex_lattice_summable a₁).add (outputComplex_lattice_summable a₂)
lemma pairComplex_lattice_poisson (a₁ a₂ : InputCoefficients) :
    (∑' v : ℤ × ℤ, pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, pairComplex a₂ a₁ (AtomicTriangular.triangularPoint v) := by
  simp only [pairComplex,Pi.add_apply]
  rw [(inputComplex_lattice_summable a₁).tsum_add (outputComplex_lattice_summable a₂),
    (inputComplex_lattice_summable a₂).tsum_add (outputComplex_lattice_summable a₁),
    input_output_lattice_poisson,input_output_lattice_poisson,add_comm]
lemma pairSchwartz_lattice_summable (a₁ a₂ : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => pairSchwartz a₁ a₂ (AtomicTriangular.triangularPoint v)) := by
  simpa only [pairSchwartz_apply,Complex.reCLM_apply] using Complex.reCLM.summable (pairComplex_lattice_summable a₁ a₂)
lemma pairSchwartz_lattice_poisson (a₁ a₂ : InputCoefficients) :
    (∑' v : ℤ × ℤ, pairSchwartz a₁ a₂ (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, pairSchwartz a₂ a₁ (AtomicTriangular.triangularPoint v) := by
  simp only [pairSchwartz_apply]
  change (∑' v : ℤ × ℤ, Complex.reCLM (pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v)))=
    ∑' v : ℤ × ℤ, Complex.reCLM (pairComplex a₂ a₁ (AtomicTriangular.triangularPoint v))
  rw [←Complex.reCLM.map_tsum (pairComplex_lattice_summable a₁ a₂),
    ←Complex.reCLM.map_tsum (pairComplex_lattice_summable a₂ a₁),pairComplex_lattice_poisson]
end AtomicTriangular.Construction
end

end OAI
