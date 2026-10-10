import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyKernel

namespace OAI

/-! # Naturality of top homology as a kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] ModuleCat.isModule

theorem topHomologyKernelEquiv_π (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : C.d (n + 1) n = 0) (z : C.cycles n) :
    (topHomologyKernelEquiv C n h (C.homologyπ n z)).val = C.iCycles n z := by
  change ((C.homologyπ n ≫
      (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).inv ≫
      (C.cyclesIsoSc' (n + 1) n (n - 1) (ChainComplex.prev ℕ n)
        (by cases n <;> simp)).hom ≫
      (C.sc' (n + 1) n (n - 1)).moduleCatCyclesIso.hom ≫
      (C.sc' (n + 1) n (n - 1)).moduleCatLeftHomologyData.i) z) = C.iCycles n z
  simp only [ShortComplex.moduleCatCyclesIso_hom_i, cyclesIsoSc'_hom_iCycles]
  change (C.homologyπ n ≫
    (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).inv ≫ C.iCycles n) z =
      C.iCycles n z
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f : C.cycles n ⟶ C.cycles n => (f ≫ C.iCycles n) z)
      (C.isoHomologyπ_hom_inv_id (n + 1) n (ChainComplex.prev ℕ n) h)

theorem topHomologyKernelEquiv_naturality
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (hC : C.d (n + 1) n = 0) (hD : D.d (n + 1) n = 0) (x : C.homology n) :
    (topHomologyKernelEquiv D n hD (HomologicalComplex.homologyMap f n x)).val =
      f.f n (topHomologyKernelEquiv C n hC x).val := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  have he := congrArg (fun k => k z) (HomologicalComplex.homologyπ_naturality f n)
  change HomologicalComplex.homologyMap f n (C.homologyπ n z) =
    D.homologyπ n (HomologicalComplex.cyclesMap f n z) at he
  rw [he, topHomologyKernelEquiv_π, topHomologyKernelEquiv_π]
  exact congrArg (fun k => k z) (HomologicalComplex.cyclesMap_i f n)

end PolycyclicRecognition

end

end OAI
