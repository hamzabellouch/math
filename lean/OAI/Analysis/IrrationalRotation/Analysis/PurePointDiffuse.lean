import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Operators.JointEigenprojection

namespace OAI

noncomputable section
namespace Invariant233

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem jointEigenspace_const_unit (D : H →L[ℂ] H) (z : ℂ) :
    jointEigenspace (fun _ : Unit => D) (fun _ => z) =
      Module.End.eigenspace D.toLinearMap z := by
  ext x
  simp only [mem_jointEigenspace, Module.End.mem_eigenspace_iff,
    ContinuousLinearMap.coe_coe, forall_const]

theorem projectionAtom_range_le_eigenspace
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    {p D : H →L[ℂ] H} (hp : IsProjectionAtom M p) (hD : D ∈ M)
    (hpure : HasCountablyAtomicSpectralType D) :
    ∃ z : ℂ, p.range ≤ Module.End.eigenspace D.toLinearMap z := by
  obtain ⟨S, _hS, hdense⟩ := hpure
  have hdense' :
      (⨆ z : S, jointEigenspace (fun _ : Unit => D) (fun _ => (z : ℂ))).topologicalClosure = ⊤ := by
    simpa only [jointEigenspace_const_unit] using hdense
  obtain ⟨z, hz⟩ := exists_mul_jointEigenprojection_ne_zero
    (fun _ : Unit => D) (fun z : S => fun _ => (z : ℂ)) hdense' p hp.2.2.1
  let q := jointEigenprojection (fun _ : Unit => D) (fun _ => (z : ℂ))
  have hqm : q ∈ M := by
    apply vonNeumannGenerated_le (Set.range (fun _ : Unit => D)) M ?_
      (jointEigenprojection_mem_generated (fun _ : Unit => D) (fun _ => (z : ℂ)))
    rintro A ⟨u, rfl⟩
    exact hD
  have hqproj : IsStarProjection q := isStarProjection_jointEigenprojection _ _
  have hpq : Commute p q := hab p q hp.1 hqm
  have hsub : (p * q) * p = p * q := by
    rw [mul_assoc, ← hpq.eq, ← mul_assoc, hp.2.1.isIdempotentElem.eq]
  have heq : p * q = p :=
    (hp.2.2.2 (p * q) (mul_mem hp.1 hqm) (hp.2.1.mul hqproj hpq) hsub).resolve_left hz
  refine ⟨z, ?_⟩
  rintro x ⟨y, rfl⟩
  have hfix : q (p y) = p y := by
    have h := DFunLike.congr_fun (hpq.eq.symm.trans heq) y
    exact h
  have hx : p y ∈ jointEigenspace (fun _ : Unit => D) (fun _ => (z : ℂ)) :=
    Submodule.starProjection_eq_self_iff.mp hfix
  rwa [jointEigenspace_const_unit] at hx

theorem projectionAtom_range_le_jointEigenspace
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    (D : ι → H →L[ℂ] H) (hD : ∀ i, D i ∈ M)
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    {p : H →L[ℂ] H} (hp : IsProjectionAtom M p) :
    ∃ ev : ι → ℂ, p.range ≤ jointEigenspace D ev := by
  choose ev hev using fun i => projectionAtom_range_le_eigenspace hab hp (hD i) (hpure i)
  refine ⟨ev, ?_⟩
  intro x hx
  rw [mem_jointEigenspace]
  intro i
  exact Module.End.mem_eigenspace_iff.mp (hev i hx)

theorem isDiffuse_of_purePoint_no_jointEigenvectors
    {M : VonNeumannAlgebra H} (hab : IsAbelianVonNeumannAlgebra M)
    (D : ι → H →L[ℂ] H) (hD : ∀ i, D i ∈ M)
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    (hjoint : ∀ ev : ι → ℂ, jointEigenspace D ev = ⊥) :
    IsDiffuseVonNeumannAlgebra M := by
  intro p hp
  obtain ⟨ev, hev⟩ := projectionAtom_range_le_jointEigenspace hab D hD hpure hp
  rw [hjoint ev] at hev
  apply hp.2.2.1
  ext x
  exact hev ⟨x, rfl⟩

theorem generated_isDiffuse_of_purePoint_no_jointEigenvectors
    (D : ι → H →L[ℂ] H)
    (hab : IsAbelianVonNeumannAlgebra (vonNeumannGenerated (Set.range D)))
    (hpure : ∀ i, HasCountablyAtomicSpectralType (D i))
    (hjoint : ∀ ev : ι → ℂ, jointEigenspace D ev = ⊥) :
    IsDiffuseVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  exact isDiffuse_of_purePoint_no_jointEigenvectors hab D
    (fun i => subset_vonNeumannGenerated _ ⟨i, rfl⟩) hpure hjoint

end Invariant233

end

end OAI
