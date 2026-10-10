import OAI.Analysis.IrrationalRotation.Model.JointEigenspace
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann

namespace OAI

noncomputable section
namespace Invariant233

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]
theorem mem_jointEigenspace {D : ι → H →L[ℂ] H} {ev : ι → ℂ} {x : H} :
    x ∈ jointEigenspace D ev ↔ ∀ i, D i x = ev i • x := by
  simp [jointEigenspace]

omit [CompleteSpace H] in

theorem map_mem_jointEigenspace {D : ι → H →L[ℂ] H} {ev : ι → ℂ}
    {T : H →L[ℂ] H} (hT : ∀ i, Commute (D i) T)
    {x : H} (hx : x ∈ jointEigenspace D ev) : T x ∈ jointEigenspace D ev := by
  rw [mem_jointEigenspace] at hx ⊢
  intro i
  calc
    D i (T x) = T (D i x) := DFunLike.congr_fun (hT i).eq x
    _ = ev i • T x := by rw [hx i, map_smul]

theorem commute_starProjection_of_reducing (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (hTstar : ∀ x ∈ K, star T x ∈ K) :
    Commute K.starProjection T := by
  apply ContinuousLinearMap.ext
  intro x
  change K.starProjection (T x) = T (K.starProjection x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · apply hT
    exact Submodule.coe_mem (K.orthogonalProjectionOnto x)
  · have horth : Kᗮ ∈ Module.End.invtSubmodule T.toLinearMap :=
      ContinuousLinearMap.orthogonal_mem_invtSubmodule hTstar
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at horth
    rw [← map_sub]
    exact horth _ (K.sub_starProjection_mem_orthogonal x)

@[simp]
theorem isStarProjection_jointEigenprojection (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    IsStarProjection (jointEigenprojection D ev) :=
  isStarProjection_starProjection

theorem jointEigenprojection_mem_generated (D : ι → H →L[ℂ] H) (ev : ι → ℂ) :
    jointEigenprojection D ev ∈ vonNeumannGenerated (Set.range D) := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff
    (isStarProjection_jointEigenprojection D ev)]
  intro T hT
  change (jointEigenspace D ev).starProjection.range ∈ Module.End.invtSubmodule T
  rw [Submodule.range_starProjection]
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  apply map_mem_jointEigenspace
  intro i
  exact ((mem_commutant_vonNeumannGenerated_iff _ T).mp hT (D i) ⟨i, rfl⟩).1

theorem jointEigenprojection_mem_commutant (D : ι → H →L[ℂ] H) (ev : ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i)) :
    jointEigenprojection D ev ∈ (vonNeumannGenerated (Set.range D)).commutant := by
  rw [mem_commutant_vonNeumannGenerated_iff]
  rintro _ ⟨i, rfl⟩
  have h : Commute (jointEigenprojection D ev) (D i) := by
    apply commute_starProjection_of_reducing
    · intro x hx
      rw [(mem_jointEigenspace.mp hx) i]
      exact (jointEigenspace D ev).smul_mem _ hx
    · intro x hx
      rw [(hD i).star_eq, (mem_jointEigenspace.mp hx) i]
      exact (jointEigenspace D ev).smul_mem _ hx
  exact ⟨h.eq.symm, by simpa only [(hD i).star_eq] using h.eq.symm⟩

theorem exists_mul_jointEigenprojection_ne_zero {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤)
    (p : H →L[ℂ] H) (hp : p ≠ 0) :
    ∃ a, p * jointEigenprojection D (ev a) ≠ 0 := by
  by_contra! h
  apply hp
  have hker : (⨆ a, jointEigenspace D (ev a)) ≤ p.ker := by
    apply iSup_le
    intro a x hx
    change p x = 0
    have hxq : jointEigenprojection D (ev a) x = x :=
      Submodule.starProjection_eq_self_iff.mpr hx
    have heq := DFunLike.congr_fun (h a) x
    simpa only [mul_apply_eq_comp, hxq, zero_apply] using heq
  have htop : (⊤ : Submodule ℂ H) ≤ p.ker := by
    rw [← hdense]
    exact Submodule.topologicalClosure_minimal _ hker p.isClosed_ker
  ext x
  exact htop (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

theorem atomic_generated_of_jointEigenprojection_atoms {A : Type*}
    (D : ι → H →L[ℂ] H) (ev : A → ι → ℂ)
    (hD : ∀ i, IsSelfAdjoint (D i))
    (hdense : (⨆ a, jointEigenspace D (ev a)).topologicalClosure = ⊤)
    (hatom : ∀ a, jointEigenprojection D (ev a) ≠ 0 →
      IsProjectionAtom (vonNeumannGenerated (Set.range D)) (jointEigenprojection D (ev a))) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) := by
  intro p hp hpp hp0
  obtain ⟨a, ha⟩ := exists_mul_jointEigenprojection_ne_zero D ev hdense p hp0
  let q := jointEigenprojection D (ev a)
  have hqm : q ∈ vonNeumannGenerated (Set.range D) := jointEigenprojection_mem_generated D _
  have hqp : IsStarProjection q := isStarProjection_jointEigenprojection D _
  have hq0 : q ≠ 0 := by
    intro hq
    apply ha
    change p * q = 0
    rw [hq, mul_zero]
  have hpq : Commute p q :=
    VonNeumannAlgebra.mem_commutant_iff.mp (jointEigenprojection_mem_commutant D _ hD) p hp
  have hqa := hatom a hq0
  have hpqq : (p * q) * q = p * q := by
    rw [mul_assoc, hqp.isIdempotentElem.eq]
  have hpeq : p * q = q :=
    (hqa.2.2.2 (p * q) (mul_mem hp hqm) (hpp.mul hqp hpq) hpqq).resolve_left ha
  exact ⟨q, hqa, hpq.eq.symm.trans hpeq⟩

end Invariant233

end

end OAI
