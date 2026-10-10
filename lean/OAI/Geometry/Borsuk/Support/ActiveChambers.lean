import Mathlib
import OAI.Geometry.Borsuk.Projectors.Restrict
import OAI.Geometry.Borsuk.Support.Chambers

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ActiveChambers
variable {E W ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

def activeVectors (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∃ i ∈ I, 0 < homogeneousLift f z i}

def commonPositiveCone (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∀ i ∈ I, 0 < homogeneousLift f z i}

lemma Admissible.commonPositiveCone_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : IsOpen (commonPositiveCone f I) := by
  have he : commonPositiveCone f I =
      ⋂ i ∈ (I : Set ι), {x | 0 < homogeneousLift f x i} := by ext x; simp [commonPositiveCone]
  rw [he]
  exact isOpen_biInter_finset (fun i _ => isOpen_lt continuous_const
    ((continuous_apply i).comp hf.lift_continuous))

lemma Admissible.commonPositiveCone_safe {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : commonPositiveCone f I ⊆ safeNormals (activeVectors f I) := by
  intro x hx z hz horth
  obtain ⟨i,hi,hzi⟩ := hz
  have hxz := mul_pos (hx i hi) hzi
  rw [hf.lift_orthogonal horth i] at hxz
  exact (lt_irrefl 0) hxz

lemma Admissible.commonPositiveCone_interior_safe {f : E → ι → ℝ}
    (hf : Admissible f) (I : Finset ι) :
    commonPositiveCone f I ⊆ interior (safeNormals (activeVectors f I)) :=
  interior_maximal (hf.commonPositiveCone_safe I) (hf.commonPositiveCone_isOpen I)

omit [Fintype ι] in
lemma commonPositiveCone_active {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c : E} (hc : c ∈ commonPositiveCone f I) : c ∈ activeVectors f I := by
  obtain ⟨i,hi⟩ := hI
  exact ⟨i,hi,hc i hi⟩

omit [Fintype ι] in
lemma commonPositiveCone_ne_zero {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c : E} (hc : c ∈ commonPositiveCone f I) : c ≠ 0 := by
  intro he
  obtain ⟨i,hi⟩ := hI
  have hh := hc i hi
  simp [he] at hh

omit [Fintype ι] in
lemma activeChamber_inner_pos {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c x : E} (hc : c ∈ commonPositiveCone f I)
    (hx : x ∈ signChamber (activeVectors f I) c) : 0 < ⟪c,x⟫ := by
  have hh := hx c (commonPositiveCone_active hI hc)
  rw [real_inner_comm c x] at hh
  exact (mul_pos_iff_of_pos_left (real_inner_self_pos.mpr
    (commonPositiveCone_ne_zero hI hc))).mp hh

lemma Admissible.safe_restriction_zero {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {x : E} (hx : x ∈ safeNormals (activeVectors f I))
    (e : W →ₗᵢ[ℝ] E) (he : ∀ u, ⟪x,e u⟫ = 0)
    {u : W} (hu : ‖u‖ = 1) {i : ι} (hi : i ∈ I) : f (e u) i = 0 := by
  have hunit : ‖e u‖ = 1 := by simpa using hu
  apply le_antisymm _ (hf.nonneg _ hunit i)
  apply le_of_not_gt
  intro hp
  have hz : e u ∈ activeVectors f I := ⟨i,hi,by simpa [homogeneousLift_unit _ hunit] using hp⟩
  exact hx (e u) hz (he u)

lemma Admissible.safe_restriction [DecidableEq ι] {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {x : E} (hx : x ∈ safeNormals (activeVectors f I))
    (e : W →ₗᵢ[ℝ] E) (he : ∀ u, ⟪x,e u⟫ = 0) :
    Admissible (fun u (i : ↥(Iᶜ : Finset ι)) => f (e u) i.val) := by
  classical
  apply (hf.comp_isometry e).restrict_labels Iᶜ
  intro u hu i hi
  exact hf.safe_restriction_zero hx e he hu (by simpa using hi)

end ActiveChambers
end BorsukNine

end OAI
