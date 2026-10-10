import Mathlib
import OAI.Geometry.Borsuk.Simplicial.UnitRadial

namespace OAI

namespace BorsukNine.SimplicialChains

lemma odd_sphere_dimension_bound_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : EuclideanSpace ℝ α → EuclideanSpace ℝ β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : Fintype.card α ≤ Fintype.card β := by
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin β)
  apply odd_sphere_dimension_bound (Fintype.card α) (Fintype.card β)
    Fintype.card_pos (fun x => B (f (A.symm x)))
  · exact B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx))
  · intro x hx
    rw [B.norm_map, hfn _ (by simpa using hx)]
  · intro x hx
    rw [map_neg, hfo _ (by simpa using hx), map_neg]

lemma odd_sphere_surjective_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (hc : Fintype.card α = Fintype.card β)
    (f : EuclideanSpace ℝ α → EuclideanSpace ℝ β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := α)))
  let ea : α ≃ Fin (n+1) := (Fintype.equivFin α).trans (finCongr hn)
  let eb : β ≃ Fin (n+1) := (Fintype.equivFin β).trans (finCongr (hc.symm.trans hn))
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eb
  have hg := odd_sphere_surjective n (fun x => B (f (A.symm x)))
    (B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx)))
    (fun x hx => by rw [B.norm_map, hfn _ (by simpa using hx)])
    (fun x hx => by rw [map_neg, hfo _ (by simpa using hx), map_neg])
  intro y hy
  obtain ⟨x,hx,he⟩ := hg (B y) (by simpa using hy)
  exact ⟨A.symm x, by simpa using hx, B.injective he⟩

end BorsukNine.SimplicialChains

namespace BorsukNine
open scoped RealInnerProductSpace

section LabelBound
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]

lemma Admissible.label_bound {f : EuclideanSpace ℝ ν → ι → ℝ} (hf : Admissible f) :
    Fintype.card (UpperTriangle ν) ≤ Fintype.card ι := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_dimension_bound_fintype (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)

lemma Admissible.sphereExtension_surjective {f : EuclideanSpace ℝ ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ sphereExtension f x = y := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_surjective_fintype hc (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)

lemma Admissible.signedExtension_ray {f : EuclideanSpace ℝ ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι)
    {y : ι → ℝ} (hy : y ≠ 0) :
    ∃ A : Matrix ν ν ℝ, IsSelfAdjoint A ∧ ∃ t : ℝ, 0 < t ∧ signedExtension f A = t • y := by
  let Y : EuclideanSpace ℝ ι := WithLp.toLp 2 y
  have hY : Y ≠ 0 := fun hh => hy (WithLp.toLp_injective 2 hh)
  obtain ⟨x,hx,he⟩ := hf.sphereExtension_surjective hc (SimplicialChains.unitRadial Y)
    (SimplicialChains.unitRadial_norm hY)
  let A := symmetricCoordinates x
  have hA : A ≠ 0 := by
    intro hzero
    have hh : x = 0 := symmetricCoordinates_injective (hzero.trans (map_zero _).symm)
    simp [hh] at hx
  have hs : signedExtension f A ≠ 0 := fun hh => hA
    ((hf.signedExtension_eq_zero_iff (symmetricCoordinates_selfAdjoint x)).mp hh)
  let Z : EuclideanSpace ℝ ι := WithLp.toLp 2 (signedExtension f A)
  have hZ : Z ≠ 0 := fun hh => hs (WithLp.toLp_injective 2 hh)
  refine ⟨A, symmetricCoordinates_selfAdjoint x, ‖Z‖ / ‖Y‖,
    div_pos (norm_pos_iff.mpr hZ) (norm_pos_iff.mpr hY), ?_⟩
  change ‖Z‖⁻¹ • Z = ‖Y‖⁻¹ • Y at he
  have he' := congrArg (fun z => ‖Z‖ • z) he
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hZ), one_smul, smul_smul,
    ← div_eq_mul_inv] at he'
  exact WithLp.toLp_injective 2 he'

end LabelBound

end BorsukNine

end OAI
