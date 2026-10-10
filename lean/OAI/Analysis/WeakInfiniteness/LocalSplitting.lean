import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma spectrum_dichotomy_of_no_orthogonal
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₙₐ[ℂ] B)
    (hno : ∀ a ∈ D,∀ b ∈ D,0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {c : A} (hc : c ∈ D) (hc0 : 0 ≤ c) {s : ℝ} (hs : s ∈ spectrum ℝ (π c)) :
    s=0 ∨ s=‖π c‖ := by
  by_contra! hn
  obtain hB | hB := subsingleton_or_nontrivial B
  · have he : spectrum ℝ (π c)=∅ := spectrum.of_subsingleton (π c)
    rw [he] at hs
    exact hs
  let : Nontrivial B := hB
  have hπc : 0 ≤ π c := map_nonneg π hc0
  have hs0 : 0 < s := lt_of_le_of_ne
    (NonnegSpectrumClass.nonneg_of_mem_quasispectrum hπc (spectrum_subset_quasispectrum ℝ (π c) hs)) hn.1.symm
  have hsN : s < ‖π c‖ := lt_of_le_of_ne
    ((Real.le_norm_self s).trans (spectrum.norm_le_norm_of_mem hs)) hn.2
  let t : ℝ := (s+‖π c‖)/2
  have hst : s < t := by dsimp [t]; linarith
  have htN : t < ‖π c‖ := by dsimp [t]; linarith
  have ht0 : 0 < t := hs0.trans hst
  let f : ℝ → ℝ := fun x => x*max (t-x) 0
  let g : ℝ → ℝ := fun x => max (x-t) 0
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : f 0=0 := by simp [f]
  have hg0 : g 0=0 := by dsimp [g]; rw [max_eq_right (by linarith)]
  have hfg : cfcₙ f c*cfcₙ g c=0 := by
    rw [← cfcₙ_mul f g c hf.continuousOn hf0 hg.continuousOn hg0]
    calc
      cfcₙ (fun x => f x*g x) c=cfcₙ (0 : ℝ → ℝ) c := by
        apply cfcₙ_congr
        intro x _
        change x*max (t-x) 0*max (x-t) 0=0
        rcases le_total x t with hx | hx
        · rw [max_eq_right (by linarith : x-t ≤ 0),mul_zero]
        · rw [max_eq_right (by linarith : t-x ≤ 0),mul_zero,zero_mul]
      _ = 0 := cfcₙ_zero ℝ c
  have hfa : 0 ≤ cfcₙ f c := cfcₙ_nonneg (fun x hx =>
    mul_nonneg (NonnegSpectrumClass.nonneg_of_mem_quasispectrum hc0 hx) (le_max_right _ _))
  have hga : 0 ≤ cfcₙ g c := cfcₙ_nonneg (fun _ _ => le_max_right _ _)
  have hfπ : π (cfcₙ f c)=cfcₙ f (π c) :=
    π.map_cfcₙ f c hf.continuousOn hf0 (by fun_prop) hc0.isSelfAdjoint hπc.isSelfAdjoint
  have hgπ : π (cfcₙ g c)=cfcₙ g (π c) :=
    π.map_cfcₙ g c hg.continuousOn hg0 (by fun_prop) hc0.isSelfAdjoint hπc.isSelfAdjoint
  obtain hz | hz := hno (cfcₙ f c) (cfcₙ_mem f hc) (cfcₙ g c) (cfcₙ_mem g hc) hfa hga hfg
  · rw [hfπ] at hz
    have hh := norm_apply_le_norm_cfcₙ f (π c)
      (spectrum_subset_quasispectrum ℝ (π c) hs) hf.continuousOn hf0 hπc.isSelfAdjoint
    rw [hz,norm_zero] at hh
    have hpos : 0 < f s := by dsimp [f]; rw [max_eq_left (by linarith)]; positivity
    exact (not_le_of_gt (norm_pos_iff.mpr (ne_of_gt hpos))) hh
  · rw [hgπ] at hz
    have hcn : π c ≠ 0 := by intro he; rw [he,norm_zero] at htN; linarith
    let : Nontrivial B := nontrivial_of_ne (π c) 0 hcn
    have hh := norm_apply_le_norm_cfcₙ g (π c)
      (spectrum_subset_quasispectrum ℝ (π c) (CStarAlgebra.norm_mem_spectrum_of_nonneg (π c) hπc))
      hg.continuousOn hg0 hπc.isSelfAdjoint
    rw [hz,norm_zero] at hh
    have hpos : 0 < g ‖π c‖ := by dsimp [g]; rw [max_eq_left (by linarith)]; linarith
    exact (not_le_of_gt (norm_pos_iff.mpr (ne_of_gt hpos))) hh

lemma square_eq_norm_smul_of_no_orthogonal
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₙₐ[ℂ] B)
    (hno : ∀ a ∈ D,∀ b ∈ D,0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {c : A} (hc : c ∈ D) (hc0 : 0 ≤ c) : π c*π c=‖π c‖ • π c := by
  have hπc : IsSelfAdjoint (π c) := (map_nonneg π hc0).isSelfAdjoint
  calc
    π c*π c=cfcₙ (fun x : ℝ => x*x) (π c) := by rw [cfcₙ_mul (fun x : ℝ => x) (fun x : ℝ => x) (π c),cfcₙ_id' ℝ _ hπc]
    _ = cfcₙ (fun x : ℝ => ‖π c‖*x) (π c) := by
      apply cfcₙ_congr
      intro x hx
      rcases (mem_quasispectrum_iff.mp hx) with rfl | hx
      · simp
      rcases spectrum_dichotomy_of_no_orthogonal D π hno hc hc0 hx with rfl | rfl <;> simp
    _ = ‖π c‖ • π c := cfcₙ_const_mul_id _ _ hπc

end

end WeakPureInfiniteness
end

end OAI
