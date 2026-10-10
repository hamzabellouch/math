import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.ReflectionTransport
import OAI.Geometry.Borsuk.Simplicial.SignVector
import OAI.Geometry.Borsuk.Simplicial.EventuallyFineSphereLabel

namespace OAI

namespace BorsukNine.SimplicialChains
open scoped RealInnerProductSpace

lemma odd_homotopy_surjective (n : ℕ) (hn : 1 < n) [NeZero n]
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) :
    ∃ x ∈ annulus n, unitRadial (H (1,x)) = y := by
  classical
  by_contra hmiss
  push Not at hmiss
  let b : Fin n → Bool := fun _ => false
  let L := householder y (facetCenter n b)
  have hLy : L y = facetCenter n b := householder_send (hy.trans (facetCenter_norm n b).symm)
  let K : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p => L (H p)
  have hK : ContinuousOn K (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := L.continuous.comp_continuousOn hH
  have hKz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, K p ≠ 0 := by
    intro p hp hz
    exact hHz p hp (L.injective (hz.trans (map_zero L).symm))
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => unitRadial (K (0,x))
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => unitRadial (K (1,x))
  have hU : ContinuousOn (fun p => unitRadial (K p)) (Set.Icc (0:ℝ) 1 ×ˢ annulus n) :=
    (unitRadial_continuousOn (S := {z | z ≠ 0}) (fun _ h => h)).comp hK hKz
  have hf : ContinuousOn f (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hg : ContinuousOn g (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn : ∀ x ∈ annulus n, ‖f x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hgn : ∀ x ∈ annulus n, ‖g x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfo : ∀ x ∈ annulus n, f (-x) = -f x := by
    intro x hx
    simp only [f,K,hHo x hx,map_neg,unitRadial_neg]
  have hgm : ∀ x ∈ annulus n, g x ≠ facetCenter n b := by
    intro x hx he
    have hnorm : L (unitRadial (H (1,x))) = unitRadial (K (1,x)) := by
      simp [unitRadial,K]
    apply hmiss x hx
    exact L.injective (hnorm.trans (he.trans hLy.symm))
  obtain ⟨δ₀,hδ₀,hdeg⟩ := eventually_odd_sphere_degree n hn f hf hfn hfo
  obtain ⟨δ₁,hδ₁,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl K hK hKz
  obtain ⟨δ₂,hδ₂,hzero⟩ := continuous_missed_facet_zero n n (by omega) hn b g hg hgn hgm
  have hnp : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hq : ((n:ℝ)-1)/n < 1 := by apply (div_lt_one hnp).mpr; linarith
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < min δ₀ (min δ₁ δ₂) / 2 by positivity) hq
  have hr0 : (((n:ℝ)-1)/n)^r * 2 < δ₀ := by
    have hh := min_le_left δ₀ (min δ₁ δ₂); linarith
  have hr1 : (((n:ℝ)-1)/n)^r * 2 < δ₁ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂); linarith
  have hr2 : (((n:ℝ)-1)/n)^r * 2 < δ₂ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂); linarith
  have he := hhom r hr1
  change approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) =
    approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) at he
  rw [hdeg r hr0] at he
  have hc := congrArg (fun c : Chain (cross n) => c ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩) he
  rw [crossFundamental_coeff n hn b,hzero r hr2] at hc
  exact one_ne_zero hc

end BorsukNine.SimplicialChains

end OAI
