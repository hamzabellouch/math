import Mathlib
import OAI.Geometry.Borsuk.Simplicial.UnitRadial
import OAI.Geometry.Borsuk.Simplicial.FineCrossMapMesh

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma eventually_fine_sphereLabel (n m : ℕ) (hn : 0 < n) [NeZero m]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ → IsFineLabel n m r (fun x => sphereLabel (g x)) := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((annulus_compact n).uniformContinuousOn_of_continuous hg) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr s hs t ht
  refine ⟨t.property.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact sphereLabel_bound _
  · intro v hv w hw he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hx' := hemisphere_vertex_annulus n hn t.property hx
    have hy' := hemisphere_vertex_annulus n hn t.property hy
    exact sphereLabel_compatible _ _ (hgn x hx') (hgn y hy')
      (hclose x hx' y hy' ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hr)) he

lemma eventually_odd_sphere_degree (n : ℕ) (hn : 1 < n) [NeZero n]
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) = crossFundamental n := by
  obtain ⟨δ,hδ,hr⟩ := eventually_fine_sphereLabel n n (by omega) g hg hgn
  refine ⟨δ,hδ,fun r hh => approximation_odd_fundamental n r hn _ (hr r hh) ?_⟩
  intro x hx
  rw [hgo x hx,sphereLabel_neg _ (hgn x hx)]

lemma unitRadial_of_norm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : ‖x‖ = 1) : unitRadial x = x := by simp [unitRadial,hx]

lemma normalized_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (unitRadial (H (1,x)))) (crossFundamental n) := by
  obtain ⟨δ,hδ,hh⟩ := sphere_homotopy_chains n m hn hmn (fun p => unitRadial (H p))
    ((unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp hH hHz)
    (fun p hp => unitRadial_norm (hHz p hp))
  exact ⟨δ,hδ,fun r hr => hh r hr 0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩⟩

lemma convex_combination_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 ≤ ⟪x,y⟫)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : (1-t) • x + t • y ≠ 0 := by
  intro hh
  by_cases ht1 : t = 1
  · simp only [ht1,sub_self,zero_smul,one_smul,zero_add] at hh
    exact hy hh
  · have hpos : 0 < (1-t) * ⟪x,x⟫ := mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) (real_inner_self_pos.mpr hx)
    have hnonneg : 0 ≤ t * ⟪x,y⟫ := mul_nonneg ht.1 hxy
    have he := congrArg (fun z : E => ⟪x,z⟫) hh
    simp only [inner_add_right,real_inner_smul_right,inner_zero_right] at he
    linarith

lemma hemispheric_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ContinuousOn g (annulus n))
    (hfn : ∀ x ∈ annulus n, ‖f x‖ = 1) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hfg : ∀ x ∈ annulus n, 0 ≤ ⟪f x,g x⟫) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (g x)) (crossFundamental n) := by
  let H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) :=
    fun p => (1-p.1) • f p.2 + p.1 • g p.2
  have hfc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.2)
      (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := hf.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hgc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.2)
      (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := hg.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hc : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n) :=
    ((continuous_const.sub continuous_fst).continuousOn.smul hfc).add
      (continuous_fst.continuousOn.smul hgc)
  obtain ⟨δ,hδ,hh⟩ := normalized_homotopy_chains n m hn hmn H hc (by
    intro p hp
    exact convex_combination_ne_zero (by have h := hfn p.2 hp.2; intro hz; simp [hz] at h)
      (by have h := hgn p.2 hp.2; intro hz; simp [hz] at h) (hfg p.2 hp.2) hp.1)
  refine ⟨δ,hδ,fun r hr => ?_⟩
  have h := hh r hr
  have he0 : ∀ x ∈ annulus n, unitRadial (H (0,x)) = f x := by
    intro x hx
    simpa [H] using unitRadial_of_norm_one (hfn x hx)
  have he1 : ∀ x ∈ annulus n, unitRadial (H (1,x)) = g x := by
    intro x hx
    simpa [H] using unitRadial_of_norm_one (hgn x hx)
  have hreplace (a c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
      (he : ∀ x ∈ annulus n, a x = c x) :
      approximation n m r (fun x => sphereLabel (a x)) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (c x)) (crossFundamental n) := by
    apply linearMap_eq_of_support (mapChains (hemisphereComplex (n:ℝ)) (cross m) (fun x => sphereLabel (a x)))
      (mapChains (hemisphereComplex (n:ℝ)) (cross m) (fun x => sphereLabel (c x)))
    intro s hs
    rw [mapChains_simplex _ _ _ s.property,mapChains_simplex _ _ _ s.property]
    have himg : s.val.image (fun x => sphereLabel (a x)) = s.val.image (fun x => sphereLabel (c x)) := by
      apply Finset.image_congr
      intro x hx
      exact congrArg sphereLabel (he x (hemisphere_vertex_annulus n hn s.property hx))
    simp only [mapSimplex,himg]
  exact (hreplace _ _ he0).symm.trans (h.trans (hreplace _ _ he1))

end BorsukNine.SimplicialChains

end OAI
