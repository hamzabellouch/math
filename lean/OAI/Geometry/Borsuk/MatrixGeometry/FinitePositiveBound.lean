import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SignVector
import OAI.Geometry.Borsuk.Simplicial.CompactAdditiveLocality
import OAI.Geometry.Borsuk.Simplicial.EventuallyFineSphereLabel

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Finset Set
open scoped Topology

lemma finite_positive_bound {A : Type*} [Fintype A] (d : A → ℝ) (hd : ∀ a, 0 < d a) :
    ∃ ε > 0, ∀ a, ε < d a := by
  classical
  by_cases hne : Nonempty A
  · let r : ℝ := Finset.univ.inf' Finset.univ_nonempty d
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (by simpa using hd)
    refine ⟨r/2,by positivity,fun a => ?_⟩
    exact (by linarith : r/2 < r).trans_le (Finset.inf'_le _ (Finset.mem_univ a))
  · exact ⟨1,zero_lt_one,fun a => False.elim (hne ⟨a⟩)⟩

end BorsukNine

namespace BorsukNine.SimplicialChains
open Finset Set
lemma odd_homotopy_local_models {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (hn : 1 < n) [NeZero n] (b : Fin n → Bool)
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    (G : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hG : ∀ a, ContinuousOn (G a) (annulus n))
    (hGz : ∀ a x, x ∈ annulus n → G a x ≠ 0)
    (hGo : ∀ a x, x ∈ annulus n → G a (-x) = -G a x)
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → H (1,x.val) = G a x.val)
    (hcover : ∀ x : annulus n, unitRadial (H (1,x.val)) = facetCenter n b → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), unitRadial (G a x.val) = facetCenter n b → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card A : F₂) = 1 := by
  classical
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => unitRadial (H (1,x))
  let g : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun a x => unitRadial (G a x)
  have hfc : ContinuousOn f (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩))
      (fun x hx => hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn (x) (hx : x ∈ annulus n) : ‖f x‖ = 1 := unitRadial_norm (hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hgc (a) : ContinuousOn (g a) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp (hG a) (hGz a)
  have hgn (a x) (hx : x ∈ annulus n) : ‖g a x‖ = 1 := unitRadial_norm (hGz a x hx)
  obtain ⟨δa,hδa,hadd⟩ := additive_approximation_coeff n n (by omega) b f g hfc hgc U hU
    (fun a x hx => congrArg unitRadial (heq a x hx))
    (fun x hx => hcover x ((all_labelRegions_iff_center n b _ (hfn _ x.property)).mp hx))
    (fun a x hx => hroot a x ((all_labelRegions_iff_center n b _ (hgn a _ x.property)).mp hx)) hdis
  obtain ⟨δh,hδh,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl H hH hHz
  have hc0 : ContinuousOn (fun x => unitRadial (H (0,x))) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
      (fun x hx => hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  obtain ⟨δ0,hδ0,hdeg0⟩ := eventually_odd_sphere_degree n hn _ hc0
    (fun x hx => unitRadial_norm (hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
    (fun x hx => by rw [hHo x hx,unitRadial_neg])
  have hgodd : ∀ a, ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n) = crossFundamental n := by
    intro a
    apply eventually_odd_sphere_degree n hn _ (hgc a) (hgn a)
    intro x hx
    change unitRadial (G a (-x)) = -unitRadial (G a x)
    rw [hGo a x hx,unitRadial_neg]
  choose dg hdg hdgprop using hgodd
  obtain ⟨δg,hδg,hδgb⟩ := finite_positive_bound dg hdg
  obtain ⟨r,hr⟩ := exists_small_cross_mesh n (by omega) (lt_min hδ0 (lt_min hδh (lt_min hδa hδg)))
  have hr0 := hr.trans_le (min_le_left _ _)
  have hrh := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hra := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrg := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he0 : approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) = crossFundamental n :=
    (hhom r hrh).symm.trans (hdeg0 r hr0)
  have hadd' := hadd r hra
  rw [he0,crossFundamental_coeff n hn b] at hadd'
  have hm (a : A) : approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 1 := by
    rw [hdgprop a r (hrg.trans (hδgb a)),crossFundamental_coeff n hn b]
  simpa only [hm,Finset.sum_const,Finset.card_univ,nsmul_one] using hadd'.symm
end BorsukNine.SimplicialChains

end OAI
