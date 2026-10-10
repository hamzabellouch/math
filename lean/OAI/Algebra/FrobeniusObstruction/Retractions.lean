import Mathlib
import OAI.Algebra.FrobeniusObstruction.SquareZero

namespace OAI

noncomputable section
open scoped BigOperators

noncomputable section
namespace BoundaryOnly.FormalObstruction

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

                                                                                           
theorem retraction_core (D : V →ₗ[k] V) (d2 : ∀ x, D (D x) = 0)
    (N : Submodule k V) :
    ∃ r h : V →ₗ[k] V,
      (∀ x, D (r x) = r (D x)) ∧
      (∀ x, r (r x) = r x) ∧
      N.map r = N ⊓ N.comap D ∧
      (∀ x ∈ N ⊓ N.comap D, r x = x) ∧
      (∀ x, x - r x = D (h x) + h (D x)) := by
  let K := N ⊓ N.comap D
  obtain ⟨E, hKE, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq (show K ≤ N from inf_le_left)
  have hEN : E ≤ N := by
    rw [← hsup]
    exact le_sup_right
  have hDz (e : E) (he : D e ∈ N) : (e : V) = 0 :=
    Submodule.disjoint_def.mp hKE _ ⟨hEN e.property, he⟩ e.property
  let f : E × N →ₗ[k] V := (D.comp E.subtype).coprod N.subtype
  have hf : LinearMap.ker f = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨e, n⟩ hz
    change D (e : V) + (n : V) = 0 at hz
    have he : (e : V) = 0 := hDz e (by
      have heq : D (e : V) = -(n : V) := eq_neg_of_add_eq_zero_left hz
      rw [heq]
      exact N.neg_mem n.property)
    have hn : (n : V) = 0 := by simpa [he] using hz
    exact Prod.ext (Subtype.ext he) (Subtype.ext hn)
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  let h : V →ₗ[k] V := E.subtype.comp ((LinearMap.fst k E N).comp g)
  have hrange (x : V) : h x ∈ E := (g x).1.property
  have hgval (e : E) (n : N) : g (D e + n) = (e,n) :=
    LinearMap.congr_fun hg (e,n)
  have hN (x : V) (hx : x ∈ N) : h x = 0 := by
    have hv := hgval 0 ⟨x,hx⟩
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add] at hv
    change ((g x).1 : V) = 0
    rw [hv]
    rfl
  have hDE (e : E) : h (D e) = e := by
    have hv := hgval e 0
    simp only [ZeroMemClass.coe_zero, add_zero] at hv
    change ((g (D e)).1 : V) = e
    rw [hv]
  let Q : V →ₗ[k] V := D.comp h + h.comp D
  have hQE (e : E) : Q e = e := by
    change D (h e) + h (D e) = e
    rw [hN e (hEN e.property), map_zero, zero_add, hDE]
  have hQDE (e : E) : Q (D e) = D e := by
    change D (h (D e)) + h (D (D e)) = D e
    rw [hDE, d2, map_zero, add_zero]
  have hQK (x : V) (hx : x ∈ K) : Q x = 0 := by
    change D (h x) + h (D x) = 0
    rw [hN x hx.1, map_zero, hN (D x) hx.2, add_zero]
  have hQQ (x : V) : Q (Q x) = Q x := by
    change Q (D (h x) + h (D x)) = D (h x) + h (D x)
    rw [map_add, hQDE ⟨h x,hrange x⟩, hQE ⟨h (D x),hrange (D x)⟩]
  have hDQ (x : V) : D (Q x) = Q (D x) := by
    change D (D (h x) + h (D x)) = D (h (D x)) + h (D (D x))
    rw [map_add, d2, zero_add, d2, map_zero, add_zero]
  let r : V →ₗ[k] V := LinearMap.id - Q
  have hr (x : V) : r x = x - Q x := rfl
  have hrK (x : V) (hx : x ∈ K) : r x = x := by rw [hr, hQK x hx, sub_zero]
  have hrE (e : E) : r e = 0 := by rw [hr, hQE, sub_self]
  have hrN (x : V) (hx : x ∈ N) : r x ∈ K := by
    rw [← hsup, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rw [map_add, hrK y hy, hrE ⟨z,hz⟩, add_zero]
    exact hy
  refine ⟨r, h, ?_, ?_, ?_, hrK, ?_⟩
  · intro x
    rw [hr, hr, map_sub, hDQ]
  · intro x
    simp only [hr, map_sub, hQQ, sub_self, sub_zero]
  · apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hrN x hx
    · intro x hx
      exact ⟨x, hx.1, hrK x hx⟩
  · intro x
    rw [hr, sub_sub_cancel]
    rfl

                                                                
theorem kernel_retraction_core [FiniteDimensional k V]
    (D S : V →ₗ[k] V) (d2 : ∀ x, D (D x) = 0) :
    ∃ r h : V →ₗ[k] V,
      (∀ x, D (r x) = r (D x)) ∧
      (∀ x, r (r x) = r x) ∧
      (LinearMap.ker S).map r = LinearMap.ker S ⊓ (LinearMap.ker S).comap D ∧
      (∀ x ∈ LinearMap.ker S ⊓ (LinearMap.ker S).comap D, r x = x) ∧
      (∀ x, x - r x = D (h x) + h (D x)) :=
  retraction_core D d2 (LinearMap.ker S)

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

                                                                             
                                                                          
                                                                     
theorem parity_retraction (htwo : (2 : k) ≠ 0)
    (D S P : V →ₗ[k] V)
    (hDD : ∀ x, D (D x) = 0) (hPP : ∀ x, P (P x) = x)
    (hDP : ∀ x, D (P x) = -P (D x))
    (hSP : ∀ x, S (P x) = P (S x)) :
    ∃ r h : V →ₗ[k] V,
      (∀ x, D (r x) = r (D x)) ∧
      (∀ x, P (r x) = r (P x)) ∧
      (∀ x, P (h x) = -h (P x)) ∧
      (∀ x, x - r x = D (h x) + h (D x)) ∧
      (∀ x, S x = 0 → S (r x) = 0 ∧ S (D (r x)) = 0) := by
  obtain ⟨r,h,hrD,_,hrN,_,hrh⟩ :=
    retraction_core D hDD (LinearMap.ker S)
  let c : k := (2 : k)⁻¹
  have hc : c+c = 1 := by dsimp [c]; field_simp; ring
  let r' : V →ₗ[k] V := c • (r + P.comp (r.comp P))
  let h' : V →ₗ[k] V := c • (h - P.comp (h.comp P))
  have hr' (x : V) : r' x = c • (r x + P (r (P x))) := rfl
  have hh' (x : V) : h' x = c • (h x - P (h (P x))) := rfl
  have hPD (x : V) : P (D x) = -D (P x) := by rw [hDP, neg_neg]
  have hrN' (x : V) (hx : S x = 0) : S (r x) = 0 ∧ S (D (r x)) = 0 := by
    have hx' : r x ∈ (LinearMap.ker S).map r := ⟨x, hx, rfl⟩
    rw [hrN] at hx'
    exact hx'
  refine ⟨r',h',?_,?_,?_,?_,?_⟩
  · intro x
    simp only [hr', map_smul, map_add, hDP, hrD, map_neg]
    module
  · intro x
    simp only [hr', map_smul, map_add, hPP]
    module
  · intro x
    simp only [hh', map_smul, map_sub, hPP]
    module
  · intro x
    have h₁ := hrh x
    have h₂ := congrArg P (hrh (P x))
    simp only [map_sub, map_add, hPP] at h₂
    rw [hPD (h (P x)), hDP x, map_neg, map_neg] at h₂
    rw [hr', hh', hh']
    simp only [map_smul, map_sub]
    have hh : c • (D (h x) + h (D x)) = c • (x - r x) := congrArg (c • ·) h₁.symm
    have hh₂ : c • (-D (P (h (P x))) - P (h (P (D x)))) =
        c • (x - P (r (P x))) := by
      apply congrArg (c • ·)
      simpa only [sub_eq_add_neg] using h₂.symm
    have hc' : c • x + c • x = x := by rw [← add_smul, hc, one_smul]
    calc
      x - c • (r x + P (r (P x))) =
          (c • x + c • x) - c • (r x + P (r (P x))) := by rw [hc']
      _ = c • (x - r x) + c • (x - P (r (P x))) := by module
      _ = c • (D (h x) + h (D x)) +
          c • (-D (P (h (P x))) - P (h (P (D x)))) := by rw [hh, hh₂]
      _ = _ := by module
  · intro x hx
    have hSx := hrN' x hx
    have hSPx := hrN' (P x) (by rw [hSP, hx, map_zero])
    constructor
    · simp only [hr', map_smul, map_add, hSP, hSx.1, hSPx.1, map_zero, add_zero,
        smul_zero]
    · simp only [hr', map_smul, map_add, hDP, hSP, map_neg, hSx.2, hSPx.2,
        map_zero, neg_zero, add_zero, smul_zero]

end BoundaryOnly.FormalObstruction

end
end

end OAI
