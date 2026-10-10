import Mathlib

namespace OAI

/-! Irreducible creation operators and one-dimensional vacuum spaces. -/

namespace BFSSScalarVacuum
noncomputable section
variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def word (c : ι → V →ₗ[ℂ] V) (v : V) : List ι → V
  | [] => v
  | i :: w => c i (word c v w)

theorem creation_span_eq_top 
    (a c : ι → V →ₗ[ℂ] V)
    (κ : ι → ι → ℂ)
    (hcar : ∀ i j x, a i (c j x) + c j (a i x) = κ i j • x)
    (hirr : ∀ W : Submodule ℂ V,
      (∀ i, ∀ x ∈ W, a i x ∈ W) → (∀ i, ∀ x ∈ W, c i x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (v : V) (hv : v ≠ 0) (ha : ∀ i, a i v = 0) :
    Submodule.span ℂ (Set.range (word c v)) = ⊤ := by
  let W := Submodule.span ℂ (Set.range (word c v))
  have hw (w : List ι) : word c v w ∈ W := Submodule.subset_span ⟨w,rfl⟩
  have hc (i : ι) : ∀ x ∈ W, c i x ∈ W := by
    intro x hx
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun r x _ hx => ?_) hx
    · obtain ⟨w,rfl⟩ := hy
      exact hw (i :: w)
    · simpa only [map_zero] using W.zero_mem
    · simpa only [map_add] using W.add_mem hx hy
    · simpa only [map_smul] using W.smul_mem r hx
  have haw (i : ι) (w : List ι) : a i (word c v w) ∈ W := by
    induction w with
    | nil => simpa only [word,ha] using W.zero_mem
    | cons j w ih =>
      have he := hcar i j (word c v w)
      change a i (c j (word c v w)) ∈ W
      rw [eq_sub_of_add_eq he]
      exact W.sub_mem (W.smul_mem (κ i j) (hw w)) (hc j _ ih)
  have haa (i : ι) : ∀ x ∈ W, a i x ∈ W := by
    intro x hx
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun r x _ hx => ?_) hx
    · obtain ⟨w,rfl⟩ := hy
      exact haw i w
    · simpa only [map_zero] using W.zero_mem
    · simpa only [map_add] using W.add_mem hx hy
    · simpa only [map_smul] using W.smul_mem r hx
  rcases hirr W haa hc with hb | ht
  · have h : v ∈ W := hw []
    rw [hb] at h
    exact (hv h).elim
  · exact ht

theorem vacuum_orthogonal_zero 
    (a c : ι → V →ₗ[ℂ] V)
    (κ : ι → ι → ℂ)
    (hcar : ∀ i j x, a i (c j x) + c j (a i x) = κ i j • x)
    (hadj : ∀ i x y, inner ℂ x (c i y) = inner ℂ (a i x) y)
    (hirr : ∀ W : Submodule ℂ V,
      (∀ i, ∀ x ∈ W, a i x ∈ W) → (∀ i, ∀ x ∈ W, c i x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (v z : V) (hv : v ≠ 0) (ha : ∀ i, a i v = 0)
    (hz : ∀ i, a i z = 0) (hip : inner ℂ z v = 0) : z = 0 := by
  have ht := creation_span_eq_top a c κ hcar hirr v hv ha
  have hw (w : List ι) : inner ℂ z (word c v w) = 0 := by
    cases w with
    | nil => exact hip
    | cons i w => simp only [word,hadj,hz,inner_zero_left]
  have hspan : ∀ x ∈ Submodule.span ℂ (Set.range (word c v)), inner ℂ z x = 0 := by
    intro x hx
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun r x _ hx => ?_) hx
    · obtain ⟨w,rfl⟩ := hy
      exact hw w
    · exact inner_zero_right z
    · simp only [inner_add_right,hx,hy,add_zero]
    · simp only [inner_smul_right,hx,mul_zero]
  have hzz : inner ℂ z z = 0 := hspan z (by rw [ht]; trivial)
  exact inner_self_eq_zero.mp hzz

theorem vacuum_line_of_exists
    (a c : ι → V →ₗ[ℂ] V) (κ : ι → ι → ℂ)
    (hcar : ∀ i j x, a i (c j x) + c j (a i x) = κ i j • x)
    (hadj : ∀ i x y, inner ℂ x (c i y) = inner ℂ (a i x) y)
    (hirr : ∀ W : Submodule ℂ V,
      (∀ i, ∀ x ∈ W, a i x ∈ W) → (∀ i, ∀ x ∈ W, c i x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (v : V) (hv : v ≠ 0) (ha : ∀ i, a i v = 0) :
    ∀ z : V, (∀ i, a i z = 0) ↔ z ∈ Submodule.span ℂ {v} := by
  intro z
  constructor
  · intro hz
    let r : ℂ := inner ℂ v z / inner ℂ v v
    have hn : inner ℂ v v ≠ 0 := by exact fun h => hv (inner_self_eq_zero.mp h)
    have hzero (i : ι) : a i (z-r • v) = 0 := by rw [map_sub,map_smul,hz,ha,smul_zero,sub_zero]
    have hip : inner ℂ (z-r • v) v = 0 := by
      apply (inner_eq_zero_symm).mp
      simp only [inner_sub_right,inner_smul_right]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ hn).symm
    have he := vacuum_orthogonal_zero a c κ hcar hadj hirr v (z-r • v) hv ha hzero hip
    rw [sub_eq_zero] at he
    rw [he]
    exact Submodule.smul_mem _ r (Submodule.subset_span (by simp))
  · intro hz i
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul,ha,smul_zero]
end
end BFSSScalarVacuum

end OAI
