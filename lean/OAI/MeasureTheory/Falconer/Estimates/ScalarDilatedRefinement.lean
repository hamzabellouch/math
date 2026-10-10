import OAI.MeasureTheory.Falconer.Estimates.ScalarMixedRefinement

namespace OAI

/-! Mixed-sum refinement with the second factor kept in its original
coordinates. Both the exact graph and all retained degrees are transported. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_dilation_filter {c : ℝ} (hc : c ≠ 0) (B : Finset ℝ) (p : ℝ → Prop) :
    (B.image (fun y => c*y)).filter (fun v => p (v/c)) =
      (B.filter p).image (fun y => c*y) := by
  classical
  have he (y : ℝ) : c*y/c = y := by field_simp
  ext v
  constructor
  · intro hv
    obtain ⟨hv,hp⟩ := Finset.mem_filter.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    rw [he] at hp
    exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hp⟩,rfl⟩
  · intro hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hy,hp⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hy,by rwa [he]⟩

 theorem scalar_dilation_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (fun y : ℝ => c*y) := by
  intro x y h
  have hh := congrArg (fun v => v/c) h
  have he (z : ℝ) : c*z/c = z := by field_simp
  simpa only [he] using hh

 theorem scalar_dilated_refinement {δ ρ c : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hc : c ≠ 0)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B.image (fun y => c*y), ∀ y ∈ B.image (fun y => c*y), x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ)
    (hdense : ρ*(A.card:ℝ)*(B.card:ℝ) ≤ ∑ a ∈ A, ((B.filter fun b => e a b).card:ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+c*b)/δ⌋ ∈ D) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ρ^2*(A.card:ℝ)/64 ≤ (X.card:ℝ) ∧ ρ*(B.card:ℝ)/4 ≤ (Y.card:ℝ) ∧
      ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ)*(ρ^8*(A.card:ℝ)^2*(B.card:ℝ)^2) ≤
        67108864*(D.card:ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(Y.card:ℝ)/64 ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  classical
  have hinj := scalar_dilation_injective hc
  have he (y : ℝ) : c*y/c = y := by field_simp
  have hcard (V : Finset ℝ) : (V.image (fun y => c*y)).card = V.card :=
    Finset.card_image_of_injective V hinj
  have hcount (V : Finset ℝ) (x : ℝ) :
      ((V.image (fun y => c*y)).filter (fun v => e x (v/c))).card =
        (V.filter fun y => e x y).card := by
    rw [scalar_dilation_filter hc,hcard]
  have hd : ρ*(A.card:ℝ)*((B.image (fun y => c*y)).card:ℝ) ≤
      ∑ a ∈ A, (((B.image (fun y => c*y)).filter fun v => e a (v/c)).card:ℝ) := by
    simp only [hcard,hcount]
    exact hdense
  have hl : ∀ a ∈ A, ∀ v ∈ B.image (fun y => c*y), e a (v/c) → ⌊(a+v)/δ⌋ ∈ D := by
    intro a ha v hv hev
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    rw [he] at hev
    exact hlabels a ha b hb hev
  obtain ⟨X,hXA,V,hVB,hX,hV,hsum,hdegrees⟩ := scalar_mixed_refinement_with_degrees hδ
    A (B.image (fun y => c*y)) hA (hB.image _) hAsep hBsep
    (fun x v => e x (v/c)) D hρ hd hl
  obtain ⟨Y,hYB,hYimage⟩ := Finset.subset_image_iff.mp hVB
  have hYc : V.card = Y.card := by rw [← hYimage,hcard]
  rw [hcard] at hV hsum
  refine ⟨X,hXA,Y,hYB,hX,by simpa only [hYc] using hV,?_,?_⟩
  · simpa only [hYimage] using hsum
  · intro x hx
    have hh := hdegrees x hx
    rw [← hYimage,hcount,hcard] at hh
    exact hh

end Falconer

end OAI
