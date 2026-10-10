import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicFunctionSpace
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry
import OAI.Probability.CriticalPercolation.Harmonic.CayleyPoincare
import OAI.Probability.CriticalPercolation.Harmonic.HarmonicEnergy

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

omit [Group A] in
lemma sum_subtype_pair (F : Finset A) (f : A → A → ℝ) :
    (∑ x:F, ∑ y:F, f x.val y.val)=∑ x∈F, ∑ y∈F, f x y := by
  simp only [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort F (fun x => ∑ y∈F, f x y)

lemma sum_neighbor_rows (S F : Finset A) (x : A) (f : A → ℝ)
    (hF : ∀ s∈S, x*s∈F) :
    (∑ y∈F, if x⁻¹*y∈S then f y else 0) = ∑ s∈S, f (x*s) := by
  have he : F.filter (fun y => x⁻¹*y∈S)=S.image (fun s => x*s) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨hy,hs⟩
      exact ⟨x⁻¹*y,hs,mul_inv_cancel_left x y⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨hF s hs,by simpa⟩
  rw [←Finset.sum_filter,he,Finset.sum_image]
  intro a _ b _ h
  exact mul_left_cancel h

lemma sum_neighbor_rows_le (S F : Finset A) (x : A) (f : A → ℝ)
    (hf : ∀ y, 0≤f y) :
    (∑ y∈F, if x⁻¹*y∈S then f y else 0) ≤ ∑ s∈S, f (x*s) := by
  have he : F.filter (fun y => x⁻¹*y∈S)⊆S.image (fun s => x*s) := by
    intro y hy
    exact Finset.mem_image.mpr ⟨x⁻¹*y,(Finset.mem_filter.mp hy).2,mul_inv_cancel_left x y⟩
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑ y∈S.image (fun s => x*s), f y :=
      Finset.sum_le_sum_of_subset_of_nonneg he (by intros; apply hf)
    _ = _ := Finset.sum_image (fun a _ b _ h => mul_left_cancel h)

namespace WordGeometry
variable (W : WordGeometry A)

def IsHarmonic (u : A → ℝ) : Prop := ∀ x, (∑ s∈W.generators, (u x-u (x*s)))=0

lemma inv_mem_generators_iff (s : A) : s⁻¹∈W.generators ↔ s∈W.generators := by
  constructor
  · intro hs
    have hh := Finset.inv_mem_inv hs
    simpa only [W.inv_eq,inv_inv] using hh
  · intro hs
    have hh := Finset.inv_mem_inv hs
    simpa only [W.inv_eq] using hh

lemma neighbor_symm (x y : A) : x⁻¹*y∈W.generators ↔ y⁻¹*x∈W.generators := by
  have hh := W.inv_mem_generators_iff (x⁻¹*y)
  simpa only [mul_inv_rev,inv_inv] using hh.symm

lemma cutoff_neighbor_mem_ball (R : ℕ) {x : A} (hx : W.cutoff R x≠0)
    {s : A} (hs : s∈W.generators) : x*s∈W.ball (2*R+1) := by
  apply W.length_le_iff.mp
  have hlen := W.cutoff_ne_zero_length R hx
  have hh := (W.length_mul_generator hs x).1
  omega

theorem caccioppoli (u : A → ℝ) (hu : W.IsHarmonic u) (R : ℕ) :
    (R:ℝ)^2*energy W.generators (W.ball R) u ≤
      4*(W.generators.card:ℝ)*squareMass (W.ball (2*R+1)) u := by
  let F := W.ball (2*R+1)
  let w : F → F → ℝ := fun x y => if x.val⁻¹*y.val∈W.generators then 1 else 0
  let η : F → ℝ := fun x => W.cutoff R x.val
  have hw (x y : F) : w x y=w y x := by
    dsimp [w]
    simp only [W.neighbor_symm x.val y.val]
  have hw0 (x y : F) : 0≤w x y := by dsimp [w]; split <;> positivity
  have hh (x : F) : η x=0 ∨ (∑ y:F, w x y*(u x.val-u y.val))=0 := by
    by_cases hx : η x=0
    · exact Or.inl hx
    right
    have hx' : W.cutoff R x.val≠0 := hx
    simp only [w,ite_mul,one_mul,zero_mul]
    rw [Finset.sum_coe_sort F (fun y : A =>
      if x.val⁻¹*y∈W.generators then u x.val-u y else 0)]
    rw [sum_neighbor_rows W.generators F x.val (fun y => u x.val-u y)
      (fun s hs => W.cutoff_neighbor_mem_ball R hx' hs)]
    exact hu x.val
  have hc := finite_caccioppoli w hw hw0 (fun x:F => u x.val) η hh
  have hL : (R:ℝ)^2*energy W.generators (W.ball R) u ≤
      ∑ x:F, ∑ y:F, w x y*(η x)^2*(u x.val-u y.val)^2 := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if x.val⁻¹*y.val∈W.generators then
      (W.cutoff R x.val)^2*(u x.val-u y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if x⁻¹*y∈W.generators then
      (W.cutoff R x)^2*(u x-u y)^2 else 0 from
      sum_subtype_pair F (fun x y => if x⁻¹*y∈W.generators then
        (W.cutoff R x)^2*(u x-u y)^2 else 0)]
    have hsub : W.ball R⊆F := W.ball_mono (by omega)
    calc
      _ = ∑ x∈W.ball R, (R:ℝ)^2*(∑ s∈W.generators, (u x-u (x*s))^2) := by
        unfold energy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ ∑ x∈W.ball R, (W.cutoff R x)^2*(∑ s∈W.generators, (u x-u (x*s))^2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_right
        · exact sq_le_sq₀ (by positivity) (W.cutoff_nonneg R x) |>.mpr (W.cutoff_large R hx)
        · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
      _ = ∑ x∈W.ball R, ∑ y∈F,
          if x⁻¹*y∈W.generators then (W.cutoff R x)^2*(u x-u y)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [sum_neighbor_rows]
        · exact Finset.mul_sum _ _ _
        · intro s hs
          apply W.length_le_iff.mp
          have hlx := W.length_le_iff.mpr hx
          have hhx := (W.length_mul_generator hs x).1
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro x hx hxn
        exact Finset.sum_nonneg (fun y hy => by split <;> positivity))
  have hU : (∑ x:F, ∑ y:F, w x y*(u x.val)^2*(η x-η y)^2) ≤
      (W.generators.card:ℝ)*squareMass F u := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if x.val⁻¹*y.val∈W.generators then
      (u x.val)^2*(W.cutoff R x.val-W.cutoff R y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if x⁻¹*y∈W.generators then
      (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0 from
      sum_subtype_pair F (fun x y => if x⁻¹*y∈W.generators then
        (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0)]
    unfold squareMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    calc
      _ ≤ ∑ y∈F, if x⁻¹*y∈W.generators then (u x)^2 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hs : x⁻¹*y∈W.generators
        · simp only [ite_eq_left hs]
          have ha := W.cutoff_lipschitz_generator R hs x
          simp only [mul_inv_cancel_left,abs_sub_comm] at ha
          have hsquare := (sq_le_one_iff_abs_le_one _).mpr ha
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare (sq_nonneg (u x))
        · simp only [ite_eq_right hs,le_refl]
      _ ≤ ∑ s∈W.generators, (u x)^2 := sum_neighbor_rows_le _ _ _ _ (by intro y; positivity)
      _ = _ := by simp
  have hU' := mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤4)
  change _≤4*(W.generators.card:ℝ)*squareMass F u
  calc
    _ ≤ _ := hL.trans hc
    _ ≤ _ := by simpa only [mul_assoc] using hU'

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
