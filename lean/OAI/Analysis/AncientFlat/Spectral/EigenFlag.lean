import Mathlib

namespace OAI
noncomputable section
open Set Module.End
namespace FlatSpectral
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def eigenFlag (v : ℕ → X) (n : ℕ) : Submodule ℂ X := Submodule.span ℂ (v '' Iio n)

lemma eigenFlag_mono (v : ℕ → X) : Monotone (eigenFlag v) := by
  intro m n h
  exact Submodule.span_mono (image_mono (fun _ hx => lt_of_lt_of_le hx h))

lemma eigenFlag_mem (v : ℕ → X) (n : ℕ) : v n ∈ eigenFlag v (n+1) :=
  Submodule.subset_span (mem_image_of_mem v (by simp))

lemma eigenFlag_not_mem (v : ℕ → X) (hv : LinearIndependent ℂ v) (n : ℕ) :
    v n ∉ eigenFlag v n := by
  apply ((hv.linearIndepOn (Iio n)).notMem_span_iff).mpr
  exact ⟨hv.linearIndepOn _,by simp⟩

lemma eigenFlag_closed (v : ℕ → X) (n : ℕ) : IsClosed (eigenFlag v n : Set X) := by
  let : FiniteDimensional ℂ (eigenFlag v n) := FiniteDimensional.span_of_finite ℂ ((finite_Iio n).image v)
  exact (eigenFlag v n).closed_of_finiteDimensional

lemma eigenFlag_invariant (T : X →L[ℂ] X) (μ : ℕ → ℂ) (v : ℕ → X)
    (hv : ∀ n, T (v n)=μ n • v n) (n : ℕ) :
    ∀ x ∈ eigenFlag v n, T x ∈ eigenFlag v n := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    rw [hv i]
    exact (eigenFlag v n).smul_mem _ (Submodule.subset_span (mem_image_of_mem v hi))
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using (eigenFlag v n).add_mem hx' hy'
  | smul a x hx hx' => simpa only [map_smul] using (eigenFlag v n).smul_mem a hx'

lemma eigenFlag_triangular (T : X →L[ℂ] X) (μ : ℕ → ℂ) (v : ℕ → X)
    (hv : ∀ n, T (v n)=μ n • v n) (n : ℕ) :
    ∀ x ∈ eigenFlag v (n+1), T x-μ n • x ∈ eigenFlag v n := by
  let L : X →L[ℂ] X := T-μ n • ContinuousLinearMap.id ℂ X
  change ∀ x ∈ eigenFlag v (n+1), L x ∈ eigenFlag v n
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change T (v i)-μ n • v i ∈ eigenFlag v n
    rw [hv i,←sub_smul]
    by_cases hin : i=n
    · simp [hin]
    · exact (eigenFlag v n).smul_mem _ (Submodule.subset_span (mem_image_of_mem v (by change i<n; change i<n+1 at hi; omega)))
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using (eigenFlag v n).add_mem hx' hy'
  | smul a x hx hx' => simpa only [map_smul] using (eigenFlag v n).smul_mem a hx'

lemma eigenFlag_riesz (v : ℕ → X) (hv : LinearIndependent ℂ v) :
    ∃ x : ℕ → X, (∀ n, x n ∈ eigenFlag v (n+1)) ∧
      (∀ n, ‖x n‖=1) ∧ (∀ n, ∀ y ∈ eigenFlag v n, (1:ℝ)/2≤‖x n-y‖) := by
  have hex (n : ℕ) : ∃ x : X, x ∈ eigenFlag v (n+1) ∧ ‖x‖=1 ∧
      ∀ y ∈ eigenFlag v n, (1:ℝ)/2≤‖x-y‖ := by
    let M := eigenFlag v (n+1)
    let F := (eigenFlag v n).comap M.subtype
    have hF : IsClosed (F : Set M) := (eigenFlag_closed v n).preimage_val
    have hn : ∃ x : M, x ∉ F :=
      ⟨⟨v n,eigenFlag_mem v n⟩,eigenFlag_not_mem v hv n⟩
    obtain ⟨x,hx,hxn,hxr⟩ := riesz_lemma_of_lt_one hF hn (by norm_num : (1:ℝ)/2<1)
    refine ⟨x.val,x.property,hxn,fun y hy => ?_⟩
    exact hxr ⟨y,eigenFlag_mono v (by omega : n≤n+1) hy⟩ hy
  choose x hx hxn hxr using hex
  exact ⟨x,hx,hxn,hxr⟩
end FlatSpectral

end

end OAI
