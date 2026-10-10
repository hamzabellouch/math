import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # Applying coordinate isometries to a Hilbert sum -/

namespace KadisonKastler

noncomputable section

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]

def hilbertSumIsometryMap (S : ∀ n, E n →ₗᵢ[ℂ] F n) : lp E 2 →ₗᵢ[ℂ] lp F 2 where
  toFun f := ⟨fun n => S n (f n), (lp.memℓp f).mono' (fun n => (S n).norm_map (f n) |>.le)⟩
  map_add' f g := by
    apply lp.ext
    funext n
    exact (S n).map_add (f n) (g n)
  map_smul' c f := by
    apply lp.ext
    funext n
    exact (S n).map_smul c (f n)
  norm_map' f := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun n => (S n).norm_map (f n) |>.le)
    · exact lp.norm_mono (by norm_num) (fun n => (S n).norm_map (f n) |>.symm.le)

@[simp] theorem hilbertSumIsometryMap_apply (S : ∀ n, E n →ₗᵢ[ℂ] F n)
    (f : lp E 2) (n : ℕ) : hilbertSumIsometryMap S f n = S n (f n) := rfl

theorem hilbertSumIsometryMap_range (S : ∀ n, E n →ₗᵢ[ℂ] F n) (g : lp F 2) :
    g ∈ LinearMap.range (hilbertSumIsometryMap S).toLinearMap ↔
      ∀ n, g n ∈ LinearMap.range (S n).toLinearMap := by
  constructor
  · rintro ⟨f, rfl⟩ n
    exact ⟨f n, rfl⟩
  · intro hg
    choose f hf using hg
    have he (n : ℕ) : S n (f n) = g n := hf n
    have hm : Memℓp f 2 := (lp.memℓp g).mono' (fun n => by
      rw [← (S n).norm_map, he n])
    refine ⟨⟨f, hm⟩, ?_⟩
    apply lp.ext
    funext n
    exact hf n

end

end KadisonKastler

end OAI
