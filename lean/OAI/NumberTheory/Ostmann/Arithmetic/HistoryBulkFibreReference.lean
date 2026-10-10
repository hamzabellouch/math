import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreReferenceBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreReference
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in

theorem fixed_reference_zero_extension
    (w : ι → ℝ) (v : κ → ℝ) (F T : ι → κ → ℂ) (Valid : ι → κ → Prop)
    (hsource : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y ≠ 0 → Valid x y)
    (hconverse : ∀ x y, w x ≠ 0 → v y ≠ 0 → T x y ≠ 0 → Valid x y)
    (htransport : ∀ x y, w x ≠ 0 → v y ≠ 0 → Valid x y → F x y = T x y) :
    ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y = T x y := by
  classical
  intro x y hx hy
  by_cases hs : Valid x y
  · exact htransport x y hx hy hs
  · have hf : F x y = 0 := by
      by_contra hn
      exact hs (hsource x y hx hy hn)
    have ht : T x y = 0 := by
      by_contra hn
      exact hs (hconverse x y hx hy hn)
    exact hf.trans ht.symm

theorem originalMean_eq_zero_or_fixed_reference
    (w : ι → ℝ) (v : κ → ℝ) (F : ι → κ → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (Valid : ι → κ → Prop)
    (T : ι → κ → ι → κ → ℂ)
    (hsource : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y ≠ 0 → Valid x y)
    (hconverse : ∀ r s, Valid r s → ∀ x y,
      w x ≠ 0 → v y ≠ 0 → T r s x y ≠ 0 → Valid x y)
    (htransport : ∀ r s, Valid r s → ∀ x y,
      w x ≠ 0 → v y ≠ 0 → Valid x y → F x y = T r s x y) :
    originalMean w v F = 0 ∨
      ∃ r s, 0 < w r ∧ 0 < v s ∧ F r s ≠ 0 ∧ Valid r s ∧
        (∀ x y, w x ≠ 0 → v y ≠ 0 → F x y = T r s x y) ∧
        originalMean w v F = originalMean w v (T r s) := by
  rcases originalMean_eq_zero_or_reference w v F hw hv Valid hsource with hz | ⟨r,s,hr,hs,hf,hvalid⟩
  · exact Or.inl hz
  · have hfixed := fixed_reference_zero_extension w v F (T r s) Valid hsource
      (hconverse r s hvalid) (htransport r s hvalid)
    exact Or.inr ⟨r,s,hr,hs,hf,hvalid,hfixed,originalMean_congr w v F (T r s) hfixed⟩

omit [Fintype ι] [Fintype κ] in

theorem fixed_references_weighted_eq
    (w : ι → ℝ) (v : κ → ℝ) (F T U : ι → κ → ℂ)
    (hT : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y = T x y)
    (hU : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y = U x y) :
    ∀ x y, ((w x*v y:ℝ):ℂ)*T x y = ((w x*v y:ℝ):ℂ)*U x y := by
  intro x y
  by_cases hx : w x = 0
  · simp only [hx,zero_mul,Complex.ofReal_zero]
  by_cases hy : v y = 0
  · simp only [hy,mul_zero,Complex.ofReal_zero,zero_mul]
  rw [←hT x y hx hy,←hU x y hx hy]

end Ostmann.Arithmetic.HistoryBulkFibreReference

end

end OAI
