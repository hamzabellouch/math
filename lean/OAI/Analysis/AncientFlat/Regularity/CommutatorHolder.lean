import OAI.Analysis.AncientFlat.Regularity.CommutatorJets
import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open Set Filter ParabolicInterior
open scoped ContDiff
namespace ParabolicCommutator
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [FiniteDimensional ℝ V] in
theorem commutator_holder (α : ℝ) (Ω : Set (V × ℝ)) (f : ℝ → V → ℝ)
    (g : ℝ → V → E) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hf : ∀ p∈Ω, ContDiff ℝ 4 (f p.2)) (hg : ∀ p∈Ω, ContDiff ℝ 4 (g p.2))
    (hfj : ∀ n : ℕ, 1≤n → n≤4 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ n (f p.2) p.1) A)
    (hgj : ∀ n : ℕ, n≤3 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ n (g p.2) p.1) B) :
    HolderBound α Ω (fun p => commutator (f p.2) (g p.2) p.1) (30*A*B) := by
  refine ⟨?_,?_⟩
  · intro p hp
    apply (norm_commutator_le _ _ _ (hf p hp) (hg p hp) A B hA hB
      (fun n hn hn4 => (hfj n hn hn4).1 p hp) (fun n hn => (hgj n hn).1 p hp)).trans
    nlinarith [mul_nonneg hA hB]
  · intro p hp q hq
    let f₁ : V → ℝ := fun z => f p.2 (z+p.1)
    let f₂ : V → ℝ := fun z => f q.2 (z+q.1)
    let g₁ : V → E := fun z => g p.2 (z+p.1)
    let g₂ : V → E := fun z => g q.2 (z+q.1)
    have hf₁ : ContDiff ℝ 4 f₁ := (hf p hp).comp (contDiff_id.add contDiff_const)
    have hf₂ : ContDiff ℝ 4 f₂ := (hf q hq).comp (contDiff_id.add contDiff_const)
    have hg₁ : ContDiff ℝ 4 g₁ := (hg p hp).comp (contDiff_id.add contDiff_const)
    have hg₂ : ContDiff ℝ 4 g₂ := (hg q hq).comp (contDiff_id.add contDiff_const)
    let d := pdist p q^α
    have hd : 0≤d := Real.rpow_nonneg (by unfold pdist; positivity) _
    have hs : commutator (f p.2) (g p.2) p.1-commutator (f q.2) (g q.2) q.1=
        commutator (f₁-f₂) g₁ 0+commutator f₂ (g₁-g₂) 0 := by
      rw [commutator_sub_left _ _ _ _ hf₁ hf₂ hg₁,
        commutator_sub_right _ _ _ _ hf₂ hg₁ hg₂]
      simp only [f₁,f₂,g₁,g₂,commutator_translate,zero_add]
      abel
    have h1 : ‖commutator (f₁-f₂) g₁ 0‖≤15*(A*d)*B := by
      apply norm_commutator_le _ _ _ (hf₁.sub hf₂) hg₁ _ _ (mul_nonneg hA hd) hB
      · intro n hn hn4
        change ‖iteratedFDeriv ℝ n (f₁-f₂) 0‖≤A*d
        rw [iteratedFDeriv_sub (i := n) (hf₁.of_le (by exact_mod_cast hn4))
          (hf₂.of_le (by exact_mod_cast hn4)),Pi.sub_apply]
        simpa only [f₁,f₂,iteratedFDeriv_comp_add_right,zero_add] using (hfj n hn hn4).2 p hp q hq
      · intro n hn
        simpa only [g₁,iteratedFDeriv_comp_add_right,zero_add] using (hgj n hn).1 p hp
    have h2 : ‖commutator f₂ (g₁-g₂) 0‖≤15*A*(B*d) := by
      apply norm_commutator_le _ _ _ hf₂ (hg₁.sub hg₂) _ _ hA (mul_nonneg hB hd)
      · intro n hn hn4
        simpa only [f₂,iteratedFDeriv_comp_add_right,zero_add] using (hfj n hn hn4).1 q hq
      · intro n hn
        change ‖iteratedFDeriv ℝ n (g₁-g₂) 0‖≤B*d
        rw [iteratedFDeriv_sub (i := n) (hg₁.of_le (by exact_mod_cast (show n≤4 by omega)))
          (hg₂.of_le (by exact_mod_cast (show n≤4 by omega))),Pi.sub_apply]
        simpa only [g₁,g₂,iteratedFDeriv_comp_add_right,zero_add] using (hgj n hn).2 p hp q hq
    rw [hs]
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp [d]; ring))
end ParabolicCommutator

end

end OAI
