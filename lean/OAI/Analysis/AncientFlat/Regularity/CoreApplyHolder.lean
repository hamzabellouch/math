import OAI.Analysis.AncientFlat.Profile.SphereJetBounds
import OAI.Analysis.AncientFlat.Geometry.InteriorCore
import OAI.Analysis.AncientFlat.Regularity.LowerOrderHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCore
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma apply_jet_product_bound (f : V → E →L[ℝ] F) (g : V → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : V) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hb : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j f x‖≤A)
    (hc : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j g x‖≤B) :
    ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (fun y => f y (g y)) x‖≤4*A*B := by
  intro j hj
  have he := norm_iteratedFDeriv_clm_apply hf hg x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  apply he.trans
  calc
    _ ≤ ∑ i∈Finset.range (j+1), ((j.choose i:ℕ):ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb i (by omega)) (Nat.cast_nonneg (j.choose i)))
        (hc (j-i) (by omega)) (norm_nonneg _) (by positivity)
    _ ≤ 4*A*B := by
      interval_cases j <;> norm_num [Finset.sum_range_succ,Nat.choose] <;>
        nlinarith [mul_nonneg hA hB]
lemma apply_jet_holder {α A B : ℝ} {Ω : Set (V × ℝ)}
    (f : ℝ → V → E →L[ℝ] F) (g : ℝ → V → E)
    (hf : ∀ p∈Ω, ContDiff ℝ ∞ (f p.2)) (hg : ∀ p∈Ω, ContDiff ℝ ∞ (g p.2))
    (hA : 0≤A) (hB : 0≤B)
    (hb : ∀ j : ℕ, j≤2 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (f p.2) p.1) A)
    (hc : ∀ j : ℕ, j≤2 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (g p.2) p.1) B) :
    ∀ j : ℕ, j≤2 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ j (fun y => f p.2 y (g p.2 y)) p.1) (8*A*B) := by
  intro j hj
  constructor
  · intro p hp
    exact (apply_jet_product_bound _ _ (hf p hp) (hg p hp) p.1 A B hA hB
      (fun i hi => (hb i hi).1 p hp) (fun i hi => (hc i hi).1 p hp) j hj).trans (by nlinarith [mul_nonneg hA hB])
  · intro p hp q hq
    let f₁ : V → E →L[ℝ] F := fun z => f p.2 (z+p.1)
    let f₂ : V → E →L[ℝ] F := fun z => f q.2 (z+q.1)
    let g₁ : V → E := fun z => g p.2 (z+p.1)
    let g₂ : V → E := fun z => g q.2 (z+q.1)
    have hf₁ : ContDiff ℝ ∞ f₁ := (hf p hp).comp (contDiff_id.add contDiff_const)
    have hf₂ : ContDiff ℝ ∞ f₂ := (hf q hq).comp (contDiff_id.add contDiff_const)
    have hg₁ : ContDiff ℝ ∞ g₁ := (hg p hp).comp (contDiff_id.add contDiff_const)
    have hg₂ : ContDiff ℝ ∞ g₂ := (hg q hq).comp (contDiff_id.add contDiff_const)
    let d := pdist p q^α
    have hd : 0≤d := Real.rpow_nonneg (by unfold pdist; positivity) _
    have hs : (fun z => f₁ z (g₁ z))-(fun z => f₂ z (g₂ z))=
        (fun z => (f₁-f₂) z (g₁ z))+(fun z => f₂ z ((g₁-g₂) z)) := by
      funext z
      simp only [Pi.sub_apply,Pi.add_apply,sub_apply,map_sub]
      abel
    have h₁ : ‖iteratedFDeriv ℝ j (fun z => (f₁-f₂) z (g₁ z)) 0‖≤4*(A*d)*B := by
      apply apply_jet_product_bound _ _ (hf₁.sub hf₂) hg₁ 0 (A*d) B (mul_nonneg hA hd) hB _ _ j hj
      · intro i hi
        change ‖iteratedFDeriv ℝ i (f₁-f₂) 0‖ ≤ A*d
        rw [iteratedFDeriv_sub (hf₁.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i))
          (hf₂.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),Pi.sub_apply]
        simpa only [f₁,f₂,iteratedFDeriv_comp_add_right,zero_add] using (hb i hi).2 p hp q hq
      · intro i hi
        simpa only [g₁,iteratedFDeriv_comp_add_right,zero_add] using (hc i hi).1 p hp
    have h₂ : ‖iteratedFDeriv ℝ j (fun z => f₂ z ((g₁-g₂) z)) 0‖≤4*A*(B*d) := by
      apply apply_jet_product_bound _ _ hf₂ (hg₁.sub hg₂) 0 A (B*d) hA (mul_nonneg hB hd) _ _ j hj
      · intro i hi
        simpa only [f₂,iteratedFDeriv_comp_add_right,zero_add] using (hb i hi).1 q hq
      · intro i hi
        change ‖iteratedFDeriv ℝ i (g₁-g₂) 0‖ ≤ B*d
        rw [iteratedFDeriv_sub (hg₁.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i))
          (hg₂.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),Pi.sub_apply]
        simpa only [g₁,g₂,iteratedFDeriv_comp_add_right,zero_add] using (hc i hi).2 p hp q hq
    have hsub := iteratedFDeriv_sub (i := j)
      ((hf₁.clm_apply hg₁).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
      ((hf₂.clm_apply hg₂).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
    have hadd := iteratedFDeriv_add (i := j)
      (((hf₁.sub hf₂).clm_apply hg₁).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
      ((hf₂.clm_apply (hg₁.sub hg₂)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
    have hh : iteratedFDeriv ℝ j (fun y => f p.2 y (g p.2 y)) p.1-
        iteratedFDeriv ℝ j (fun y => f q.2 y (g q.2 y)) q.1=
        iteratedFDeriv ℝ j (fun z => (f₁-f₂) z (g₁ z)) 0+
        iteratedFDeriv ℝ j (fun z => f₂ z ((g₁-g₂) z)) 0 := by
      have he := congrFun hsub 0
      rw [hs] at he
      simp only [Pi.sub_apply] at he
      rw [hadd,Pi.add_apply] at he
      have he₁ := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => f p.2 y (g p.2 y)) j p.1 0
      have he₂ := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => f q.2 y (g q.2 y)) j q.1 0
      change iteratedFDeriv ℝ j (fun x => f p.2 (x+p.1) (g p.2 (x+p.1))) 0 = _ at he₁
      change iteratedFDeriv ℝ j (fun x => f q.2 (x+q.1) (g q.2 (x+q.1))) 0 = _ at he₂
      dsimp only [f₁,f₂,g₁,g₂] at he ⊢
      simp only [zero_add] at he₁ he₂
      rw [he₁,he₂] at he
      exact he.symm
    rw [hh]
    exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by dsimp [d]; ring))
end CompactCore

end

end OAI
