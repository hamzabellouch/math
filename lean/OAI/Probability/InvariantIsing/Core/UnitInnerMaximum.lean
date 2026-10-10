import OAI.Probability.InvariantIsing.Core.UnitBilinearNorm

namespace OAI

/-! Unit linear tests recover the norm, including the zero vector. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace InvariantIsing

lemma norm_eq_iSup_unitInner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty (UnitVector E)] (w : E) : ‖w‖ = ⨆ u : UnitVector E, ⟪u.1,w⟫ := by
  have hb : BddAbove (range (fun u : UnitVector E => ⟪u.1,w⟫)) :=
    ⟨‖w‖,by rintro _ ⟨u,rfl⟩; simpa only [u.2,one_mul] using real_inner_le_norm u.1 w⟩
  have hn : 0 ≤ ⨆ u : UnitVector E, ⟪u.1,w⟫ := by
    let u : UnitVector E := Classical.choice inferInstance
    let un : UnitVector E := ⟨-u.1,by simp only [norm_neg,u.2]⟩
    have h₁ := le_ciSup hb u
    have h₂ := le_ciSup hb un
    change ⟪-u.1,w⟫ ≤ _ at h₂
    rw [inner_neg_left] at h₂
    linarith
  apply le_antisymm
  · by_cases hz : w = 0
    · simpa only [hz,norm_zero] using hn
    have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let u : UnitVector E := ⟨‖w‖⁻¹ • w,by simp [norm_smul,hnorm]⟩
    have hh := le_ciSup hb u
    change ⟪‖w‖⁻¹ • w,w⟫ ≤ _ at hh
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_mul_norm,
      ← mul_assoc,inv_mul_cancel₀ hnorm,one_mul] using hh
  · exact ciSup_le (fun u => by simpa only [u.2,one_mul] using real_inner_le_norm u.1 w)

lemma unitInner_prefix_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty (UnitVector E)] (s : ℕ → UnitVector E) (hs : DenseRange s) (w : E) :
    Tendsto (prefixMaximum (fun i => ⟪(s i).1,w⟫)) atTop (𝓝 ‖w‖) := by
  have ht := dense_prefixMaximum_tendsto s hs (fun u => ⟪u.1,w⟫)
    (by fun_prop) ⟨‖w‖,by
      rintro _ ⟨u,rfl⟩
      simpa only [u.2,one_mul] using real_inner_le_norm u.1 w⟩
  rw [← norm_eq_iSup_unitInner] at ht
  exact ht

end InvariantIsing

end

end OAI
