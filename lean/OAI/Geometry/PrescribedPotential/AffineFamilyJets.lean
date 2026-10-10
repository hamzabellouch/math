import Mathlib
import OAI.Geometry.PrescribedPotential.QuasilinearJetBasics

namespace OAI

/-! Affine Family Jets. -/

section

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma affine_family_jets {U : Set E} (hU : IsOpen U) {f g : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (m : ℕ) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ j, j ≤ m → ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y => (1-t) • f y-t • g y) x‖ ≤ C := by
  obtain ⟨A,hA,hfa⟩ := compact_coefficient_jets hK (fun x hx => hf.contDiffAt (hU.mem_nhds (hKU hx))) m
  obtain ⟨B,hB,hgb⟩ := compact_coefficient_jets hK (fun x hx => hg.contDiffAt (hU.mem_nhds (hKU hx))) m
  refine ⟨A+B,fun j hj t ht x hx => ?_⟩
  have hf' := hf.contDiffAt (hU.mem_nhds (hKU hx))
  have hg' := hg.contDiffAt (hU.mem_nhds (hKU hx))
  have hn : (j:ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : iteratedFDeriv ℝ j ((1-t) • f-t • g) x =
      (1-t) • iteratedFDeriv ℝ j f x-t • iteratedFDeriv ℝ j g x := by
    calc
      _ = iteratedFDeriv ℝ j ((1-t) • f) x-iteratedFDeriv ℝ j (t • g) x :=
        iteratedFDeriv_sub_apply ((hf'.const_smul (1-t)).of_le hn) ((hg'.const_smul t).of_le hn)
      _ = _ := by rw [iteratedFDeriv_const_smul_apply (hf'.of_le hn),iteratedFDeriv_const_smul_apply (hg'.of_le hn)]
  change ‖iteratedFDeriv ℝ j ((1-t) • f-t • g) x‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have ha := mul_le_mul_of_nonneg_left (hfa j hj x hx) (sub_nonneg.mpr ht.2)
  have hb := mul_le_mul_of_nonneg_left (hgb j hj x hx) ht.1
  nlinarith [ht.1,ht.2]
end HigherJet

end
end

end OAI
