import OAI.Probability.InvariantIsing.Core.Model
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! The sup-to-norm operator maximum is attained at an Ising vertex. -/
noncomputable section
open Set
open scoped Classical
namespace InvariantIsing

lemma spinSigns_range (N : ℕ) :
    Set.range (fun σ : Spin N => fun i => spinValue (σ i))=
      Set.univ.pi (fun _ : Fin N => ({(-1 : ℝ),1} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨σ,rfl⟩ i _
    cases h : σ i <;> simp [spinValue,h]
  · intro hx
    refine ⟨fun i => decide (x i=1),?_⟩
    funext i
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi
    rcases hi with hi|hi <;> norm_num [spinValue,hi]

lemma mem_spinSigns_convexHull {N : ℕ} (x : Fin N → ℝ) (hx : ‖x‖ ≤ 1) :
    x∈convexHull ℝ (Set.range (fun σ : Spin N => fun i => spinValue (σ i))) := by
  rw [spinSigns_range,convexHull_pi]
  intro i _
  rw [convexHull_pair,segment_eq_Icc (by norm_num : (-1 : ℝ)≤1)]
  exact abs_le.mp ((pi_norm_le_iff_of_nonneg zero_le_one).mp hx i)

lemma cube_operator_norm {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : (Fin N → ℝ) →L[ℝ] E) :
    ‖T‖=Finset.univ.sup' Finset.univ_nonempty
      (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖) := by
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖)
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (Finset.le_sup' (fun σ : Spin N => ‖T (fun i => spinValue (σ i))‖)
      (Finset.mem_univ (fun _ => false)))
  have hball (x : Fin N → ℝ) (hx : ‖x‖≤1) : ‖T x‖≤M := by
    have hc := (convexOn_univ_norm (E := E)).comp_linearMap T.toLinearMap
    obtain ⟨y,⟨σ,rfl⟩,hσ⟩ := hc.exists_ge_of_mem_convexHull
      (show Set.range (fun σ : Spin N => fun i => spinValue (σ i)) ⊆
        T.toLinearMap ⁻¹' Set.univ from fun _ _ => Set.mem_univ _)
      (mem_spinSigns_convexHull x hx)
    exact hσ.trans (Finset.le_sup'
      (fun τ : Spin N => ‖T (fun i => spinValue (τ i))‖) (Finset.mem_univ σ))
  apply le_antisymm
  · apply T.opNorm_le_bound' hM
    intro x hx
    have hn : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hb := hball (‖x‖⁻¹ • x) (by simp [norm_smul,hn.ne'])
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hb
    simpa only [mul_comm] using (inv_mul_le_iff₀ hn).mp hb
  · apply Finset.sup'_le
    intro σ _
    have hs : ‖(fun i => spinValue (σ i))‖ ≤ (1 : ℝ) :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp [Real.norm_eq_abs]
    exact (T.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg T) hs)

end InvariantIsing

end

end OAI
