import Mathlib
import OAI.Geometry.PrescribedRicci.DeterminantJet
import OAI.Geometry.PrescribedRicci.JetRemainderBound
import OAI.Geometry.PrescribedRicci.UniformSchwartz

namespace OAI

/-! Uniform Determinant Remainder. -/

section

 

noncomputable section
open Set Finset _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical BigOperators ENNReal SchwartzMap
namespace TameInterpolation
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ} [Nonempty (Fin n)] {Z : Type*}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Nonempty ι] in
lemma monoEval_compact (e : ι → E) (f : Fin n → E → ℂ)
    (hc : ∀ i, HasCompactSupport (f i)) (s : Fin n → List ι) :
    HasCompactSupport (monoEval e f s) := by
  let i : Fin n := Classical.choice inferInstance
  apply (cword_compact e (hc i) (s i)).mono
  intro x hx
  apply Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)

lemma list_uniformLp {ν : Type*} (L : List ν) (F : ν → Z → E → ℂ)
    (hf : ∀ a ∈ L, ∀ z, MemLp (F a z) 2 volume)
    (hb : ∀ a ∈ L, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, lpNorm (F a z) 2 volume ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, lpNorm (fun x => (L.map (fun a => F a z x)).sum) 2 volume ≤ C := by
  induction L with
  | nil => exact ⟨0,le_rfl,fun z => by simp⟩
  | cons a L ih =>
    obtain ⟨C,hC,hc⟩ := hb a (by simp)
    obtain ⟨B,hB,hb'⟩ := ih (fun b h => hf b (List.mem_cons_of_mem a h))
      (fun b h => hb b (List.mem_cons_of_mem a h))
    refine ⟨C+B,add_nonneg hC hB,fun z => ?_⟩
    simp only [List.map_cons,List.sum_cons]
    exact (lpNorm_add_le (hf a (by simp) z) (by norm_num)).trans (add_le_add (hc z) (hb' z))

lemma detJetRemainder_uniform_bound (e : ι → E)
    (F : Z → Fin n → Fin n → 𝓢(E,ℂ))
    (hc : ∀ z i j, HasCompactSupport (F z i j : E → ℂ)) (ws : List ι)
    (h0 : ∀ σ : Equiv.Perm (Fin n), ∃ A : ℝ, 0 ≤ A ∧ ∀ z,
      familyJetNorm e (realComponents (initialJet e (fun i x => F z (σ i) i x))) 0 ∞ ≤ A)
    (hS : ∀ i j, UniformSobolev ((ws.length:ℝ)-1) (fun z => F z i j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      lpNorm (detJetRemainder e (fun x i j => F z i j x) ws) 2 volume ≤ C := by
  have hσ (σ : Equiv.Perm (Fin n)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      lpNorm (fun x => ((monoRemainder ws).map
        (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) 2 volume ≤ C := by
    obtain ⟨A,hA,ha⟩ := h0 σ
    apply list_uniformLp
    · intro s hs z
      exact (monoEval_smooth e _ (fun i => (F z (σ i) i).smooth') s).continuous.memLp_of_hasCompactSupport
        (monoEval_compact e _ (fun i => hc z (σ i) i) s)
    · intro s hs
      apply monoRemainder_uniform_bound e _ (fun z i => (F z (σ i) i).smooth')
        (fun z i => hc z (σ i) i) ws s hs hA ha
      intro j hj
      have hlen : 2 ≤ ws.length := by
        cases ws with
        | nil => simp [monoRemainder] at hs
        | cons a ws =>
          cases ws with
          | nil => simp [monoRemainder] at hs
          | cons b ws => simp
      have hjs : (j:ℝ)+1 ≤ (ws.length:ℝ)-1 := by
        have hh : j+2 ≤ ws.length := by omega
        have hh' : (j:ℝ)+2 ≤ (ws.length:ℝ) := by exact_mod_cast hh
        linarith only [hh']
      obtain ⟨B,hB,hb⟩ := initialJet_sobolev_bound (κ:=Fin n) e j ((ws.length:ℝ)-1) hjs
      choose C hC hcb using fun i => hS (σ i) i
      refine ⟨B*∑ i, C i,mul_nonneg hB (Finset.sum_nonneg fun i _ => hC i),fun z => ?_⟩
      exact (hb (fun i => F z (σ i) i)).trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => hcb i z) hB)
  choose C hC hcb using hσ
  refine ⟨∑ σ : Equiv.Perm (Fin n), ‖(Equiv.Perm.sign σ : ℂ)‖*C σ,
    Finset.sum_nonneg (fun σ _ => mul_nonneg (norm_nonneg _) (hC σ)),fun z => ?_⟩
  unfold detJetRemainder
  have hm (σ : Equiv.Perm (Fin n)) : MemLp (fun x => (Equiv.Perm.sign σ : ℂ)*
      ((monoRemainder ws).map (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) 2 volume := by
    have hs : ∀ L : List (Fin n → List ι), MemLp (fun x => (L.map
        (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) 2 volume := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        exact ((monoEval_smooth e _ (fun i => (F z (σ i) i).smooth') a).continuous.memLp_of_hasCompactSupport
          (monoEval_compact e _ (fun i => hc z (σ i) i) a)).add ih
    exact (hs _).const_mul _
  have hh := lpNorm_sum_le (s:=Finset.univ) (fun σ _ => hm σ) (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have heval : (∑ σ : Equiv.Perm (Fin n), fun x => (Equiv.Perm.sign σ : ℂ)*((monoRemainder ws).map
      (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) =
      (fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ)*((monoRemainder ws).map
      (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) := by
    funext x
    exact Finset.sum_apply _ _ _
  rw [heval] at hh
  apply hh.trans
  apply Finset.sum_le_sum
  intro σ _
  have he : (fun x => (Equiv.Perm.sign σ : ℂ)*((monoRemainder ws).map
      (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) =
      (Equiv.Perm.sign σ : ℂ) • (fun x => ((monoRemainder ws).map
      (fun s => monoEval e (fun i x => F z (σ i) i x) s x)).sum) := rfl
  rw [he,lpNorm_const_smul]
  exact mul_le_mul_of_nonneg_left (hcb σ z) (norm_nonneg _)
end TameInterpolation

end
end

end OAI
