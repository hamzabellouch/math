import Mathlib
import OAI.Probability.SKRatio.Quantization.BinForm
import OAI.Probability.SKRatio.Quantization.BinNet

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def binFormBad {n : ℕ} (β : ℝ) (h : α → ℝ) (σ : Fin n → α)
    (K C : ℝ) : Set ((Fin n × Fin n) → ℝ) :=
  {g | euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n)≤K ∧
    ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
      p ⬝ᵥ ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
        (fun i => v (h (σ i))*p i))+ correctedForm β (fun i => h (σ i)) p}

theorem binForm_tail {β K a : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
    (h : α → ℝ) :
    ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n) (σ : Fin n → α),
      (∀ d, 2≤count σ d) → ∀ C : ℝ,
      (∀ z : Parameters α, finiteV β (binT σ) h z≤C) →
      (standardArrayLaw (Fin n × Fin n)).real (binFormBad β h σ K (C+2*a)) ≤
        N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  obtain ⟨F,hF⟩ := binForm_finite_net β h hK ha
  refine ⟨F.card,?_⟩
  intro n hn σ hc C hC
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have : Nonempty (Directions σ) := directions_nonempty hc
  let E := fun z : Parameters α => {g : (Fin n × Fin n) → ℝ |
    finiteGaussian β (binT σ) (fun d => v (h d)) z+a ≤
      projectedSup β (fun i => v (h (σ i))) (vectorOf z : Directions σ → Fin n → ℝ) g}
  have hsub : binFormBad β h σ K (C+2*a) ⊆ ⋃ z∈F, E z := by
    intro g hg
    obtain ⟨hM,p,hp,hbad⟩ := hg
    obtain ⟨u,hu⟩ := vectorOf_surjective hc p hp
    let z := parametersOf σ p hp
    obtain ⟨z',hz',hnet⟩ := hF hn σ hc _ hM z u
    have he : correctedForm β (fun i => h (σ i)) p=finiteA β (binT σ) h z := by
      rw [←hu]
      exact correctedForm_bin (fun d => lt_of_lt_of_le (by norm_num) (hc d)) β h z u
    change vectorOf z u=p at hu
    rw [hu] at hnet
    rw [he] at hbad
    have hsup := le_projectedSup β (fun i => v (h (σ i)))
      (vectorOf_continuous z') g u
    have hCZ := hC z'
    dsimp only [finiteV] at hCZ
    have htail : g∈E z' := by
      change finiteGaussian β (binT σ) (fun d => v (h d)) z'+a ≤
        projectedSup β (fun i => v (h (σ i))) (vectorOf z' : Directions σ → Fin n → ℝ) g
      have hS : (vectorOf z' u ⬝ᵥ
          ((fieldProjection n*(β • goe g)*fieldProjection n)*ᵥ
            (fun i => v (h (σ i))*vectorOf z' u i))) ≤
          projectedSup β (fun i => v (h (σ i)))
            (vectorOf z' : Directions σ → Fin n → ℝ) g := hsup
      have hT := hbad.trans_le hnet
      have hU := _root_.add_le_add_left (_root_.add_le_add_left hS (finiteA β (binT σ) h z')) a
      have hV := hT.trans_le hU
      linarith only [hV,hCZ]
    exact Set.mem_iUnion.mpr ⟨z',Set.mem_iUnion.mpr ⟨hz',htail⟩⟩
  calc
    _ ≤ (standardArrayLaw (Fin n × Fin n)).real (⋃ z∈F, E z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z∈F, (standardArrayLaw (Fin n × Fin n)).real (E z) := measureReal_biUnion_finset_le F E
    _ ≤ ∑ _z∈F, exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
      apply Finset.sum_le_sum
      intro z _
      exact normalized_projected_tail hn hc (fun d => v (h d))
        (fun d => by rw [abs_of_nonneg (v_pos _).le]; exact v_le_one _) hβ z ha.le
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SKRatio.Bins

end

end OAI
