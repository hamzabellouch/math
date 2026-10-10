import Mathlib
import OAI.Computability.VertexCover.Analysis.IntegralUpdate
import OAI.Computability.VertexCover.Analysis.PrivateMassSumHits

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover
open MeasureTheory

theorem integrable_finiteMean {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : α → Ω → ℝ) (hF : ∀ a, Integrable (F a) μ) :
    Integrable (fun x => finiteMean (fun a => F a x)) μ := by
  classical
  exact (integrable_finsetSum Finset.univ (fun a _ => hF a)).div_const _

theorem integral_finiteMean {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : α → Ω → ℝ) (hF : ∀ a, Integrable (F a) μ) :
    (∫ x, finiteMean (fun a => F a x) ∂μ) = finiteMean (fun a => ∫ x, F a x ∂μ) := by
  classical
  unfold finiteMean
  rw [integral_div, integral_finsetSum _ (fun a _ => hF a)]

end VertexCover

namespace VertexCover.LabelCover
open MeasureTheory

noncomputable def ownTotalEnergy (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : ℝ :=
  ∑ j : J, ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
    ∑ k, (Φ.ownGradient J frozen c0 A hA j
      (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2)
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))

theorem ownEnergy_integral_le_mass (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (j : J) {β : ℝ} (hβ : 0 < β) :
    (∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∑ k, (Φ.ownGradient J frozen c0 A hA j
        (Φ.query (Φ.spliceSeeds J frozen hidden) j) s k)^2)
          ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d))) ≤ β/2 +
    VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J) := by
  classical
  let μ := VertexCover.Cube.law (Fin (Φ.WeightDimension d))
  let R : Φ.HiddenSeeds J → (Fin (Φ.WeightDimension d) → ℝ) → ℝ := fun hidden s =>
    ∫ other, Φ.privateMass J frozen c0 A hA β hidden
      (Function.update other j s) j ∂Φ.batchLaw J
  have hR : ∀ hidden, Integrable (R hidden) μ := by
    intro hidden
    have hp := VertexCover.Product.update_measurePreserving μ j
    have hf := hp.integrable_comp_of_integrable
      (Φ.privateMass_integrable J frozen c0 A hA β hidden j)
    exact hf.integral_prod_left
  have ht : ∀ hidden, (∫ s, R hidden s ∂μ) =
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J := by
    intro hidden
    exact VertexCover.Product.integral_update μ j
      (Φ.privateMass_integrable J frozen c0 A hA β hidden j)
  have hI := VertexCover.integrable_finiteMean μ R hR
  calc
    _ ≤ ∫ s, β/2 + VertexCover.finiteMean (fun hidden => R hidden s) ∂μ := by
      apply integral_mono_of_nonneg
      · apply Filter.Eventually.of_forall
        intro s
        exact div_nonneg (Finset.sum_nonneg (fun hidden _ =>
          Finset.sum_nonneg (fun k _ => sq_nonneg _))) (Nat.cast_nonneg _)
      · exact (integrable_const _).add hI
      · exact Filter.Eventually.of_forall (fun s =>
          Φ.ownEnergy_le_resampled_mass J frozen c0 A hA j s hβ)
    _ = β/2 + VertexCover.finiteMean (fun hidden => ∫ s, R hidden s ∂μ) := by
      rw [integral_add (integrable_const _) hI, VertexCover.integral_finiteMean μ R hR]
      simp only [integral_const, probReal_univ, one_smul]
    _ = _ := by simp only [ht]

theorem ownTotalEnergy_le_hits (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    {β : ℝ} (hβ : 0 < β) :
    Φ.ownTotalEnergy J frozen c0 A hA ≤ (J.card : ℝ)*β/2 +
      ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
          (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J := by
  classical
  let mass := fun (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) =>
    ∑ j : J, Φ.privateMass J frozen c0 A hA β hidden s j
  have hm : ∀ hidden, Integrable (mass hidden) (Φ.batchLaw J) := fun hidden =>
    integrable_finsetSum _ (fun j _ => Φ.privateMass_integrable J frozen c0 A hA β hidden j)
  have he : (∑ j : J, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J)) =
      ∫ s, VertexCover.finiteMean (fun hidden => mass hidden s) ∂Φ.batchLaw J := by
    rw [VertexCover.integral_finiteMean _ mass hm]
    simp only [mass, integral_finsetSum _ (fun j _ =>
      Φ.privateMass_integrable J frozen c0 A hA β _ j)]
    exact (VertexCover.finiteMean_sum _).symm
  have hh : (∫ s, VertexCover.finiteMean (fun hidden => mass hidden s) ∂Φ.batchLaw J) ≤
      ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        (Φ.listHitMaximum (Φ.ownPrivateLists J frozen c0 A hA s β)
          (Φ.spliceSeeds J frozen hidden) J : ℝ)) ∂Φ.batchLaw J := by
    apply integral_mono_of_nonneg
    · apply Filter.Eventually.of_forall
      intro s
      exact div_nonneg (Finset.sum_nonneg (fun hidden _ => Finset.sum_nonneg
        (fun j _ => Φ.privateMass_nonneg J frozen c0 A hA β hidden s j))) (Nat.cast_nonneg _)
    · exact VertexCover.integrable_finiteMean _ _ (fun hidden =>
        Φ.ownPrivateLists_hits_integrable J frozen (Φ.spliceSeeds J frozen hidden) c0 A hA β)
    · exact Filter.Eventually.of_forall (fun s => VertexCover.finiteMean_mono
        (fun hidden => Φ.privateMass_sum_le_hits J frozen c0 A hA β hidden s))
  calc
    _ ≤ ∑ j : J, (β/2 + VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
        ∫ s, Φ.privateMass J frozen c0 A hA β hidden s j ∂Φ.batchLaw J)) :=
      Finset.sum_le_sum (fun j _ => Φ.ownEnergy_integral_le_mass J frozen c0 A hA j hβ)
    _ = (J.card : ℝ)*β/2 + ∫ s, VertexCover.finiteMean (fun hidden => mass hidden s)
        ∂Φ.batchLaw J := by
      rw [Finset.sum_add_distrib, he]
      simp [mul_div_assoc]
    _ ≤ _ := add_le_add le_rfl hh

theorem ownTotalEnergy_no_upper (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m)
    (J : Finset (Fin (Parameters.d m))) (hJ : J.card = Parameters.h m)
    (frozen : Φ.Seeds (Parameters.d m)) (c0 : Φ.Coordinate (Parameters.d m) → ℝ)
    (A : Finset (Φ.Coordinate (Parameters.d m) → ℝ)) (hA : A.Nonempty) :
    Φ.ownTotalEnergy J frozen c0 A hA < 7/2 := by
  have hm0 : 0 < m := by omega
  have hβ := (Parameters.positive m hm0).2.1
  have he := Φ.ownTotalEnergy_le_hits J frozen c0 A hA hβ
  have hz := Φ.ownPrivateLists_decoding_upper m hm hval J hJ frozen c0 A hA
  have hc : (J.card : ℝ)*Parameters.β m/2 = 2 := by
    rw [hJ, mul_comm]
    exact Parameters.β_h m hm0
  rw [hc] at he
  linarith

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
