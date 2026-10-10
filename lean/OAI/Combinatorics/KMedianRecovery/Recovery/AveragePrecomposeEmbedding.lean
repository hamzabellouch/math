import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DyadicExponent
import OAI.Combinatorics.KMedianRecovery.Sampling.ProbabilityProd

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω] [Nonempty Ω]
  [DecidableEq I] [DecidableEq J]

lemma average_precompose_embedding (e : I ↪ J) (X : (I → Ω) → ℝ) :
    average (fun seed : J → Ω => X (fun i => seed (e i))) = average X := by
  classical
  let Q : Finset J := Finset.univ.image e
  let eqv : I ≃ ↥Q :=
    { toFun := fun i => ⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
      invFun := fun j => Classical.choose (Finset.mem_image.mp j.property)
      left_inv := by
        intro i
        apply e.injective
        exact (Classical.choose_spec (Finset.mem_image.mp
          (show e i ∈ Q from Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).2
      right_inv := by
        intro j
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp j.property)).2 }
  let ee : (↥Q → Ω) ≃ (I → Ω) :=
    { toFun := fun seed i => seed (eqv i)
      invFun := fun seed j => seed (eqv.symm j)
      left_inv := by intro s; funext j; simp
      right_inv := by intro s; funext i; simp }
  calc
    _ = average (fun seed : ↥Q → Ω => X (ee seed)) :=
      average_pi_restrict Q (fun seed => X (ee seed))
    _ = average X := average_equiv ee _ X (fun _ => rfl)

lemma probability_precompose_embedding (e : I ↪ J) (E : (I → Ω) → Prop) :
    probability (fun seed : J → Ω => E (fun i => seed (e i))) = probability E := by
  classical
  exact average_precompose_embedding e (fun seed => if E seed then 1 else 0)

lemma probability_pad {n : ℕ} (hn : Fintype.card I ≤ n) (E : (I → Bool) → Prop) :
    probability (fun seed : Fin n → Bool => E
      (fun i => seed (Fin.castLE hn (Fintype.equivFin I i)))) = probability E := by
  exact probability_precompose_embedding
    ⟨fun i => Fin.castLE hn (Fintype.equivFin I i),
      (Fin.castLE_injective hn).comp (Fintype.equivFin I).injective⟩ E

end MetricKMedianRecovery.FiniteSampling

namespace MetricKMedianRecovery.Categorical
lemma stepExponent_mono {a m : ℕ} (ham : a ≤ m) (epsilon : ℝ) :
    stepExponent a epsilon ≤ stepExponent m epsilon := by
  apply Nat.clog_mono_right
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right
  · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr ham) _
  · unfold tolerance
    positivity

lemma sampleCount_mono {q q' a m : ℕ} (hq : q ≤ q') (ha : a ≤ m) (epsilon : ℝ) :
    sampleCount q a epsilon ≤ sampleCount q' m epsilon := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right
  · have he := stepExponent_mono ha epsilon
    have hpow : (2 ^ stepExponent a epsilon : ℕ) ≤ 2 ^ stepExponent m epsilon := by
      gcongr
    gcongr
  · unfold tolerance
    positivity
end MetricKMedianRecovery.Categorical

end OAI
