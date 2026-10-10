import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCompletion
import OAI.NumberTheory.CubicGram.DyadicRecurrence

namespace OAI

/-! The actual long inverse sum has a finite, canonical norm-dyad
partition. Each nonempty block lies above half the inverse cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticLongSupport (C F : ℝ) : Finset Eisenstein :=
  (((primaryElementBall F).product (primaryElementBall F)).image
    (fun cd => cd.1*cd.2)).filter (fun e => C < norm e)

def metaplecticLongDyad (C F : ℝ) (j : ℕ) : Finset Eisenstein :=
  (metaplecticLongSupport C F).filter (fun e => Nat.log 2 (normNat e) = j)

def metaplecticLongDyads (C F : ℝ) : Finset ℕ :=
  (metaplecticLongSupport C F).image (fun e => Nat.log 2 (normNat e))

lemma metaplecticLongSupport_primary {C F : ℝ} {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : primary e := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1

lemma metaplecticLongSupport_norm {C F : ℝ} (hF : 0 ≤ F) {e : Eisenstein}
    (he : e ∈ metaplecticLongSupport C F) : norm e ≤ F^2 := by
  obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  rw [norm_mul_eq,pow_two]
  exact mul_le_mul (mem_primaryElementBall.mp hc).2 (mem_primaryElementBall.mp hd).2
    (norm_nonneg _) hF

lemma metaplecticLongDyad_norm {C F : ℝ} {j : ℕ} {e : Eisenstein}
    (he : e ∈ metaplecticLongDyad C F j) :
    primary e ∧ (2:ℝ)^j ≤ norm e ∧ norm e ≤ 2*(2:ℝ)^j := by
  obtain ⟨hs,hj⟩ := Finset.mem_filter.mp he
  have hp := metaplecticLongSupport_primary hs
  have hd : e ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨primary_ne_zero hp,hj⟩
  have hn := frequencyDyad_norm hd
  exact ⟨hp,hn.1,hn.2⟩

lemma metaplecticLongDyad_cutoff {C F : ℝ} {j : ℕ}
    (hj : j ∈ metaplecticLongDyads C F) : C < 2*(2:ℝ)^j := by
  obtain ⟨e,he,hlog⟩ := Finset.mem_image.mp hj
  have hmem : e ∈ metaplecticLongDyad C F j := Finset.mem_filter.mpr ⟨he,hlog⟩
  exact (Finset.mem_filter.mp he).2.trans_le (metaplecticLongDyad_norm hmem).2.2

lemma metaplecticLongDyads_card {C F : ℝ} (hF : 0 ≤ F) :
    (metaplecticLongDyads C F).card ≤ Nat.log 2 ⌊F^2⌋₊+1 := by
  have hsub : metaplecticLongDyads C F ⊆ Finset.range (Nat.log 2 ⌊F^2⌋₊+1) := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    simpa only [normNat_cast] using metaplecticLongSupport_norm hF he
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem metaplectic_long_completion_active (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ metaplecticLongSupport C F, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [metaplectic_long_completion_collect r ℓ W hU hB hBF hW C]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  have hp : primary e := by
    obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    exact primary_mul (mem_primaryElementBall.mp hc).1 (mem_primaryElementBall.mp hd).1
  have hCe : norm e ≤ C := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨he,lt_of_not_ge h⟩)
  rw [metaplecticTailCoefficient_zero r ℓ hp hCe,zero_mul]

lemma metaplectic_long_dyad_partition (C F : ℝ) (f : Eisenstein → ℂ) :
    (∑ e ∈ metaplecticLongSupport C F, f e) =
      ∑ j ∈ metaplecticLongDyads C F, ∑ e ∈ metaplecticLongDyad C F j, f e := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image_of_mem (fun e => Nat.log 2 (normNat e)) he) f).symm

end CubicFirstMoment

end

end OAI
