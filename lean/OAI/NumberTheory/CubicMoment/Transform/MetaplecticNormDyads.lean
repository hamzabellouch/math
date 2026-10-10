import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualFinite
import OAI.NumberTheory.CubicGram.InnerExtension

namespace OAI

/-! Canonical finite norm-dyad partition of the retained Voronoi pairs.
The integral frequency d³n has norm exactly three times N(d³ν). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticIntegralFrequency (nd : MetaplecticDualArgument × PrimaryArgument) : Eisenstein :=
  nd.2.val^3*nd.1.val

lemma metaplecticIntegralFrequency_ne_zero (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticIntegralFrequency nd ≠ 0 :=
  mul_ne_zero (pow_ne_zero 3 (primary_ne_zero nd.2.property)) nd.1.property

lemma norm_metaplecticIntegralFrequency (nd : MetaplecticDualArgument × PrimaryArgument) :
    norm (metaplecticIntegralFrequency nd) = 3*metaplecticDualNorm nd := by
  have hn : norm (metaplecticIntegralFrequency nd) = norm nd.2^3*norm nd.1 := by
    change Complex.normSq ((nd.2:ℂ)^3*(nd.1.val:ℂ)) = _
    rw [Complex.normSq_mul,map_pow]
    rfl
  rw [hn]
  unfold metaplecticDualNorm
  rw [metaplectic_frequency_norm_numerator]
  ring

def metaplecticNormDyadIndex (nd : MetaplecticDualArgument × PrimaryArgument) : ℕ :=
  Nat.log 2 (normNat (metaplecticIntegralFrequency nd))

def metaplecticNormDyad (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (j : ℕ) :
    Finset (MetaplecticDualArgument × PrimaryArgument) :=
  S.filter (fun nd => metaplecticNormDyadIndex nd = j)

def metaplecticNormDyadLength (j : ℕ) : ℝ := 2*(2:ℝ)^j/3

lemma metaplecticNormDyadLength_pos (j : ℕ) : 0 < metaplecticNormDyadLength j := by
  unfold metaplecticNormDyadLength
  positivity

lemma metaplectic_norm_dyad_bounds
    {S : Finset (MetaplecticDualArgument × PrimaryArgument)} {j : ℕ}
    {nd : MetaplecticDualArgument × PrimaryArgument} (hnd : nd ∈ metaplecticNormDyad S j) :
    metaplecticNormDyadLength j/2 ≤ metaplecticDualNorm nd ∧
      metaplecticDualNorm nd ≤ metaplecticNormDyadLength j := by
  have hmem : metaplecticIntegralFrequency nd ∈ frequencyDyad j :=
    mem_frequencyDyad.mpr ⟨metaplecticIntegralFrequency_ne_zero nd,
      (Finset.mem_filter.mp hnd).2⟩
  have hb := frequencyDyad_norm hmem
  rw [norm_metaplecticIntegralFrequency] at hb
  unfold metaplecticNormDyadLength
  constructor <;> nlinarith [hb.1,hb.2]

lemma metaplectic_norm_dyad_partition
    (S : Finset (MetaplecticDualArgument × PrimaryArgument))
    (F : MetaplecticDualArgument × PrimaryArgument → ℂ) :
    (∑ nd ∈ S, F nd) = ∑ j ∈ S.image metaplecticNormDyadIndex,
      ∑ nd ∈ metaplecticNormDyad S j, F nd := by
  unfold metaplecticNormDyad
  exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image metaplecticNormDyadIndex)
    (g := metaplecticNormDyadIndex) (fun nd hnd => by
      simp only [Finset.mem_image]
      exact ⟨nd,hnd,rfl⟩) F).symm

lemma metaplectic_norm_dyad_length_le
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) {J : ℝ}
    (hS : ∀ nd ∈ S, metaplecticDualNorm nd ≤ J) {j : ℕ}
    (hj : j ∈ S.image metaplecticNormDyadIndex) : metaplecticNormDyadLength j ≤ 2*J := by
  obtain ⟨nd,hnd,rfl⟩ := Finset.mem_image.mp hj
  have hm : nd ∈ metaplecticNormDyad S (metaplecticNormDyadIndex nd) :=
    Finset.mem_filter.mpr ⟨hnd,rfl⟩
  have hb := (metaplectic_norm_dyad_bounds hm).1
  linarith [hS nd hnd]

lemma metaplectic_norm_dyad_count
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) {J : ℝ}
    (hS : ∀ nd ∈ S, metaplecticDualNorm nd ≤ J) :
    (S.image metaplecticNormDyadIndex).card ≤ Nat.log 2 ⌊3*J⌋₊+1 := by
  apply le_trans (Finset.card_le_card (show S.image metaplecticNormDyadIndex ⊆
    Finset.range (Nat.log 2 ⌊3*J⌋₊+1) from ?_))
    (by rw [Finset.card_range])
  intro j hj
  obtain ⟨nd,hnd,rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.log_mono_right
  apply Nat.le_floor
  rw [normNat_cast,norm_metaplecticIntegralFrequency]
  linarith [hS nd hnd]

end CubicFirstMoment

end

end OAI
