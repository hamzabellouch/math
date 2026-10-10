import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoreBlocks
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoreScale

namespace OAI

/-! All finite noncube frequencies in the small-coefficient range have
arbitrary logarithmic cancellation for the literal stopped sequence.
The statement is pointwise in the logarithmic norm height. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_noncube_mass
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 65536 ≤ b →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ X^2 → 8*B ≤ b^(3/4:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₀,K₁,hK₀,hK₁,hbound⟩ := stopped_noncube_core_blocks (ι := ι)
    hpnt hSW hHuxley hξ hξz hκ hH hF hJ (4*(k+2)) k (by omega)
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨C,hC,hnorm⟩ := log_power_normalization_bound (k+2)
    (show 0 < κ/20000 by positivity)
  let K := K₀+K₁*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (Real.exp 1)] with X hbound hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hlog : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlogp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hbp : 0 < b := by linarith
  let I := (largeCoreDyadicIndices ((Real.log X)^(4*(k+2))) B).card
  have hI : (I:ℝ) ≤ (4*CI)*(Real.log X)^2 := by
    apply (hcount _ B X hB hX1 hBX).trans
    calc
      _ ≤ CI*(2*Real.log X)^2 := by gcongr; linarith
      _ = _ := by ring
  have hpower : b^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤ C :=
    (stopped_length_log_power hX1 hb k).trans (hnorm X hX1)
  have hlarge := stopped_large_core_scale hbp hlogp (by positivity : 0 ≤ 4*CI)
    k hI hpower
  have hm := hbound δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left hlarge
    (show 0 ≤ K₁*B^(1/3:ℝ) by positivity)
  calc
    _ = K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        (K₁*B^(1/3:ℝ))*((I:ℝ)*
          (b*(((Real.log X)^(4*(k+2)))/5832)^(-(1/4:ℝ))+
            b^(1-1/20000:ℝ))*b) := by dsimp [I]; ring
    _ ≤ K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        (K₁*B^(1/3:ℝ))*((4*CI)*((5832:ℝ)^(1/4:ℝ)+C)*b^2/(Real.log X)^k) :=
      add_le_add_right hh _
    _ = _ := by dsimp [K]; ring

end CubicFirstMoment

end

end OAI
