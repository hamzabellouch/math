import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorSequences

namespace OAI

/-! The exceptional short-factor contradictions allow conductor scales
with the required limiting exponent, without fixing the scales to exact powers. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With a fixed gap below length one, an actual first-configuration
moment cannot remain at exponent `7/3`. All subsequences are constructed. -/
theorem ShortFactorFamily.first_varying_conductor_sequence_impossible (F : ShortFactorFamily ι)
    (Y N G : ℕ → ℝ) (S : ℕ → Finset Eisenstein) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hN : ∀ j, 1 ≤ N j) (hNexp : HasPowerExponent Y N 1)
    (hS : ∀ j, ∀ p ∈ S j, gramDyad (N j) p)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.cubicValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.cubicValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.cubicValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  have hYφψ : Tendsto ((Y ∘ φ) ∘ ψ) atTop atTop :=
    (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  apply ((F.comp φ).comp ψ).first_rows_contradiction P B hYφψ
    (fun j => hN (φ (ψ j)))
    (fun j p hp => hS (φ (ψ j)) p ((hP j).2 hp))
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (by simpa only [Function.comp_def] using
      (show 0 < Y (φ (ψ j)) by linarith [hY₂ (φ (ψ j))])) _).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp ((hNexp.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)


/-- The balanced actual short-factor family also cannot retain an unsaved
moment; its row and value limits are extracted inside the proof. -/
theorem ShortFactorFamily.balanced_varying_conductor_sequence_impossible (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) (Y L G : ℕ → ℝ)
    (S : ℕ → Finset (Eisenstein × Eisenstein)) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hL : ∀ j, 1 ≤ L j) (hLexp : HasPowerExponent Y L (1/3))
    (hS : ∀ j, ∀ p ∈ S j, PrimarySquarefreePair p ∧
      norm p.1 ≤ L j ∧ norm p.2 ≤ L j)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.mixedValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.mixedValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.mixedValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  let Z : ℕ → ℝ := (Y ∘ φ) ∘ ψ
  have hZ : Tendsto Z atTop atTop := (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hZ₁ (j : ℕ) : 1 ≤ Z j := by dsimp [Z]; linarith [hY₂ (φ (ψ j))]
  have hZp (j : ℕ) : 0 < Z j := zero_lt_one.trans_le (hZ₁ j)
  let L' : ℕ → ℝ := (L ∘ φ) ∘ ψ
  have hL' (j : ℕ) : 1 ≤ L' j := hL (φ (ψ j))
  have hLexp' : HasPowerExponent Z L' (1/3) :=
    (hLexp.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hQexp : HasPowerExponent Z (fun j => (L' j)^2) (2/3) := by
    convert hLexp'.natPow 2 using 1
    norm_num
  have hP' (j : ℕ) (p : Eisenstein × Eisenstein) (hp : p ∈ P j) :
      PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ (L' j)^2 := by
    have hs := hS (φ (ψ j)) p ((hP j).2 hp)
    refine ⟨hs.1,?_⟩
    rw [pairConductor,norm_mul_eq]
    calc
      _ ≤ L' j * L' j :=
        mul_le_mul hs.2.1 hs.2.2 (norm_nonneg _) (zero_le_one.trans (hL' j))
      _ = _ := by ring
  apply ((F.comp φ).comp ψ).balanced_rows_contradiction hHuxley P B hZ
    (fun j => one_le_pow₀ (hL' j)) hL' hP'
    (fun j p hp => (hS (φ (ψ j)) p ((hP j).2 hp)).2)
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (hZp j) (-K)).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp hQexp hLexp'
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)

end CubicFirstMoment

end

end OAI
