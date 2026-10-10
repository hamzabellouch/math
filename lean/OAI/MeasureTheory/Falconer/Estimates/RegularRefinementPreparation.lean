import OAI.MeasureTheory.Falconer.Estimates.BuildRegularRefinement

namespace OAI

/-! Construct the frozen refinement from the original regular point set and
fine pencils. No coarse-cover smallness is used in this preparation. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem regular_refinement_preparation (n : ℕ) {s t K D : ℝ}
    (hn : 3 ≤ n) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 2)
    (hK : 1 ≤ K) (hKD : K ≤ D) (hD : 80 ≤ D)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPsmall : ∀ p ∈ P, |p 0| ≤ 1/8 ∧ |p 1| ≤ 1/8)
    (hPball : NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) t K P)
    (hV : ∀ p ∈ P, 1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((V p).card:ℝ) ∧
      ((V p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^n)^2) p l)
    (hJp : (Nat.log 2 P.card+1:ℕ) ≤ D)
    (hJv : (Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ) ≤ D)
    (hJall : (Nat.log 2 (13*(P.biUnion V).card)+1:ℕ) ≤ D)
    (hpoint : ((P.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ K/(1/(2:ℝ)^n)^t) :
    Nonempty (RegularRefinementData n s t (D^40) P V) := by
  let Δ := 1/(2:ℝ)^n
  let ρ := 1/(2:ℝ)^(n+3)
  let q := coarsePlanarRound ρ
  let S := fun c => P.filter fun p => q p = c
  let Jp : ℝ := ((Nat.log 2 P.card+1:ℕ):ℝ)
  let Jv : ℝ := ((Nat.log 2 (∑ p ∈ P, (V p).card)+1:ℕ):ℝ)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hJpR : Jp ≤ D := hJp
  have hJvR : Jv ≤ D := hJv
  have hK4 : K ≤ D^4 := hKD.trans (by simpa using pow_le_pow_right₀ hD1 (show 1 ≤ 4 by norm_num))
  have mono {δ v A B : ℝ} (hd : 0 ≤ δ) (hAB : A ≤ B) {F : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound δ v A F) : NormalizedFiniteBallBound δ v B F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hVne (p : Space 2) (hp : p ∈ P) : (V p).Nonempty := by
    have hh : 0 < ((V p).card:ℝ) := (by positivity : 0 < 1/(D*(Δ^s)^2)).trans_le (hV p hp).1
    exact Finset.card_pos.mp (Nat.cast_pos.mp hh)
  obtain ⟨k,C,_,hC,hCsmall,_,hCb,hmass,hcell,T,hT,hTU,hG,hGsum,hGcap⟩ :=
    regular_cell_configuration n hn hs ht ht1 hK P V hP hPsmall hPball
      (fun p hp => ⟨hVne p hp,(hV p hp).2.2.1,(hV p hp).2.2.2⟩) hpoint
  have hCp : 8*K*Jp ≤ D^4 := by
    calc
      _ ≤ 8*D*D := by gcongr
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = D^3 := by ring
      _ ≤ D^4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hCl : 2*K*Jp*K ≤ D^4 := by
    calc
      _ ≤ 2*D*D*D := by gcongr
      _ ≤ D*D*D*D := by gcongr; linarith only [hD]
      _ = _ := by ring
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hCt : 2*(K*7^s)*Jv ≤ D^4 := by
    calc
      _ ≤ 2*(D*7)*D := by gcongr
      _ = 14*D*D := by ring
      _ ≤ D*D*D := by gcongr; linarith only [hD]
      _ = D^3 := by ring
      _ ≤ D^4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hTcard : (C.biUnion T).card ≤ 13*(P.biUnion V).card := by
    have hh := hTU.trans (mul_le_mul_of_nonneg_left
      (show (((P.biUnion V).image q).card:ℝ) ≤ ((P.biUnion V).card:ℝ) by
        exact_mod_cast Finset.card_image_le) (by norm_num : (0:ℝ) ≤ 13))
    exact_mod_cast hh
  have hJc : (Nat.log 2 (C.biUnion T).card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.log_mono_right hTcard) 1)).trans hJall
  have hJg : (Nat.log 2 (P.biUnion V).card+1:ℕ) ≤ D :=
    (Nat.cast_le.mpr (Nat.add_le_add_right (Nat.log_mono_right
      (show (P.biUnion V).card ≤ 13*(P.biUnion V).card by omega)) 1)).trans hJall
  apply build_regular_refinement n k hn hD P C V T
    (fineCoarsePacket ρ C (fun c => (S c).biUnion V)) hC
    (fun c hc => ⟨(hCsmall c hc).1.trans (by norm_num),(hCsmall c hc).2.trans (by norm_num)⟩)
    (mono (sq_nonneg Δ) hK4 hPball) (mono hρ.le hCp hCb) hJp hJv hJc hJg hmass
  · intro c hc
    exact ⟨(hcell c hc).1,(hcell c hc).2.1,(hcell c hc).2.2.1,(hcell c hc).2.2.2.1,
      mono hΔ.le hCl (hcell c hc).2.2.2.2⟩
  · intro p hp
    exact ⟨(hV p hp).1,(hV p hp).2.1,mono (sq_nonneg Δ) hK4 (hV p hp).2.2.1,(hV p hp).2.2.2⟩
  · intro c hc
    exact ⟨(hT c hc).1,(hT c hc).2.1,(hT c hc).2.2.1,
      mono hρ.le hCt (hT c hc).2.2.2.1,(hT c hc).2.2.2.2⟩
  · exact hG
  · exact hGsum
  · exact hGcap

end Falconer

end OAI
