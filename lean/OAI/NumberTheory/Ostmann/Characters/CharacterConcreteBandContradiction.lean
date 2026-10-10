import OAI.NumberTheory.Ostmann.Characters.CharacterTailShellContradiction
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectedShellGeometry
import OAI.NumberTheory.Ostmann.Characters.CharacterAmbientPrimeBounds
import OAI.NumberTheory.Ostmann.Characters.CharacterIndexCutoff
import OAI.NumberTheory.Ostmann.Construction.PositiveFourierCutoff

namespace OAI

/-! # Concrete separated prime bands instantiate the character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.concrete_character_band_contradiction
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c₀ δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc₀ : 0 < c₀)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let Ctotal := (Real.exp 1 + 1) * (β - α + 1)
    let Aend := 8 * β + 10
    let Bword := β + 1 - 2 * Real.log δ
    let B₁ := Aend + 2 * Bword + 3
    let Cdy := β + Real.log ((Real.log 2)⁻¹ + 1)
    let Cfinal := β + 1 + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + 1
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (q n : ℕ), 0 < q → 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
      ∀ (i j k : Fin q), i.val + 1 < j.val → j.val + 1 < k.val →
      ∀ (a z B : ℝ), 0 < a → a ≤ 1 → 1 < z → 1 ≤ B → 2 * B₁ + 5 ≤ B →
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B →
      2 * B₁ + (Cdy / a + max (Real.log 3) 0 + 1) + Real.log 2 + 6 ≤ B + 20 * Real.log a →
      Cfinal + (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1 →
      4 * (β + 1) * (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      let γs := characterBandPoint α β q (i.val + 1)
      let νw := characterBandPoint α β q j.val
      let γw := characterBandPoint α β q (j.val + 1)
      let νa := characterBandPoint α β q k.val
      a * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
        (νw * L) (γw * L) →
      ∀ us Ulate v : ℝ, characterBandPoint α β q i.val * L ≤ us → us + 1 ≤ γs * L →
      νa * L ≤ Ulate → Ulate + 5 * (n + 1) ≤ characterBandPoint α β q (k.val + 1) * L →
      Ulate + ((n + 1 : ℕ) : ℝ) / 10000 ≤ v → v + 1 ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 →
      c₀ ≤ ∑ p ∈ loglogShell P us, (p : ℝ)⁻¹ → c₀ ≤ ∑ p ∈ loglogShell P v, (p : ℝ)⁻¹ →
      (∀ x y : ℝ, Ulate ≤ x → y ≤ Ulate + 5 * (n + 1) →
        ((n + 1 : ℕ) : ℝ) / 10000 ≤ y - x →
        ∃ t : ℕ, x ≤ Ulate + t ∧ Ulate + t + 1 ≤ y ∧
          c₀ ≤ ∑ p ∈ loglogShell P (Ulate + t), (p : ℝ)⁻¹) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
      (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
        (realTranslatedCharacterTest χ center ζ p)) → False := by
  intro Ctotal Aend Bword B₁ Cdy Cfinal
  obtain ⟨s, ψ, hs, hconj, hψ, hlower, hsupp, heven⟩ := exists_positive_even_fourier_cutoff
  have hreal (x) : (ψ x).im = 0 := by
    have hh := congrArg Complex.im (hconj x)
    simp only [Complex.conj_im] at hh
    linarith only [hh]
  let Kψ := SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ))
  have hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp Kψ := by
    have hh := Real.add_one_le_exp Kψ
    linarith only [hh]
  obtain ⟨C₀, hC₀, htail⟩ := P0.eventual_tail_character_shell_contradiction
    hsize hM.lower hAset hBset hsum N₀ hN₀ c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro q n hq hn hC₀n i j k hij hjk a z B ha ha1 hz hB hstrong hrepeat hanchor hentropy hbudget
  let γs := characterBandPoint α β q (i.val + 1)
  let νw := characterBandPoint α β q j.val
  let γw := characterBandPoint α β q (j.val + 1)
  let νa := characterBandPoint α β q k.val
  let βw := (γs + νw) / 2
  let βa := (γw + νa) / 2
  have hmargins := character_three_band_margins α β q hα hαβ hq i j k hij hjk
  rcases hmargins with ⟨hαhalf, hαw, hsw, hβw, hαa, hwa, hβa, hγw0, hγwg, hνag⟩
  have hγwβ := (characterBandPoint_bounds α β q (j.val + 1) hαβ hq (by omega)).2
  have hβ : 0 < β := hα.trans hαβ
  have hword : 0 ≤ Bword := by
    have hh := Real.log_nonpos hδ.le hδ1
    dsimp only [Bword]
    linarith only [hh, hβ]
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁, Aend]; linarith only [hword, hβ]
  have hCtotal : 0 ≤ Ctotal := by dsimp [Ctotal]; positivity
  have hcover : 1 ≤ characterCellCoveringError c₀ δ (n + 1) :=
    (characterCellCoveringError_gt_one c₀ δ (n + 1) hc₀ hδ).le
  have hfinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + 1) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a := by
    have hh := div_le_div_of_nonneg_right
      (show γw + Real.log ((Real.log 2)⁻¹ + 1) ≤ Cdy by dsimp [Cdy]; linarith only [hγwβ]) ha.le
    linarith only [hh, hanchor]
  have hcut := htail n hn hC₀n a c₀ z (β + 1) Ctotal Aend Bword B B₁
    (characterCellCoveringError c₀ δ (n + 1)) s (δ / 2) 9 (α / 2) Kψ
    (β + 1) βw γs βa γw νw νa 1 β (β + 1) (3 * β + 1)
    ha hc₀ hz (by linarith only [hβ]) hCtotal hcover hs (by positivity) (by norm_num)
    (by positivity) hrepeat (by linarith only [hB]) hB₁ rfl hstrong hB ha1
    (by linarith only [hβ]) hγw0 hαw hsw hαa hwa hγwg hβw hβa (by norm_num)
    hbudget hfinal hentropy hβ.le (lt_add_one β) le_rfl le_rfl (by linarith only [hβ])
    (by change 3 * β + 1 + (β + 1) + 4 * (β + 1) + 4 ≤ 8 * β + 10; linarith only [])
    le_rfl le_rfl le_rfl le_rfl
    ψ hψ hreal heven hψK (by simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using hsupp) hlower
  have hgeom := eventual_character_selected_shell_geometry α β z hα hαβ (by linarith only [hz])
    q (n + 1) hq hn i j k hij hjk
  filter_upwards [hcut, hgeom, eventual_character_prime_total hM α β hα hαβ,
    eventual_character_index_cutoff β hβ (n + 1), eventually_ge_atTop (0 : ℝ)]
    with L hcut hgeom htotal hindex hL
  intro P hP hrange γs' νw' γw' νa' hbulk us Ulate v huslo hushi hUlo hUhi hvlo hvhi hsmallmass htopmass
    hrich χ hχ center ζ hζ href
  let m := ⌊z * L⌋₊
  let U : Finset ℕ := P.filter (fun p : ℕ => νw * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ γw * L)
  let T₀ := loglogShell P v
  let Q : Fin (m + 1) → Finset ℕ := Fin.cases T₀ (fun _ => U)
  let τ := characterRoundedTau (n + 1) v
  have hg := hgeom us Ulate v huslo hushi hUlo (by simpa only [Nat.cast_add, Nat.cast_one] using hUhi) hvlo hvhi
  rcases hg with ⟨hv2, husv, hαus, hαv, hβus, hβv, hαU, hβU, hUτ, hτU, hpair, hwordsize⟩
  have hround := character_rounded_endpoint_bounds (n + 1) v Ulate hv2 (by
    have hnR : (20000 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn
    linarith only [hvlo, hnR])
  have hτpos : 0 < τ := by linarith only [hround.2.2.1]
  have hUP : U ⊆ P := Finset.filter_subset _ _
  have hTP : T₀ ⊆ P := Finset.filter_subset _ _
  have hUrange : ∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L)) := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact ⟨prime_of_loglog_lower p (hP p hh.1) _ hh.2.1.le,
      prime_of_loglog_upper p (hP p hh.1) _ hh.2.2⟩
  have hUlog : ∀ p ∈ U, νw * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ γw * L := fun _ hp => (Finset.mem_filter.mp hp).2
  have hUT : Disjoint U T₀ := by
    apply Finset.disjoint_left.mpr
    intro p hp ht
    have hu := (hUlog p hp).2
    have hv := (Finset.mem_filter.mp ht).2.1
    have hgap := (characterBandPoint_strictMono α β q hαβ hq hjk).le
    have hh := mul_le_mul_of_nonneg_right hgap hL
    linarith only [hu, hv, hh, hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hQsub (i : Fin (m + 1)) : Q i ⊆ P := by exact Fin.cases hTP (fun _ => hUP) i
  have hbulklog (p : ℕ) (hp : p ∈ U) : Real.log (p : ℝ) ≤ Real.exp (γw * L) :=
    (Real.log_le_iff_le_exp (Real.log_pos (by exact_mod_cast (hP p (hUP hp)).one_lt))).mp (hUlog p hp).2
  let u : Fin (n + 1) × Bool → ℝ := fun j => if j.2 then v else us
  refine hcut Ulate τ (Real.exp (γw * L)) P U T₀ hP Q (characterIndexCutoff β L)
    (by nlinarith only [hαU, mul_nonneg hα.le hL])
    hβU hUτ hτU
    hτpos hround.2.2.1 rfl (fun _ => rfl) hQsub hbulk htopmass (htotal P hP hrange)
    (character_ambient_prime_ranges α β L hα hL P hP hrange) hUrange hUT
    (hwordsize _ (Nat.floor_le (by positivity)))
    (character_rounded_top_shell (n + 1) v Ulate hv2 (by
      have hnR : (20000 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn
      linarith only [hvlo, hnR]) P hP) hbulklog
    (νw * L) (γw * L) hUlog (by
      have hh := mul_le_mul_of_nonneg_right (characterBandPoint_strictMono α β q hαβ hq hjk).le hL
      exact hh.trans hUlo)
    hindex.2 hindex.1 (fun p hp => primeLogIndex_le_characterIndexCutoff β L p (hP p hp) (hrange p hp).2)
    hrich u ?_ ?_ ?_ ?_ ?_ ?_ χ hχ center ζ hζ
    (characterRoundedEndpoint (n + 1) v) hround.2.1 href
  · rintro ⟨j, b⟩
    cases b <;> simp only [u, Bool.false_eq_true, ↓reduceIte]
    · constructor
      · nlinarith only [hαus, mul_nonneg hα.le hL]
      · exact hβus
    · constructor
      · nlinarith only [hαv, mul_nonneg hα.le hL]
      · exact hβv
  · rintro ⟨j, b⟩
    cases b
    · left
      change us + 1 ≤ νw * L
      exact hushi.trans (mul_le_mul_of_nonneg_right
        (characterBandPoint_strictMono α β q hαβ hq hij).le hL)
    · right
      change γw * L ≤ v
      have hh := mul_le_mul_of_nonneg_right (characterBandPoint_strictMono α β q hαβ hq hjk).le hL
      nlinarith only [hh, hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  · exact fun _ => hushi
  · intro j
    change νa * L ≤ v
    nlinarith only [hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  · exact fun _ => hpair
  · rintro ⟨j, b⟩
    cases b
    · exact hsmallmass
    · exact htopmass

end Ostmann

end OAI
