import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorOffchild
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopEnvelope

namespace OAI

/-! On a unary block, the actual off-child packet sum with original
smooth-selector coefficients is exponentially small. The proof retains
its lost-mass factor and uses only the precise raw-interval concentration,
top masks and the actual eligibility geometry. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_offchild (C q : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item)
      (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ) (v : ℝ × ℝ → ℝ)
      (test : ℝ × ℝ → EuclideanSpace ℂ κ)
      (g : AngularGrid) (w cut D : ℝ) (hw : 0 < w), 0 ≤ D →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
        (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ A → A ≤ L^q →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ × ℝ),
      let weight := fun t zz => (T t).weight (L^(maskExponent+2)) D zz
      (∀ t ∈ tops, weight t z ≤ C) →
      Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L →
      let Q := fun t => (P t).withProfile (alt t) (hAlt t)
      let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
      let stop := fun t j => g.lastEligible cut (w/(P t).length j)
        (div_pos hw ((P t).length_pos j))
      let value := fun t j => (Q t).rawBand (coeff t) 0 j z.1 (z.2-(T t).slope*z.1)
      (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
        ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
          A*(weight t z)^8) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ (s : ℝ),
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cut weight
        lower (g.index lower s) z-
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cut weight
        upper (g.index upper s) z < 1 →
      let child := g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut upper (g.index upper s)
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight Kb gap ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter fun p => p.1 ∉ child)
        Prod.fst (fun p => stop p.1 p.2)
        (fun p => ((T p.1).mask L maskExponent z : ℂ) • value p.1 p.2) phase a z
        lower (g.index lower s)‖ ≤
      (L^(q+6)*Real.exp (-L*Real.log L))*(
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cut weight
          lower (g.index lower s) z-
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cut weight
          upper (g.index upper s) z) := by
  filter_upwards [eventually_source_snapshot_envelope C q (by linarith),
    eventually_ge_atTop (2:ℝ)] with L hpoly hL
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut D hw hD
    hlength hzero Kb hKb hKbL gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hZL hA hAq hz0 hz z
  dsimp only
  intro hweight htotal hinterval lower upper hlu s hdrop
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight (L^(maskExponent+2)) D zz
  have hscale : 0 < L^(maskExponent+2) := Real.rpow_pos_of_pos (by linarith) _
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ w/(T t).length := (div_pos hw (T t).length_pos).le
  have hwp (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hscale D zz
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    have hanti := (P t).stopping_antitone g cut w hw (hzero t ht)
    intro i j hij
    exact min_le_min (hanti hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hsupported (t : ι) (ht : t ∈ tops) (j : Fin N) (l : (P t).labels j)
      (u : Item j l) : rawStop t j ≤ M t := by
    apply hMmax t ht
    have hj := g.eligible_lastEligible cut (w/(P t).length j)
      (div_pos hw ((P t).length_pos j)) (hzero t ht j)
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hlength t ht j l u))
      (by positivity)).trans hj
  have he (t : ι) (ht : t ∈ tops) (j : Fin N) (_hj : j ∈ Finset.univ) :
      g.eligible cut (w/(T t).length) (stop t j) :=
    g.eligible_of_le (hp t ht) (hmax t ht j) (hM t ht)
  have heq : g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter fun p =>
        p.1 ∉ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut upper (g.index upper s)) Prod.fst (fun p => rawStop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand (coeff p.1) 0 p.2 z.1 (z.2-(T p.1).slope*z.1))
      phase a z lower (g.index lower s) =
    g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter fun p =>
        p.1 ∉ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut upper (g.index upper s)) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand (coeff p.1) 0 p.2 z.1 (z.2-(T p.1).slope*z.1))
      phase a z lower (g.index lower s) := by
    apply g.sourcePacketAmplitude_stop_congr_of_zero
    intro p hp
    have ht : p.1 ∈ tops := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    by_cases hs : rawStop p.1 p.2 ≤ M p.1
    · exact Or.inl (min_eq_left hs).symm
    · right
      have hz : (Q p.1).rawBand (coeff p.1) 0 p.2 z.1 (z.2-(T p.1).slope*z.1) = 0 := by
        apply (Q p.1).rawBand_eq_zero_of_no_item
        intro l u
        exact hs (hsupported p.1 ht p.2 l u)
      rw [hz,smul_zero]
  rw [heq]
  apply g.source_offchild_masked_amplitude_bound tops T w cut D L maskExponent hw hD hL Kb gap
    Finset.univ stop (fun t j => (Q t).rawBand (coeff t) 0 j z.1 (z.2-(T t).slope*z.1))
    he phase a z hlu s (L^(q+6)) hdrop
  intro t ht
  obtain ⟨htt,_,hel⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
  have hb := g.sourcePacketAmplitude_fourth_envelope tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight hp hwp hKb gap phase (M t) t htt (hM t htt) z
    a Z ha0 ha1 hZ (hz0 t htt) (hz t htt) (Q t) (coeff t) 0 (stop t) (hstop t htt)
    lower (hMmax t htt lower hel) (hmax t htt) z.1 (z.2-(T t).slope*z.1) A C hA hC
    (hweight t htt) (hinterval t htt)
  have hpow : (weight t z)^4 ≤ C^3*weight t z := by
    calc
      _ = (weight t z)^3*weight t z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hwp t z).le (hweight t htt) 3) (hwp t z).le
  have henv := hpoly A a Z (∑ t ∈ tops, weight t z) Kb
    hA hAq ha0 ha1 hZ hZL hKbL htotal
  have he0 : 0 ≤ C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1)) := by
    have := Real.log_nonneg (le_max_left 1 (∑ t ∈ tops, weight t z))
    positivity
  calc
    _ ≤ (C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1)))*
        (C^3*weight t z) := hb.trans (mul_le_mul_of_nonneg_left hpow he0)
    _ = ((C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1)))*C^3)*
        weight t z := by ring
    _ ≤ L^(q+6)*weight t z := mul_le_mul_of_nonneg_right henv (hwp t z).le

end LipschitzHilbert.AngularGrid

end

end OAI
