import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopEnvelope

namespace OAI

/-! The supported-scale node estimate with its explicit linear phase
factor. No restriction is placed on the size of the imaginary phases;
this is the bound used for the Gaussian tail in §11. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem source_supported_selector_linear_envelope (C L : ℝ) (hC : 1 ≤ C) :
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item)
      (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ) (v : ℝ × ℝ → ℝ)
      (test : ℝ × ℝ → EuclideanSpace ℂ κ)
      (g : AngularGrid) (w cut Kw D : ℝ) (hw : 0 < w),
      0 < Kw →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
        (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, g.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ A →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ × ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      let Q := fun t => (P t).withProfile (alt t) (hAlt t)
      let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
      let stop := fun t j => g.lastEligible cut (w/(P t).length j)
        (div_pos hw ((P t).length_pos j))
      let weight := fun t zz => (T t).weight Kw D zz
      (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
        ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
          A*(weight t z)^8) →
      ∀ (level : ℕ) (cell : ℤ),
      let value := fun t j => (Q t).rawBand
        (fun j l u => (T t).mask L maskExponent z • coeff t j l u) 0 j
        z.1 (z.2-(T t).slope*z.1)
      let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut weight Kb gap
        (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
        (fun p => value p.1 p.2) phase a z level cell
      let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight level cell z
      ‖amplitude‖ ≤
        (C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*mass := by
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut Kw D hw hKw
    hlength hzero Kb hKb gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hA hz0 hz z hweight
  dsimp only
  intro hinterval level cell
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cut (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw D zz
  let ε : ℝ := 1
  let amplitude := g.sourcePacketAmplitude tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight Kb gap
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
    (fun p => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u) 0 p.2
      z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell
  let mass := g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
    cut weight level cell z
  have hprecision (t : ι) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw D zz
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
  have hmask (t : ι)
      (_ht : t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut level cell) : ‖((T t).mask L maskExponent z : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact topSincMask_abs_le_one L maskExponent ((T t).horizontal z) ((T t).transverse z)
  have hb := g.sourcePacketAmplitude_node_envelope tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut weight hprecision hwpos hKb gap phase M hM hMmax
    a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-(T t).slope*z.1) A C ε hA hC (show 0 ≤ ε by norm_num [ε]) z
    hweight hinterval 0 N (fun t => ((T t).mask L maskExponent z : ℂ)) level cell hmask
  have heq : amplitude = g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L maskExponent z : ℂ) •
        (Q p.1).rawBand ((Q p.1).restrictCoefficient (coeff p.1) 0 N) 0 p.2
          z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
    dsimp only [amplitude]
    apply Eq.trans ?_
      (show g.sourcePacketAmplitude tops (fun t => (T t).slope)
          (fun t => w/(T t).length) cut weight Kb gap
          (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
          (fun p => (Q p.1).rawBand
            (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u) 0 p.2
            z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell = _ from ?_)
    · apply g.sourcePacketAmplitude_stop_congr_of_zero
      intro p hp
      have ht : p.1 ∈ tops := (Finset.mem_product.mp hp).1
      by_cases hs : rawStop p.1 p.2 ≤ M p.1
      · exact Or.inl (min_eq_left hs).symm
      · right
        apply (Q p.1).rawBand_eq_zero_of_no_item
        intro l u
        exact hs (hsupported p.1 ht p.2 l u)
    · congr 1
      funext p
      rw [SourceLabeledLattice.restrictCoefficient_full,
        SourceLabeledLattice.rawBand_coeff_real_smul]
      exact (IsScalarTower.algebraMap_smul ℂ _ _).symm
  rw [← heq] at hb
  simpa only [ε,mul_one] using hb

end LipschitzHilbert.AngularGrid

end

end OAI
