import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorNodeEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceBandAll

namespace OAI

/-! Assigned packets need length bounds only on their nonempty scales.
Clipping empty-scale stopping levels preserves the exact source amplitude.
The original-selector concentration then supplies the needed intervals. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawBand_eq_zero_of_no_item (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (j : Fin N) (x y : ℝ)
    (hempty : ∀ (l : P.labels j), Item j l → False) :
    P.rawBand coeff i j x y = 0 := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,PiLp.zero_apply]
  apply Finset.sum_eq_zero
  intro u _
  exact False.elim (hempty u.1 u.2)

end LipschitzHilbert.SourceLabeledLattice

namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable


variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Stopping times may change freely for zero packets. -/
theorem sourcePacketAmplitude_stop_congr_of_zero
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cut : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop stop' : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ)
    (h : ∀ p ∈ packets, stop p = stop' p ∨ value p = 0) :
    g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop
      value phase a z level cell =
    g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop'
      value phase a z level cell := by
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rcases h p hp with he | hz
  · simp only [sourcePacketBase,he]
  · simp only [sourcePacketBase,hz,smul_zero,ite_self]

theorem eventually_source_supported_selector_node_envelope (C q : ℝ) (hC : 1 ≤ C) :
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
      (g : AngularGrid) (w cut Kw D : ℝ) (hw : 0 < w),
      0 < Kw →
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
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z)) ≤ 3*L →
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
      ‖amplitude‖ ≤ L^(q+6)*mass := by
  have hpoly := eventually_source_snapshot_envelope C q (by linarith)
  filter_upwards [hpoly,eventually_ge_atTop (2:ℝ)] with L hpoly hL
  intro ι tops T N κ Label Item _ _ P alt hAlt selector v test g w cut Kw D hw hKw
    hlength hzero Kb hKb hKbL gap phase M hM hMmax a Z A maskExponent
    ha0 ha1 hZ hZL hA hAq hz0 hz z hweight htotal
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
  have henv := hpoly A a Z (∑ t ∈ tops, weight t z) Kb
    hA hAq ha0 ha1 hZ hZL hKbL htotal
  have hmass : 0 ≤ mass := by
    unfold mass AngularGrid.mass
    exact Finset.sum_nonneg fun t _ => (hwpos t z).le
  have hbound : ‖amplitude‖ ≤ (L^(q+6)*ε)*mass := by
    rw [← heq] at hb
    calc
      _ ≤ (C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*ε*C^3)*mass := hb
      _ = ((C^8*A*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*C^3)*ε)*mass := by ring
      _ ≤ (L^(q+6)*ε)*mass := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right henv (show 0 ≤ ε by norm_num [ε])) hmass
  simpa only [ε,mul_one] using hbound

end LipschitzHilbert.AngularGrid

namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (T : τ → SlopeBox)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w

/-- Empty long scales impose no artificial restriction on the global
longest-scale field. Every retained packet has the true assigned length. -/
theorem assignedTopReference_supported_length
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (j : Fin N) (l : (Q).labels j) (u : P.AssignedTopItem packets assigned j l) :
    (Q).length j ≤ (T top).length := by
  have h := hshort ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
  have ht := P.assignedTopItem_assignment packets assigned top j (orig j l) u
  change P.length j ≤ (T top).length
  simpa only [ht] using h


/-- The supported assigned/reference bands remain the original physical
synthesis with its original top mask, including empty scales. -/
theorem assignedTopReference_topMaskBand_all
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope R cone w q.1 q.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L maskExponent : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (Q).physicalMaskedBand
      (fun j l u k => alt j (orig j l).val.2 u.val k)
      (fun j l u k => hAlt j (orig j l).val.2 u.val k)
      (T top).slope (fun j l => b j (orig j l).val.2) v f
      (fun _ _ _ => T top) L maskExponent (z.2-(T top).slope*z.1) j z.1 =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent packets assigned z (top,j) := by
  have href := (P.assignedTopFamily packets assigned top).referenceFamily_physicalMaskedBand_all
    oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopFamily_referenceCondition packets assigned top oldSlope (T top).slope
      R cone w hcondition)
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top)
    (P.assignedTopSelector packets assigned top b) v f (fun _ _ _ => T top) L maskExponent z j
  exact href.trans (P.assignedTopFamily_topMaskBand packets assigned alt hAlt top oldSlope
    b v f T L maskExponent z j)


/-- The joint estimate returned by assigned-top concentration supplies
the interval premise of the supported envelope and off-child lemmas. -/
theorem assignedTopReference_interval_norm_of_joint
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (A Kw D : ℝ) (z : ℝ×ℝ)
    (hjoint : ∀ lower upper, lower ≤ upper → upper ≤ N →
      let V := fun x y => ((Q).withProfile
        (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
          j (orig j l).val.2 u.val) 0 lower upper x y
      ‖V z.1 (z.2-(T top).slope*z.1)‖+(T top).width*
        ‖covariantSignal P.frequency (fun k y => V z.1 y k) (z.2-(T top).slope*z.1)‖ ≤
          A*((T top).weight Kw D z)^8) :
    ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).rawInterval
        ((Q).physicalMultiplierCoefficient (T top).slope
          (fun j l => b j (orig j l).val.2) v f) 0 lower upper
        z.1 (z.2-(T top).slope*z.1)‖ ≤ A*((T top).weight Kw D z)^8 := by
  intro lower upper hlu hu
  have hcoeff : (Q).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig j l).val.2) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top
      oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency b v f j l u
  rw [hcoeff]
  have h := hjoint lower upper hlu hu
  exact (le_add_of_nonneg_right (mul_nonneg (T top).width_pos.le (norm_nonneg _))).trans h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
