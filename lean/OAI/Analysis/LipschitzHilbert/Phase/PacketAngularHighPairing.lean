import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularPartition
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelBilinearRecovery
import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelConstructionCost
import OAI.Analysis.LipschitzHilbert.Phase.SourceFullAngularGrid

namespace OAI

/-! The full high-disparity estimate for the actual three angular pieces.
All model costs are absorbed before choosing the finite lattice. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_high_pairing (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cv radius F c0 cone p0 decay : ℝ) (D K H J : ℕ)
    (hcStar : 0≤cStar) (hcEta : 0<cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta<cb/4)
    (hr : 0≤radius) (hF : 0≤F) (hc0 : 0<c0) (hcone : 1≤cone)
    (hrcone : radius≤cone) (hconeK : cone≤K) (hp0 : 0≤p0) (hdecay : 0≤decay)
    (hD : 4≤D) (hJ : 2*cone+1≤(2:ℝ)^J)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ A L0 : ℝ, 0≤A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex) (w : ℝ),
      0<w → w≤P.width → 207≤P.order → 6+2*(8*D+1)≤P.order →
      P.scale=4*(L^(A+2)*P.width) → P.ratioBound=4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order)≤L^p0 →
      P.topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ k, c0/w≤|P.frequency k|) → (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) H) →
      (∀ j l, |P.rowSlope j l|+w/P.length j≤1) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → f z=0) → (∀ z, z∉Fset → g z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0<ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      P.width=widthScale*w →
      Integrable (fun z => inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z)
        ∂volume.prod volume‖≤6*L^(-decay)*ratio*(volume.prod volume).real Fset := by
  have hsep : cStar<cEta*cb := by
    have h : cStar/cEta<cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  let aDensity := 4*(3*p0+4+decay)
  obtain ⟨CD,CS,CT,LD,LS,LT,_hCD,_hCS,_hCT,_hLD,_hLS,_hLT,A,Lbase,hA,hbase,hmain⟩ :=
    source_model_bilinear_recovery hVariation hLL cStar cEta CEta cb radius F c0 cone 1 Cv
      aDensity p0 decay D K H J hcStar hcEta hCEta hcb hcbQuarter hCv hr hF hc0
      hcone hconeK (by norm_num) (by dsimp only [aDensity]; positivity) hp0 hdecay
      (le_refl _) hD hsep hJ
  let L0 := max Lbase (max (num.modelUnitCost H CD CS CT) (num.modelUnitCost H LD LS LT))
  have haDensity : 0≤aDensity := by dsimp only [aDensity]; positivity
  refine ⟨A,L0,by linarith,hbase.trans (le_max_left _ _),?_⟩
  intro L hL N κ Label Item _ _ P S w hw hW horder hDorder hscale hratioBound hprofile
    hshort hfrequencyLo hfrequency hlocal hunitRange spectrum bin alt hAlt altSpectrum altBin
    b hb hb1 haway hradius hLip field hfield f g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin
    hFpos hfs hgs l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq
    hwidthLo hwidthHi hwidthEq
  classical
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hL16 : 16≤L := hbase.trans hLb
  have hhigh : num.modelUnitCost H CD CS CT≤L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hlow : num.modelUnitCost H LD LS LT≤L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨tag,cell,hcover⟩ := P.exists_angular_assignment w cStar cEta cb radius
    hw hcStar hcEta hcb.le hr hcoverSmall
  let d := fun gamma => angularModelConfig P S cStar cEta CEta cb Cv w F radius H
    hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num hw hW hF hr horder hfrequency hlocal
    tag cell hcover spectrum bin b hb hb1 haway hradius (fun j l k s t _ => hLip j l k s t) gamma
  obtain ⟨grid,hbranch,hroot,hzero⟩ := exists_source_full_angular_grid L (by linarith : 1≤L)
    (fun j => w/P.length j) (fun j => (div_pos hw (P.length_pos j)).le)
  let V := fun (gamma : DyadicLineGrid.GridChoice) (z : ℝ×ℝ) =>
    ∑ a∈P.angularPackets S tag gamma, P.crossPacketValue alt hAlt 0
      (P.angularSelector tag gamma b) (fun z => field (planeCoordinates z)) f z a
  have hpiece (gamma : DyadicLineGrid.GridChoice) :
      Integrable (fun z => inner ℂ (V gamma z) (g z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (V gamma z) (g z) ∂volume.prod volume‖≤
        2*L^(-decay)*ratio*(volume.prod volume).real Fset := by
    by_cases hne : (P.angularPackets S tag gamma).Nonempty
    · have hcost (X Y Z : ℝ) : (d gamma).unitModelCost X Y Z=num.modelUnitCost H X Y Z :=
        OrdinaryModelConfig.unitModelCost_of_numeric_fields (d gamma) cStar cEta cb radius num H
          X Y Z rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have htag (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) : tag j a=gamma ∧ b j a k s≠0 := by
        by_cases ht : tag j a=gamma
        · exact ⟨ht,by simpa [angularSelector,ht] using hn⟩
        · simp [angularSelector,ht] at hn
      have hcell (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma) :
          P.rowSlope a.1 a.2.1 ∈ scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) := by
        have ht := (Finset.mem_filter.mp ha).2
        have hs := (hcover a.1 a.2.1).1 (P.rowSlope a.1 a.2.1) (by
          simpa only [sub_self,abs_zero] using mul_nonneg hr (div_pos hw (P.length_pos a.1)).le)
        simpa only [ht] using hs
      have hcellrange (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma) :
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) ⊆ Icc (-1) 1 := by
        apply PacketRepresentation.angular_cell_subset_unit _ (div_pos hw P.topLength_pos)
          gamma.val a.1.val (cell a.1 a.2.1) (P.rowSlope a.1 a.2.1) (hcell a ha)
        rw [← P.precision_eq_scaled_grid w a.1]
        exact hunitRange a.1 a.2.1
      have hmargin (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma)
          (k : κ) (xi et : ℝ)
          (hs : planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 a.1 a.2.1 a.2.2 k) (xi,et)≠0) :
          Icc (-xi/et-(d gamma).margin*((d gamma).w/P.length a.1))
            (-xi/et+(d gamma).margin*((d gamma).w/P.length a.1))⊆
            scaledAngularCell ((d gamma).w/P.topLength) (d gamma).grid a.1.val
              ((d gamma).cell a.1 a.2.1) := by
        have ht := (Finset.mem_filter.mp ha).2
        have sp := altSpectrum a.1 a.2.1 a.2.2 k xi et hs
        change Icc (-xi/et-cb*(w/P.length a.1)) (-xi/et+cb*(w/P.length a.1))⊆
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1)
        simpa only [ht] using (hcover a.1 a.2.1).2 xi et sp.2.1 sp.1
      have hmeas (j : Fin N) (a : P.labels j) (k : κ) :
          Measurable (P.angularSelector tag gamma b j a k) := by
        change Measurable (fun s => if tag j a=gamma then b j a k s else 0)
        by_cases ht : tag j a=gamma
        · simpa [ht] using hb j a k
        · simp [ht]
      have hbound (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ) :
          ‖P.angularSelector tag gamma b j a k s‖≤1 := by
        by_cases ht : tag j a=gamma
        · simpa [angularSelector,ht] using hb1 j a k s
        · simp [angularSelector,ht]
      have hsupp (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) :
          |s-(0+P.rowSlope j a)|≤cone*(w/P.length j) := by
        simpa only [zero_add] using (hradius j a k s (htag j a k s hn).2).trans
          (mul_le_mul_of_nonneg_right hrcone (div_pos hw (P.length_pos j)).le)
      have hlip (j : Fin N) (a : P.labels j) (k : κ) (s t : ℝ) :
          ‖P.angularSelector tag gamma b j a k s-P.angularSelector tag gamma b j a k t‖≤
            1*(|s-t|/(w/P.length j)) := by
        by_cases ht : tag j a=gamma
        · simpa [angularSelector,ht,one_mul] using hLip j a k s t
        · simp only [angularSelector,ht,ite_false,sub_self,norm_zero,one_mul]
          exact div_nonneg (abs_nonneg _) (div_pos hw (P.length_pos j)).le
      have hactive (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) :
          cb*w/P.length j≤|s-(0+P.rowSlope j a)| ∧
            |s-(0+P.rowSlope j a)|≤radius*w/P.length j := by
        constructor
        · simpa only [zero_add,abs_sub_comm] using haway j a k s (htag j a k s hn).2
        · simpa only [zero_add,mul_div_assoc] using hradius j a k s (htag j a k s hn).2
      exact hmain L hLb κ N Label Item P (P.angularPackets S tag gamma) w P.topLength hw
        hscale hratioBound hprofile hDorder hne (d gamma) rfl rfl rfl rfl rfl rfl rfl
        (by rw [hcost]; exact hhigh) (by rw [hcost]; exact hlow)
        E Fset field cell gamma.val rfl rfl hE hEfin
        (by simpa only [zero_add] using hcell) hcellrange l r hfield hstrip hEstrip hFstrip
        hFset hFfin hFpos ratio widthScale hratio hloglo hloghi hratioEq
        hwidthLo hwidthHi hwidthEq P.topLength_pos.le hshort alt hAlt hmargin
        (fun a _ k xi et hs => altBin a.1 a.2.1 a.2.2 k xi et hs)
        (P.angularSelector tag gamma b) rfl hmeas hbound hsupp hlip hactive
        (by simpa only [zero_add] using hlocal) hfrequencyLo hfrequency
        (by simpa only [zero_add] using spectrum) (by simpa only [zero_add] using altSpectrum)
        f hfm hfb hfs grid hbranch hzero hroot g hgm hgb hgs
    · have he : P.angularPackets S tag gamma=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [V,he,Finset.sum_empty,inner_zero_left,integral_zero,norm_zero]
      exact ⟨integrable_zero _ _ _, by positivity⟩
  have heq (z : ℝ×ℝ) : (∑ gamma, inner ℂ (V gamma z) (g z))=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b
        (fun z => field (planeCoordinates z)) f z a) (g z) := by
    rw [←sum_inner]
    exact congrArg (fun x => inner ℂ x (g z))
      (P.sum_crossPacketValue_angularPartition alt hAlt S tag b 0
        (fun z => field (planeCoordinates z)) f z)
  refine ⟨(integrable_finsetSum _ (fun gamma _ => (hpiece gamma).1)).congr
    (Filter.Eventually.of_forall heq),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_finsetSum _ (fun gamma _ => (hpiece gamma).1)]
  calc
    _ ≤ ∑ gamma : DyadicLineGrid.GridChoice,
        ‖∫ z, inner ℂ (V gamma z) (g z) ∂volume.prod volume‖ := norm_sum_le _ _
    _ ≤ ∑ _gamma : DyadicLineGrid.GridChoice, 2*L^(-decay)*ratio*(volume.prod volume).real Fset :=
      Finset.sum_le_sum (fun gamma _ => (hpiece gamma).2)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,DyadicLineGrid.gridChoice_card,nsmul_eq_mul,
        Nat.cast_ofNat]
      ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
