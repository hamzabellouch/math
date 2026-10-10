import OAI.NumberTheory.TotientAsymptotic.PPTTruncatedCoordinates
import OAI.NumberTheory.TotientAsymptotic.PPTFiniteLabels

namespace OAI

/-! Construct the actual finite comparison label after terminal selection. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ppt_seed_tail_largest_le {d h : ℕ} (tail : Fin h → ℕ) {S V : ℝ}
    (hV : 1 ≤ V) (hSV : S ≤ V) (hseed : (largestPrimeFactor d : ℝ) ≤ S)
    (hp : ∀ i, (tail i).Prime) (hinj : Function.Injective tail)
    (hsmall : ∀ i, (largestPrimeFactor (tail i-1) : ℝ) ≤ V) :
    (largestPrimeFactor (d*(∏ i,tail i).totient) : ℝ) ≤ V := by
  have hnat : largestPrimeFactor (d*(∏ i,tail i).totient) ≤ ⌊V⌋₊ := by
    apply largestPrimeFactor_mul_le (Nat.le_floor (hseed.trans hSV))
    rw [ppt_totient_primeProduct tail hp hinj]
    apply largestPrimeFactor_prod_le _ _ (Nat.le_floor (by simpa only [Nat.cast_one] using hV))
    intro i _
    exact Nat.le_floor (hsmall i)
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (zero_le_one.trans hV))

/-- A retained prime above the vacant window has predecessor above
the middle cutoff. This does not require any right-coordinate alignment. -/
theorem ppt_terminal_retained_predecessor : ∀ᶠ z : ℝ in atTop,
    ∀ (p H : ℕ) (S L U : ℝ), 3 ≤ p → 1 < S → 0 ≤ B S → S ≤ z →
      IsNormalPrime S p → (p-1 : ℕ) ≤ z → U < B p →
      (8*(H : ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      Real.exp (Real.exp ((L+U)/2)) ≤ (p-1 : ℕ) := by
  filter_upwards [ppt_normal_factor_loss_mesh,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with z hfactor hB
  intro p H S L U hp3 hS hBS hSz hp hpz hhigh hbudget
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hδ : 0 ≤ δ := by
    have hlog : 0 < Real.log (B z) := Real.log_pos hB
    dsimp only [δ]
    positivity
  have hc : δ*B z < (U-L)/4 := by
    have hh : 1 ≤ 8*(H : ℝ)+20 := by
      have := Nat.cast_nonneg (α := ℝ) H
      linarith only [this]
    have hle := mul_le_mul_of_nonneg_right hh (mul_nonneg hδ hB0.le)
    change (8*(H : ℝ)+20)*δ*B z < _ at hbudget
    nlinarith only [hle,hbudget]
  have hh := mul_le_mul_of_nonneg_right (hfactor p S hp3 hS hBS hSz hp hpz).1 hB0.le
  change (B p/B z-δ)*B z ≤ (B (largestPrimeFactor (p-1))/B z)*B z at hh
  rw [sub_mul,div_mul_cancel₀ _ hB0.ne',div_mul_cancel₀ _ hB0.ne'] at hh
  have hm : (L+U)/2 < B (largestPrimeFactor (p-1)) := by
    have hp : 0 ≤ δ*B z := mul_nonneg hδ hB0.le
    linarith only [hh,hhigh,hc,hp]
  have hlp : (1 : ℝ) < largestPrimeFactor (p-1) := by
    exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ p-1 by omega)
  have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hm.le)
  rw [exp_exp_doubleLog hlp] at he
  exact he.trans (Nat.cast_le.mpr (largestPrimeFactor_le_self (by omega)))

/-- The selected actual prefix yields a finite arithmetic label and the
literal comparison data, including its strict exponent. All size,
normality and geometric assumptions concern the original candidate and
the chosen preimage; no bound for a residual family is assumed. -/
theorem ppt_selected_grid_data (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N Q J H E r j : ℕ) (p : Fin N → ℕ) (q : Fin Q → ℕ)
      (v : Fin n → ℝ) (ι : Fin N ↪o Fin n) (budget g S L U V : ℝ),
      ∀ hJ : 0 < J, ∀ hJN : J ≤ N, ∀ hJQ : J ≤ Q,
      n ≤ m → N ≤ H → j ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      m-(ι ⟨0,hJ.trans_le hJN⟩).val ≤ H →
      v ∈ relaxedGeometricFamily m n budget g → (∀ i,v (ι i)=B (p i)) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H : ℝ)^4 →
      V=Real.exp (Real.exp ((L+U)/2)) → S ≤ V → V ≤ z →
      (B z)^(2/3 : ℝ) ≤ L → L < U → U ≤ 2*(B z)^(2/3 : ℝ) →
      (largestPrimeFactor d : ℝ) ≤ S →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, IsNormalPrime S (q i)) →
      (∀ i, 3 ≤ p i) → (∀ i, 3 ≤ q i) → StrictAnti p → StrictAnti q →
      p ⟨0,hJ.trans_le hJN⟩ ≠ q ⟨0,hJ.trans_le hJQ⟩ →
      r=∏ i,p i → d*shiftedProduct p=E*shiftedProduct q → 0 < E →
      (largestPrimeFactor E : ℝ) ≤ S →
      (∀ i : Fin N,i.val < J → U < B (p i)) →
      (∀ i : Fin Q,i.val < J → V ≤ (q i-1 : ℕ)) →
      (∀ i : Fin N,J ≤ i.val → (largestPrimeFactor (p i-1):ℝ) ≤ V) →
      (∀ i : Fin Q,J ≤ i.val → (largestPrimeFactor (q i-1):ℝ) ≤ V) →
      (∀ i,(p i-1:ℕ) ≤ z) → (∀ i,(q i-1:ℕ) ≤ z) →
      ((d*r.totient:ℕ):ℝ) ≤ z → SquarefreeAbove (d*r.totient) S →
      (∀ i,p i ≤ discardPrimeBound (B z)) →
      (((∏ i ∈ Finset.univ.filter (fun i : Fin N => 0 < i.val),p i):ℕ):ℝ) ≤ z^(1/10:ℝ) →
      z^(9/10:ℝ) ≤ p ⟨0,hJ.trans_le hJN⟩ →
      (8*(H:ℝ)+20)*(2*((Real.log (B z))^5/Real.sqrt (B z)))*B z < (U-L)/4 →
      let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
      let ζ := (L+U)/(2*B z)
      let θ := pptUniformHeadEdge (B z)-δ
      ∃ (b h s c a : ℕ) (pair : ShiftedPair b) (tail : Fin h → ℕ) (grid : Fin b → ℕ),
        let ν := pairedGridUpper δ ζ grid
        let μ := pptGridLower δ θ grid
        0 < b ∧ b ≤ H ∧ h ≤ H ∧
        pptResidualLabel b h s c a j grid ∈
          pptResidualLabels (discardPrimeBound (B z)) H δ ∧
        a=∏ i,tail i ∧ Function.Injective tail ∧
        (∀ i,IsNormalPrime S (tail i) ∧ (largestPrimeFactor (tail i-1):ℝ) ≤ V) ∧
        r=c*a*∏ i,pair.left i ∧
        FordComparisonParameters b z S (d*a.totient) c.totient
          (comparisonCutoffs z ν) (comparisonCutoffs z μ) ∧
        FordComparisonConditions b z S (d*a.totient) c.totient
          (comparisonCutoffs z ν) (comparisonCutoffs z μ) pair ∧
        -2+(∑ i ∈ Finset.Icc 1 (b-1),TotientAsymptotic.a i*(B (comparisonCutoffs z ν i)/B z))+
          comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤ 
          -1-(1/(80*A^3))/(Real.log (B z))^3 := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_terminal_retained_predecessor, ppt_pair_alignment_in_mesh hA,
    ppt_geometric_pair_grid hA, ppt_pointwise_grid_realization hA hγ,
    ppt_geometric_pair_exponent hA,
    ppt_normal_small_tail_subpower d hA.le (by norm_num : (0:ℝ) < 1/100),
    B_tendsto.eventually (ppt_local_normality_error_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hretained halign hgeometry hgrid hexponent hsmall hmesh hB
  intro m n N Q J H E r j p q v ι budget g S L U V hJ hJN hJQ hnm hNH hjH
    hdim hremaining hgeom hcoords hS hheight hV hSV hVz hL hLU hU hseed hp hq
    hp3 hq3 hpa hqa hfirst hr heq hE hES hpHigh hqHigh hpLow hqLow hpz hqz
    hsize hsq hpBound hcommon hhead hbudget
  dsimp only
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBS : 0 ≤ B S := by
    have hh := ppt_B_mono (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS
    have hh' : (1 : ℝ) ≤ B S := by simpa only [B,Real.log_exp] using hh
    exact (by norm_num : (0 : ℝ) ≤ 1).trans hh'
  have hV1 : 1 < V := hS1.trans_le hSV
  have hBV : B V=(L+U)/2 := by rw [hV,B_exp_exp]
  have hL1 : 1 ≤ L := by
    have hh : 1 ≤ (B z)^(2/3:ℝ) := Real.one_le_rpow hB.le (by norm_num)
    exact hh.trans hL
  have hBV1 : 1 ≤ B V := by rw [hBV]; linarith only [hL1,hLU]
  have hBVupper : B V ≤ 2*(B z)^(2/3:ℝ) := by rw [hBV]; linarith only [hLU,hU]
  have hpV (i : Fin N) (hi : i.val < J) : V ≤ (p i-1:ℕ) := by
    rw [hV]
    exact hretained (p i) H S L U (hp3 i) hS1 hBS (hSV.trans hVz)
      (hp i) (hpz i) (hpHigh i hi) hbudget
  obtain ⟨b,h,s,c,a,pair,tail,hb,hbJ,hhN,hsJ,hc,ha,hreal,hclabel,halabel,
    hatail,htailinj,htail,htailindices,hpair,hpairAnti,hpairAnti',hrem,hremV,
    hequation,hpairSize,hpairSq,hcdef,hembed,_hleftEmbed,hheadData⟩ :=
    ppt_actual_truncated_block p q hJN hJQ hJ hp hq hpa hqa hp3 hq3 hfirst hr heq
      hE hV1.le (hES.trans hSV) hpLow hqLow hsize hsq hpBound
  let e := hembed.choose
  have he := hembed.choose_spec
  have hheadEq : pair.left ⟨0,hb⟩=p ⟨0,hJ.trans_le hJN⟩ := hheadData.choose_spec
  have hbH : b ≤ H := hbJ.trans (hJN.trans hNH)
  have hhH : h ≤ H := hhN.trans hNH
  have hsH : s ≤ H := hsJ.trans (hJN.trans hNH)
  have hpairPred (i : Fin b) : (pair.left i-1:ℕ) ≤ z ∧ (pair.right i-1:ℕ) ≤ z := by
    rw [(he i).1,(he i).2]
    exact ⟨hpz _,hqz _⟩
  have hpairV (i : Fin b) : V ≤ (pair.left i-1:ℕ) ∧ V ≤ (pair.right i-1:ℕ) := by
    rw [(he i).1,(he i).2]
    exact ⟨hpV _ (e i).isLt,hqHigh _ (e i).isLt⟩
  have hpairHigh (i : Fin b) : U < B (pair.left i) := by
    rw [(he i).1]
    exact hpHigh _ (e i).isLt
  have htail3 (i : Fin h) : 3 ≤ tail i := by
    obtain ⟨k,_,hk⟩ := htailindices i
    rw [hk]
    exact hp3 k
  have hDsmall : ((d*a.totient:ℕ):ℝ) ≤ z^(1/100:ℝ) := by
    rw [hatail]
    exact hsmall h tail S V ((Nat.cast_le.mpr hhH).trans hdim) hS1 hBS hSV hBV1
      hBVupper (fun i => (htail i).1) htail3 (fun i => (htail i).2)
  have hDV : (largestPrimeFactor (d*a.totient):ℝ) ≤ V := by
    rw [hatail]
    exact ppt_seed_tail_largest_le tail hV1.le hSV hseed
      (fun i => (htail i).1.1) htailinj (fun i => (htail i).2)
  have hcsmall : (c.totient:ℝ) ≤ z^(1/10:ℝ) := by
    apply (Nat.cast_le.mpr (Nat.totient_le c)).trans
    apply le_trans _ hcommon
    rw [hcdef]
    exact Nat.cast_le.mpr (ppt_canceled_prefix_factor_le_tail p q hJN hJQ hJ
      (fun i => (hp i).1.one_le) hfirst)
  let f : Fin b ↪o Fin n := (e.trans (Fin.castLEOrderEmb hJN)).trans ι
  have hfcoords (i : Fin b) : v (f i)=B (pair.left i) := by
    rw [(he i).1]
    exact hcoords _
  have hezero : (e ⟨0,hb⟩).val=0 := by
    have hx : p ((e ⟨0,hb⟩).castLE hJN)=p ⟨0,hJ.trans_le hJN⟩ := by
      rw [←(he ⟨0,hb⟩).1]
      exact hheadEq
    have hh := congrArg Fin.val (hpa.injective hx)
    exact hh
  have hfremaining : m-(f ⟨0,hb⟩).val ≤ H := by
    have hfzero : f ⟨0,hb⟩=ι ⟨0,hJ.trans_le hJN⟩ := by
      apply congrArg ι
      exact Fin.ext hezero
    rw [hfzero]
    exact hremaining
  have hcontract := ppt_geometric_embedded_contraction hgeom hnm f hb hfremaining
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hleftContract (i : Fin b) (hi : i.val+1 < b) :
      B (pair.left ⟨i.val+1,hi⟩) ≤ B (pair.left i)/(1+ω) := by
    have hh := hcontract.2 i ⟨i.val+1,hi⟩ (by change i.val < i.val+1; omega)
    simpa only [hfcoords] using hh
  have hpairAlign := halign b H (d*a.totient) S V pair hdim hS1 hBS hheight hSV hVz
    (Nat.mul_pos hd (Nat.totient_pos.mpr ha)) hrem
    (fun i => ⟨(hpair i).1,(hpair i).2.1⟩)
    (fun i => ⟨(hpair i).2.2.1,(hpair i).2.2.2.1⟩)
    hpairAnti.antitone hpairAnti'.antitone hequation hDV hremV hpairV hpairPred
  obtain ⟨hfirstGrid,hgaps⟩ := hgeometry b H S L U ω pair hb hbH hdim hS1 hBS
    (hSV.trans hVz) (fun i => (hpair i).1) (fun i => (hpair i).2.2.1)
    (fun i => (hpairPred i).1) le_rfl hcontract.1
    (fun i => hL.trans (hLU.le.trans (hpairHigh i).le)) hleftContract hLU.le hU hpairAlign
  let δ := 2*((Real.log (B z))^5/Real.sqrt (B z))
  let u := fun i => B (largestPrimeFactor (pair.left i-1))/B z
  let w := fun i => B (largestPrimeFactor (pair.right i-1))/B z
  let grid := fun i => collisionGridIndex δ (u i) (w i)
  let ν := pairedGridUpper δ ((L+U)/(2*B z)) grid
  let μ := pptGridLower δ (pptUniformHeadEdge (B z)-δ) grid
  have hgridData := hgrid b H (d*a.totient) c S V L U pair hb hbH hdim hS hheight
    hV hSV hVz (Nat.mul_pos hd (Nat.totient_pos.mpr ha)) hc hrem hDsmall hcsmall
    (fun i => ⟨(hpair i).1,(hpair i).2.1⟩)
    (fun i => ⟨(hpair i).2.2.1,(hpair i).2.2.2⟩)
    hpairAnti.antitone hpairAnti'.antitone hequation hpairSize
    (ppt_squarefreeAbove_mono hSV hpairSq) hDV hremV hpairV hpairPred
    (by rw [hheadEq]; exact hhead) (zero_le_one.trans hL1) (hpairHigh _)
    hbudget hfirstGrid hgaps
  obtain ⟨hgridmem,hparams,hconditions,hround,hwidth⟩ := hgridData
  have hδ : 0 ≤ δ := by
    have hlog : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
    dsimp only [δ]
    positivity
  have hη : Real.sqrt (B S/B z) ≤ δ := by
    have hh := hmesh H S hdim hBS hheight
    dsimp only [δ]
    have hm : 0 ≤ (Real.log (B z))^5/Real.sqrt (B z) := by
      have hlog0 := (Real.log_pos hB).le
      positivity
    linarith only [hh,hm]
  have hrow : m-((f ⟨0,hb⟩).val+1)+1 ≤ H := by
    have hi := (f ⟨0,hb⟩).isLt
    omega
  have hExp := hexponent m n b H budget g S ((2*(b:ℝ)+3)*δ) ((2*(b:ℝ)+3)*δ)
    δ pair v f ν μ hb hgeom (fun i => (hpair i).2.2.1) (hpairPred _).1
    hfcoords (by omega) hbH hrow hdim hδ le_rfl
    (by nlinarith only [hδ]) (by have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b; nlinarith only [hδ,hb0])
    hη hround hwidth
  refine ⟨b,h,s,c,a,pair,tail,grid,hb,hbH,hhH,?_,hatail,htailinj,htail,hreal,
    hparams,hconditions,hExp⟩
  exact ppt_residual_label_mem hbH hhH hsH hjH hgridmem halabel hclabel

end TotientAsymptotic

end

end OAI
