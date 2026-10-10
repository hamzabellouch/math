import OAI.NumberTheory.TotientAsymptotic.PPTSelectedGrid
import OAI.NumberTheory.TotientAsymptotic.PPTHeadResidualFamily

namespace OAI

/-! The original-head grid keeps only the surviving nonleading primes
inside the geometric tail. The head itself is handled by the top row. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- Delete the leading coordinate from an ordered embedding fixing zero. -/
def pptRemoveHeadEmbedding {b N : ℕ} (e : Fin b ↪o Fin N)
    (hb : 0 < b) (_hN : 0 < N) (he : (e ⟨0,hb⟩).val=0) : Fin (b-1) ↪o Fin (N-1) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(e ⟨i.val+1,by omega⟩).val-1,by
      have hh := e.strictMono (show (⟨0,hb⟩ : Fin b) < ⟨i.val+1,by omega⟩ by
        change 0 < i.val+1; omega)
      change (e ⟨0,hb⟩).val < (e ⟨i.val+1,by omega⟩).val at hh
      have hi := (e ⟨i.val+1,by omega⟩).isLt
      omega⟩)
    (by
      intro i j hij
      have hh := e.strictMono (show (⟨i.val+1,by omega⟩ : Fin b) < ⟨j.val+1,by omega⟩ by
        change i.val+1 < j.val+1
        exact Nat.add_lt_add_right hij 1)
      have hzero := e.strictMono (show (⟨0,hb⟩ : Fin b) < ⟨i.val+1,by omega⟩ by
        change 0 < i.val+1; omega)
      change (e ⟨i.val+1,by omega⟩).val-1 < (e ⟨j.val+1,by omega⟩).val-1
      change (e ⟨i.val+1,by omega⟩).val < (e ⟨j.val+1,by omega⟩).val at hh
      change (e ⟨0,hb⟩).val < (e ⟨i.val+1,by omega⟩).val at hzero
      omega)

lemma ppt_remove_head_embedding_succ {b N : ℕ} (e : Fin b ↪o Fin N)
    (hb : 0 < b) (hN : 0 < N) (he : (e ⟨0,hb⟩).val=0) (i : Fin (b-1)) :
    (pptRemoveHeadEmbedding e hb hN he i).val+1=(e ⟨i.val+1,by omega⟩).val := by
  have hh := e.strictMono (show (⟨0,hb⟩ : Fin b) < ⟨i.val+1,by omega⟩ by
    change 0 < i.val+1; omega)
  change (e ⟨0,hb⟩).val < (e ⟨i.val+1,by omega⟩).val at hh
  change (e ⟨i.val+1,by omega⟩).val-1+1=_
  omega

/-- Finite comparison labels for a head outside the geometric vector. -/
theorem ppt_head_selected_grid_data (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N Q J H E r j : ℕ) (p : Fin N → ℕ) (q : Fin Q → ℕ)
      (v : Fin n → ℝ) (ι : Fin (N-1) ↪o Fin n) (budget g S L U V : ℝ),
      ∀ hJ : 0 < J, ∀ hJN : J ≤ N, ∀ hJQ : J ≤ Q,
      n ≤ m → N ≤ H → j ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      m+1 ≤ H → budget ≤ B z+1 →
      v ∈ relaxedGeometricFamily m n budget g →
      (∀ i : Fin (N-1),v (ι i)=B (p ⟨i.val+1,by omega⟩)) →
      (∀ i k : Fin N,i < k → B (p k) ≤ B (p i)/(1+1/(10*(H:ℝ)^3))) →
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
    ppt_head_pair_exponent hA,
    ppt_normal_small_tail_subpower d hA.le (by norm_num : (0:ℝ) < 1/100),
    B_tendsto.eventually (ppt_local_normality_error_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ))]
    with z hretained halign hgeometry hgrid hexponent hsmall hmesh hB
  intro m n N Q J H E r j p q v ι budget g S L U V hJ hJN hJQ hnm hNH hjH
    hdim hmH hbudgetTop hgeom hcoords hcontractAll hS hheight hV hSV hVz hL hLU hU hseed hp hq
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
  let eFull : Fin b ↪o Fin N := e.trans (Fin.castLEOrderEmb hJN)
  have hezero : (eFull ⟨0,hb⟩).val=0 := by
    have hx : p (eFull ⟨0,hb⟩)=p ⟨0,hJ.trans_le hJN⟩ :=
      (he ⟨0,hb⟩).1.symm.trans hheadEq
    exact congrArg Fin.val (hpa.injective hx)
  let f : Fin (b-1) ↪o Fin n :=
    (pptRemoveHeadEmbedding eFull hb (hJ.trans_le hJN) hezero).trans ι
  have hfcoords (i : Fin (b-1)) : v (f i)=B (pair.left ⟨i.val+1,by omega⟩) := by
    rw [(he ⟨i.val+1,by omega⟩).1]
    have hh := hcoords (pptRemoveHeadEmbedding eFull hb (hJ.trans_le hJN) hezero i)
    change v (f i)=B (p _) at hh
    have hiEq : (⟨(pptRemoveHeadEmbedding eFull hb (hJ.trans_le hJN) hezero i).val+1,
        by omega⟩ : Fin N)=(e ⟨i.val+1,by omega⟩).castLE hJN := by
      apply Fin.ext
      exact ppt_remove_head_embedding_succ eFull hb (hJ.trans_le hJN) hezero i
    rw [hiEq] at hh
    exact hh
  let ω : ℝ := 1/(10*(H:ℝ)^3)
  have hH : 1 ≤ H := by omega
  have hω1 : ω ≤ 1 := by
    have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
    have hpow : (1:ℝ) ≤ (H:ℝ)^3 := one_le_pow₀ hHr
    have hH0 : (0:ℝ) < H := zero_lt_one.trans_le hHr
    apply (div_le_iff₀ (by positivity : 0 < 10*(H:ℝ)^3)).mpr
    linarith only [hpow]
  have hleftContract (i : Fin b) (hi : i.val+1 < b) :
      B (pair.left ⟨i.val+1,hi⟩) ≤ B (pair.left i)/(1+ω) := by
    rw [(he ⟨i.val+1,hi⟩).1,(he i).1]
    exact hcontractAll _ _ (eFull.strictMono (show i < ⟨i.val+1,hi⟩ by
      change i.val < i.val+1; omega))
  have hpairAlign := halign b H (d*a.totient) S V pair hdim hS1 hBS hheight hSV hVz
    (Nat.mul_pos hd (Nat.totient_pos.mpr ha)) hrem
    (fun i => ⟨(hpair i).1,(hpair i).2.1⟩)
    (fun i => ⟨(hpair i).2.2.1,(hpair i).2.2.2.1⟩)
    hpairAnti.antitone hpairAnti'.antitone hequation hDV hremV hpairV hpairPred
  obtain ⟨hfirstGrid,hgaps⟩ := hgeometry b H S L U ω pair hb hbH hdim hS1 hBS
    (hSV.trans hVz) (fun i => (hpair i).1) (fun i => (hpair i).2.2.1)
    (fun i => (hpairPred i).1) le_rfl hω1
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
  have hExp := hexponent m n b H budget g S ((2*(b:ℝ)+3)*δ) ((2*(b:ℝ)+3)*δ)
    δ pair v f ν μ hb hgeom (fun i => (hpair i).2.2.1) hbudgetTop hfcoords
    hH hbH hmH hdim hδ le_rfl
    (by nlinarith only [hδ])
    (by have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b; nlinarith only [hδ,hb0])
    hη (fun i hi => hround i hi) hwidth
  refine ⟨b,h,s,c,a,pair,tail,grid,hb,hbH,hhH,?_,hatail,htailinj,htail,hreal,
    hparams,hconditions,hExp⟩
  exact ppt_residual_label_mem hbH hhH hsH hjH hgridmem halabel hclabel

end TotientAsymptotic

end

end OAI
