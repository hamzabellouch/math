import OAI.Dynamics.StandardMap.ObservationExponential

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusPrefixGrowth (k : ℝ) (B : ℕ) (z : Torus) : Prop :=
  ∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤ ‖torusSegmentTransfer k z 0 i‖
lemma isClosed_torusPrefixGrowth (k : ℝ) (B : ℕ) : IsClosed {z | torusPrefixGrowth k B z} := by
  simp only [torusPrefixGrowth,ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 i).norm
lemma torusPrefixGrowth_lift (k : ℝ) (B : ℕ) (z : ℝ × ℝ) :
    torusPrefixGrowth k B (liftProjection z) ↔
    ∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤
      ‖transferProduct (orbitCoefficient k z.2 z.1) i‖ := by
  simp only [torusPrefixGrowth,torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
lemma prefix_row_cover (k : ℝ) (hc : BridgeScalarControl k) (B : ℕ) (hB : 2 ≤ B)
    (z : ℝ × ℝ) (hz : torusPrefixGrowth k B (liftProjection z.swap)) :
    prefixEligible k B B z ∨ prefixEligible k B (B+1) z := by
  have hg := (torusPrefixGrowth_lift k B z.swap).mp hz
  obtain ⟨J,hJ,hrow⟩ := fast_prefix_row (orbitCoefficient k z.1 z.2) (growthBase k) B hB
    (by linarith [growthBase_ge_four k hc.nonneg]) hc.prefix_geom hc.prefix_small
    (fun i _ _ => potential_bound k _ hc.nonneg) hg
  rcases hJ with rfl|rfl
  · exact Or.inl ⟨hg,hrow⟩
  · exact Or.inr ⟨hg,hrow⟩
def bridgeRowLength (B : ℕ) (b : Bool) : ℕ := if b then B else B-1
lemma bridgeRowLength_pos (B : ℕ) (hB : 2 ≤ B) (b : Bool) : 1 ≤ bridgeRowLength B b := by
  cases b <;> simp only [bridgeRowLength,Bool.false_eq_true,ite_false,ite_true] <;> omega
lemma bridgeRowLength_choice (B : ℕ) (hB : 2 ≤ B) (b : Bool) :
    B=bridgeRowLength B b ∨ B=bridgeRowLength B b+1 := by
  cases b with
  | false => right; change B=B-1+1; omega
  | true => left; rfl
lemma prefix_row_cover_bool (k : ℝ) (hc : BridgeScalarControl k) (B : ℕ) (hB : 2 ≤ B)
    (z : ℝ × ℝ) (hz : torusPrefixGrowth k B (liftProjection z.swap)) :
    ∃ b : Bool, prefixEligible k B (bridgeRowLength B b+1) z := by
  rcases prefix_row_cover k hc B hB z hz with h|h
  · exact ⟨false,by simpa [bridgeRowLength,Nat.sub_add_cancel (show 1 ≤ B by omega)] using h⟩
  · exact ⟨true,by simpa [bridgeRowLength] using h⟩
noncomputable def middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : Set Torus :=
  {z | torusPrefixGrowth k Bp z ∧ torusPrefixGrowth k Bm z.swap}
lemma measurableSet_middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : MeasurableSet (middlePrefixEvent k Bp Bm) :=
  ((isClosed_torusPrefixGrowth k Bp).inter ((isClosed_torusPrefixGrowth k Bm).preimage continuous_swap)).measurableSet
noncomputable def middleBridgeConstant : ℝ≥0∞ := 4096*bridgeLocalConstant/bridgeAreaScale
lemma middleBridgeConstant_ne_top : middleBridgeConstant ≠ ∞ := by
  exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) bridgeLocalConstant_ne_top) bridgeAreaScale_pos.ne'
lemma actual_middle_prefix_product (k : ℝ) (hc : BridgeScalarControl k)
    (Bp Bm : ℕ) (hBp : 2 ≤ Bp) (hBm : 2 ≤ Bm)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    (∫⁻ z in middlePrefixEvent k Bp Bm ∩ {z | h < H z}, ENNReal.ofReal (W z) ∂area) ≤
      middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  classical
  let E := middlePrefixEvent k Bp Bm ∩ {z | h < H z}
  have hE : MeasurableSet E := (measurableSet_middlePrefixEvent k Bp Bm).inter (isOpen_lt continuous_const hH).measurableSet
  let cell := Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1
  let U := cell ∩ liftProjection ⁻¹' E
  let A : ((Fin 32 × Fin 32) × (Bool × Bool)) → Set (ℝ × ℝ) := fun j =>
    {z | z ∈ bridgeGridCell j.1.1 ×ˢ bridgeGridCell j.1.2 ∧
      prefixEligible k Bp (bridgeRowLength Bp j.2.1+1) z.swap ∧
      prefixEligible k Bm (bridgeRowLength Bm j.2.2+1) z ∧ h < H (liftProjection z)}
  have hcover : U ⊆ ⋃ j, A j := by
    intro z hz
    obtain ⟨ix,hix⟩ := bridgeGrid_cover z.1 ⟨hz.1.1.1.le,hz.1.1.2⟩
    obtain ⟨iy,hiy⟩ := bridgeGrid_cover z.2 ⟨hz.1.2.1.le,hz.1.2.2⟩
    obtain ⟨bp,hbp⟩ := prefix_row_cover_bool k hc Bp hBp z.swap (by simpa only [Prod.swap_swap] using hz.2.1.1)
    obtain ⟨bm,hbm⟩ := prefix_row_cover_bool k hc Bm hBm z hz.2.1.2
    exact mem_iUnion.mpr ⟨((ix,iy),(bp,bm)),⟨hix,hiy⟩,hbp,hbm,hz.2.2⟩
  have hu : (∫⁻ z in U, ENNReal.ofReal (W (liftProjection z)))=
      ∫⁻ z in E, ENNReal.ofReal (W z) ∂area := by
    have hi := unit_cell_integral (E.indicator (fun z => ENNReal.ofReal (W z)))
      (hW.measurable.ennreal_ofReal.indicator hE) 0 0
    simp only [zero_add] at hi
    rw [lintegral_indicator hE] at hi
    have hid : (fun z => E.indicator (fun z => ENNReal.ofReal (W z)) (liftProjection z))=
        (liftProjection ⁻¹' E).indicator (fun z => ENNReal.ofReal (W (liftProjection z))) := by
      funext z
      by_cases hz : liftProjection z ∈ E <;> simp [hz]
    rw [hid,setLIntegral_indicator (hE.preimage measurable_liftProjection)] at hi
    simpa only [U,cell,inter_comm] using hi
  let K := bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z}
  have hlocal (j : ((Fin 32 × Fin 32) × (Bool × Bool))) :
      bridgeAreaScale*(∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) ≤ K :=
    actual_grid_square_product k hc (bridgeRowLength Bp j.2.1) (bridgeRowLength Bm j.2.2) Bp Bm
      (bridgeRowLength_pos Bp hBp _) (bridgeRowLength_pos Bm hBm _)
      (bridgeRowLength_choice Bp hBp _) (bridgeRowLength_choice Bm hBm _) hBp hBm j.1.1 j.1.2
      W H hW hH hW0 h δ hδ hδh hWp hHp
  have hsum : bridgeAreaScale*(∫⁻ z in E, ENNReal.ofReal (W z) ∂area) ≤ 4096*K := by
    rw [← hu]
    calc
      _ ≤ bridgeAreaScale*(∫⁻ z in ⋃ j, A j, ENNReal.ofReal (W (liftProjection z))) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hcover) bot_le
      _ ≤ bridgeAreaScale*(∑' j, ∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) :=
        mul_le_mul_of_nonneg_left (lintegral_iUnion_le _ _) bot_le
      _ = ∑ j, bridgeAreaScale*(∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) := by rw [tsum_fintype,Finset.mul_sum]
      _ ≤ ∑ _j : ((Fin 32 × Fin 32) × (Bool × Bool)), K := Finset.sum_le_sum (fun j _ => hlocal j)
      _ = 4096*K := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul]; norm_num
  have hd := (ENNReal.le_div_iff_mul_le (Or.inl bridgeAreaScale_pos.ne') (Or.inl bridgeAreaScale_ne_top)).mpr
    (show (∫⁻ z in E, ENNReal.ofReal (W z) ∂area)*bridgeAreaScale ≤ 4096*K by simpa only [mul_comm] using hsum)
  apply hd.trans_eq
  unfold K middleBridgeConstant
  simp only [div_eq_mul_inv]
  ac_rfl
end StandardMapEntropy

end OAI
