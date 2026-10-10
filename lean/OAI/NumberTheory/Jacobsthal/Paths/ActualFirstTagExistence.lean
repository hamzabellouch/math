import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceScale

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PaperOwnerHeight
open _root_.Filter JacobsthalSourceScale


theorem sourceW_square_two_L : ∀ᶠ L : ℝ in atTop,2*L ≤ (sourceW L)^2 := by
  have hh := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (s := 1) (by norm_num)).bound
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with L hsmall hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hl : 0 < Real.log L := Real.log_pos hL
  have h4 : (Real.log L)^4 ≤ L/2 := by
    simpa only [Real.rpow_ofNat,Real.rpow_one,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hl.le 4),abs_of_pos hL0,one_div,mul_comm,div_eq_mul_inv,one_mul] using hsmall
  rw [sourceW,div_pow,← pow_mul]
  apply (le_div_iff₀ (pow_pos hl 4)).mpr
  have hm := mul_le_mul_of_nonneg_left h4 hL0.le
  nlinarith

theorem literal_source_floor_height : ∀ᶠ z : ℝ in atTop,
    ((⌊z^2/(Real.log z)^2⌋₊:ℕ):ℝ) ≤ Real.exp ((sourceW (Real.log z))^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually sourceW_square_two_L,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with z hW hz hlog
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hy : ((⌊z^2/(Real.log z)^2⌋₊:ℕ):ℝ) ≤ z^2 := by
    exact (Nat.floor_le (div_nonneg (sq_nonneg z) (sq_nonneg (Real.log z)))).trans
      (div_le_self (sq_nonneg z) (by nlinarith : 1 ≤ (Real.log z)^2))
  have he : z^2=Real.exp (2*Real.log z) := by
    rw [show 2*Real.log z=Real.log (z^2) by rw [Real.log_pow]; norm_num]
    exact (Real.exp_log (sq_pos_of_pos hz0)).symm
  exact hy.trans (he.trans_le (Real.exp_le_exp.mpr hW))
end NumberTheoryLean.PaperOwnerHeight



namespace NumberTheoryLean.PaperBinOwners
open _root_.Filter JacobsthalSourceScale PaperOwnerHeight CorrectSearchTags UniformSearchOwner ActualBinOwners
open ActualSourceTags LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinMaps
open ErdosInverseAlignment ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem paper_bin_span {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,2 ≤ sourceW (Real.log z) ∧ sourceW (Real.log z) < z ∧
      (1+xi)*sourceW (Real.log z) ≤ z := by
  have hsmall := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).bound (by norm_num : (0:ℝ)<1/2)
  filter_upwards [Real.tendsto_log_atTop.eventually sourceW_bounds_eventually,
    (sourceW_tendsto.comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
    hsmall,eventually_gt_atTop (1:ℝ)] with z hW hw2 hlog hz
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlog0 : 0 < Real.log z := Real.log_pos hz
  have hlog' : Real.log z ≤ z/2 := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hlog0,abs_of_pos hz0,
      one_div,mul_comm,div_eq_mul_inv,one_mul] using hlog
  have hspan : (1+xi)*sourceW (Real.log z) ≤ z := by
    have hh := mul_le_mul_of_nonneg_right (show 1+xi ≤ 2 by linarith) (by linarith : 0 ≤ sourceW (Real.log z))
    nlinarith [hW.2.2]
  have hzw : sourceW (Real.log z) < z := by
    have hh := mul_pos hxi (show 0 < sourceW (Real.log z) by linarith)
    nlinarith
  exact ⟨hw2,hzw,hspan⟩

theorem paper_owner_unique {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ (Y : ℕ),Y ≤ ⌊z^2/(Real.log z)^2⌋₊ →
      ∀ b : Fin (binCount (sourceW (Real.log z)) z xi),
      searchBin (sourceW (Real.log z)) (lower (sourceW (Real.log z)) z xi b) →
      ∀ a : ℕ → ℤ,∀ q ∈ ownerCandidates Y (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b) a,
      ∀ r ∈ ownerCandidates Y (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b) a,q=r := by
  have ht : 0 < xi/4 := by positivity
  filter_upwards [paper_bin_span hxi hxi1,literal_source_floor_height,
    (sourceW_tendsto.comp Real.tendsto_log_atTop).eventually (uniform_search_owner_unique hCs heta ht)] with z hspan hheight howner
  intro Y hY b hs a
  have hw : 1 < sourceW (Real.log z) := by linarith [hspan.1]
  have hw0 : 0 < sourceW (Real.log z) := zero_lt_one.trans hw
  have hwidth := common_width_bounds hw0 hspan.2.1 hxi hxi1 hspan.2.2
  have hYup : (Y:ℝ) ≤ Real.exp ((sourceW (Real.log z))^2) :=
    (show (Y:ℝ) ≤ (⌊z^2/(Real.log z)^2⌋₊:ℕ) by exact_mod_cast hY).trans hheight
  exact howner.2 Y (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b)
    (Nat.cast_nonneg Y) hYup (searchBin_lower hw (endpoint_pos hw0 _) hs)
    hwidth.2.1 (hwidth.2.2.1.trans hxi1) a

theorem paper_owner_identifies {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ (Y : ℕ),Y ≤ ⌊z^2/(Real.log z)^2⌋₊ →
      ∀ b : Fin (binCount (sourceW (Real.log z)) z xi),
      searchBin (sourceW (Real.log z)) (lower (sourceW (Real.log z)) z xi b) →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y (sourceW (Real.log z)) Cs q →
      (1-eta)*((primeBin (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b)).card:ℝ) ≤
        (((primeBin (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b)).filter (aligns a q)).card:ℝ) →
      owner Y (sourceW (Real.log z)) Cs eta (lower (sourceW (Real.log z)) z xi b)
        (width (sourceW (Real.log z)) z xi b) a=some q := by
  filter_upwards [paper_owner_unique hCs heta hxi hxi1,paper_bin_span hxi hxi1] with z hu hspan
  intro Y hY b hs a q he hd
  exact owner_eq_of_unique (Nat.cast_nonneg Y) (by linarith [hspan.1]) a (hu Y hY b hs a) q he hd
end NumberTheoryLean.PaperBinOwners



namespace NumberTheoryLean.PaperCorrectTag
open _root_.Filter JacobsthalSourceScale PaperBinOwners ActualBinOwners ActualSourceTags FiniteFirstTag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

theorem paper_correct_candidate {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ (hw : 1 < sourceW (Real.log z)) (htop : sourceW (Real.log z) < z)
      (Y : ℕ),Y ≤ ⌊z^2/(Real.log z)^2⌋₊ → ∀ (a : ℕ → ℤ) (p : ℕ) (q : ℚ),
      p ∈ sourcePrimeSet (sourceW (Real.log z)) z →
      let b := label (zero_lt_one.trans hw) htop hxi p
      searchBin (sourceW (Real.log z)) (lower (sourceW (Real.log z)) z xi b) →
      eligible Y (sourceW (Real.log z)) Cs q →
      (1-eta)*((primeBin (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b)).card:ℝ) ≤
        (((primeBin (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b)).filter (aligns a q)).card:ℝ) →
      aligns a q p → tagCandidate Y (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi) (width (sourceW (Real.log z)) z xi)
        (label (zero_lt_one.trans hw) htop hxi) a p=some (b,q) := by
  filter_upwards [paper_owner_identifies hCs heta hxi hxi1] with z hz
  intro hw htop Y hY a p q hp
  dsimp only
  intro hs he hd ha
  have hps := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hmem := label_prime_membership (zero_lt_one.trans hw) htop hxi hps.1 hps.2
  have ho := hz Y hY (label (zero_lt_one.trans hw) htop hxi p) hs a q he hd
  exact candidate_of_witness Y (sourceW (Real.log z)) Cs eta
    (lower (sourceW (Real.log z)) z xi) (width (sourceW (Real.log z)) z xi)
    (label (zero_lt_one.trans hw) htop hxi) a p q hmem hs ho ha

theorem paper_first_tag_correct {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ (hw : 1 < sourceW (Real.log z)) (htop : sourceW (Real.log z) < z)
      (Y : ℕ),Y ≤ ⌊z^2/(Real.log z)^2⌋₊ → ∀ (a : ℕ → ℤ) (ps : List ℕ)
      (t : Tag (binCount (sourceW (Real.log z)) z xi)) (q : ℚ),
      sourceTag Y (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi) (width (sourceW (Real.log z)) z xi)
        (label (zero_lt_one.trans hw) htop hxi) a ps=some t →
      eligible Y (sourceW (Real.log z)) Cs q →
      (1-eta)*((primeBin (lower (sourceW (Real.log z)) z xi t.bin) (width (sourceW (Real.log z)) z xi t.bin)).card:ℝ) ≤
        (((primeBin (lower (sourceW (Real.log z)) z xi t.bin) (width (sourceW (Real.log z)) z xi t.bin)).filter (aligns a q)).card:ℝ) →
      t.rational=q := by
  filter_upwards [paper_owner_identifies hCs heta hxi hxi1] with z hz
  intro hw htop Y hY a ps t q ht he hd
  obtain ⟨_pre,p,_tail,_hps,_hindex,hbin,_hp,hs,ho,_ha,_hbefore⟩ := sourceTag_witness Y (sourceW (Real.log z)) Cs eta
    (lower (sourceW (Real.log z)) z xi) (width (sourceW (Real.log z)) z xi)
    (label (zero_lt_one.trans hw) htop hxi) a ps ht
  rw [← hbin] at hs ho
  have ho' := hz Y hY t.bin hs a q he hd
  exact Option.some.inj (ho.symm.trans ho')
end NumberTheoryLean.PaperCorrectTag



namespace NumberTheoryLean.SourceOwnerAudit
open _root_.Filter JacobsthalSourceScale PaperBinOwners ActualBinOwners ActualSourceTags
open LogarithmicBinScale LogarithmicBinEndpoints


theorem literal_floor_owner_unique {Cs eta xi : ℝ} (hCs : 0 ≤ Cs) (heta : eta < 1/2)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ b : Fin (binCount (sourceW (Real.log z)) z xi),
      searchBin (sourceW (Real.log z)) (lower (sourceW (Real.log z)) z xi b) →
      ∀ a : ℕ → ℤ,
      ∀ q ∈ ownerCandidates (⌊z^2/(Real.log z)^2⌋₊:ℕ) (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b) a,
      ∀ r ∈ ownerCandidates (⌊z^2/(Real.log z)^2⌋₊:ℕ) (sourceW (Real.log z)) Cs eta
        (lower (sourceW (Real.log z)) z xi b) (width (sourceW (Real.log z)) z xi b) a,q=r := by
  filter_upwards [paper_owner_unique hCs heta hxi hxi1] with z hz
  exact hz _ le_rfl
end NumberTheoryLean.SourceOwnerAudit



namespace ErdosTagEvent
open NumberTheoryLean FiniteFirstTag ActualSourceTags


theorem firstTagFrom_none_iff {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ) :
    firstTagFrom F k ps=none ↔ ∀ p ∈ ps,F p=none := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom]
  | cons p ps ih =>
    cases he : F p with
    | none => simp [firstTagFrom,he,ih]
    | some bq => rcases bq with ⟨b,q⟩; simp [firstTagFrom,he]

theorem firstTag_exists_of_candidate {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ)
    {p : ℕ} {bq : Fin n × ℚ} (hp : p ∈ ps) (hc : F p=some bq) :
    ∃ t,firstTag F ps=some t := by
  cases ht : firstTag F ps with
  | none =>
    have hnone := (firstTagFrom_none_iff F 0 ps).mp ht p hp
    rw [hc] at hnone
    contradiction
  | some t => exact ⟨t,rfl⟩

theorem sourceTag_exists_of_candidate {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {p : ℕ} {b : Fin n} {q : ℚ}
    (hp : p ∈ ps) (hc : tagCandidate Y w Cs eta lower width label a p=some (b,q)) :
    ∃ t,sourceTag Y w Cs eta lower width label a ps=some t :=
  firstTag_exists_of_candidate _ ps hp hc

end ErdosTagEvent


end Erdos970

end OAI
