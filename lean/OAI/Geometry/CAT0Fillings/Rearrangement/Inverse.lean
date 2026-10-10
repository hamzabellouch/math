import Mathlib
import OAI.Geometry.CAT0Fillings.Transport.Sharp

namespace OAI

section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CAT0Fillings
open RadialSobolev

lemma fillingCoefficient_pos {m : ℕ} (hm : 0 < m) : 0 < fillingCoefficient m := by
  unfold fillingCoefficient sphereArea
  have hω := omega_pos (Nat.succ_pos m)
  positivity

lemma ball_filling_identity {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) :
    fillingCoefficient m * (((m+1:ℝ)*omega (m+1)*r^m)^(fillingPower m)) =
      omega (m+1)*r^(m+1) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hω := omega_pos (Nat.succ_pos m)
  have hM : 0 < (m+1:ℝ)*omega (m+1) := by positivity
  have hp : (m+1:ℝ)/(m:ℝ) = 1+1/(m:ℝ) := by field_simp
  have hpow : ((r^m)^((m+1:ℝ)/(m:ℝ))) = r^(m+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    have he : (m:ℝ)*((m+1:ℝ)/(m:ℝ)) = (m+1:ℝ) := by field_simp
    rw [he]
    norm_cast
  rw [fillingCoefficient,fillingPower,Real.mul_rpow hM.le (pow_nonneg hr _),hpow]
  rw [hp,Real.rpow_add hM,Real.rpow_one]
  unfold sphereArea
  field_simp [hM.ne',Real.rpow_ne_zero hM.le hM.ne']

lemma perimeter_of_small_isoperimetry {m : ℕ} (hm : 0 < m) {r P η : ℝ}
    (hr : 0 ≤ r) (hP : 0 ≤ P) (hη : 0 < η) (hη1 : η < 1)
    (hiso : (1-η)*(omega (m+1)*r^(m+1)) ≤
      fillingCoefficient m * P^(fillingPower m)) :
    (1-η)*((m+1:ℝ)*omega (m+1)*r^m) ≤ P := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hp : 1 < fillingPower m := by unfold fillingPower; apply (lt_div_iff₀ hmR).mpr; linarith
  have hc := fillingCoefficient_pos hm
  let B := (m+1:ℝ)*omega (m+1)*r^m
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) (omega_pos (Nat.succ_pos m)).le) (pow_nonneg hr _)
  by_contra hn
  have hlt : P < (1-η)*B := not_le.mp hn
  have hpow := Real.rpow_lt_rpow hP hlt (lt_trans zero_lt_one hp)
  have hmul := mul_lt_mul_of_pos_left hpow hc
  rw [Real.mul_rpow (sub_pos.mpr hη1).le hB] at hmul
  have hsmall : (1-η)^(fillingPower m) ≤ 1-η := Real.rpow_le_self_of_le_one
    (sub_pos.mpr hη1).le (by linarith) hp.le
  have hid := ball_filling_identity hm hr
  change fillingCoefficient m * B^(fillingPower m) = _ at hid
  have hnonneg : 0 ≤ fillingCoefficient m * B^(fillingPower m) := mul_nonneg hc.le (Real.rpow_nonneg hB _)
  have hbd := mul_le_mul_of_nonneg_right hsmall hnonneg
  rw [hid] at hbd
  nlinarith

end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def radialInverse (R : ℝ → ℝ) (U ρ : ℝ) : ℝ :=
  sSup {t | 0 ≤ t ∧ t < U ∧ ρ < R t}

lemma radialInverse_bdd (R : ℝ → ℝ) (U ρ : ℝ) :
    BddAbove {t | 0 ≤ t ∧ t < U ∧ ρ < R t} := ⟨U,fun _ ht => ht.2.1.le⟩

lemma radialInverse_nonneg (R : ℝ → ℝ) (U ρ : ℝ) : 0 ≤ radialInverse R U ρ :=
  Real.sSup_nonneg (fun _ ht => ht.1)

lemma radialInverse_le (R : ℝ → ℝ) {U : ℝ} (hU : 0 ≤ U) (ρ : ℝ) :
    radialInverse R U ρ ≤ U := by
  apply Real.sSup_le
  · exact fun _ ht => ht.2.1.le
  · exact hU

lemma radialInverse_antitone (R : ℝ → ℝ) (U : ℝ) : Antitone (radialInverse R U) := by
  intro a b hab
  apply Real.sSup_le
  · intro t ht
    apply le_csSup (radialInverse_bdd R U a)
    exact ⟨ht.1,ht.2.1,hab.trans_lt ht.2.2⟩
  · exact radialInverse_nonneg R U a

lemma mem_of_lt_radialInverse {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 ≤ t) (h : t < radialInverse R U ρ) :
    t < U ∧ ρ < R t := by
  have hne : {s | 0 ≤ s ∧ s < U ∧ ρ < R s}.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [radialInverse,he,Real.sSup_empty] at h
    linarith
  obtain ⟨s,hs,hts⟩ := (lt_csSup_iff (radialInverse_bdd R U ρ) hne).mp h
  have htU := hts.trans hs.2.1
  exact ⟨htU,hs.2.2.trans_le (hR ⟨ht,htU.le⟩ ⟨hs.1,hs.2.1.le⟩ hts.le)⟩

lemma radius_le_of_inverse_lt {R : ℝ → ℝ} {U ρ t : ℝ}
    (ht : 0 ≤ t) (htU : t < U) (h : radialInverse R U ρ < t) : R t ≤ ρ := by
  by_contra hn
  have hx : t ≤ radialInverse R U ρ := le_csSup (radialInverse_bdd R U ρ)
    ⟨ht,htU,not_le.mp hn⟩
  linarith

lemma radialInverse_lipschitz {R : ℝ → ℝ} {U c : ℝ}
    (_ : 0 ≤ U) (hc : 0 < c) (hR : AntitoneOn R (Icc 0 U))
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t) :
    LipschitzWith (Real.toNNReal c⁻¹) (radialInverse R U) := by
  have hdiff {a b : ℝ} (hab : a ≤ b) :
      c*(radialInverse R U a-radialInverse R U b) ≤ b-a := by
    by_contra hn
    have hn' : b-a < c*(radialInverse R U a-radialInverse R U b) := not_le.mp hn
    have hgap : radialInverse R U b < radialInverse R U a := by
      by_contra hg
      have := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr (not_lt.mp hg))
      linarith
    let ε := ((radialInverse R U a-radialInverse R U b)-(b-a)/c)/4
    have hε : 0 < ε := by
      dsimp only [ε]
      apply div_pos _ (by norm_num)
      exact sub_pos.mpr ((div_lt_iff₀ hc).mpr (by nlinarith))
    have hεgap : 2*ε < radialInverse R U a-radialInverse R U b := by
      have hba : 0 ≤ (b-a)/c := div_nonneg (sub_nonneg.mpr hab) hc.le
      dsimp only [ε]
      linarith
    let s := radialInverse R U b+ε
    let t := radialInverse R U a-ε
    have hs0 : 0 < s := by
      have := radialInverse_nonneg R U b
      dsimp only [s]; linarith
    have hst : s < t := by dsimp only [s,t]; linarith
    have hta : t < radialInverse R U a := by dsimp only [t]; linarith
    have htU := (mem_of_lt_radialInverse hR (hs0.trans hst).le hta).1
    have hRt := (mem_of_lt_radialInverse hR (hs0.trans hst).le hta).2
    have hRs := radius_le_of_inverse_lt hs0.le (hst.trans htU)
      (show radialInverse R U b < s by dsimp only [s]; linarith)
    have hbound := hD s t hs0 hst htU
    have heq : c*((radialInverse R U a-radialInverse R U b)-4*ε) = b-a := by
      dsimp only [ε]
      field_simp
      ring
    dsimp only [s,t] at hbound
    nlinarith [mul_pos hc hε]
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (radialInverse_antitone R U hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    have := hdiff hab
    have hi : c⁻¹*c = 1 := inv_mul_cancel₀ hc.ne'
    have hm := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc.le)
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (radialInverse_antitone R U hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    have := hdiff hab
    have hi : c⁻¹*c = 1 := inv_mul_cancel₀ hc.ne'
    have hm := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc.le)
    nlinarith

lemma radialInverse_superlevel {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 ≤ t) (htU : t < U)
    (hcont : ContinuousWithinAt R (Ici t) t) :
    t < radialInverse R U ρ ↔ ρ < R t := by
  constructor
  · exact fun h => (mem_of_lt_radialInverse hR ht h).2
  · intro hρ
    have hright : ContinuousWithinAt R (Ioi t) t :=
      hcont.mono (Ioi_subset_Ici_self)
    have hr : ∀ᶠ s in 𝓝[>] t, ρ < R s :=
      hright (isOpen_Ioi.mem_nhds hρ)
    have hu : ∀ᶠ s in 𝓝[>] t, s < U :=
      (eventually_lt_nhds htU).filter_mono nhdsWithin_le_nhds
    have hall : ∀ᶠ s in 𝓝[>] t, t < s ∧ ρ < R s ∧ s < U := by
      filter_upwards [self_mem_nhdsWithin, hr, hu] with s hs hr hu
      exact ⟨hs,hr,hu⟩
    obtain ⟨s,hs,hsr,hsU⟩ := hall.exists
    exact hs.trans_le (le_csSup (radialInverse_bdd R U ρ) ⟨ht.trans hs.le,hsU,hsr⟩)

lemma radialInverse_zero_outside {R : ℝ → ℝ} {U ρ : ℝ}
    (hU : 0 ≤ U) (hR : AntitoneOn R (Icc 0 U)) (hρ : R 0 ≤ ρ) :
    radialInverse R U ρ = 0 := by
  have he : {t | 0 ≤ t ∧ t < U ∧ ρ < R t} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hh := hR ⟨le_rfl,hU⟩ ⟨ht.1,ht.2.1.le⟩ ht.1
    exact hρ.not_gt (ht.2.2.trans_le hh)
  simp only [radialInverse,he,Real.sSup_empty]

lemma radialInverse_at_zero {R : ℝ → ℝ} {U : ℝ} (hU : 0 < U)
    (hpos : ∀ t ∈ Ico 0 U, 0 < R t) : radialInverse R U 0 = U := by
  apply le_antisymm (radialInverse_le R hU.le 0)
  apply le_of_forall_lt_imp_le_of_dense
  intro a ha
  by_cases ha0 : a < 0
  · exact ha0.le.trans (radialInverse_nonneg R U 0)
  · apply le_csSup (radialInverse_bdd R U 0)
    exact ⟨not_lt.mp ha0,ha,hpos a ⟨not_lt.mp ha0,ha⟩⟩

lemma radialInverse_radius_identity {R : ℝ → ℝ} {U c t : ℝ}
    (hc : 0 < c) (hR : AntitoneOn R (Icc 0 U)) (ht : 0 < t) (htU : t < U)
    (hD : ∀ s v : ℝ, 0 < s → s < v → v < U → c*(v-s) ≤ R s-R v) :
    radialInverse R U (R t) = t := by
  apply le_antisymm
  · apply Real.sSup_le
    · intro s hs
      by_contra hn
      have hh := hR ⟨ht.le,htU.le⟩ ⟨hs.1,hs.2.1.le⟩ (not_le.mp hn).le
      exact (hs.2.2.trans_le hh).false
    · exact ht.le
  · apply le_of_forall_lt_imp_le_of_dense
    intro a hat
    by_cases ha0 : a ≤ 0
    · exact ha0.trans (radialInverse_nonneg R U (R t))
    · have ha : 0 < a := lt_of_not_ge ha0
      have hr : R t < R a := by
        have hh := hD a t ha hat htU
        have hp := mul_pos hc (sub_pos.mpr hat)
        linarith
      exact le_csSup (radialInverse_bdd R U (R t)) ⟨ha.le,hat.trans htU,hr⟩

lemma radialInverse_fiber {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 < t) (htU : t < U)
    (hcont : ContinuousAt R t) (heq : radialInverse R U ρ = t) : ρ = R t := by
  apply le_antisymm
  · have hc : Tendsto R (𝓝[<] t) (𝓝 (R t)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hc
    have hz : ∀ᶠ s in 𝓝[<] t, 0 < s :=
      (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hz] with s hs hs0
    exact (mem_of_lt_radialInverse hR hs0.le (by rwa [heq])).2.le
  · by_contra hn
    have h := (radialInverse_superlevel hR ht.le htU hcont.continuousWithinAt).mpr
      (not_le.mp hn)
    rw [heq] at h
    exact lt_irrefl t h

end CAT0Fillings.Rearrangement
end

end OAI
