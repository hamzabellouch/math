import Mathlib
import OAI.Geometry.CAT0Fillings.Isoperimetry.SmallCells

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations MassMeasure BorelRestriction CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem compact_cell_filling (hX : IsCAT0 X) {k : ℕ} {c p r : ℝ}
    (hc : 0 ≤ c) (hp : 0 < p) (hr : 0 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ c*(mass P)^p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Functional X (k+2), IsIntegral (k+2) T →
      boundarySucc T = 0 → fillingVolume T ≤ 2*r*mass T+C*(mass T)^p := by
  classical
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun o : X => ball o r)
    (fun _ => isOpen_ball) (by intro x _; exact mem_iUnion.mpr ⟨x,mem_ball_self hr⟩)
  obtain ⟨C,hC,hCF⟩ := finite_cell_filling hX hc hp hr hfill F
  refine ⟨2*diam (univ : Set X)*C,by positivity,?_⟩
  intro T hT hz
  have hs : currentMassMeasure hT.1 (⋃ o ∈ F,ball o r)ᶜ = 0 := by
    rw [eq_univ_of_univ_subset hF,compl_univ,measure_empty]
  obtain ⟨R,S,hR,hS,hRb,hSb,hRm,hSm⟩ := hCF T hT hs
  have hRz : boundarySucc R = 0 := hRb.trans hz
  obtain ⟨U,hU,hUb,hUm⟩ := hX.exists_integral_filling_weighted hR hRz (Classical.arbitrary X)
  have hUma : mass U ≤ diam (univ : Set X)*mass R :=
    hUm.trans (integral_dist_le_diam hR.1 _)
  have hb : boundarySucc (S+U) = T := by
    rw [boundarySucc_add,hSb,hUb,sub_add_cancel]
  apply (fillingVolume_le (hS.add hU) hb).trans
  apply (mass_add_le hS.1 hU.1).trans
  simp only [hz,show mass (0 : Functional X (k+1)) = 0 from mass_zero _,add_zero] at hRm hSm
  have hh := mul_le_mul_of_nonneg_left hRm (diam_nonneg (s := univ (α := X)))
  nlinarith

theorem uniform_filling_littleO (hX : IsCAT0 X) {k : ℕ} {c p : ℝ}
    (hc : 0 ≤ c) (hp : 1 < p)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ c*(mass P)^p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : Functional X (k+2), IsIntegral (k+2) T →
      boundarySucc T = 0 → mass T < δ → fillingVolume T ≤ ε*mass T := by
  obtain ⟨C,hC,hbound⟩ := compact_cell_filling hX hc (by linarith : 0 < p)
    (by positivity : 0 < ε/4) hfill
  have hp1 : 0 < p-1 := sub_pos.mpr hp
  have hcont : ContinuousAt (fun t : ℝ => C*t^(p-1)) 0 :=
    ((Real.continuous_rpow_const hp1.le).const_mul C).continuousAt
  have hnb : ∀ᶠ t : ℝ in 𝓝 0, C*t^(p-1) < ε/2 :=
    hcont.eventually (gt_mem_nhds (by simpa only [Real.zero_rpow hp1.ne',mul_zero] using half_pos hε))
  obtain ⟨δ,hδ,hδb⟩ := Metric.eventually_nhds_iff.mp hnb
  refine ⟨δ,hδ,?_⟩
  intro T hT hz hsmall
  have hm := mass_nonneg T
  by_cases hzero : mass T = 0
  · have hh := hbound T hT hz
    rw [hzero,Real.zero_rpow (by linarith : p ≠ 0)] at hh
    simpa only [hzero,mul_zero,add_zero] using hh
  have hpos : 0 < mass T := lt_of_le_of_ne hm (Ne.symm hzero)
  have hexp : (mass T)^p = mass T*(mass T)^(p-1) := by
    calc
      _ = (mass T)^(1+(p-1)) := by congr 1; ring
      _ = (mass T)^1*(mass T)^(p-1) := Real.rpow_add hpos _ _
      _ = _ := by rw [Real.rpow_one]
  have hs := hδb (y := mass T) (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hm] using hsmall)
  have hh := hbound T hT hz
  rw [hexp] at hh
  nlinarith [mul_le_mul_of_nonneg_left hs.le hm]

end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations MassMeasure BorelRestriction CurrentOperations

lemma rpow_difference_lower {m x q : ℝ} (hm : 0 < m) (hq : 1 < q)
    (hx : m/2 ≤ x) (hxm : x ≤ m) :
    (m/2)^(q-1)*(m-x) ≤ m^q-x^q := by
  have hx0 : 0 < x := lt_of_lt_of_le (half_pos hm) hx
  have hp0 : 0 ≤ q-1 := by linarith
  have hmx := Real.rpow_le_rpow hx0.le hxm hp0
  have hhalf := Real.rpow_le_rpow (half_pos hm).le hx hp0
  have hf (t : ℝ) (ht : 0 < t) : t^q = t*t^(q-1) := by
    conv_lhs => rw [show q = 1+(q-1) by ring]
    rw [Real.rpow_add ht,Real.rpow_one]
  rw [hf m hm,hf x hx0]
  nlinarith [mul_le_mul_of_nonneg_left hmx hm.le,
    mul_le_mul_of_nonneg_right hhalf (sub_nonneg.mpr hxm)]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem small_restriction_mass_bound (hX : IsCAT0 X) {k : ℕ} {c p d q : ℝ}
    (hc : 0 ≤ c) (hp : 1 < p) (hd : 0 < d) (hq : 1 < q)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ c*(mass P)^p)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T)
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^q-(mass B)^q) ≤ fillingVolume (T-B))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, δ ∈ Ioo 0 (mass T/2) ∧ ∀ E : Set X, ∀ _hE : MeasurableSet E,
      IsIntegral (k+2) (restrictCurrent hT.1 E) → mass (restrictCurrent hT.1 E) ≤ δ →
      (1-η)*mass (restrictCurrent hT.1 E) ≤
        c*(mass (boundarySucc (restrictCurrent hT.1 E)))^p := by
  let α := d*(mass T/2)^(q-1)
  have hα : 0 < α := mul_pos hd (Real.rpow_pos_of_pos (half_pos hm) _)
  obtain ⟨δ₀,hδ₀,hsmall⟩ := uniform_filling_littleO hX hc hp hfill
    (show 0 < α*η/4 by positivity)
  let δ := min (mass T/4) (δ₀/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδm : δ < mass T/2 := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ,⟨hδ,hδm⟩,?_⟩
  intro E hE hU hUa
  let U := restrictCurrent hT.1 E
  let V := restrictCurrent hT.1 Eᶜ
  have hsum : U+V = T := restrictCurrent_add_compl hT.1 hE
  have hVeq : V = T-U := eq_sub_iff_add_eq.mpr ((add_comm V U).trans hsum)
  have hV : IsIntegral (k+2) V := by rw [hVeq]; exact hT.sub hU
  have hmasssum : mass U+mass V = mass T := mass_restriction_add_compl hT.1 hE
  obtain ⟨R,hR,hRb,hRm⟩ := hfill (boundarySucc U) hU.boundarySucc
    (boundarySucc_boundarySucc hU.1)
  have hb : boundarySucc (U-R) = 0 := by rw [boundarySucc_sub,hRb,sub_self]
  by_cases hRa : mass U ≤ mass R
  · apply le_trans _ hRm
    have hUn := mass_nonneg U
    nlinarith
  have hRa' : mass R < mass U := lt_of_not_ge hRa
  have hBa : mass (V+R) ≤ mass T-mass U+mass R := by
    have hh := mass_add_le hV.1 hR.1
    linarith
  have hBz : boundarySucc (V+R) = 0 := by
    rw [boundarySucc_add,hVeq,boundarySucc_sub,hz,zero_sub,hRb,neg_add_cancel]
  have hdiff : T-(V+R) = U-R := by
    calc
      _ = (U+V)-(V+R) := congrArg (fun W : Functional X (k+2) => W-(V+R)) hsum.symm
      _ = _ := by abel
  have hExt := hext (V+R) (hV.add hR) hBz
  rw [hdiff] at hExt
  have hx : mass T/2 ≤ mass T-mass U+mass R := by
    have hRn := mass_nonneg R
    change mass U ≤ δ at hUa
    linarith
  have hxm : mass T-mass U+mass R ≤ mass T := by linarith
  have hpbase := rpow_difference_lower hm hq hx hxm
  have hpow := Real.rpow_le_rpow (mass_nonneg (V+R)) hBa (by linarith : 0 ≤ q)
  have hlow : α*(mass U-mass R) ≤ fillingVolume (U-R) := by
    have h1 := mul_le_mul_of_nonneg_left hpbase hd.le
    have h2 := mul_le_mul_of_nonneg_left hpow hd.le
    dsimp only [α]
    nlinarith
  have htiny : mass (U-R) < δ₀ := by
    have hu : mass U ≤ δ₀/4 := hUa.trans (min_le_right _ _)
    have hsub := mass_sub_le hU.1 hR.1
    linarith
  have hupper := hsmall (U-R) (hU.sub hR) hb htiny
  have hupper' : fillingVolume (U-R) ≤ α*η/4*(mass U+mass R) :=
    hupper.trans (mul_le_mul_of_nonneg_left (mass_sub_le hU.1 hR.1) (by positivity))
  apply le_trans _ hRm
  by_contra hn
  have hn' : mass R < (1-η)*mass U := lt_of_not_ge hn
  have hu0 : 0 < mass U := lt_of_le_of_lt (mass_nonneg R) hRa'
  have he : α*(mass U-mass R) > α*η*mass U := by
    have hh := mul_lt_mul_of_pos_left hn' hα
    nlinarith
  have hpos := mul_pos (mul_pos hα hη) hu0
  have hh := mul_lt_mul_of_pos_left hRa' (show 0 < α*η/4 by positivity)
  nlinarith

end CAT0Fillings
end

end OAI
