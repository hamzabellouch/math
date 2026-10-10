import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FlagSignalEnergy
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagTentMass

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WeightedAveragingError
open Classical

theorem weighted_average_error {ι : Type*} (T : Finset ι) (k h : ι → ℝ) (h₀ E H δ : ℝ)
    (hk : ∀i∈T,0≤k i) (hE : 0≤E) (hH : |h₀|≤H)
    (hmass : |(∑i∈T,k i)-1|≤δ)
    (hnear : ∀i∈T,k i≠0 → |h i-h₀|≤E) :
    |(∑i∈T,k i*h i)-h₀| ≤ E*(1+δ)+H*δ := by
  have hδ : 0≤δ := (abs_nonneg _).trans hmass
  have hH₀ : 0≤H := (abs_nonneg _).trans hH
  have he : (∑i∈T,k i*h i)-h₀=
      (∑i∈T,k i*(h i-h₀))+h₀*((∑i∈T,k i)-1) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    ring
  have hb : |∑i∈T,k i*(h i-h₀)| ≤ E*(∑i∈T,k i) := by
    calc
      _ ≤ ∑i∈T,|k i*(h i-h₀)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i∈T,k i*E := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_of_nonneg (hk i hi)]
        by_cases hh : k i=0
        · simp [hh]
        · exact mul_le_mul_of_nonneg_left (hnear i hi hh) (hk i hi)
      _ = _ := by rw [← Finset.sum_mul,mul_comm]
  rw [he]
  calc
    _ ≤ |∑i∈T,k i*(h i-h₀)|+|h₀*((∑i∈T,k i)-1)| := abs_add_le _ _
    _ ≤ E*(∑i∈T,k i)+H*δ := add_le_add hb (by rw [abs_mul]; exact mul_le_mul hH hmass (abs_nonneg _) hH₀)
    _ ≤ _ := by nlinarith [(abs_le.mp hmass).2]

theorem squared_error_good_bad {ι : Type*} (T B : Finset ι) (e : ι → ℝ)
    {E H : ℝ} (hE : 0≤E) (hH : 0≤H)
    (hgood : ∀i∈T,i∉B → |e i|≤E) (hbad : ∀i∈T,|e i|≤H) :
    ∑i∈T,(e i)^2 ≤ (T.card:ℝ)*E^2+(B.card:ℝ)*H^2 := by
  have hh : ∀i∈T,(e i)^2 ≤ E^2 + (if i∈B then H^2 else 0) := by
    intro i hi
    by_cases hb : i∈B
    · rw [ite_eq_left hb]
      have he := (sq_le_sq₀ (abs_nonneg _) hH).mpr (hbad i hi)
      rw [sq_abs] at he
      linarith [sq_nonneg E]
    · rw [ite_eq_right hb,add_zero]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hgood i hi hb)
  calc
    _ ≤ ∑i∈T,(E^2+(if i∈B then H^2 else 0)) := Finset.sum_le_sum hh
    _ = (T.card:ℝ)*E^2+((T.filter (·∈B)).card:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : ((T.filter (·∈B)).card:ℝ) ≤ (B.card:ℝ) := by
        exact_mod_cast Finset.card_le_card (show T.filter (·∈B) ⊆ B from fun i hi => (Finset.mem_filter.mp hi).2)
      linarith [mul_le_mul_of_nonneg_right hc (sq_nonneg H)]

end WeightedAveragingError

section SignalChartVariation
open Classical

theorem flagSignalDifference_add_constant {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) (q N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g (fun x => q+ψ x) N z=flagSignalDifference hD g ψ N z := by
  unfold flagSignalDifference flagMeanSignal
  ring

theorem flagSignalDifference_vector_chart {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g θ N z=
      θ (scaledSiteConjugate N z+N⁻¹ •
        (conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1,
         conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2))-θ (scaledSiteConjugate N z) := by
  rw [flagSignalDifference_chart hD]
  congr 2
  simp [scaledSiteConjugate,div_eq_mul_inv,mul_comm]

theorem flagSignalDifference_chart_variation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀(N η : ℝ),0<N → 0 ≤ η → ∀z w : FlagSite a m D v,
      flagAffineData g⁻¹ z.val.1 z.val.2=flagAffineData g⁻¹ w.val.1 w.val.2 →
      ‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ ≤ η →
      |flagSignalDifference hD g (fun x => q+ψ x) N z-
        flagSignalDifference hD g (fun x => q+ψ x) N w| ≤ C*η/N := by
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨Q,hQ,hbound⟩ := flagAffineData_bounded (v:=v) g⁻¹
    (fun u => ‖(conjugate u.1,conjugate u.2)‖)
  refine ⟨(L₁:ℝ)*Q,mul_nonneg L₁.coe_nonneg hQ,fun N η hN hη z w hchart hnear => ?_⟩
  rw [flagSignalDifference_add_constant,flagSignalDifference_add_constant,
    flagSignalDifference_vector_chart hD,flagSignalDifference_vector_chart hD,← hchart]
  let u := (conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1,
    conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2)
  have hu : ‖u‖ ≤ Q := by simpa only [abs_of_nonneg (norm_nonneg _)] using hbound z.val
  have hd : ‖N⁻¹ • u‖ ≤ Q/N := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN),div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left hu (inv_pos.mpr hN).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ (L₁:ℝ)*‖N⁻¹ • u‖*‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ := hL₁ _ _ _
    _ ≤ (L₁:ℝ)*(Q/N)*η := by gcongr
    _ = _ := by ring

theorem planeTent_scaled_near {a m D : ℕ} {v : ℝ×ℝ} {N η : ℝ} (hN : 0<N)
    (hη : 0<η) (z w : FlagSite a m D v)
    (h : planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)≠0) :
    ‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ ≤ η := by
  have hh := (planeTent_ne_zero (mul_pos hN hη) _ _).mp h
  rw [Prod.norm_def]
  apply max_le <;> simp only [scaledSiteConjugate,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,
    ← sub_div,abs_div,abs_of_pos hN]
  · exact (div_le_iff₀ hN).mpr (by nlinarith [hh.1.le])
  · exact (div_le_iff₀ hN).mpr (by nlinarith [hh.2.le])

end SignalChartVariation

section GoodRowAveraging
open Classical

def flagGoodRow {a m D : ℕ} {v : ℝ×ℝ} (s κ : ℝ) (z : FlagSite a m D v) : Prop :=
  ∀j c,|conjugate c| ≤ 2*κ/s →
    (1+|ordinary (cutTau^a)|)*s < |cutForm a j z.val.2.val-ordinary c|

theorem flagGoodRow_interior {a m D : ℕ} {v : ℝ×ℝ} {s κ : ℝ} (hs : 0<s)
    (hκ : 1 ≤ 2*κ/s) (z : FlagSite a m D v) (hz : flagGoodRow s κ z) :
    s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s := by
  have hzero : |conjugate (0:CutRing)| ≤ 2*κ/s := by simpa only [map_zero,abs_zero] using zero_le_one.trans hκ
  have hone : |conjugate (1:CutRing)| ≤ 2*κ/s := by simpa only [map_one,abs_one] using hκ
  have hx₀ := hz 0 0 hzero
  have hx₁ := hz 0 1 hone
  have hy₀ := hz 1 0 hzero
  have hy₁ := hz 1 1 hone
  have hx := z.val.2.property.2.1
  have hy := z.val.2.property.2.2.1
  simp [cutForm,map_zero,map_one,sub_zero,abs_of_nonneg hx.1,abs_of_nonneg hy.1,
    abs_of_nonpos (sub_nonpos.mpr hx.2),abs_of_nonpos (sub_nonpos.mpr hy.2)] at hx₀ hx₁ hy₀ hy₁
  change s<z.val.2.val.1 ∧ z.val.2.val.1<1-s ∧ s<z.val.2.val.2 ∧ z.val.2.val.2<1-s
  have hL : s ≤ (1+|ordinary (cutTau^a)|)*s := by nlinarith [abs_nonneg (ordinary (cutTau^a))]
  simp only [map_pow,ordinary_cutTau,abs_pow] at hL
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem flagRowTent_nonneg {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ) (z w : FlagSite a m D v) :
    0 ≤ flagRowTent s t z w := by
  unfold flagRowTent
  split_ifs
  · exact mul_nonneg (planeTent_nonneg _ _ _) (planeTent_nonneg _ _ _)
  · exact le_rfl

theorem flagRowTent_ne_zero_iff {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ) (z w : FlagSite a m D v) :
    flagRowTent s t z w≠0 ↔ z.val.1=w.val.1 ∧
      planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w)≠0 ∧
      planeTent t (flagSiteConjugate z) (flagSiteConjugate w)≠0 := by
  by_cases ht : z.val.1=w.val.1 <;> simp [flagRowTent,ht]

theorem flagRowTent_separator_one {a m D : ℕ} {v : ℝ×ℝ} {s κ : ℝ} (hs : 0<s)
    (hκ : 0<κ) (t : ℝ) (z w : FlagSite a m D v)
    (hz : flagGoodRow s κ z) (hw : flagRowTent s t z w≠0) :
    separatorMatrix (thresholdLaw s κ) z.val.2 w.val.2=1 := by
  apply separatorMatrix_eq_one_on_good_row hs hκ _ _ _ hz
  have hh := (planeTent_ne_zero hs _ _).mp ((flagRowTent_ne_zero_iff s t z w).mp hw).2.1
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le hh.1.le hh.2.le

theorem flagNormalization {D : ℕ} {N r η : ℝ} (hN : 0<N) :
    5/((D:ℝ)^4*(r/N)^2*(N*η)^2) = (((D:ℝ)^4/5)*(r*η)^2)⁻¹ := by
  have hd : (D:ℝ)^4*(r/N)^2*(N*η)^2=(D:ℝ)^4*(r*η)^2 := by field_simp
  rw [hd]
  ring

theorem flagAveragingMatrix_eq_rowTent {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v) :
    flagAveragingMatrix χ ρ N r η κ z w=
      (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)/(ρ*(r*η)^2))*
        flagRowTent (r/N) (N*η) z w*separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2 := by
  dsimp only [flagAveragingMatrix,flagRowTent,Matrix.of,Equiv.refl,DFunLike.coe,
    EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Matrix,id]
  split_ifs <;> ring

theorem flagAveragingMatrix_good_action {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ : ℝ}
    (hN : 0<N) (hr : 0<r) (hκ : 0<κ) (z : FlagSite a m D v)
    (hz : flagGoodRow (r/N) κ z)
    (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
      χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1) (w : FlagSite a m D v) :
    flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=
      (5/((D:ℝ)^4*(r/N)^2*(N*η)^2))*flagRowTent (r/N) (N*η) z w*h w := by
  rw [flagAveragingMatrix_eq_rowTent,flagNormalization hN]
  by_cases hhw : h w=0
  · simp [hhw]
  by_cases hkw : flagRowTent (r/N) (N*η) z w=0
  · simp [hkw]
  rw [(hχ w hkw hhw).1,(hχ w hkw hhw).2,flagRowTent_separator_one (div_pos hr hN) hκ _ z w hz hkw]
  ring

theorem flagAveragingMatrix_good_row_error {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ E H : ℝ}
    (hN : 0<N) (hr : 0<r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 36 ≤ r*η) (hline : 1 ≤ 2*κ/(r/N))
    (hE : 0 ≤ E) (z : FlagSite a m D v) (hz : flagGoodRow (r/N) κ z)
    (hH : |h z| ≤ H)
    (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
      χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1)
    (hnear : ∀w,flagRowTent (r/N) (N*η) z w≠0 → |h w-h z| ≤ E) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0) ∧
      |(∑w∈T,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤
        E*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+H*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  have hst : (r/N)*(N*η)=r*η := by field_simp
  obtain ⟨T,hT,hmass⟩ := flagRowTent_mass hD (div_pos hr hN) (mul_pos hN hη)
    (by rwa [hst]) z (flagGoodRow_interior (div_pos hr hN) hline z hz)
  let c := 5/((D:ℝ)^4*(r/N)^2*(N*η)^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hact := flagAveragingMatrix_good_action χ h hN hr hκ z hz hχ
  refine ⟨T,fun w hw => ?_,?_⟩
  · rw [hact w,hT w hw,mul_zero,zero_mul]
  · simp_rw [hact]
    have hh := weighted_average_error T (fun w => c*flagRowTent (r/N) (N*η) z w) h (h z) E H
      (38880/((D:ℝ)*Real.sqrt (r*η)))
      (fun w _ => mul_nonneg hc (flagRowTent_nonneg _ _ _ _)) hE hH
      (by simpa only [← Finset.mul_sum,hst] using hmass)
      (fun w _ hn => hnear w (fun he => hn (by simp [he])))
    exact hh

end GoodRowAveraging

end SimpleAmenable
end
end

end OAI
