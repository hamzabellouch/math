import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.SignalCutoff

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SignalGoodRows
open Classical

theorem finset_sum_eq_of_zero_outside {ι : Type*} (f : ι → ℝ) (S T : Finset ι)
    (hS : ∀i,i∉S → f i=0) (hT : ∀i,i∉T → f i=0) :
    (∑i∈S,f i)=∑i∈T,f i := by
  calc
    _ = ∑i∈S∪T,f i := Finset.sum_subset Finset.subset_union_left (fun i _ hi => hS i hi)
    _ = _ := (Finset.sum_subset Finset.subset_union_right (fun i _ hi => hT i hi)).symm

theorem flagSignal_good_row_constants {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      (∀N : ℝ,0<N → ∀z : FlagSite a m D v,
        |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ Ca/N) ∧
      ∀(N r η κ : ℝ),0<N → Q ≤ N → 0<r → 0<η → η ≤ 1 → 0<κ →
        36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        ∀(z : FlagSite a m D v) (J : Finset (FlagSite a m D v)),flagGoodRow (r/N) κ z →
        (∀w,w∉J → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w=0) →
        |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w)-
          flagSignalDifference hD g (fun x => q+ψ x) N z| ≤
          (Cv*η/N)*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+
          (Ca/N)*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  obtain ⟨R,hR,hcharts⟩ := flagAffineData_separator_control (v:=v) g⁻¹
  obtain ⟨Q,hQ,hcutoff⟩ := flagSignalDifference_cutoff (v:=v) hD g ψ χ q hcompact hχ
  obtain ⟨Cv,hCv,hvar⟩ := flagSignalDifference_chart_variation (v:=v) hD g ψ hψ hsψ q
  obtain ⟨Ca,hCa,hamp⟩ := compactSignal_amplitude (v:=v) hD g ψ hψ hsψ q
  refine ⟨R,Q,Cv,Ca,hR,hQ,hCv,hCa,hamp,fun N r η κ hN hQN hr hη hη₁ hκ hscale hline hRf z J hz hJ => ?_⟩
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  obtain ⟨T,hT,herror⟩ := flagAveragingMatrix_good_row_error hD χ h hN hr hη hκ hscale hline
    (show 0 ≤ Cv*η/N by positivity) z hz (hamp N hN z) (hcutoff N r η hN hQN hη hη₁ z) (by
      intro w hw
      obtain ⟨ht,hord,hconj⟩ := (flagRowTent_ne_zero_iff _ _ _ _).mp hw
      have hsep := flagRowTent_separator_one (div_pos hr hN) hκ (N*η) z w hz hw
      have hchart : flagAffineData g⁻¹ z.val.1 z.val.2=flagAffineData g⁻¹ w.val.1 w.val.2 := by
        rw [← ht]
        exact hcharts (r/N) κ (div_pos hr hN) hκ hRf z.val.1 z.val.2 w.val.2 (by rw [hsep]; norm_num)
      have hv := hvar N η hN hη.le z w hchart (planeTent_scaled_near hN hη z w hconj)
      simpa only [abs_sub_comm] using hv)
  have he := finset_sum_eq_of_zero_outside
    (fun w => flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w) J T hJ hT
  change |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤ _
  rw [he]
  exact herror

end SignalGoodRows

section SignalActiveBox
open Classical

noncomputable def flagBoxFinset {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) {R : ℝ} (hR : 0<R) :
    Finset (FlagSite a m D v) := (flagSiteBox_finite (v:=v) hD hR).toFinset

@[simp] theorem mem_flagBoxFinset {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) {R : ℝ} (hR : 0<R)
    (z : FlagSite a m D v) : z∈flagBoxFinset hD hR ↔ z∈flagSiteBox R :=
  Set.Finite.mem_toFinset _

theorem flagAveragingMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L N : ℝ} (hL : 0<L) (hN : 0<N)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) (ρ r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos hN hL) ∨ w∉flagBoxFinset hD (mul_pos hN hL)) :
    flagAveragingMatrix χ ρ N r η κ z w=0 := by
  rcases hz with hz | hw
  · exact flagAveragingMatrix_cutoff_left χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc z (by simpa only [mem_flagBoxFinset] using hz))
  · exact flagAveragingMatrix_cutoff_right χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc w (by simpa only [mem_flagBoxFinset] using hw))

theorem flagSignal_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) (q : ℝ) {K L : ℝ}
    (hL : 0<L) (hKL : K+1 ≤ L) (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀(N : ℝ) (hN : 0<N),Q ≤ N → ∀z : FlagSite a m D v,
      z∉flagBoxFinset hD (mul_pos hN hL) →
        flagSignalDifference hD g (fun x => q+ψ x) N z=0 := by
  obtain ⟨Q,hQ,hdisp⟩ := scaledSiteConjugate_displacement (v:=v) hD g⁻¹
  refine ⟨Q,hQ,fun N hN hQN z hz => ?_⟩
  by_contra hh
  have hn := flagSignalDifference_ne_zero_near hD g ψ q hcompact hQ hN (hdisp N hN) z hh
  simp only [scaledSiteConjugate] at hn
  have hqn : Q/N ≤ 1 := (div_le_one hN).mpr hQN
  have hx := norm_fst_le (scaledSiteConjugate N z)
  have hy := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at hx hy
  apply hz
  rw [mem_flagBoxFinset]
  have hxL : |(flagSiteConjugate z).1|/N ≤ L := by linarith
  have hyL : |(flagSiteConjugate z).2|/N ≤ L := by linarith
  exact ⟨by simpa only [mul_comm L N] using (div_le_iff₀ hN).mp hxL,
    by simpa only [mul_comm L N] using (div_le_iff₀ hN).mp hyL⟩

theorem flagBoxFinset_card_quadratic {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) {L N : ℝ}
    (hL : 0<L) (hN : 1 ≤ N) :
    ((flagBoxFinset (a:=a) (m:=m) (v:=v) hD
      (mul_pos (lt_of_lt_of_le zero_lt_one hN) hL)).card:ℝ) ≤
      (m*(2*(D:ℝ)^2*L+2)^2)*N^2 := by
  have hN' : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hh := flagSiteBox_card_bound (a:=a) (m:=m) (v:=v) hD (mul_pos hN' hL)
    (flagBoxFinset hD (mul_pos hN' hL)) (fun z hz => (mem_flagBoxFinset _ _ _).mp hz)
  have he : 2*(D:ℝ)^2*(N*L)+2 ≤ (2*(D:ℝ)^2*L+2)*N := by nlinarith
  refine hh.trans ?_
  calc
    _ ≤ m*((2*(D:ℝ)^2*L+2)*N)^2 := by gcongr
    _ = _ := by ring

end SignalActiveBox

section ApproximationEnergy
open Classical

noncomputable def flagVolumeConstant (m D : ℕ) (Q : ℝ) : ℝ := m*(2*(D:ℝ)^2*Q+2)^2
noncomputable def flagExceptionalConstant (a m D : ℕ) (Q : ℝ) : ℝ :=
  4*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(1+|ordinary (cutTau^a)|)*Q+2)*
    (2*(D:ℝ)^2*Q+2)*(16*(1+|ordinary (cutTau^a)|)+2))
noncomputable def flagRowSumConstant (D : ℕ) : ℝ := (4*(D:ℝ)^2+2)^2/((D:ℝ)^4/5)+1

theorem flag_good_bad_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {Q κ s N E H : ℝ} (hQ : 0<Q) (hκ : 0<κ) (hs : 0<s) (hs₁ : s ≤ 1)
    (hN : 1 ≤ N) (hscale : 1 ≤ s*N) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (T : Finset (FlagSite a m D v)) (hT : ∀z∈T,z∈flagSiteBox (Q*N))
    (e : FlagSite a m D v → ℝ)
    (hgood : ∀z∈T,flagGoodRow s κ z → |e z| ≤ E/N)
    (hbad : ∀z∈T,|e z| ≤ H/N) :
    ∑z∈T,(e z)^2 ≤ flagVolumeConstant m D Q*E^2+
      flagExceptionalConstant a m D Q*(κ+s)*H^2 := by
  have hN' : 0<N := lt_of_lt_of_le zero_lt_one hN
  let B := T.filter (fun z => ¬flagGoodRow s κ z)
  have hb : (B.card:ℝ) ≤ flagExceptionalConstant a m D Q*(κ+s)*N^2 := by
    apply flagBadSeparatorRow_card_bound hD hQ hκ hs hs₁ hN hscale B
    intro z hz
    obtain ⟨hzt,hzb⟩ := Finset.mem_filter.mp hz
    refine ⟨hT z hzt,?_⟩
    simp only [flagGoodRow,not_forall,not_lt] at hzb
    obtain ⟨j,c,hc,he⟩ := hzb
    exact ⟨j,c,hc,he⟩
  have ht : (T.card:ℝ) ≤ flagVolumeConstant m D Q*N^2 := by
    have hh := flagSiteBox_card_bound hD (mul_pos hQ hN') T hT
    have he : 2*(D:ℝ)^2*(Q*N)+2 ≤ (2*(D:ℝ)^2*Q+2)*N := by nlinarith
    refine hh.trans ?_
    calc
      _ ≤ m*((2*(D:ℝ)^2*Q+2)*N)^2 := by gcongr
      _ = _ := by dsimp [flagVolumeConstant]; ring
  have hh := squared_error_good_bad T B e (div_nonneg hE hN'.le) (div_nonneg hH hN'.le)
    (by
      intro z hz hzb
      apply hgood z hz
      by_contra he
      exact hzb (Finset.mem_filter.mpr ⟨hz,he⟩)) hbad
  refine hh.trans ?_
  calc
    _ ≤ (flagVolumeConstant m D Q*N^2)*(E/N)^2+
        (flagExceptionalConstant a m D Q*(κ+s)*N^2)*(H/N)^2 := by
      gcongr
    _ = _ := by field_simp

end ApproximationEnergy

end SimpleAmenable
end
end

end OAI
