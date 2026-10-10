import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FlagAveragingMatrices
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FullGroupAffineData

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSignalEnergy
open Classical

noncomputable def flagMeanSignal {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) : ℝ :=
  θ (scaledSiteConjugate N z)

noncomputable def flagSignalDifference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) : ℝ :=
  flagMeanSignal θ N (flagSiteAction hD g⁻¹ z)-flagMeanSignal θ N z

theorem flagSignalDifference_chart {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g θ N z=
      θ ((flagSiteConjugate z).1/N+conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1/N,
         (flagSiteConjugate z).2/N+conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2/N)-
      θ (scaledSiteConjugate N z) := by
  simp only [flagSignalDifference,flagMeanSignal,scaledSiteConjugate,
    flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_div]

theorem flagSiteAction_displacement {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃Q : ℝ,0≤Q ∧ ∀z : FlagSite a m D v,
      |(flagSiteConjugate (flagSiteAction hD g z)).1-(flagSiteConjugate z).1|+
      |(flagSiteConjugate (flagSiteAction hD g z)).2-(flagSiteConjugate z).2| ≤ Q := by
  obtain ⟨Q,hQ,hb⟩ := flagAffineData_bounded (v:=v) g
    (fun u => |conjugate u.1|+|conjugate u.2|)
  refine ⟨Q,hQ,fun z => ?_⟩
  have hh := hb z.val
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hh
  simpa only [flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_sub_cancel_left] using hh

theorem flagSignalDifference_amplitude {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0≤L)
    (hLip : ∀x y,|θ x-θ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃ C : ℝ,0≤C ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      |flagSignalDifference hD g θ N z| ≤ C/N := by
  obtain ⟨Q,hQ,hdisp⟩ := flagSiteAction_displacement (v:=v) hD g⁻¹
  refine ⟨L*Q,mul_nonneg hL hQ,fun N hN z => ?_⟩
  have h := hLip (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)) (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,← sub_div,abs_div,abs_of_pos hN,← add_div] at h
  change |flagSignalDifference hD g θ N z| ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ L*(Q/N) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hdisp z) hN.le) hL
    _ = _ := (mul_div_assoc _ _ _).symm

theorem flagMeanSignal_outside {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSiteBox (N*K)) : flagMeanSignal θ N z=q := by
  apply hcompact
  by_contra hh
  have hh' : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge hh
  have h₁ := norm_fst_le (scaledSiteConjugate N z)
  have h₂ := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at h₁ h₂
  apply hz
  constructor
  · have h := (div_lt_iff₀ hN).mp (h₁.trans_lt hh'); nlinarith
  · have h := (div_lt_iff₀ hN).mp (h₂.trans_lt hh'); nlinarith

noncomputable def flagSignalSupport {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {K N : ℝ} (hK : 0<K) (hN : 0<N) : Finset (FlagSite a m D v) :=
  let S := (flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset
  S ∪ S.image (flagSiteAction hD g)

theorem flagSignalDifference_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hK : 0<K) (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSignalSupport hD g hK hN) : flagSignalDifference hD g θ N z=0 := by
  have hpair : z∉flagSiteBox (N*K) ∧ flagSiteAction hD g⁻¹ z∉flagSiteBox (N*K) := by
    have hn : z∉(flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset ∧
        z∉((flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset.image (flagSiteAction hD g)) := by
      simpa only [flagSignalSupport,Finset.mem_union,not_or] using hz
    refine ⟨?_,?_⟩
    · simpa only [Set.Finite.mem_toFinset] using hn.1
    · intro hh
      apply hn.2
      apply Finset.mem_image.mpr
      refine ⟨flagSiteAction hD g⁻¹ z,(Set.Finite.mem_toFinset _).mpr hh,?_⟩
      rw [← flagSiteAction_mul,mul_inv_cancel,flagSiteAction_one]
  simp only [flagSignalDifference,flagMeanSignal_outside θ hN hcompact z hpair.1,
    flagMeanSignal_outside θ hN hcompact _ hpair.2,sub_self]

theorem flagSignalSupport_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {K N : ℝ} (hK : 0<K) (hN : 0<N) (hN₁ : 1≤N) :
    ((flagSignalSupport (v:=v) hD g hK hN).card:ℝ) ≤
      2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*N^2 := by
  let S := (flagSiteBox_finite (a:=a) (m:=m) (v:=v) hD (mul_pos hN hK)).toFinset
  have hc : ((flagSignalSupport (v:=v) hD g hK hN).card:ℝ) ≤ 2*(S.card:ℝ) := by
    have hh := (Finset.card_union_le S (S.image (flagSiteAction hD g))).trans
      (Nat.add_le_add_left (Finset.card_image_le) S.card)
    change (S∪S.image (flagSiteAction hD g)).card ≤ S.card+S.card at hh
    have hh' : (((S∪S.image (flagSiteAction hD g)).card:ℝ)) ≤ (S.card:ℝ)+(S.card:ℝ) := by exact_mod_cast hh
    change ((S∪S.image (flagSiteAction hD g)).card:ℝ) ≤ 2*(S.card:ℝ)
    simpa only [← two_mul] using hh'
  have hb := flagSiteBox_card_bound hD (mul_pos hN hK) S
    (fun z hz => (Set.Finite.mem_toFinset _).mp hz)
  have hn : 2*(D:ℝ)^2*(N*K)+2 ≤ (2*(D:ℝ)^2*K+2)*N := by nlinarith
  calc
    _ ≤ 2*(S.card:ℝ) := hc
    _ ≤ 2*((m:ℝ)*(2*(D:ℝ)^2*(N*K)+2)^2) := by linarith
    _ ≤ 2*((m:ℝ)*((2*(D:ℝ)^2*K+2)*N)^2) := by gcongr
    _ = _ := by ring

theorem flagSignalDifference_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {q K L : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (hL : 0≤L)
    (hLip : ∀x y,|θ x-θ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃C : ℝ,0≤C ∧ ∀N : ℝ,1≤N → ∀T : Finset (FlagSite a m D v),
      ∑z∈T,(flagSignalDifference hD g θ N z)^2 ≤ C := by
  obtain ⟨B,hB,hamp⟩ := flagSignalDifference_amplitude (v:=v) hD g θ hL hLip
  refine ⟨2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*B^2,by positivity,fun N hN T => ?_⟩
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  let S := flagSignalSupport (v:=v) hD g hK hN₀
  have hsub : ∑z∈T,(flagSignalDifference hD g θ N z)^2 ≤ ∑z∈S,(flagSignalDifference hD g θ N z)^2 := by
    calc
      _ = ∑z∈T∩S,(flagSignalDifference hD g θ N z)^2 := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro z hz hnot
        have hzS : z∉S := by simpa only [Finset.mem_inter,hz,true_and] using hnot
        rw [flagSignalDifference_support hD g θ hK hN₀ hcompact z hzS]
        norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => sq_nonneg _)
  have hb (z : FlagSite a m D v) : (flagSignalDifference hD g θ N z)^2 ≤ (B/N)^2 :=
    by
      have hh := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hB hN₀.le)).mpr (hamp N hN₀ z)
      simpa only [sq_abs] using hh
  calc
    _ ≤ ∑z∈S,(flagSignalDifference hD g θ N z)^2 := hsub
    _ ≤ ∑_z∈S,(B/N)^2 := Finset.sum_le_sum (fun z _ => hb z)
    _ = (S.card:ℝ)*(B/N)^2 := by simp
    _ ≤ (2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*N^2)*(B/N)^2 :=
      mul_le_mul_of_nonneg_right (flagSignalSupport_card hD g hK hN₀ hN) (sq_nonneg _)
    _ = _ := by field_simp

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
