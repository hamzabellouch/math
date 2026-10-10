import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRaw

namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0<c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0<c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤capacityGap c/200 ∧ τ≤capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_retained_margins (H D c B θ v Hfreq η τ Q : ℝ)
    (hH : 1<H) (hD : 1≤D) (hc : 0<c) (hcap : D^(1+c)≤H)
    (hP : -2*η≤B-θ) (hQ : Q≤B-θ+3*η) (hη : 0≤η)
    (hηsmall : η≤capacityGap c/100) (hτ : τ≤capacityGap c/100)
    (hcut : InverseInitialProfile.radialCenter 1 Hfreq θ (Real.logb H D) B≤4*η+τ) :
    CanonicalMargins
      (max 0 (Real.logb H D-B-v)+(θ+v+2*η)) (θ+Hfreq+2*η) Q 0
      (3*capacityGap c/4) := by
  obtain ⟨hr,hfirst,hsecond,_⟩:=raw_log_capacity H D c hH hD hc hcap
  have hh:=enlarged_initial_margins 1 (Real.logb H D) 0 0 B θ v Hfreq η τ Q
    (capacityGap c) (capacityGap c)
    (by simpa using hfirst) (by simpa using hsecond) (by norm_num) hP
    (by simpa using hQ) (by simpa using (capacityGap_pos c hc).le) hη
    (by simpa using hηsmall) (by simpa using hτ) (by simpa using hcut)
  simpa using hh

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤H*(H*max 1 D)^κ := by
  have hHp : 0<H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI
