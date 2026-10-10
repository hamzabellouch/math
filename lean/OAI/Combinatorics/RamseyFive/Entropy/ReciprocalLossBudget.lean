import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.StreamGeometry
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalDropNumerics
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalRoundNumerics

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking
open scoped Topology
noncomputable section

lemma reciprocal_total_fraction {w n l bad drop : ℝ}
    (hw : 0≤w) (hn : 0≤n) (hl : l≤w*n)
    (hbad : bad≤w*n/10000) (hdrop : drop≤w/10000) :
    5*bad+(2*n)*drop+(w*(2*n))*(1/10000)≤(w*(2*n)-l)/10 := by
  have := mul_le_mul_of_nonneg_left hdrop (show 0≤2*n by positivity)
  nlinarith [mul_nonneg hw hn]

theorem eventually_reciprocal_loss_budget {η : ℝ} (hη : 0<η)
    (c C Cm : ℝ) (hc : 0<c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D m w n B T rem M G l : ℝ),
      0<q→σ^beta η≤D→1≤w→0<n→m≤8*w*n→0≤B→B≤C*m*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2≤T→n/2≤rem→0≤M→M≤Cm*σ→l≤w*n→
      ∀closed : Bool,(closed=true→(c/8)*q*σ^(1+η)≤n)→
        (closed=false→(c/8)*σ^(1+η/2)≤w*D)→
        (closed=true→G≤2*D*σ^(3*beta η))→(closed=false→G≤3*σ)→
      5*(B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q))+
        (2*n)*((G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η)))+
        (w*(2*n))*(1/10000)≤(w*(2*n)-l)/10 := by
  have hcd : 0≤2+24/c := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_reciprocal_round_fraction hη (c/8) (2*C) Cm (1/10000) (by positivity) (by positivity) hCm (by norm_num),
    eventually_reciprocal_drop_fraction hη (2+24/c) (1/10000) hcd (by norm_num)] with σ hσ hround hdrop
  intro q D m w n B T rem M G l hq hD hw hn hm hB hBhi hT hr hM hMhi hl closed hclosed hopen hGc hGo
  have hw0 : 0≤w := by linarith
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have hB' : B≤(2*C)*(4*w*n)*D*σ^(-beta η) := by
    apply hBhi.trans
    calc
      _ ≤C*(8*w*n)*D*σ^(-beta η) := by gcongr
      _ =_ := by ring
  have hG : G≤(2+24/c)*w*D*σ^(3*beta η) := by
    cases closed with
    | true =>
      calc
        G≤2*D*σ^(3*beta η) := hGc rfl
        _ ≤2*w*D*σ^(3*beta η) := by gcongr;linarith
        _ ≤_ := by
          have hh : (2:ℝ)≤2+24/c := le_add_of_nonneg_right (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hh hw0) hDp.le) (by positivity)
    | false =>
      calc
        G≤3*σ := hGo rfl
        _ ≤(3/(c/8))*w*D*σ^(3*beta η) :=
          open_gap_scale hη hσ (by positivity) hw0 hDp.le (hopen rfl)
        _ = (24/c)*w*D*σ^(3*beta η) := by ring
        _ ≤_ := by gcongr; linarith
  have hh:=hround q D w n B T rem M hq hD hw0 hn hB hB' hT hr hM hMhi closed hclosed
  have hh':=hdrop D w G hD hw0 hG
  apply reciprocal_total_fraction hw0 hn.le hl
  · simpa only [mul_one_div] using hh
  · simpa only [mul_one_div] using hh'
end
end SharpRamseyFive.ParameterHierarchy

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype β] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {Λ J Λ' J' : ℝ}
def ContextDescription.mono (C : ContextDescription (κ:=κ) p x Λ J)
    (hΛ : Λ≤Λ') (hJ : J≤J') : ContextDescription (κ:=κ) p x Λ' J' where
  context:=C.context
  domain:=C.domain
  entropy_bound:=C.entropy_bound.trans hΛ
  contains:=C.contains
  cap z hz i:=(C.cap z hz i).trans hJ
lemma card_le_of_log_le {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (h : Real.log a≤Real.log b) : a≤b := by
  rcases eq_or_lt_of_le ha with he|he
  · linarith
  · exact (Real.log_le_log_iff he hb).mp h
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype α]
  {N n : ℕ} {admissible : (Fin N→α)→Prop} {d Λ J M d' Λ' J' : ℝ}
def CodedStream.mono (S : CodedStream (K:=K) (V:=V) N n admissible d Λ J M)
    (hd : d≤d') (hΛ : Λ≤Λ') (hJ : J≤J') :
    CodedStream (K:=K) (V:=V) N n admissible d' Λ' J' M where
  sample:=S.sample
  stream:=S.stream
  code:=S.code
  description:=S.description.mono hΛ hJ
  density_bound:=S.density_bound.trans hd
  geometric:=S.geometric
end
end SharpRamseyFive.SelectedTuple

end OAI
