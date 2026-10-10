import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicGapScale
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma exists_uniform_inner_scale {f : ℝ → ℝ} (hf : Tendsto f (𝓝[>] 0) (𝓝 0))
    {A ε : ℝ} (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0<s₀ ∧ ∀ {s a : ℝ}, 0<s → s<s₀ → 0<a → a≤A*s → f a<ε := by
  obtain ⟨d,hd,Hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hf.eventually (gt_mem_nhds hε))
  refine ⟨d/A,div_pos hd hA,?_⟩
  intro s a _ hss ha has
  apply Hd
  refine ⟨ha,has.trans_lt ?_⟩
  have h := (lt_div_iff₀ hA).mp hss
  simpa only [mul_comm] using h

def inverseResponseError (D F K κ L M a : ℝ) : ℝ :=
  Real.sqrt (D/(κ*a^(1+packetExponent))^5*a^(-699/100:ℝ))+
    (F/(κ*a^(1+packetExponent))^4*(2*a^(6/5:ℝ))+
      K/(κ*a^(1+packetExponent))^4*(Real.sqrt 3*(L*a^(101/100:ℝ))))*(M*a^(-3:ℝ))

lemma inverseResponseError_majorizes {D F K κ L M a v ell m : ℝ}
    (hD : 0≤D) (hF : 0≤F) (hK : 0≤K) (hκ : 0<κ) (hL : 0≤L) (_ : 0≤M)
    (ha : 0<a) (hv : κ*a^(1+packetExponent)≤v) (hell : ell≤L*a^(101/100:ℝ))
    (hm : m≤M*a^(-3:ℝ)) (hell0 : 0≤ell) (hm0 : 0 ≤ m) :
    Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m≤
        inverseResponseError D F K κ L M a := by
  have hv0 : 0<κ*a^(1+packetExponent) := by positivity
  unfold inverseResponseError
  gcongr

lemma inverseResponseError_expansion {D F K κ L M a : ℝ}
    (hD : 0≤D) (hκ : 0<κ) (ha : 0<a) :
    inverseResponseError D F K κ L M a*a^6=
      Real.sqrt (D/κ^5)*a^(1/200-5*packetExponent/2)+
      (2*F*M/κ^4)*a^(1/5-4*packetExponent)+
      (K*Real.sqrt 3*L*M/κ^4)*a^(1/100-4*packetExponent) := by
  have hpow (n : ℕ) : (κ*a^(1+packetExponent))^n=κ^n*a^((1+packetExponent)*n) := by
    rw [mul_pow,Real.rpow_mul_natCast ha.le]
  have hfirst : D/(κ*a^(1+packetExponent))^5*a^(-699/100:ℝ)=
      (D/κ^5)*a^(-(1+packetExponent)*5-699/100) := by
    rw [hpow]
    calc
      _ = (D/κ^5)*(a^(-699/100:ℝ)/a^((1+packetExponent)*5)) := by ring_nf
      _ = _ := by rw [←Real.rpow_sub ha]; congr 2; ring
  have hfrac : (κ*a^(1+packetExponent))^4=κ^4*a^((1+packetExponent)*4) := hpow 4
  unfold inverseResponseError
  rw [hfirst,Coulomb.sqrt_rpow_monomial ha (div_nonneg hD (pow_nonneg hκ.le _)),hfrac]
  have hterm₁ : (Real.sqrt (D/κ^5)*a^((-(1+packetExponent)*5-699/100)/2))*a^6=
      Real.sqrt (D/κ^5)*a^(1/200-5*packetExponent/2) := by
    rw [←Real.rpow_natCast a 6,mul_assoc,←Real.rpow_add ha]
    congr 2; ring
  have hterm₂ : (F/(κ^4*a^((1+packetExponent)*4))*(2*a^(6/5:ℝ)))*(M*a^(-3:ℝ))*a^6=
      (2*F*M/κ^4)*a^(1/5-4*packetExponent) := by
    calc
      _ = (2*F*M/κ^4)*((a^(6/5:ℝ)*a^(-3:ℝ)*a^6)/a^((1+packetExponent)*4)) := by ring
      _ = _ := by
        rw [←Real.rpow_natCast a 6,←Real.rpow_add ha,←Real.rpow_add ha,←Real.rpow_sub ha]
        congr 2; ring
  have hterm₃ : (K/(κ^4*a^((1+packetExponent)*4))*(Real.sqrt 3*(L*a^(101/100:ℝ))))*(M*a^(-3:ℝ))*a^6=
      (K*Real.sqrt 3*L*M/κ^4)*a^(1/100-4*packetExponent) := by
    calc
      _ = (K*Real.sqrt 3*L*M/κ^4)*((a^(101/100:ℝ)*a^(-3:ℝ)*a^6)/a^((1+packetExponent)*4)) := by ring
      _ = _ := by
        rw [←Real.rpow_natCast a 6,←Real.rpow_add ha,←Real.rpow_add ha,←Real.rpow_sub ha]
        congr 2; ring
  rw [add_mul,add_mul,add_mul,hterm₁,hterm₂,hterm₃]
  ring

lemma inverseResponseError_scaled_tendsto {D κ : ℝ} (hD : 0≤D) (hκ : 0<κ)
    (F K L M : ℝ) :
    Tendsto (fun a => inverseResponseError D F K κ L M a*a^6) (𝓝[>] 0) (𝓝 0) := by
  have H := (((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/200-5*packetExponent/2)).const_mul (Real.sqrt (D/κ^5))).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/5-4*packetExponent)).const_mul (2*F*M/κ^4))).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/100-4*packetExponent)).const_mul (K*Real.sqrt 3*L*M/κ^4))
  simp only [mul_zero,add_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (inverseResponseError_expansion hD hκ ha).symm

lemma lower_width_div_pow {a v κ : ℝ} (ha : 0<a) (hκ : 0<κ)
    (hv : κ*a^(1+packetExponent)≤v) (p : ℝ) (n : ℕ) :
    a^p/v^n≤(1/κ^n)*a^(p-(1+packetExponent)*n) := by
  have hbase : 0<κ*a^(1+packetExponent) := by positivity
  calc
    _ ≤ a^p/(κ*a^(1+packetExponent))^n := div_le_div_of_nonneg_left
      (Real.rpow_nonneg ha.le _) (pow_pos hbase _) (pow_le_pow_left₀ hbase.le hv n)
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast ha.le,Real.rpow_sub ha]
      ring

def inverseHighMeanError (H B γ κ N a v : ℝ) : ℝ :=
  2*H*a^(1/100:ℝ)+(4*B/(γ*κ^3))*a^(1/50-3*packetExponent)+4*N*(v/a)

lemma inverseHighMeanError_bound {H B γ κ N a v L G : ℝ}
    (hH : 0≤H) (hB : 0≤B) (hγ : 0<γ) (hκ : 0<κ) (_ : 0≤N)
    (ha : 0<a) (hv : κ*a^(1+packetExponent)≤v) (hL : 0≤L) (hLH : L≤H/a^4)
    (hG : G≤2*a^(-349/50:ℝ)) :
    ((L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*G+
        2*(N*(2*v/a))*(a^4)⁻¹)*a^4 ≤ inverseHighMeanError H B γ κ N a v := by
  have hv0 : 0<v := (by positivity : 0<κ*a^(1+packetExponent)).trans_le hv
  have he : 0≤L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6) := by positivity
  have hcap := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG he) (pow_nonneg ha.le 4)
  have hLcap : (L/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))*a^4≤
      2*H*a^(1/100:ℝ) := by
    calc
      _ ≤ ((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))*a^4 := by gcongr
      _ = _ := by
        have hrat : a^(-349/50:ℝ)/a^(-699/100:ℝ)=a^(1/100:ℝ) := by
          rw [←Real.rpow_sub ha]; norm_num
        field_simp [ha.ne'] at hrat ⊢
        nlinarith
  have hBcap : (2*(B/v^3)/(γ/a^6))*(2*a^(-349/50:ℝ))*a^4≤
      (4*B/(γ*κ^3))*a^(1/50-3*packetExponent) := by
    have hp : (a^6*a^(-349/50:ℝ)*a^4)=a^(151/50:ℝ) := by
      rw [←Real.rpow_natCast a 6,←Real.rpow_natCast a 4,←Real.rpow_add ha,←Real.rpow_add ha]
      norm_num
    calc
      _ = (4*B/γ)*(a^(151/50:ℝ)/v^3) := by rw [←hp]; field_simp; ring
      _ ≤ (4*B/γ)*((1/κ^3)*a^(151/50-(1+packetExponent)*3)) :=
        mul_le_mul_of_nonneg_left (lower_width_div_pow ha hκ hv _ _) (by positivity)
      _ = _ := by
        rw [show (151/50:ℝ)-(1+packetExponent)*3=1/50-3*packetExponent by ring]
        ring
  have hlast : (2*(N*(2*v/a))*(a^4)⁻¹)*a^4=4*N*(v/a) := by field_simp; ring
  unfold inverseHighMeanError
  rw [add_mul,hlast]
  have hh : (L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*G*a^4≤
      2*H*a^(1/100:ℝ)+(4*B/(γ*κ^3))*a^(1/50-3*packetExponent) := by
    apply hcap.trans
    rw [add_mul,add_mul]
    exact add_le_add hLcap hBcap
  exact add_le_add hh le_rfl

lemma inverseHighMeanError_uniform {H B γ κ N A V ε : ℝ}
    (hA : 0<A) (hN : 0≤N) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0<s₀ ∧ ∀ {s a v : ℝ}, 0<s → s<s₀ → 0<a → a≤A*s →
      v/a≤V*s^packetExponent → inverseHighMeanError H B γ κ N a v<ε := by
  have ht := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (2*H)).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] : (0:ℝ)<1/50-3*packetExponent)).const_mul (4*B/(γ*κ^3)))
  simp only [mul_zero,add_zero] at ht
  obtain ⟨s₁,hs₁,Hs₁⟩ := exists_uniform_inner_scale ht hA (by linarith : 0<ε/2)
  have ht' := (tendsto_positive_rpow_zero (by norm_num [packetExponent] : 0<packetExponent)).const_mul (4*N*V)
  simp only [mul_zero] at ht'
  obtain ⟨s₂,hs₂,Hs₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht'.eventually (gt_mem_nhds (by linarith : 0<ε/2)))
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,?_⟩
  intro s a v hs hss ha has hv
  have h1 := Hs₁ hs (hss.trans_le (min_le_left _ _)) ha has
  have h2 := Hs₂ ⟨hs,hss.trans_le (min_le_right _ _)⟩
  change 4*N*V*s^packetExponent < ε/2 at h2
  have h3 := mul_le_mul_of_nonneg_left hv (show 0≤4*N by positivity)
  unfold inverseHighMeanError
  nlinarith

end NeutralAtom
end

end

end OAI
