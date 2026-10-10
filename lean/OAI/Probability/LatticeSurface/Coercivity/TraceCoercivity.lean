import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.DenseSpread
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.PinSpread

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

lemma trace_coercivity (C : ℝ) (hC : 1≤C) :
    ∃ T : ℝ,0<T ∧ ∀ (N : ℕ),1≤N → ∀ (w ν u v : Vertex → ℝ) (d : Vertex → ℕ)
    (K D : ℝ),0≤K → 0≤D →
    (∑ z∈square N,|w z|)≤C → (∀ z∈square N,|w z|≤C/(N:ℝ)^2) →
    (∀ z∈square N,0≤ν z) → (∑ z∈square N,ν z)≤1 →
    (∀ z∈square N,∀ r : ℝ,0≤r → r≤2*(N:ℝ) →
      (∑ y∈ball N z r,ν y)≤C*((r+1)/(N:ℝ))) →
    (∑ z∈square N,(d z+1:ℝ)^12)≤D*(N:ℝ)^2 →
    (∑ z∈square N,ν z*(d z+1:ℝ))≤D →
    (∀ z∈square N,|u z-v z|≤2*K*(d z+1:ℝ)) →
    ((∑ z∈square N,w z)=0 ∨
      ((∑ z∈square N,ν z)=1 ∧ ∀ z∈square N,ν z≠0 → u z=0)) →
    |∑ z∈square N,w z*u z|≤4*K*C*D+
      (1+C)*T*(N:ℝ)^(-(1/3:ℝ))*(energy N (3/2) v)^(2/3:ℝ) := by
  classical
  obtain ⟨T,hT,htrace⟩ := signed_spread_trace (3/2) 1 (4*C) (by norm_num)
    (by norm_num) (by norm_num) (by linarith)
  refine ⟨T,hT,?_⟩
  intro N hN w ν u v d K D hK hD hw hdense hν hνmass hνspread hm hνmom herr hanchor
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hC0 : 0≤C := by linarith
  let g : ℝ := (N:ℝ)^(-(1/3:ℝ))*(energy N (3/2) v)^(2/3:ℝ)
  have hg : 0≤g := by dsimp [g,energy];positivity
  have htw : |(∑ z∈square N,w z*v z)-(∑ z∈square N,w z)*mean N v|≤T*g := by
    have hh := htrace N hN w v (hw.trans (by linarith)) (by
      intro z hz r hr hrN
      simpa only [Real.rpow_one] using dense_spread N hN C hC0 (fun z => |w z|) hdense z r hr)
    norm_num only [show (1-2/(3/2):ℝ)= -(1/3) by norm_num,
      show (1/(3/2):ℝ)=2/3 by norm_num] at hh
    simpa only [g,mul_assoc] using hh
  have htn : |(∑ z∈square N,ν z*v z)-(∑ z∈square N,ν z)*mean N v|≤T*g := by
    have hh := htrace N hN ν v (by
      rw [Finset.sum_congr rfl (fun z hz => abs_of_nonneg (hν z hz))]
      exact hνmass.trans (by linarith)) (by
      intro z hz r hr hrN
      have habs : (∑ y∈ball N z r,|ν y|)=(∑ y∈ball N z r,ν y) :=
        Finset.sum_congr rfl (fun y hy => abs_of_nonneg (hν y (Finset.mem_filter.mp hy).1))
      rw [habs]
      rw [Real.rpow_one]
      exact (hνspread z hz r hr hrN).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
    norm_num only [show (1-2/(3/2):ℝ)= -(1/3) by norm_num,
      show (1/(3/2):ℝ)=2/3 by norm_num] at hh
    simpa only [g,mul_assoc] using hh
  have hfill : |(∑ z∈square N,w z*u z)-(∑ z∈square N,w z*v z)|≤2*K*C*D := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ z∈square N,|w z*u z-w z*v z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z∈square N,(2*K*C/(N:ℝ)^2)*(d z+1:ℝ)^12 := by
        apply Finset.sum_le_sum
        intro z hz
        rw [← mul_sub,abs_mul]
        have hd : (d z+1:ℝ)≤(d z+1:ℝ)^12 := le_self_pow₀ (by nlinarith [(show (0:ℝ)≤d z from Nat.cast_nonneg _)]) (by norm_num)
        calc
          _ ≤ (C/(N:ℝ)^2)*(2*K*(d z+1:ℝ)) :=
            mul_le_mul (hdense z hz) (herr z hz) (abs_nonneg _) (by positivity)
          _ ≤ (C/(N:ℝ)^2)*(2*K*(d z+1:ℝ)^12) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
          _ = _ := by ring
      _ = (2*K*C/(N:ℝ)^2)*(∑ z∈square N,(d z+1:ℝ)^12) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2*K*C/(N:ℝ)^2)*(D*(N:ℝ)^2) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by field_simp
  have htest : |∑ z∈square N,w z*v z|≤2*K*C*D+(1+C)*T*g := by
    rcases hanchor with hz|⟨hmass,hpin⟩
    · rw [hz,zero_mul,sub_zero] at htw
      nlinarith [mul_nonneg hC0 (mul_nonneg hT.le hg),mul_nonneg hK hD]
    · have hnval : |∑ z∈square N,ν z*v z|≤2*K*D := by
        calc
          _ ≤ ∑ z∈square N,|ν z*v z| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ z∈square N,2*K*(ν z*(d z+1:ℝ)) := by
            apply Finset.sum_le_sum
            intro z hz
            by_cases hn : ν z=0
            · simp [hn]
            have hu := hpin z hz hn
            have he := herr z hz
            rw [hu,zero_sub,abs_neg] at he
            rw [abs_mul,abs_of_nonneg (hν z hz)]
            calc
              _ ≤ ν z*(2*K*(d z+1:ℝ)) := mul_le_mul_of_nonneg_left he (hν z hz)
              _ = _ := by ring
          _ = 2*K*(∑ z∈square N,ν z*(d z+1:ℝ)) := (Finset.mul_sum _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hνmom (by positivity)
      rw [hmass,one_mul] at htn
      have hmean : |mean N v|≤2*K*D+T*g := by
        have hh := abs_sub_le (∑ z∈square N,ν z*v z) (mean N v) 0
        simpa only [sub_zero,abs_sub_comm] using (show |mean N v|≤2*K*D+T*g by
          have htri := abs_add_le ((∑ z∈square N,ν z*v z)-mean N v) (mean N v)
          have htri' := abs_sub_le (mean N v) (∑ z∈square N,ν z*v z) 0
          rw [sub_zero,sub_zero,abs_sub_comm (mean N v)] at htri'
          linarith)
      have hwm : |(∑ z∈square N,w z)*mean N v|≤C*(2*K*D+T*g) := by
        rw [abs_mul]
        exact mul_le_mul ((Finset.abs_sum_le_sum_abs _ _).trans hw) hmean (abs_nonneg _) hC0
      have ht := abs_add_le ((∑ z∈square N,w z*v z)-(∑ z∈square N,w z)*mean N v)
        ((∑ z∈square N,w z)*mean N v)
      rw [sub_add_cancel] at ht
      nlinarith
  have htri := abs_add_le ((∑ z∈square N,w z*u z)-(∑ z∈square N,w z*v z))
    (∑ z∈square N,w z*v z)
  rw [sub_add_cancel] at htri
  dsimp [g] at htest
  nlinarith

end GridTrace

end

end OAI
