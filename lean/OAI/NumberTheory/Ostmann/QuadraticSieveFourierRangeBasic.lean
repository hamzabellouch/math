import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRowsFourier
import OAI.NumberTheory.Ostmann.QuadraticSieveRootGaussMellinScale

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def twoSidedMellinMass (ρ : 𝓢(ℝ,ℂ)) (σ : ℝ) : ℝ :=
  1 + (∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖) +
    (∫ r : ℝ, ‖mellin (Ostmann.reflectedSchwartz ρ : ℝ → ℂ) (σ+r*Complex.I)‖)

theorem twoSidedMellinMass_pos (ρ : 𝓢(ℝ,ℂ)) (σ : ℝ) : 0 < twoSidedMellinMass ρ σ := by
  have h₁ : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
  have h₂ : 0 ≤ ∫ r : ℝ, ‖mellin (Ostmann.reflectedSchwartz ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
  unfold twoSidedMellinMass
  linarith

theorem nonzeroIntegerCutoff_card_le {T : ℝ} (hT : 1 ≤ T) :
    ((nonzeroIntegerCutoff (16*T^2)).card : ℝ) ≤ 33*T^2 := by
  have hL : 0 ≤ 16*T^2 := by positivity
  have hfl : (⌊16*T^2⌋ : ℤ) ≥ 0 := Int.floor_nonneg.mpr hL
  have hce : (⌈-(16*T^2)⌉ : ℤ) ≤ 0 := Int.ceil_nonpos.mpr (by linarith)
  have hcard := Finset.card_le_card (Finset.erase_subset (0 : ℤ)
    (Finset.Icc ⌈-(16*T^2)⌉ ⌊16*T^2⌋))
  have hc := Int.card_Icc_of_le ⌈-(16*T^2)⌉ ⌊16*T^2⌋ (show (⌈-(16*T^2)⌉ : ℤ) ≤ ⌊16*T^2⌋+1 by omega)
  have hcr : ((Finset.Icc ⌈-(16*T^2)⌉ ⌊16*T^2⌋).card : ℝ) =
      (⌊16*T^2⌋ : ℤ)+1-(⌈-(16*T^2)⌉ : ℤ) := by exact_mod_cast hc
  have hf : ((⌊16*T^2⌋ : ℤ) : ℝ) ≤ 16*T^2 := Int.floor_le _
  have he : -(16*T^2) ≤ ((⌈-(16*T^2)⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hh : ((nonzeroIntegerCutoff (16*T^2)).card : ℝ) ≤
      ((Finset.Icc ⌈-(16*T^2)⌉ ⌊16*T^2⌋).card : ℝ) := by exact_mod_cast hcard
  rw [hcr] at hh
  nlinarith [sq_nonneg (T-1)]

theorem rootGauss_signed_frequency_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ),
      0 < D → 0 < N → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      ∃ p ∈ divisorRangeScales D, ∀ (ρ : 𝓢(ℝ,ℂ)) (σ c B L : ℝ)
        (a b : ℕ → ℂ) (z l : ℤ),
      0 < σ → 0 < c → 0 < B → 0 < L → l ≠ 0 →
      (∀ v ∈ V, 0 < v ∧ (v : ℝ) ≤ B) →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) →
      (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
        rootGaussMellinKernel a b z d v n t *
          ρ (((l : ℝ)*c)*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v))‖) ≤
        (1/(2*Real.pi))*twoSidedMellinMass ρ σ*
          (c/((2*D : ℕ)*Real.sqrt B))^(-σ)*(2*(N : ℝ)/L)*
          Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
            quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
            quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
            coefficientEnergy S a*coefficientEnergy T b) := by
  classical
  obtain ⟨C,hC,hbound⟩ := rootGauss_mellin_sqrt_divisor_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T hD hN hVo hS hT
  have hne : (divisorRangeScales D).Nonempty := by
    refine ⟨(D,1),mem_divisorRangeScales.mpr ?_⟩
    simp only [mul_one]
    omega
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image (divisorRangeScales D)
    (fun q => (q.1*q.2 : ℕ)*quadraticNorm V (oddSquarefreeUpTo (N/q.1))*
      quadraticNorm V (oddSquarefreeUpTo (N/q.2))) hne
  refine ⟨p,hp,?_⟩
  intro ρ σ c B L a b z l hσ hc hB hL hl hV hSL hTL
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hla : 1 ≤ |(l : ℝ)| := by exact_mod_cast Int.one_le_abs hl
  let ρ' : 𝓢(ℝ,ℂ) := if 0 < l then ρ else Ostmann.reflectedSchwartz ρ
  have hmass : (∫ r : ℝ, ‖mellin (ρ' : ℝ → ℂ) (σ+r*Complex.I)‖) ≤ twoSidedMellinMass ρ σ := by
    have h₁ : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
    have h₂ : 0 ≤ ∫ r : ℝ, ‖mellin (Ostmann.reflectedSchwartz ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [ρ',twoSidedMellinMass]
    split_ifs <;> linarith
  obtain ⟨q,hq,hqbound⟩ := hbound ρ' σ hσ D N V S T a b z (|l| *c) B L hD hN hL
    (fun v hv => ⟨(hV v hv).1,hVo v hv,(hV v hv).2⟩) hS hT hSL hTL (by positivity) hB
  have heval (x : ℝ) : ρ' (|(l : ℝ)| *c*x) = ρ ((l : ℝ)*c*x) := by
    by_cases hlp : 0 < l
    · have hp : (0 : ℝ) < l := by exact_mod_cast hlp
      simp [ρ',hlp,abs_of_pos hp]
    · have hn : (l : ℝ) < 0 := by exact_mod_cast (show l < 0 by omega)
      simp [ρ',hlp,Ostmann.reflectedSchwartz_apply,abs_of_neg hn]
  have heval' (d v n t : ℕ) :
      ρ' (|(l : ℝ)| *c*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v)) =
      ρ ((l : ℝ)*c*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v)) := by
    convert heval (Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v)) using 1 <;> ring_nf
  simp only [Int.cast_abs] at hqbound
  simp_rw [heval'] at hqbound
  have hscale : (|(l : ℝ)| *c/((2*D : ℕ)*Real.sqrt B))^(-σ) ≤
      (c/((2*D : ℕ)*Real.sqrt B))^(-σ) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hc.le hla) (by positivity)
  have hrad : Real.sqrt (C*(N : ℝ)^ε*(q.1*q.2 : ℕ)*
      quadraticNorm V (oddSquarefreeUpTo (N/q.1))*quadraticNorm V (oddSquarefreeUpTo (N/q.2))*
      coefficientEnergy S a*coefficientEnergy T b) ≤
      Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
      quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
      coefficientEnergy S a*coefficientEnergy T b) := by
    apply Real.sqrt_le_sqrt
    have hm := hmax q hq
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm
      (show 0 ≤ C*(N : ℝ)^ε by positivity))
      (mul_nonneg (coefficientEnergy_nonneg S a) (coefficientEnergy_nonneg T b))
    simpa only [mul_assoc] using h
  apply hqbound.trans
  have hmi : 0 ≤ ∫ r : ℝ, ‖mellin (ρ' : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hmass0 := (twoSidedMellinMass_pos ρ σ).le
  gcongr

end Ostmann.QuadraticSieve

end OAI
