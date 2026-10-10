import OAI.NumberTheory.Ostmann.QuadraticSieveFourierRange
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBoundaryRootMellin

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory ComplexConjugate
open scoped SchwartzMap FourierTransform

theorem rootGauss_signed_frequency_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ,ℂ)) (σ c B L : ℝ)
      (N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (z l : ℤ),
      0 < σ → 0 < c → 0 < B → 0 < L → 0 < N → l ≠ 0 →
      (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) →
      (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
        rootGaussMellinKernel a b z 1 v n t *
          ρ (((l : ℝ)*c)*Real.sqrt ((n : ℝ)*t)/Real.sqrt v)‖) ≤
        (1/(2*Real.pi))*twoSidedMellinMass ρ σ*
          (c/Real.sqrt B)^(-σ)*(2*(N : ℝ)/L)*
          Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            coefficientEnergy S a*coefficientEnergy T b) := by
  classical
  obtain ⟨C,hC,hbound⟩ := rootGauss_mellin_sqrt_boundary_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ c B L N V S T a b z l hσ hc hB hL hN hl hV hS hT hSL hTL
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hla : 1 ≤ |(l : ℝ)| := by exact_mod_cast Int.one_le_abs hl
  let ρ' : 𝓢(ℝ,ℂ) := if 0 < l then ρ else Ostmann.reflectedSchwartz ρ
  have hmass : (∫ r : ℝ, ‖mellin (ρ' : ℝ → ℂ) (σ+r*Complex.I)‖) ≤ twoSidedMellinMass ρ σ := by
    have h₁ : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
    have h₂ : 0 ≤ ∫ r : ℝ, ‖mellin (Ostmann.reflectedSchwartz ρ : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [ρ',twoSidedMellinMass]
    split_ifs <;> linarith
  have hrow := hbound ρ' σ hσ N V S T a b z (|(l:ℝ)| * c) B L hN hL
    hV hS hT hSL hTL (by positivity) hB
  have heval (x : ℝ) : ρ' (|(l : ℝ)| *c*x) = ρ ((l : ℝ)*c*x) := by
    by_cases hlp : 0 < l
    · have hp : (0 : ℝ) < l := by exact_mod_cast hlp
      simp [ρ',hlp,abs_of_pos hp]
    · have hn : (l : ℝ) < 0 := by exact_mod_cast (show l < 0 by omega)
      simp [ρ',hlp,Ostmann.reflectedSchwartz_apply,abs_of_neg hn]
  have heval' (v n t : ℕ) :
      ρ' (|(l : ℝ)| *c*Real.sqrt ((n : ℝ)*t)/Real.sqrt v) =
      ρ ((l : ℝ)*c*Real.sqrt ((n : ℝ)*t)/Real.sqrt v) := by
    convert heval (Real.sqrt ((n : ℝ)*t)/Real.sqrt v) using 1 <;> ring_nf
  simp_rw [heval'] at hrow
  have hscale : (|(l : ℝ)| *c/Real.sqrt B)^(-σ) ≤
      (c/Real.sqrt B)^(-σ) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hc.le hla) (by positivity)
  apply hrow.trans
  have hmi : 0 ≤ ∫ r : ℝ, ‖mellin (ρ' : ℝ → ℂ) (σ+r*Complex.I)‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hmass0 := (twoSidedMellinMass_pos ρ σ).le
  gcongr

theorem dual_fourier_mellin_boundary_scale {M e B : ℝ} (hM : 0 < M) (he : 0 < e)
    (hB : 0 < B) (σ : ℝ) :
    (Real.sqrt (e/M)/Real.sqrt B)^(-σ) =
      (Real.sqrt B*Real.sqrt (M/e))^σ := by
  have hscale : Real.sqrt (e/M)/Real.sqrt B =
      (Real.sqrt B*Real.sqrt (M/e))⁻¹ := by
    have hsm : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    have hse : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
    have hsb : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
    rw [Real.sqrt_div he.le,Real.sqrt_div hM.le]
    field_simp
  rw [hscale,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]

theorem dual_fourier_frequency_boundary_bound (W : 𝓢(ℝ,ℂ)) (σ δ : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (e N : ℕ) (T B H : ℝ)
      (V S : Finset ℕ) (a : ℕ → ℂ),
      0 < M → 0 < e → 0 < N → 1 ≤ T → 0 < B → 0 < H →
      (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      ∀ s ∈ signedSquarefreeMultipliers,
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), ∑ v ∈ V,
          ‖∑ n ∈ S, ∑ t ∈ S,
            rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) 1 v n t *
              𝓕 (dualSignedSquareWeight W s)
                (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/Real.sqrt v)‖) ≤
          C*T^2*(Real.sqrt B*Real.sqrt (M/e))^σ*(N/H)*(N : ℝ)^δ*
            quadraticNorm V (oddSquarefreeUpTo N)*coefficientEnergy S a := by
  classical
  obtain ⟨C,hC,hbound⟩ := rootGauss_signed_frequency_boundary_bound (2*δ) (by positivity)
  let J : ℝ := 1 + ∑ s ∈ signedSquarefreeMultipliers,
    twoSidedMellinMass (𝓕 (dualSignedSquareWeight W s)) σ
  have hJ : 0 < J := by
    dsimp [J]
    have hh := Finset.sum_nonneg (s := signedSquarefreeMultipliers)
      (fun s hs => (twoSidedMellinMass_pos (𝓕 (dualSignedSquareWeight W s)) σ).le)
    linarith
  refine ⟨66*(1/(2*Real.pi))*J*Real.sqrt C,by positivity,?_⟩
  intro M e N T B H V S a hM he hN hT hB hH hV hS hSH s hs
  have hmJ : twoSidedMellinMass (𝓕 (dualSignedSquareWeight W s)) σ ≤ J := by
    have hh := Finset.single_le_sum
      (fun t ht => (twoSidedMellinMass_pos (𝓕 (dualSignedSquareWeight W t)) σ).le) hs
    dsimp [J]
    linarith
  have hQ := quadraticNorm_nonneg V (oddSquarefreeUpTo N)
  have hE := coefficientEnergy_nonneg S a
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have her : (0 : ℝ) < e := by exact_mod_cast he
  let Z : ℝ := (1/(2*Real.pi))*J*(Real.sqrt B*Real.sqrt (M/e))^σ*
    (2*(N : ℝ)/H)*(Real.sqrt C*(N : ℝ)^δ*quadraticNorm V (oddSquarefreeUpTo N)*coefficientEnergy S a)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hrow (l : ℤ) (hl : l ∈ nonzeroIntegerCutoff (16*T^2)) :
      (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ S,
        rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) 1 v n t *
          𝓕 (dualSignedSquareWeight W s)
            (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/Real.sqrt v)‖) ≤ Z := by
    have hh := hbound (𝓕 (dualSignedSquareWeight W s)) σ (Real.sqrt ((e : ℝ)/M)) B H
      N V S S a (fun n => conj (a n)) ((e : ℤ)*s) l hσ (by positivity) hB hH hN
      (mem_nonzeroIntegerCutoff _ _ |>.mp hl).1 hV hS hS hSH hSH
    rw [coefficientEnergy_conj,dual_fourier_mellin_boundary_scale hM her hB] at hh
    rw [gauss_mellin_radical_eq hC.le hNr (sq_nonneg _) hE δ, Real.sqrt_sq hQ] at hh
    apply hh.trans
    dsimp [Z]
    gcongr
  calc
    _ ≤ ∑ _l ∈ nonzeroIntegerCutoff (16*T^2), Z := Finset.sum_le_sum hrow
    _ = ((nonzeroIntegerCutoff (16*T^2)).card : ℝ)*Z := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (33*T^2)*Z := mul_le_mul_of_nonneg_right (nonzeroIntegerCutoff_card_le hT) hZ
    _ = _ := by dsimp [Z]; ring

end Ostmann.QuadraticSieve

end OAI
