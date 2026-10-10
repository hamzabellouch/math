import OAI.NumberTheory.Ostmann.QuadraticSieveFourierRangeBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory ComplexConjugate
open scoped SchwartzMap FourierTransform

theorem dual_fourier_mellin_scale {M e B : ℝ} (hM : 0 < M) (he : 0 < e)
    (hB : 0 < B) (D : ℕ) (hD : 0 < D) (σ : ℝ) :
    (Real.sqrt (e/M)/((2*D : ℕ)*Real.sqrt B))^(-σ) =
      (((2*D : ℕ) : ℝ)*Real.sqrt B*Real.sqrt (M/e))^σ := by
  have hscale : Real.sqrt (e/M)/((2*D : ℕ)*Real.sqrt B) =
      ((((2*D : ℕ) : ℝ)*Real.sqrt B*Real.sqrt (M/e)))⁻¹ := by
    have hsm : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    have hse : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
    have hsb : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
    have hd : (0 : ℝ) < (2*D : ℕ) := by exact_mod_cast (show 0 < 2*D by omega)
    rw [Real.sqrt_div he.le,Real.sqrt_div hM.le]
    field_simp
  rw [hscale,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]

theorem gauss_mellin_radical_eq {C N R E : ℝ} (hC : 0 ≤ C) (hN : 0 < N)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (δ : ℝ) :
    Real.sqrt (C*N^(2*δ)*R*E*E) = Real.sqrt C*N^δ*Real.sqrt R*E := by
  have he : N^(2*δ) = (N^δ)^2 := by
    rw [show 2*δ = δ+δ by ring,Real.rpow_add hN]
    ring
  rw [he,show C*(N^δ)^2*R*E*E = (C*(N^δ)^2*R)*E^2 by ring,
    Real.sqrt_mul (by positivity),Real.sqrt_sq hE,
    Real.sqrt_mul (by positivity),Real.sqrt_mul hC,
    Real.sqrt_sq (Real.rpow_nonneg hN.le _)]

theorem dual_fourier_frequency_divisor_range_bound (W : 𝓢(ℝ,ℂ)) (σ δ : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (e D N : ℕ) (T B H : ℝ)
      (V S : Finset ℕ) (a : ℕ → ℂ),
      0 < M → 0 < e → 0 < D → 0 < N → 1 ≤ T → 0 < B → 0 < H →
      (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      ∃ p ∈ divisorRangeScales D, ∀ s ∈ signedSquarefreeMultipliers,
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), ∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          ‖∑ n ∈ S, ∑ t ∈ S,
            rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) d v n t *
              𝓕 (dualSignedSquareWeight W s)
                (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v))‖) ≤
          C*T^2*(((2*D : ℕ) : ℝ)*Real.sqrt B*Real.sqrt (M/e))^σ*(N/H)*(N : ℝ)^δ*
            Real.sqrt ((p.1*p.2 : ℕ)*quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
              quadraticNorm V (oddSquarefreeUpTo (N/p.2)))*coefficientEnergy S a := by
  classical
  obtain ⟨C,hC,hbound⟩ := rootGauss_signed_frequency_range_bound (2*δ) (by positivity)
  let J : ℝ := 1 + ∑ s ∈ signedSquarefreeMultipliers,
    twoSidedMellinMass (𝓕 (dualSignedSquareWeight W s)) σ
  have hJ : 0 < J := by
    dsimp [J]
    have hh := Finset.sum_nonneg (s := signedSquarefreeMultipliers)
      (fun s hs => (twoSidedMellinMass_pos (𝓕 (dualSignedSquareWeight W s)) σ).le)
    linarith
  refine ⟨66*(1/(2*Real.pi))*J*Real.sqrt C,by positivity,?_⟩
  intro M e D N T B H V S a hM he hD hN hT hB hH hV hS hSH
  obtain ⟨p,hp,hpbound⟩ := hbound D N V S S hD hN (fun v hv => (hV v hv).2.1) hS hS
  refine ⟨p,hp,?_⟩
  intro s hs
  have hmJ : twoSidedMellinMass (𝓕 (dualSignedSquareWeight W s)) σ ≤ J := by
    have hh := Finset.single_le_sum
      (fun t ht => (twoSidedMellinMass_pos (𝓕 (dualSignedSquareWeight W t)) σ).le) hs
    dsimp [J]
    linarith
  let R : ℝ := (p.1*p.2 : ℕ)*quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
    quadraticNorm V (oddSquarefreeUpTo (N/p.2))
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (quadraticNorm_nonneg _ _))
      (quadraticNorm_nonneg _ _)
  have hE := coefficientEnergy_nonneg S a
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have her : (0 : ℝ) < e := by exact_mod_cast he
  let Z : ℝ := (1/(2*Real.pi))*J*(((2*D : ℕ) : ℝ)*Real.sqrt B*Real.sqrt (M/e))^σ*
    (2*(N : ℝ)/H)*(Real.sqrt C*(N : ℝ)^δ*Real.sqrt R*coefficientEnergy S a)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hrow (l : ℤ) (hl : l ∈ nonzeroIntegerCutoff (16*T^2)) :
      (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ S,
        rootGaussMellinKernel a (fun n => conj (a n)) ((e : ℤ)*s) d v n t *
          𝓕 (dualSignedSquareWeight W s)
            (((l : ℝ)*Real.sqrt ((e : ℝ)/M))*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v))‖) ≤ Z := by
    have hh := hpbound (𝓕 (dualSignedSquareWeight W s)) σ (Real.sqrt ((e : ℝ)/M)) B H
      a (fun n => conj (a n)) ((e : ℤ)*s) l hσ (by positivity) hB hH
      (mem_nonzeroIntegerCutoff _ _ |>.mp hl).1
      (fun v hv => ⟨(hV v hv).1,(hV v hv).2.2⟩) hSH hSH
    rw [coefficientEnergy_conj,dual_fourier_mellin_scale hM her hB D hD] at hh
    have hrad : Real.sqrt (C*(N : ℝ)^(2*δ)*(p.1*p.2 : ℕ)*
        quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
        coefficientEnergy S a*coefficientEnergy S a) =
        Real.sqrt C*(N : ℝ)^δ*Real.sqrt R*coefficientEnergy S a := by
      convert gauss_mellin_radical_eq hC.le hNr hR hE δ using 1
      dsimp [R]
      ring_nf
    rw [hrad] at hh
    apply hh.trans
    dsimp [Z]
    gcongr
  calc
    _ ≤ ∑ _l ∈ nonzeroIntegerCutoff (16*T^2), Z := Finset.sum_le_sum hrow
    _ = ((nonzeroIntegerCutoff (16*T^2)).card : ℝ)*Z := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (33*T^2)*Z := mul_le_mul_of_nonneg_right (nonzeroIntegerCutoff_card_le hT) hZ
    _ = _ := by dsimp [Z,R]; ring

end Ostmann.QuadraticSieve

end OAI
