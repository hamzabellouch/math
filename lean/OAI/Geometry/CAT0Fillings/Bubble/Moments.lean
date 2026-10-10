import Mathlib
import OAI.Geometry.CAT0Fillings.Model
import OAI.Geometry.CAT0Fillings.Bubble.Beta

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

noncomputable def sobolevP (n : ℕ) : ℝ := 2*n/(n-2)
noncomputable def sobolevQ (n : ℕ) : ℝ := 2*(n-1)/(n-2)
noncomputable def bubble (n : ℕ) (r : ℝ) : ℝ := (1+r^2)^(-((n:ℝ)-2)/2)
noncomputable def bubbleMass (n : ℕ) : ℝ :=
  Real.Gamma ((n:ℝ)/2)^2/(2*Real.Gamma n)

lemma sobolev_exponents {n : ℕ} (hn : 2 < n) :
    0 < sobolevP n ∧ 1 ≤ sobolevQ n ∧ sobolevQ n+sobolevP n/(n:ℝ)=sobolevP n ∧
      2*(sobolevQ n-1)=sobolevP n ∧ 2*sobolevQ n-sobolevP n=2 := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  dsimp [sobolevP,sobolevQ]
  have hd : 0 < (n:ℝ)-2 := by linarith
  refine ⟨div_pos (by positivity) hd, (le_div_iff₀ hd).mpr (by linarith), ?_, ?_, ?_⟩ <;>
    field_simp <;> ring

lemma bubble_pos (n : ℕ) (r : ℝ) : 0 < bubble n r :=
  Real.rpow_pos_of_pos (by positivity) _

lemma bubble_continuous (n : ℕ) : Continuous (bubble n) := by
  apply Continuous.rpow_const
  · fun_prop
  · intro r
    exact Or.inl (by positivity)

lemma bubble_power_p {n : ℕ} (hn : 2 < n) (r : ℝ) :
    (bubble n r)^(sobolevP n) = (1+r^2)^(-(n:ℝ)) := by
  have h : (n:ℝ)-2 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [bubble, ←Real.rpow_mul (by positivity)]
  congr 1
  dsimp [sobolevP]
  field_simp

lemma bubble_power_q {n : ℕ} (hn : 2 < n) (r : ℝ) :
    (bubble n r)^(sobolevQ n) = (1+r^2)^(1-(n:ℝ)) := by
  have h : (n:ℝ)-2 ≠ 0 := by exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [bubble, ←Real.rpow_mul (by positivity)]
  congr 1
  dsimp [sobolevQ]
  field_simp
  ring

lemma bubbleMoment_algebra {n : ℕ} (hn : 2 < n) {r : ℝ} (hr : 0 < r) :
    r^(n-1)*(bubble n r)^(sobolevP n) = r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+(n:ℝ)/2)) ∧
    r^(n-1)*(bubble n r)^(sobolevQ n) = r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+((n:ℝ)/2-1))) ∧
    r^(n-1)*(bubble n r)^(sobolevP n)*r^2 =
      r^(2*((n:ℝ)/2+1)-1)*(1+r^2)^(-(((n:ℝ)/2+1)+((n:ℝ)/2-1))) := by
  have h1 : 1 ≤ n := by omega
  rw [bubble_power_p hn, bubble_power_q hn, ←Real.rpow_natCast,
    Nat.cast_sub h1, Nat.cast_one]
  refine ⟨?_, ?_, ?_⟩
  · congr 2 <;> ring
  · congr 2 <;> ring
  · calc
      _ = (r^((n:ℝ)-1)*r^(2:ℝ))*(1+r^2)^(-(n:ℝ)) := by rw [Real.rpow_two]; ring
      _ = _ := by rw [←Real.rpow_add hr]; congr 2 <;> ring

lemma bubble_moments_integrable {n : ℕ} (hn : 2 < n) :
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevP n)) (Ioi 0) ∧
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevQ n)) (Ioi 0) ∧
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevP n)*r^2) (Ioi 0) := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  refine ⟨?_,?_,?_⟩
  · apply (bubble_integrable (a := (n:ℝ)/2) (b := (n:ℝ)/2) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).1.symm) measurableSet_Ioi
  · apply (bubble_integrable (a := (n:ℝ)/2) (b := (n:ℝ)/2-1) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).2.1.symm) measurableSet_Ioi
  · apply (bubble_integrable (a := (n:ℝ)/2+1) (b := (n:ℝ)/2-1) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).2.2.symm) measurableSet_Ioi

lemma bubble_mass_pos {n : ℕ} (hn : 2 < n) : 0 < bubbleMass n := by
  have h : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact div_pos (sq_pos_of_pos (Real.Gamma_pos_of_pos (by positivity)))
    (mul_pos (by norm_num) (Real.Gamma_pos_of_pos h))

lemma bubble_moments {n : ℕ} (hn : 2 < n) :
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevP n)) = bubbleMass n ∧
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevQ n)) = sobolevQ n*bubbleMass n ∧
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevP n)*r^2) =
      (n:ℝ)/(n-2)*bubbleMass n := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  have h0 : (0:ℝ) < n/2 := by linarith
  have h1 : (0:ℝ) < n/2-1 := by linarith
  have he0 : (n:ℝ)/2+(n:ℝ)/2 = n := by ring
  have he1 : (n:ℝ)/2+((n:ℝ)/2-1) = (n:ℝ)-1 := by ring
  have he2 : ((n:ℝ)/2+1)+((n:ℝ)/2-1) = n := by ring
  have G1 : Real.Gamma ((n:ℝ)/2) = ((n:ℝ)/2-1)*Real.Gamma ((n:ℝ)/2-1) := by
    convert Real.Gamma_add_one h1.ne' using 1
    congr 1
    ring
  have G2 : Real.Gamma (n:ℝ) = ((n:ℝ)-1)*Real.Gamma ((n:ℝ)-1) := by
    convert Real.Gamma_add_one (by linarith : (n:ℝ)-1 ≠ 0) using 1
    congr 1
    ring
  have G3 := Real.Gamma_add_one h0.ne'
  have d1 : Real.Gamma ((n:ℝ)-1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have d2 : (n:ℝ)-2 ≠ 0 := by linarith
  have d3 : (n:ℝ)-1 ≠ 0 := by linarith
  refine ⟨?_,?_,?_⟩
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+(n:ℝ)/2)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).1)
      _ = bubbleMass n := by rw [bubble_integral h0 h0,he0]; simp only [bubbleMass,pow_two]
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+((n:ℝ)/2-1))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).2.1)
      _ = sobolevQ n*bubbleMass n := by
        rw [bubble_integral h0 h1,he1]
        dsimp [sobolevQ,bubbleMass]
        rw [G1,G2]
        field_simp [d1,d2,d3]
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2+1)-1)*(1+r^2)^(-(((n:ℝ)/2+1)+((n:ℝ)/2-1))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).2.2)
      _ = (n:ℝ)/(n-2)*bubbleMass n := by
        rw [bubble_integral (by linarith : (0:ℝ) < n/2+1) h1,he2,G3]
        dsimp [bubbleMass]
        rw [G1]
        field_simp [d1,d2,d3]

end CAT0Fillings.RadialSobolev
end

end OAI
