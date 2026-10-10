import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothingDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def primeDilationCoefficients (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * (jacobiSym (n:ℤ) p : ℂ)

theorem coefficientEnergy_primeDilation_le (p : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    coefficientEnergy S (primeDilationCoefficients p a) ≤ coefficientEnergy S a := by
  apply Finset.sum_le_sum
  intro n hn
  rcases jacobiSym.trichotomy (n:ℤ) p with h | h | h <;>
    simp [primeDilationCoefficients,h]

theorem primeDilation_row_eq {p v : ℕ} (hp : p.Prime) (hv : 0 < v)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, primeDilationCoefficients p a n * (jacobiSym (n:ℤ) (p*v):ℂ)) =
      ∑ n ∈ S.filter (fun n => ¬p∣n), a n*(jacobiSym (n:ℤ) v:ℂ) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeDilationCoefficients,jacobiSym.mul_right' _ hp.ne_zero hv.ne',Int.cast_mul]
  by_cases hpn : p∣n
  · have hc : (n:ℤ).gcd p ≠ 1 := by
      simpa only [Int.gcd_natCast_natCast] using
        (show ¬Nat.Coprime n p from fun h => hp.not_dvd_one (h.symm.dvd_of_dvd_mul_left (by simpa using hpn)))
    have hz := jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero,hc⟩
    simp [hpn,hz]
  · have hc : (n:ℤ).gcd p = 1 := by
      simpa only [Int.gcd_natCast_natCast] using (hp.coprime_iff_not_dvd.mpr hpn).symm
    have hs : (jacobiSym (n:ℤ) p:ℂ)^2 = 1 := by exact_mod_cast jacobiSym.sq_one hc
    rw [ite_eq_left hpn]
    calc
      _ = a n * (jacobiSym (n:ℤ) p:ℂ)^2 * (jacobiSym (n:ℤ) v:ℂ) := by ring
      _ = _ := by rw [hs]; ring

theorem primeDilation_good_energy_le {p : ℕ} (hp : p.Prime)
    (V W S : Finset ℕ) (a : ℕ → ℂ)
    (hV : ∀ v ∈ V, 0 < v)
    (hmap : ∀ v ∈ V, ¬p∣v → p*v ∈ W) :
    jacobiEnergy (V.filter (fun v => ¬p∣v)) (S.filter (fun n => ¬p∣n)) a ≤
      quadraticNorm W S * coefficientEnergy S a := by
  classical
  have heq : jacobiEnergy (V.filter (fun v => ¬p∣v)) (S.filter (fun n => ¬p∣n)) a =
      jacobiEnergy ((V.filter (fun v => ¬p∣v)).image (fun v => p*v)) S
        (primeDilationCoefficients p a) := by
    unfold jacobiEnergy
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [primeDilation_row_eq hp (hV v (Finset.mem_filter.mp hv).1)]
    · intro v hv w hw he
      exact Nat.eq_of_mul_eq_mul_left hp.pos he
  rw [heq]
  have hsub : (V.filter (fun v => ¬p∣v)).image (fun v => p*v) ⊆ W := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact hmap v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  exact ((jacobiEnergy_mono_rows hsub S _).trans (jacobiEnergy_le_quadraticNorm W S _)).trans
    (mul_le_mul_of_nonneg_left (coefficientEnergy_primeDilation_le p S a) (quadraticNorm_nonneg W S))

theorem rowInflation_norm_add_sq (z w : ℂ) : ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have h := norm_add_le z w
  have hn := norm_nonneg (z+w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

theorem primeDilation_energy_le {p : ℕ} (hp : p.Prime)
    (V W S : Finset ℕ) (a : ℕ → ℂ)
    (hV : ∀ v ∈ V, 0 < v)
    (hmap : ∀ v ∈ V, ¬p∣v → p*v ∈ W) :
    jacobiEnergy V S a ≤ jacobiEnergy (V.filter (fun v => p∣v)) S a +
      2*quadraticNorm W S*coefficientEnergy S a +
      2*quadraticNorm V S*coefficientEnergy (S.filter (fun n => p∣n)) a := by
  classical
  have hsplit : jacobiEnergy V S a = jacobiEnergy (V.filter (fun v => p∣v)) S a +
      jacobiEnergy (V.filter (fun v => ¬p∣v)) S a := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcols : jacobiEnergy (V.filter (fun v => ¬p∣v)) S a ≤
      2*jacobiEnergy (V.filter (fun v => ¬p∣v)) (S.filter (fun n => ¬p∣n)) a +
      2*jacobiEnergy (V.filter (fun v => ¬p∣v)) (S.filter (fun n => p∣n)) a := by
    unfold jacobiEnergy
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v hv
    have he := Finset.sum_filter_add_sum_filter_not S (fun n => p∣n)
      (fun n => a n*(jacobiSym (n:ℤ) v:ℂ))
    rw [← he]
    have hh := rowInflation_norm_add_sq
      (∑ n ∈ S.filter (fun n => p∣n), a n*(jacobiSym (n:ℤ) v:ℂ))
      (∑ n ∈ S.filter (fun n => ¬p∣n), a n*(jacobiSym (n:ℤ) v:ℂ))
    linarith
  have hgood := primeDilation_good_energy_le hp V W S a hV hmap
  have hbad := jacobiEnergy_le_quadraticNorm V S
    (supportCoefficients (S.filter (fun n => p∣n)) a)
  rw [jacobiEnergy_supportCoefficients V (Finset.filter_subset _ _),
    coefficientEnergy_supportCoefficients (Finset.filter_subset _ _)] at hbad
  have hbad' : jacobiEnergy (V.filter (fun v => ¬p∣v)) (S.filter (fun n => p∣n)) a ≤
      quadraticNorm V S*coefficientEnergy (S.filter (fun n => p∣n)) a :=
    (jacobiEnergy_mono_rows (Finset.filter_subset _ _) _ a).trans hbad
  rw [hsplit]
  linarith

end Ostmann.QuadraticSieve

end

end OAI
