import OAI.Probability.InvariantIsing.Magnetic.MagneticDerivativeLimit

namespace OAI

/-! Uniform finite-difference estimates for a varying Gaussian slab. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_family_derivative_tendsto_zero {ι : Type*} {l : Filter ι}
    {F G D : ι → ℝ → ℝ} {x : ι → ℝ} {c L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ i z, HasDerivAt (F i) (G i z) z)
    (hG : ∀ i z, HasDerivAt (G i) (D i z) z) (hD : ∀ i z, |D i z| ≤ L)
    (hlimit : ∀ h : ℝ, Tendsto (fun i => F i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => G i (x i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h := ε / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  have hh : 0 < h := div_pos hε hden
  have hheq : 2 * (L + 1) * h = ε := by
    dsimp only [h]
    field_simp [hden.ne']
  have hLh : L * h ^ 2 < ε * h / 2 := by
    have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
    nlinarith
  have hinc : Tendsto (fun i => F i (x i + h) - F i (x i)) l (𝓝 0) := by
    simpa only [add_zero, sub_self] using (hlimit h).sub (hlimit 0)
  have hevent := (Metric.tendsto_nhds.mp hinc) (ε * h / 2) (by positivity)
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq, sub_zero] at hi ⊢
  have hr := magnetic_derivative_increment_bound hL (hF i) (hG i) (hD i) (x i) hh.le
  have hg : |h * G i (x i)| ≤ |F i (x i + h) - F i (x i)| + L * h ^ 2 := by
    calc
      _ = |(F i (x i + h) - F i (x i)) -
          (F i (x i + h) - F i (x i) - h * G i (x i))| := by congr 1; ring
      _ ≤ |F i (x i + h) - F i (x i)| +
          |F i (x i + h) - F i (x i) - h * G i (x i)| := abs_sub _ _
      _ ≤ _ := add_le_add_right hr _
  rw [abs_mul, abs_of_pos hh] at hg
  nlinarith

lemma magnetic_family_second_tendsto_zero {ι : Type*} {l : Filter ι}
    {F G D E : ι → ℝ → ℝ} {x : ι → ℝ} {c L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hF : ∀ i z, HasDerivAt (F i) (G i z) z)
    (hG : ∀ i z, HasDerivAt (G i) (D i z) z)
    (hD : ∀ i z, HasDerivAt (D i) (E i z) z)
    (bD : ∀ i z, |D i z| ≤ L) (bE : ∀ i z, |E i z| ≤ K)
    (hlimit : ∀ h : ℝ, Tendsto (fun i => F i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => D i (x i)) l (𝓝 0) := by
  apply magnetic_family_derivative_tendsto_zero hK hG hD bE
  intro h
  apply magnetic_family_derivative_tendsto_zero hL hF hG bD
  intro k
  simpa only [add_assoc] using hlimit (h + k)

end InvariantIsing

end

end OAI
