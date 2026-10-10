import OAI.Combinatorics.SparsestCut.GaussianNonparallel

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionInterpolation
open GaussianTools FiniteNets MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
noncomputable def empiricalSin (g : Fin N → E) (w : E) : E :=
  (N : ℝ)⁻¹ • ∑ i, Real.sin (inner ℝ (g i) w) • g i
noncomputable def empiricalCov (g : Fin N → E) (v : E) : ℝ :=
  (∑ i, (inner ℝ v (g i))^2)/(N : ℝ)

lemma sin_vector_lipschitz (g w w' : E) :
    ‖Real.sin (inner ℝ g w) • g - Real.sin (inner ℝ g w') • g‖ ≤
      ‖g‖^2 * ‖w-w'‖ := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hs : |Real.sin (inner ℝ g w) - Real.sin (inner ℝ g w')| ≤
      |inner ℝ g (w-w')| := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, inner_sub_right, NNReal.coe_one, one_mul] using
      Real.lipschitzWith_sin.dist_le_mul (inner ℝ g w) (inner ℝ g w')
  calc
    _ ≤ |inner ℝ g (w-w')| * ‖g‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ (‖g‖*‖w-w'‖)*‖g‖ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

lemma empiricalSin_lipschitz (hN : 0 < N) (g : Fin N → E) {B : ℝ}
    (hB : ∀ i, ‖g i‖^2 ≤ B) (w w' : E) :
    ‖empiricalSin g w - empiricalSin g w'‖ ≤ B*‖w-w'‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [empiricalSin, empiricalSin, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, ‖Real.sin (inner ℝ (g i) w) • g i -
        Real.sin (inner ℝ (g i) w') • g i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _ : Fin N, B * ‖w-w'‖ := by
      gcongr with i
      exact (sin_vector_lipschitz _ _ _).trans (mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _))
    _ = _ := by simp [hn.ne']

lemma gaussian_norm_sq_mean : (∫ g : E, ‖g‖^2 ∂stdGaussian E) = m := by
  have hid (g : E) : ‖g‖^2 = ∑ i : Fin m, (inner ℝ (EuclideanSpace.single i 1) g)^2 := by
    simp only [EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_single_left, conj_trivial, one_mul,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hid]
  rw [integral_finsetSum _ (fun i _ => inner_sq_integrable _)]
  simp_rw [gaussian_inner_sq]
  simp

lemma gaussianTransform_lipschitz (w w' : E) :
    ‖Real.exp (-‖w‖^2/2) • w - Real.exp (-‖w'‖^2/2) • w'‖ ≤ (m : ℝ)*‖w-w'‖ := by
  rw [← gaussian_vector_sin w, ← gaussian_vector_sin w',
    ← integral_sub (gaussian_vector_sin_integrable w) (gaussian_vector_sin_integrable w')]
  calc
    _ ≤ ∫ g : E, ‖Real.sin (inner ℝ g w) • g - Real.sin (inner ℝ g w') • g‖ ∂stdGaussian E :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g : E, ‖g‖^2 * ‖w-w'‖ ∂stdGaussian E := by
      apply integral_mono ((gaussian_vector_sin_integrable w).sub (gaussian_vector_sin_integrable w')).norm
        (gaussian_norm_sq_integrable.mul_const ‖w-w'‖)
      exact fun g => sin_vector_lipschitz g w w'
    _ = _ := by rw [integral_mul_const, gaussian_norm_sq_mean]

lemma covariance_lipschitz (hN : 0 < N) (g : Fin N → E) {B : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) {v v' : E} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    |empiricalCov g v - empiricalCov g v'| ≤ 2*B*‖v-v'‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (i : Fin N) : |(inner ℝ v (g i))^2 - (inner ℝ v' (g i))^2| ≤
      2*B*‖v-v'‖ := by
    rw [sq_sub_sq, abs_mul, mul_comm]
    have ha : |inner ℝ v (g i)| ≤ ‖g i‖ := by simpa [hv] using abs_real_inner_le_norm v (g i)
    have hb : |inner ℝ v' (g i)| ≤ ‖g i‖ := by simpa [hv'] using abs_real_inner_le_norm v' (g i)
    have hd : |inner ℝ v (g i) - inner ℝ v' (g i)| ≤ ‖v-v'‖*‖g i‖ := by
      simpa only [inner_sub_left] using abs_real_inner_le_norm (v-v') (g i)
    calc
      _ ≤ (‖v-v'‖*‖g i‖)*(2*‖g i‖) :=
        mul_le_mul hd ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) (by positivity)
      _ = 2*‖g i‖^2*‖v-v'‖ := by ring
      _ ≤ 2*B*‖v-v'‖ := by gcongr; exact hg i
  rw [empiricalCov, empiricalCov, ← sub_div, abs_div, abs_of_pos hn, ← Finset.sum_sub_distrib]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i : Fin N, |(inner ℝ v (g i))^2 - (inner ℝ v' (g i))^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, 2*B*‖v-v'‖ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_comm]

lemma covariance_net_bound (hN : 0 < N) (g : Fin N → E) {B b ρ : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) (hB : 0 ≤ B) (V : Finset E)
    (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    (hdev : ∀ v ∈ V, |empiricalCov g v - 1| ≤ b)
    (x : E) (hx : ‖x‖ = 1) : |empiricalCov g x - 1| ≤ b + 2*B*ρ := by
  obtain ⟨v,hv,hd⟩ := hnet x hx
  calc
    _ ≤ |empiricalCov g x - empiricalCov g v| + |empiricalCov g v - 1| := abs_sub_le _ _ _
    _ ≤ 2*B*‖x-v‖ + b := add_le_add (covariance_lipschitz hN g hg hx (hV v hv)) (hdev v hv)
    _ ≤ b + 2*B*ρ := by nlinarith

lemma fourier_net_bound (hN : 0 < N) (g : Fin N → E) {B b ρ δ R : ℝ}
    (hg : ∀ i, ‖g i‖^2 ≤ B) (hB : 0 ≤ B) (hb : 0 ≤ b) (hρ : ρ < 1)
    (V W : Finset E)
    (hV : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ V, ‖x-v‖ ≤ ρ)
    (hW : ∀ w : E, ‖w‖ ≤ R → ∃ w' ∈ W, ‖w-w'‖ ≤ δ)
    (hdev : ∀ v ∈ V, ∀ w ∈ W,
      |inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v| ≤ b)
    (w : E) (hw : ‖w‖ ≤ R) :
    ‖empiricalSin g w - Real.exp (-‖w‖^2/2) • w‖ ≤ b/(1-ρ) + (B+(m : ℝ))*δ := by
  obtain ⟨w',hw',hd⟩ := hW w hw
  have hn : ‖empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w'‖ ≤ b/(1-ρ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-ρ)).mpr
    nlinarith [sphere_net_norm_bound hV (fun v hv => hdev v hv w' hw') hb]
  calc
    _ ≤ ‖empiricalSin g w - empiricalSin g w'‖ +
        ‖empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w'‖ +
        ‖Real.exp (-‖w'‖^2/2) • w' - Real.exp (-‖w‖^2/2) • w‖ :=
      by
        have hid : empiricalSin g w - Real.exp (-‖w‖^2/2) • w =
            (empiricalSin g w - empiricalSin g w') +
            (empiricalSin g w' - Real.exp (-‖w'‖^2/2) • w') +
            (Real.exp (-‖w'‖^2/2) • w' - Real.exp (-‖w‖^2/2) • w) := by abel
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ B*‖w-w'‖ + b/(1-ρ) + (m : ℝ)*‖w-w'‖ := by
      apply add_le_add (add_le_add (empiricalSin_lipschitz hN g hg w w') hn)
      simpa only [norm_sub_rev] using gaussianTransform_lipschitz w' w
    _ ≤ b/(1-ρ) + (B+(m : ℝ))*δ := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith

lemma projection_interpolate {g v v' : E} {q K ρ : ℝ}
    (hg : ‖g‖ ≤ K) (_hK : 0 ≤ K) (hd : ‖v-v'‖ ≤ ρ)
    (hp : |inner ℝ v' g| ≤ q) : |inner ℝ v g| ≤ q + K*ρ := by
  have hi : inner ℝ v g = inner ℝ v' g + inner ℝ (v-v') g := by rw [inner_sub_left]; ring
  calc
    _ ≤ |inner ℝ v' g| + |inner ℝ (v-v') g| := by rw [hi]; exact abs_add_le _ _
    _ ≤ q + ‖v-v'‖*‖g‖ := add_le_add hp (abs_real_inner_le_norm _ _)
    _ ≤ q + K*ρ := by
      have hρ : 0 ≤ ρ := (norm_nonneg _).trans hd
      nlinarith [mul_le_mul hd hg (norm_nonneg _) hρ]

end UniformSparsestCut.DirectionInterpolation

end

end OAI
