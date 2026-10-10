import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetOperations

namespace OAI

/-! Products and linear maps preserve the uniform symbol bounds needed by
the finite remote block reduction. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
namespace HasUniformLogJetBound

variable {L : ℕ → ℝ}

theorem of_single {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {sigma : ℝ} {f : ℝ → A} (hf : HasLogJetBound sigma f)
    (hL : Tendsto L atTop atTop) : HasUniformLogJetBound L sigma (fun _ => f) := by
  obtain ⟨T,hT⟩ := hf.smooth
  refine ⟨?_,?_⟩
  · filter_upwards [hL.eventually (eventually_ge_atTop T)] with n hn
    exact hT.mono (Ioi_subset_Ioi hn)
  · intro k
    obtain ⟨C,hC,hb⟩ := hf.bound k
    obtain ⟨S,hS⟩ := eventually_atTop.mp hb
    refine ⟨C,hC,?_⟩
    filter_upwards [hL.eventually (eventually_ge_atTop S)] with n hn
    intro t ht
    exact hS t (hn.trans ht.le)

theorem eventually_congr {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {sigma : ℝ} {f g : ℕ → ℝ → A} (hf : HasUniformLogJetBound L sigma f)
    (hfg : ∀ᶠ n in atTop, EqOn (f n) (g n) (Ioi (L n))) :
    HasUniformLogJetBound L sigma g := by
  refine ⟨?_,?_⟩
  · filter_upwards [hf.smooth,hfg] with n hn he
    exact hn.congr (fun t ht => (he ht).symm)
  · intro k
    obtain ⟨C,hC,hb⟩ := hf.bound k
    refine ⟨C,hC,?_⟩
    filter_upwards [hb,hfg] with n hn he
    intro t ht
    rw [← he.iteratedDeriv_of_isOpen isOpen_Ioi k ht]
    exact hn t ht

theorem map {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {sigma : ℝ} {f : ℕ → ℝ → A}
    (hf : HasUniformLogJetBound L sigma f) (T : A →L[ℝ] B) :
    HasUniformLogJetBound L sigma (fun n t => T (f n t)) := by
  refine ⟨hf.smooth.mono (fun _ hn => T.contDiff.comp_contDiffOn hn),?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := hf.bound k
  refine ⟨‖T‖*C,by positivity,?_⟩
  filter_upwards [hb,hf.smooth] with n hn hs
  intro t ht
  have hft := (hs t ht).contDiffAt (Ioi_mem_nhds ht)
  have hh := T.norm_iteratedFDeriv_comp_left hft (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Function.comp_def] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (hn t ht) (norm_nonneg _)).trans_eq (by ring))

theorem mul {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    {sigma tau : ℝ} {f g : ℕ → ℝ → R}
    (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L tau g) :
    HasUniformLogJetBound L (sigma+tau) (fun n t => f n t*g n t) := by
  refine ⟨?_,?_⟩
  · filter_upwards [hf.smooth,hg.smooth] with n hn hn'
    exact hn.mul hn'
  · intro k
    choose C hC hb using hf.bound
    choose D hD hd using hg.bound
    let A := ∑ i ∈ Finset.range (k+1), ‖(k.choose i : R)‖*C i*D (k-i)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (hC i)) (hD (k-i)))
    refine ⟨A,hA,?_⟩
    have hfb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
        ‖iteratedDeriv i (f n) t‖ ≤ C i*Real.exp (sigma*t) :=
      (eventually_all_finset _).mpr (fun i _ => hb i)
    have hgb : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ t ∈ Ioi (L n),
        ‖iteratedDeriv (k-i) (g n) t‖ ≤ D (k-i)*Real.exp (tau*t) :=
      (eventually_all_finset _).mpr (fun i _ => hd (k-i))
    filter_upwards [hfb,hgb,hf.smooth,hg.smooth] with n hn hn' hfn hgn
    intro t ht
    rw [iteratedDeriv_fun_mul
      (((hfn t ht).contDiffAt (Ioi_mem_nhds ht)).of_le (by simp))
      (((hgn t ht).contDiffAt (Ioi_mem_nhds ht)).of_le (by simp))]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1),
          (‖(k.choose i : R)‖*C i*D (k-i))*Real.exp ((sigma+tau)*t) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul (hn i hi t ht) (hn' i hi t ht) (norm_nonneg _)
            (mul_nonneg (hC i) (Real.exp_pos _).le)) (norm_nonneg (k.choose i : R))
        apply ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans
        convert hh using 1
        · ring
        · rw [add_mul,Real.exp_add]
          ring
      _ = A*Real.exp ((sigma+tau)*t) := by rw [← Finset.sum_mul]

end HasUniformLogJetBound
end DefocusingNLS

end OAI
