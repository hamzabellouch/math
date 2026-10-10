import OAI.Analysis.CircleDomains.Sobolev.WeakPartialPairingLimit
import OAI.Analysis.CircleDomains.Sobolev.SmoothPhysicalPullback

namespace OAI

/-! Bounded smooth scalar energies give an actual Sobolev limit, retaining
the common subsequence and every L2 derivative pairing. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure ScalarSmoothWeakLimit (v : ℕ → EuclideanPlane → ℝ)
    (u : EuclideanPlane → ℝ) where
  witness : DeGiorgi.MemW1pWitness 2 u univ
  index : ℕ → ℕ
  index_strict : StrictMono index
  pairing : ∀ (i : Fin 2) (w : Lp ℝ 2 (volume : Measure EuclideanPlane)),
    Tendsto (fun n => ∫ x, fderiv ℝ (v (index n)) x (EuclideanSpace.single i 1)*w x)
      atTop (𝓝 (∫ x, witness.weakGrad x i*w x))

lemma exists_scalarSmoothWeakLimit
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 volume)
    (v : ℕ → EuclideanPlane → ℝ)
    (hv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n))
    (hgrad : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1)) 2 volume)
    {C M : ℝ} (hb : ∀ n x, ‖v n x‖ ≤ C)
    (hp : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    (henergy : ∀ n, (∫ x, physicalSmoothEnergy (v n) x) ≤ M) :
    Nonempty (ScalarSmoothWeakLimit v u) := by
  let g (i : Fin 2) (n : ℕ) (x : EuclideanPlane) :=
    fderiv ℝ (v n) x (EuclideanSpace.single i 1)
  have hnorm (n : ℕ) (i : Fin 2) : ‖(hgrad n i).toLp (g i n)‖ ≤ M+1 := by
    have he (j : Fin 2) : (∫ x, g j n x^2) = ‖(hgrad n j).toLp (g j n)‖^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hgrad n j)]
    have hm := henergy n
    change (∫ x, g 0 n x^2+g 1 n x^2) ≤ M at hm
    rw [integral_add (hgrad n 0).integrable_sq (hgrad n 1).integrable_sq, he, he] at hm
    fin_cases i
    · change ‖(hgrad n 0).toLp (g 0 n)‖ ≤ M+1
      nlinarith [sq_nonneg (‖(hgrad n 0).toLp (g 0 n)‖-1),
        sq_nonneg ‖(hgrad n 1).toLp (g 1 n)‖]
    · change ‖(hgrad n 1).toLp (g 1 n)‖ ≤ M+1
      nlinarith [sq_nonneg (‖(hgrad n 1).toLp (g 1 n)‖-1),
        sq_nonneg ‖(hgrad n 0).toLp (g 0 n)‖]
  obtain ⟨G₀, _, s₀, hs₀, hl₀⟩ := exists_L2_weak_subsequence volume (g 0)
    (fun n => hgrad n 0) (M+1) (fun n => hnorm n 0)
  obtain ⟨G₁, _, s₁, hs₁, hl₁⟩ := exists_L2_weak_subsequence volume (g 1 ∘ s₀)
    (fun n => hgrad (s₀ n) 1) (M+1) (fun n => hnorm (s₀ n) 1)
  let σ := s₀ ∘ s₁
  have hσ : StrictMono σ := hs₀.comp hs₁
  have hpair₀ (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      Tendsto (fun n => ∫ x, g 0 (σ n) x*w x) atTop (𝓝 (∫ x, G₀ x*w x)) :=
    (hl₀ w).comp hs₁.tendsto_atTop
  let W : DeGiorgi.MemW1pWitness 2 u univ := {
    memLp := by simpa only [Measure.restrict_univ] using hu
    weakGrad := fun x => WithLp.toLp 2 (fun i => if i=0 then G₀ x else G₁ x)
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · simpa using Lp.memLp G₀
      · simpa using Lp.memLp G₁
    isWeakGrad := by
      intro i
      fin_cases i
      · apply weakPartial_of_bounded_pointwise_weak_limit
          (fun n => (hv (σ n)).continuous) (fun n x => hb (σ n) x)
          (fun x => (hp x).comp hσ.tendsto_atTop)
          (fun n => weakPartial_of_smooth_on isOpen_univ ((hv (σ n)).of_le (by simp)).contDiffOn 0)
        exact hpair₀
      · apply weakPartial_of_bounded_pointwise_weak_limit
          (fun n => (hv (σ n)).continuous) (fun n x => hb (σ n) x)
          (fun x => (hp x).comp hσ.tendsto_atTop)
          (fun n => weakPartial_of_smooth_on isOpen_univ ((hv (σ n)).of_le (by simp)).contDiffOn 1)
        exact hl₁ }
  refine ⟨⟨W, σ, hσ, ?_⟩⟩
  intro i w
  fin_cases i
  · exact hpair₀ w
  · exact hl₁ w

end CircleDomainRigidity

end

end OAI
