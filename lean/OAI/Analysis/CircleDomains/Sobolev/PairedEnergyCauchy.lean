import OAI.Analysis.CircleDomains.Sobolev.StrongGradientEnergyLimit

namespace OAI

/-! Equality of two-component Dirichlet energies of differences transfers
strong Cauchy control. This is the Hilbert-space step in conformal energy
transport for nonsmooth functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_sub_eq_Lp_dist_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x-g x)^2 ∂μ) = dist (hf.toLp f) (hg.toLp g)^2 := by
  rw [Lp.dist_edist,Lp.edist_toLp_toLp]
  exact integral_sq_eq_eLpNorm_toReal_sq (hf.sub hg)

 theorem cauchy_partials_of_paired_energy_isometry
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (f : Fin 2 → ℕ → X → ℝ) (g : Fin 2 → ℕ → Y → ℝ)
    (hf : ∀ i n, MemLp (f i n) 2 μ) (hg : ∀ i n, MemLp (g i n) 2 ν)
    (hc : ∀ i, CauchySeq (fun n => (hf i n).toLp (f i n)))
    (he : ∀ m n,
      (∫ y, (g 0 m y-g 0 n y)^2+(g 1 m y-g 1 n y)^2 ∂ν) =
      ∫ x, (f 0 m x-f 0 n x)^2+(f 1 m x-f 1 n x)^2 ∂μ) :
    ∀ i, CauchySeq (fun n => (hg i n).toLp (g i n)) := by
  intro i
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N₀,hN₀⟩ := Metric.cauchySeq_iff.mp (hc 0) (ε/2) (half_pos hε)
  obtain ⟨N₁,hN₁⟩ := Metric.cauchySeq_iff.mp (hc 1) (ε/2) (half_pos hε)
  refine ⟨max N₀ N₁,?_⟩
  intro m hm n hn
  have h₀ := hN₀ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
  have h₁ := hN₁ m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
  have h := he m n
  have hig (j : Fin 2) : Integrable (fun y => (g j m y-g j n y)^2) ν :=
    ((hg j m).sub (hg j n)).integrable_sq
  have hif (j : Fin 2) : Integrable (fun x => (f j m x-f j n x)^2) μ :=
    ((hf j m).sub (hf j n)).integrable_sq
  rw [integral_add (hig 0) (hig 1), integral_add (hif 0) (hif 1),
    integral_sq_sub_eq_Lp_dist_sq (hg 0 m) (hg 0 n),
    integral_sq_sub_eq_Lp_dist_sq (hg 1 m) (hg 1 n),
    integral_sq_sub_eq_Lp_dist_sq (hf 0 m) (hf 0 n),
    integral_sq_sub_eq_Lp_dist_sq (hf 1 m) (hf 1 n)] at h
  have hb₀ := dist_nonneg (x := (hf 0 m).toLp (f 0 m)) (y := (hf 0 n).toLp (f 0 n))
  have hb₁ := dist_nonneg (x := (hf 1 m).toLp (f 1 m)) (y := (hf 1 n).toLp (f 1 n))
  have ht₀ := dist_nonneg (x := (hg 0 m).toLp (g 0 m)) (y := (hg 0 n).toLp (g 0 n))
  have ht₁ := dist_nonneg (x := (hg 1 m).toLp (g 1 m)) (y := (hg 1 n).toLp (g 1 n))
  have hf₀ := (sq_lt_sq₀ hb₀ (half_pos hε).le).mpr h₀
  have hf₁ := (sq_lt_sq₀ hb₁ (half_pos hε).le).mpr h₁
  have hsmall : dist ((hf 0 m).toLp (f 0 m)) ((hf 0 n).toLp (f 0 n))^2+
      dist ((hf 1 m).toLp (f 1 m)) ((hf 1 n).toLp (f 1 n))^2 < ε^2 := by
    nlinarith only [hf₀,hf₁,sq_pos_of_pos hε]
  have hs := h.trans_lt hsmall
  fin_cases i
  · change dist ((hg 0 m).toLp (g 0 m)) ((hg 0 n).toLp (g 0 n)) < ε
    exact (sq_lt_sq₀ ht₀ hε.le).mp ((le_add_of_nonneg_right (sq_nonneg _)).trans_lt hs)
  · change dist ((hg 1 m).toLp (g 1 m)) ((hg 1 n).toLp (g 1 n)) < ε
    exact (sq_lt_sq₀ ht₁ hε.le).mp ((le_add_of_nonneg_left (sq_nonneg _)).trans_lt hs)

end CircleDomainRigidity

end

end OAI
