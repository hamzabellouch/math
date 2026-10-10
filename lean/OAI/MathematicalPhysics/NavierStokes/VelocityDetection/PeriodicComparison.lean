import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ParabolicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculusPartialDSub
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceRestrictRestrict

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicComparison
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open PeriodicSpace ParabolicComparison

theorem nonnegative {n : ℕ} {ν T : ℝ} {a : VectorField n} {ρ : ScalarField n}
    (hν : 0 ≤ ν) (_hT : 0 ≤ T) (hρ : ContDiff ℝ 2 (uncurry ρ))
    (hp : ∀ t, FactorsThrough (ρ t) cover)
    (heq : ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      ν * laplacian ρ t X ≤ deriv (fun s => ρ s X) t + advection a ρ t X)
    (hinit : ∀ X, 0 ≤ ρ 0 X) : ∀ t ∈ Icc (0:ℝ) T, ∀ X, 0 ≤ ρ t X := by
  intro t ht X
  by_contra hneg
  have hvneg : ρ t X < 0 := lt_of_not_ge hneg
  let ε : ℝ := -ρ t X / (2 * (1+t))
  have hε : 0 < ε := div_pos (neg_pos.mpr hvneg) (by linarith [ht.1])
  have hmul : ε * (1+t) = -ρ t X / 2 := by
    dsimp [ε]
    field_simp [show (1+t : ℝ) ≠ 0 by linarith [ht.1]]
  let q : ℝ → compatible n := fun r => ofPeriodic (ρ r)
    (hρ.continuous.comp (continuous_const.prodMk continuous_id)) (hp r)
  have hq : Continuous q := continuous_ofPeriodic_curve hρ.continuous hp
  have hqval (r : ℝ) (Y : Coord n) : q r (cover Y) = ρ r Y :=
    realLift_ofPeriodic (ρ r) (hρ.continuous.comp (continuous_const.prodMk continuous_id)) (hp r) Y
  let v : ℝ × Torus n → ℝ := fun p => q p.1 p.2 + ε * (1+p.1)
  have hv : Continuous v := by
    exact (continuous_eval.comp ((hq.comp continuous_fst).prodMk continuous_snd)).add
      (continuous_const.mul (continuous_const.add continuous_fst))
  have hcompact : IsCompact (Icc (0:ℝ) t ×ˢ (univ : Set (Torus n))) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨p, hpmem, hmin⟩ := hcompact.exists_isMinOn
    ⟨(0,cover X), ⟨⟨le_refl _,ht.1⟩,mem_univ _⟩⟩ hv.continuousOn
  obtain ⟨Y, hY⟩ := cover_surjective n p.2
  have hpneg : v p < 0 := by
    have hle := hmin (a := (t,cover X)) ⟨⟨ht.1,le_refl _⟩,mem_univ (cover X)⟩
    change v p ≤ q t (cover X) + ε * (1+t) at hle
    rw [hqval, hmul] at hle
    linarith
  have hp0 : 0 < p.1 := by
    by_contra hn
    have hz : p.1 = 0 := le_antisymm (not_lt.mp hn) hpmem.1.1
    have hh := hinit Y
    have he : v p = ρ 0 Y + ε := by
      change q p.1 p.2 + ε * (1+p.1) = _
      rw [hz, ← hY, hqval]
      ring
    rw [he] at hpneg
    linarith
  have hminX : ∀ Z, ρ p.1 Y ≤ ρ p.1 Z := by
    intro Z
    have hh := hmin (a := (p.1,cover Z)) ⟨hpmem.1,mem_univ _⟩
    change q p.1 p.2 + ε*(1+p.1) ≤ q p.1 (cover Z) + ε*(1+p.1) at hh
    rw [← hY, hqval, hqval] at hh
    linarith
  obtain ⟨hgrad, hlap⟩ := spatial_minimum
    (hρ.continuous.comp (continuous_const.prodMk continuous_id)) hminX
  have hadv : advection a ρ p.1 Y = 0 := by
    simp only [advection, hgrad, mul_zero, Finset.sum_const_zero]
  have htime : HasDerivAt (fun s => ρ s Y + ε*(1+s))
      (deriv (fun s => ρ s Y) p.1 + ε) p.1 := by
    have hd : Differentiable ℝ (fun s => ρ s Y) :=
      (hρ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
    have heps := (((hasDerivAt_const p.1 (1:ℝ)).add (hasDerivAt_id p.1)).const_mul ε)
    simpa only [Pi.add_def, id_eq, zero_add, mul_one] using (hd p.1).hasDerivAt.add heps
  have htimemin : ∀ s ∈ Icc 0 p.1, ρ p.1 Y + ε*(1+p.1) ≤ ρ s Y + ε*(1+s) := by
    intro s hs
    have hh := hmin (a := (s,cover Y)) ⟨⟨hs.1,hs.2.trans hpmem.1.2⟩,mem_univ _⟩
    change q p.1 p.2 + ε*(1+p.1) ≤ q s (cover Y) + ε*(1+s) at hh
    rwa [← hY, hqval, hqval] at hh
  have hnonpos := deriv_nonpos_at_past_min hp0 htime htimemin
  have hpde := heq p.1 ⟨hp0.le,hpmem.1.2.trans ht.2⟩ Y
  rw [hadv] at hpde
  nlinarith [mul_nonneg hν hlap]

end VelocityDetection.PeriodicComparison
end

noncomputable section
namespace VelocityDetection.PeriodicComparison
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open PeriodicSpace SpatialCalculus

def residual {n : ℕ} (ν : ℝ) (a : VectorField n) (ρ : ScalarField n) : ScalarField n :=
  fun t X => deriv (fun s => ρ s X) t + advection a ρ t X - ν * laplacian ρ t X

theorem residual_sub {n : ℕ} (ν : ℝ) (a : VectorField n) {ρ σ : ScalarField n}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hσ : ContDiff ℝ 2 (uncurry σ)) (t : ℝ) (X : Coord n) :
    residual ν a (fun s Y => ρ s Y - σ s Y) t X = residual ν a ρ t X - residual ν a σ t X := by
  have hρt : ContDiff ℝ 2 (fun s => ρ s X) := hρ.comp (contDiff_id.prodMk contDiff_const)
  have hσt : ContDiff ℝ 2 (fun s => σ s X) := hσ.comp (contDiff_id.prodMk contDiff_const)
  have hρx : ContDiff ℝ 2 (ρ t) := hρ.comp (contDiff_const.prodMk contDiff_id)
  have hσx : ContDiff ℝ 2 (σ t) := hσ.comp (contDiff_const.prodMk contDiff_id)
  have hadv : advection a (fun s Y => ρ s Y - σ s Y) t X =
      advection a ρ t X - advection a σ t X := by
    change (∑ i : Fin n, a t X i * partialD i (fun Y => ρ t Y - σ t Y) X) = _
    simp_rw [partialD_sub _ (hρx.differentiable (by norm_num))
      (hσx.differentiable (by norm_num)), mul_sub, Finset.sum_sub_distrib]
    rfl
  have hlap := laplacian_sub hρx hσx X
  change laplacian (fun s Y => ρ s Y-σ s Y) t X = laplacian ρ t X - laplacian σ t X at hlap
  simp only [residual, deriv_fun_sub (hρt.differentiable (by norm_num) t)
    (hσt.differentiable (by norm_num) t), hadv, hlap]
  ring

theorem comparison {n : ℕ} {ν T : ℝ} {a : VectorField n} {ρ σ : ScalarField n}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hσ : ContDiff ℝ 2 (uncurry σ))
    (hpρ : ∀ t, FactorsThrough (ρ t) cover) (hpσ : ∀ t, FactorsThrough (σ t) cover)
    (heq : ∀ t ∈ Icc (0:ℝ) T, ∀ X, residual ν a ρ t X ≤ residual ν a σ t X)
    (hinit : ∀ X, ρ 0 X ≤ σ 0 X) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ X, ρ t X ≤ σ t X := by
  have hp : ∀ t, FactorsThrough (fun X => σ t X - ρ t X) cover := by
    intro t X Y hXY
    change σ t X - ρ t X = σ t Y - ρ t Y
    rw [hpσ t hXY,hpρ t hXY]
  have he : ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      ν * laplacian (fun s Y => σ s Y - ρ s Y) t X ≤
        deriv (fun s => σ s X - ρ s X) t + advection a (fun s Y => σ s Y - ρ s Y) t X := by
    intro t ht X
    have hh : 0 ≤ residual ν a (fun s Y => σ s Y - ρ s Y) t X := by
      rw [residual_sub ν a hσ hρ]
      exact sub_nonneg.mpr (heq t ht X)
    exact sub_nonneg.mp hh
  have hh := nonnegative hν hT (hσ.sub hρ) hp he (fun X => sub_nonneg.mpr (hinit X))
  exact fun t ht X => sub_nonneg.mp (hh t ht X)

theorem residual_timeConstant {n : ℕ} (ν : ℝ) (a : VectorField n) (B : ℝ → ℝ)
    (t : ℝ) (X : Coord n) : residual ν a (fun s _ => B s) t X = deriv B t := by
  simp [residual, advection, laplacian, spatialD]

theorem uniqueness {n : ℕ} {ν T : ℝ} {a : VectorField n} {ρ σ : ScalarField n}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hσ : ContDiff ℝ 2 (uncurry σ))
    (hpρ : ∀ t, FactorsThrough (ρ t) cover) (hpσ : ∀ t, FactorsThrough (σ t) cover)
    (heq : ∀ t ∈ Icc (0:ℝ) T, ∀ X, residual ν a ρ t X = residual ν a σ t X)
    (hinit : ∀ X, ρ 0 X = σ 0 X) : ∀ t ∈ Icc (0:ℝ) T, ρ t = σ t := by
  have hu := comparison hν hT hρ hσ hpρ hpσ (fun t ht X => (heq t ht X).le)
    (fun X => (hinit X).le)
  have hl := comparison hν hT hσ hρ hpσ hpρ (fun t ht X => (heq t ht X).ge)
    (fun X => (hinit X).ge)
  exact fun t ht => funext (fun X => le_antisymm (hu t ht X) (hl t ht X))

theorem abs_le_barrier {n : ℕ} {ν T : ℝ} {a : VectorField n} {ρ : ScalarField n}
    {B : ℝ → ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hpρ : ∀ t, FactorsThrough (ρ t) cover)
    (hB : ContDiff ℝ 2 B)
    (heq : ∀ t ∈ Icc (0:ℝ) T, ∀ X, |residual ν a ρ t X| ≤ deriv B t)
    (hinit : ∀ X, |ρ 0 X| ≤ B 0) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ X, |ρ t X| ≤ B t := by
  have hbc : ContDiff ℝ 2 (fun p : ℝ × Coord n => B p.1) := hB.comp contDiff_fst
  have hpB : ∀ t, FactorsThrough (fun _ : Coord n => B t) cover := fun _ _ _ _ => rfl
  have upper := comparison (σ := fun s _ => B s) hν hT hρ hbc hpρ hpB
    (fun t ht X => by rw [residual_timeConstant]; exact (abs_le.mp (heq t ht X)).2)
    (fun X => (abs_le.mp (hinit X)).2)
  have hz : ContDiff ℝ 2 (fun _ : ℝ × Coord n => (0:ℝ)) := contDiff_const
  have hneg : ∀ t X, residual ν a (fun s Y => -ρ s Y) t X = -residual ν a ρ t X := by
    intro t X
    have hh := residual_sub (ρ := fun _ _ => 0) ν a hz hρ t X
    simpa [residual_timeConstant] using hh
  have hnρ : ContDiff ℝ 2 (fun p : ℝ × Coord n => -ρ p.1 p.2) := hρ.neg
  have hnp : ∀ t, FactorsThrough (fun X => -ρ t X) cover := by
    intro t X Y hXY
    change -ρ t X = -ρ t Y
    rw [hpρ t hXY]
  have lower := comparison (ρ := fun s Y => -ρ s Y) (σ := fun s _ => B s) hν hT hnρ hbc hnp hpB
    (fun t ht X => by rw [hneg, residual_timeConstant]; linarith [(abs_le.mp (heq t ht X)).1])
    (fun X => by linarith [(abs_le.mp (hinit X)).1])
  intro t ht X
  exact abs_le.mpr ⟨by linarith [lower t ht X],upper t ht X⟩

theorem diffusion_error {n : ℕ} {ν T : ℝ} {a : VectorField n} {ρ ψ g : ScalarField n}
    {B : ℝ → ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hψ : ContDiff ℝ 2 (uncurry ψ))
    (hpρ : ∀ t, FactorsThrough (ρ t) cover) (hpψ : ∀ t, FactorsThrough (ψ t) cover)
    (hB : ContDiff ℝ 2 B)
    (hρeq : ∀ t ∈ Icc (0:ℝ) T, ∀ X, residual ν a ρ t X = g t X)
    (hψeq : ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      deriv (fun s => ψ s X) t + advection a ψ t X = g t X)
    (hlap : ∀ t ∈ Icc (0:ℝ) T, ∀ X, ν * |laplacian ψ t X| ≤ deriv B t)
    (hinit : ∀ X, |ρ 0 X - ψ 0 X| ≤ B 0) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ X, |ρ t X - ψ t X| ≤ B t := by
  have hp : ∀ t, FactorsThrough (fun X => ρ t X - ψ t X) cover := by
    intro t X Y hXY
    change ρ t X - ψ t X = ρ t Y - ψ t Y
    rw [hpρ t hXY,hpψ t hXY]
  apply abs_le_barrier (a := a) (ρ := fun s Y => ρ s Y - ψ s Y) hν hT (hρ.sub hψ) hp hB _ hinit
  intro t ht X
  rw [residual_sub ν a hρ hψ, hρeq t ht X]
  dsimp only [residual]
  rw [hψeq t ht X]
  have he : g t X - (g t X - ν * laplacian ψ t X) = ν * laplacian ψ t X := by ring
  rw [he,abs_mul,abs_of_nonneg hν]
  exact hlap t ht X

end VelocityDetection.PeriodicComparison
end

end OAI
