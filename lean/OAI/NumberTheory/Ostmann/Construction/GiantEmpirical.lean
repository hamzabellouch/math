import OAI.NumberTheory.Ostmann.Construction.GiantMeanBounds
import OAI.NumberTheory.Ostmann.Preliminaries.WindowTestStability
import OAI.NumberTheory.Ostmann.Supply.Statement

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries
open scoped BigOperators

def giantNatTest (d : Decomposition) (p n : ℕ) : ℝ :=
  if hp : p=0 then 0 else letI : NeZero p := ⟨hp⟩
    giantTestReal (d.residueSupport p) (n : ZMod p)

def giantSupportMean (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p=0 then 0 else letI : NeZero p := ⟨hp⟩
    (∑r∈d.residueSupport p,giantTestReal (d.residueSupport p) r)/((d.residueSupport p).card:ℝ)

def giantEmpiricalMean (d : Decomposition) (X p : ℕ) : ℝ :=
  (∑n∈upperWindow d.A X,giantNatTest d p n)/((upperWindow d.A X).card:ℝ)

lemma giantNatTest_eq (d : Decomposition) (p n : ℕ) [NeZero p] :
    giantNatTest d p n=giantTestReal (d.residueSupport p) (n:ZMod p) := by
  simp [giantNatTest,NeZero.ne p]

lemma giantSupportMean_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    giantSupportMean d p=(∑r∈d.residueSupport p,giantTestReal (d.residueSupport p) r)/
      ((d.residueSupport p).card:ℝ) := by
  simp [giantSupportMean,NeZero.ne p]

theorem giantSupportMean_lower (d : Decomposition) {p : ℕ} (hp : p.Prime)
    {δ : ℝ} (hδ : 0≤δ) (hlo : (1/3:ℝ)≤Supply.residueDensityTotal d p)
    (hhi : Supply.residueDensityTotal d p≤(2/3:ℝ)) (hγ : δ≤Supply.residueGamma d p) :
    δ/Real.sqrt 2≤giantSupportMean d p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [giantSupportMean_eq]
  rw [Supply.residueDensityTotal_eq] at hlo hhi
  rw [Supply.residueGamma_eq] at hγ
  exact giantTestReal_support_mean_lower (d.residueSupport p) hδ hlo hhi hγ

theorem eventually_giant_mean_square_error (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop,
      (∑p∈(collisionScale 4 X).primesLE,(Real.log p/(p:ℝ))*
        (giantEmpiricalMean d X p-giantSupportMean d p)^2)≤
        collisionConstant 4*Real.log (Real.log (X:ℝ)) := by
  filter_upwards [eventually_upperWindow_A_test_stability d] with X hX
  let f := fun (p : PrimeUpTo (collisionScale 4 X)) (r : ZMod p.val) =>
    (giantTestReal (d.residueSupport p.val) r : ℂ)
  have hf (p : PrimeUpTo (collisionScale 4 X)) : ∑r,‖f p r‖^2≤p.val := by
    simpa only [f,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      giantTestReal_sq_sum_le (d.residueSupport p.val)
  have hb := hX f hf
  rw [← sum_primeUpTo]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  have hreal :
      ((∑ n∈upperWindow d.A X,f p (n:ZMod p.val))/((upperWindow d.A X).card:ℂ)) -
      ((∑ r∈d.residueSupport p.val,f p r)/((d.residueSupport p.val).card:ℂ)) =
      ((giantEmpiricalMean d X p.val-giantSupportMean d p.val : ℝ):ℂ) := by
    simp only [giantEmpiricalMean,giantSupportMean_eq,giantNatTest_eq,f,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast]
  rw [hreal,Complex.norm_real,Real.norm_eq_abs,sq_abs]

end Ostmann.Construction

end

end OAI
