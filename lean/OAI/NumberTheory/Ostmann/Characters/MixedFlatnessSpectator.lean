import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorSelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction QuadraticCenter Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def mixedSpectatorSource (d : Decomposition) (δ L : ℝ)
    (hZ : 0<harmonicPrimeMass (mixedSpectatorPrimes d δ L)) : PrimeSource :=
  harmonicPrimeSource (mixedSpectatorPrimes d δ L)
    (fun _prime hp=>(mixedSpectator_prime_support d δ L hp).1) hZ

theorem mixedSpectatorSource_balanced (d : Decomposition) (δ L : ℝ)
    (hZ : 0<harmonicPrimeMass (mixedSpectatorPrimes d δ L)) :
    (mixedSpectatorSource d δ L hZ).law.mean (fun p=>balancedPrimeIndicator d p)=1 := by
  change (harmonicPrimeSource _ _ hZ).law.mean
    (fun p=>if Supply.balancedDensity d p then 1 else 0)=1
  rw [harmonicPrimeSource_event_mean]
  have hf : (mixedSpectatorPrimes d δ L).filter (Supply.balancedDensity d)=mixedSpectatorPrimes d δ L := by
    exact Finset.filter_eq_self.mpr (fun p hp=>(mixedSpectator_prime_support d δ L hp).2.2.2.1)
  rw [hf,div_self hZ.ne']

theorem mixedSpectator_correlation_bound (d : Decomposition) (δ L : ℝ)
    {p : ℕ} [Fact p.Prime] (hp : p∈mixedSpectatorPrimes d δ L) :
    (FiniteField.correlationBound (Supply.additiveTransform (d.residueSupport p)):ℝ)<δ := by
  simpa only [mixedPrimeBias_prime] using (mixedSpectator_prime_support d δ L hp).2.2.2.2

theorem mixedSpectator_card_lower (d : Decomposition) (δ L : ℝ) :
    harmonicPrimeMass (mixedSpectatorPrimes d δ L)*Real.exp (Real.exp ((1/2000:ℝ)*L)) ≤
      ((mixedSpectatorPrimes d δ L).card:ℝ) := by
  unfold harmonicPrimeMass
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑p∈mixedSpectatorPrimes d δ L,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hs := mixedSpectator_prime_support d δ L hp
      have hp0 : (0:ℝ)<p := by exact_mod_cast hs.1.pos
      have hh := Real.exp_le_exp.mpr hs.2.1
      rw [Real.exp_log hp0] at hh
      have hb := (div_le_one hp0).mpr hh
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hb
    _ = _ := by simp

theorem eventually_exists_mixed_spectator (d : Decomposition)
    (hhigher : HigherHarmonicBandInput d (1/2000) (1/1000))
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ L : ℝ in atTop,∃ (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
      (hZ : 0<harmonicPrimeMass P),
      P=mixedSpectatorPrimes d δ L ∧ L/5000≤harmonicPrimeMass P ∧
      (L/5000)*Real.exp (Real.exp ((1/2000:ℝ)*L))≤(P.card:ℝ) ∧
      (∀p∈P,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
        Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L)) ∧
      (1/2:ℝ)≤(harmonicPrimeSource P hP hZ).law.mean (fun p=>balancedPrimeIndicator d p) ∧
      (∀p∈P,Supply.balancedDensity d p ∧ mixedPrimeBias d p<δ) := by
  filter_upwards [eventually_mixedSpectator_mass d hhigher δ hδ,eventually_gt_atTop (0:ℝ)]
    with L hmass hL
  have hZ : 0<harmonicPrimeMass (mixedSpectatorPrimes d δ L) :=
    (by positivity : 0<L/5000).trans_le hmass
  refine ⟨mixedSpectatorPrimes d δ L,(fun p hp=>(mixedSpectator_prime_support d δ L hp).1),hZ,
    rfl,hmass,?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le).trans
      (mixedSpectator_card_lower d δ L)
  · intro p hp
    exact ⟨(mixedSpectator_prime_support d δ L hp).2.1,(mixedSpectator_prime_support d δ L hp).2.2.1⟩
  · have hh := mixedSpectatorSource_balanced d δ L hZ
    change (mixedSpectatorSource d δ L hZ).law.mean (fun p=>balancedPrimeIndicator d p)=1 at hh
    change (1/2:ℝ)≤(mixedSpectatorSource d δ L hZ).law.mean (fun p=>balancedPrimeIndicator d p)
    rw [hh]
    norm_num
  · intro p hp
    exact (mixedSpectator_prime_support d δ L hp).2.2.2

end Ostmann.Characters

end

end OAI
