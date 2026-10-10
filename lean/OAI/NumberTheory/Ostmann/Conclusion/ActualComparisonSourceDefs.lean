import OAI.NumberTheory.Ostmann.Characters.MixedPrimeBiasDefs
import OAI.NumberTheory.Ostmann.Construction.BroadBandBalance
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction

structure ActualComparisonSource {d : Decomposition} {BD Bz L : ℝ} {k : ℕ}
    {E : Finset ℕ} (C : InitialSourceChoice d 200 BD Bz k L E)
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) (hZ : 0<harmonicPrimeMass P) (ε : ℝ) : Prop where
  block_lower : Real.exp ((1/20:ℝ)*L)≤C.blockBase
  block_upper : C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L)
  center_lower : C.blockBase-2<(C.giantCenter:ℝ)
  center_upper : (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2
  bulk_bin : |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16
  spectator_bin : |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16
  separated : C.CrossRoleSeparation (harmonicPrimeSource P hP hZ)
  harmonic_mass : L/5000≤harmonicPrimeMass P
  cardinal : (L/5000)*Real.exp (Real.exp ((1/2000:ℝ)*L))≤(P.card:ℝ)
  band : ∀p∈P,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
    Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L)
  balanced_mass : (1/2:ℝ)≤(harmonicPrimeSource P hP hZ).law.mean
    (fun p=>balancedPrimeIndicator d p)
  flat : ∀p∈P,Supply.balancedDensity d p ∧ Characters.mixedPrimeBias d p<ε

theorem ActualComparisonSource.mono {d : Decomposition} {BD Bz L ε ε' : ℝ} {k : ℕ}
    {E : Finset ℕ} {C : InitialSourceChoice d 200 BD Bz k L E}
    {P : Finset ℕ} {hP : ∀p∈P,p.Prime} {hZ : 0<harmonicPrimeMass P}
    (h : ActualComparisonSource C P hP hZ ε) (hε : ε≤ε') :
    ActualComparisonSource C P hP hZ ε' :=
  ⟨h.block_lower,h.block_upper,h.center_lower,h.center_upper,h.bulk_bin,h.spectator_bin,
    h.separated,h.harmonic_mass,h.cardinal,h.band,h.balanced_mass,
    fun p hp=>⟨(h.flat p hp).1,lt_of_lt_of_le (h.flat p hp).2 hε⟩⟩

end Ostmann.Conclusion

end

end OAI
