import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTTransform

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

theorem favorableTransform_zero_of_dvd (d : Decomposition) (P : Finset ℕ)
    (p : ℕ) (hp : p.Prime) (s : ℤ) (D : ℕ) (hdiv : p ∣ s.natAbs) :
    favorableGiantResidueTransform d P p (modFraction p s D) = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hs : (s : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd s p).2 (Int.natCast_dvd.mpr hdiv)
  simp only [modFraction,hs,zero_mul,favorableGiantResidueTransform,
    giantResidueTransform,residueTransform_eq,Supply.additiveTransform_zero,phase_zero]
  split_ifs <;> rfl

open Classical in

theorem actualCoefficient_level_zero (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (X G : ℝ) (g : (p:ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (a : State) :
    actualCoefficient sources seed V X G g bins outside 0 a =
      if (History.leaf a).Supported V outside then
        baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside a else 0 := by
  classical
  change (∑ _c : Unit, (1:ℂ) * (History.leaf a).supportedWeight V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G) = _
  simp [History.supportedWeight,History.weight]

theorem regular_mul_actualCoefficient_level_zero (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (X G : ℝ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (a : State)
    (hplus : a.giantPlus.Prime) (hminus : a.giantMinus.Prime)
    (ha : a.Positive) (hs : a.PrimeSmall) (ht : a.TemplateAt 0)
    (hc : a.Coprime outside) (hv : a.frequency.natAbs ≤ V 0) :
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a *
      actualCoefficient sources seed V X G (residueTransform d) bins outside 0 a =
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a *
      baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) (residueTransform d) bins outside a := by
  classical
  rw [actualCoefficient_level_zero]
  by_cases hfreq : a.frequency = 0
  · have hz := favorableTransform_zero_of_dvd d P a.giantPlus hplus a.frequency
      (outsideProduct outside*(a.product/a.giantPlus)) (by simp [hfreq])
    simp only [regularTransform,hz,zero_mul]
  · by_cases hp : a.giantPlus.Coprime a.frequency.natAbs
    · by_cases hm : a.giantMinus.Coprime a.frequency.natAbs
      · have hsupport : (History.leaf a).Supported V outside := by
          rw [History.Supported.eq_def]
          exact ⟨ha,hs,ht,hc,hfreq,hv,by simpa [History.GiantUnits,History.frequencies,History.root] using And.intro hp hm, trivial⟩
        rw [ite_eq_left hsupport]
      · have hz := favorableTransform_zero_of_dvd d P a.giantMinus hminus a.frequency
          (outsideProduct outside*(a.product/a.giantMinus)) (hminus.dvd_iff_not_coprime.mpr hm)
        simp only [regularTransform,hz,mul_zero,zero_mul]
    · have hz := favorableTransform_zero_of_dvd d P a.giantPlus hplus a.frequency
        (outsideProduct outside*(a.product/a.giantPlus)) (hplus.dvd_iff_not_coprime.mpr hp)
      simp only [regularTransform,hz,zero_mul]

end Ostmann.Construction.InitialEta

end

end OAI
