import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.SignalRemainder
import OAI.GroupTheory.SimpleAmenable.RandomFields.FieldSignalData
import OAI.GroupTheory.SimpleAmenable.Simplicial.BitReindex

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceTransportEstimate
open Classical Matrix MeasureTheory
attribute [local irreducible] sourceCommonSites flagBoxFinset

theorem smoothNoiseTransportError_le_decidable {ι : Type*} [Fintype ι] [H : DecidableEq ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) :
    smoothNoiseTransportError B C h ≤ smoothNoiseTransportConstant*
      (matrixHSNorm (C-B)+(1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh)) := by
  have he : H=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  exact smoothNoiseTransportError_le B C h

theorem smoothNoiseTransportError_of_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) {d b : ℝ} (hd : 0≤d)
    (hh : matrixHSNorm (C-B)≤d) (hi : finiteL2Norm ((1+B)⁻¹*ᵥh)≤b) :
    smoothNoiseTransportError B C h≤ smoothNoiseTransportConstant*(d+(1+d)*b) := by
  apply (smoothNoiseTransportError_le_decidable B C h).trans
  apply mul_le_mul_of_nonneg_left _ smoothNoiseTransportConstant_pos.le
  exact add_le_add hh (mul_le_mul (add_le_add le_rfl hh) hi (finiteL2Norm_nonneg _)
    (add_nonneg zero_le_one hd))

theorem sourceSmoothFieldLaw_transportEstimate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L ρ η κ : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (q : ℝ) (hθc : ∀x,L≤‖x‖ → θ x=q)
    (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) (d b : ℝ) (hd : 0≤d) :
    let T := sourceCommonSites (v:=v) hD g hL n
    let B : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n z.val w.val)
    let C : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
    let h : T → ℝ := fun z => flagSignalDifference hD g θ (sourceDyadicN n) z.val
    matrixHSNorm (C-B) ≤ d → finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ b →
    ObservableClose (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n)
      ((sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map
        (fieldReindex (flagSitePermutation hD g)))
      (smoothNoiseTransportConstant*(d+(1+d)*b)) := by
  intro T B C h hh hi
  have hc := sourceSmoothFieldLaw_close (v:=v) (η:=η) hD g θ χ hL hχc q hθc hρ hκ n
  exact hc.mono (smoothNoiseTransportError_of_bounds B C h hd hh hi)

end SourceTransportEstimate

section SourceTransportConstants
open Classical Matrix MeasureTheory Filter
open scoped Topology

theorem sourceSmoothFieldLaw_transport_constants {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L Λ : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0)
    (hΛ : 0≤Λ) (hLip : ∀x y,|χ x-χ y| ≤ Λ*(|x.1-y.1|+|x.2-y.2|)) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n)
        ((sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n).map
          (fieldReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hinv⟩ := sourceFlagMatrix_inverse_signal (v:=v) hD g ψ χ hψ hsψ q K L hL hKL hcompact hχ hχ₁ hχc
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro η hη hη₁ κ hκ δ d hδ hd
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  let T := sourceCommonSites (v:=v) hD g hL
  let B (n : ℕ) : Matrix (T n) (T n) ℝ := Matrix.of (fun z w =>
    sourceFlagMatrix χ ((D:ℝ)^4/5) η κ n z.val w.val)
  let C (n : ℕ) : Matrix (T n) (T n) ℝ := Matrix.of (fun z w =>
    sourceFlagMatrix χ ((D:ℝ)^4/5) η κ n (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
  let h (n : ℕ) : T n → ℝ := fun z => flagSignalDifference hD g (fun x => q+ψ x) (sourceDyadicN n) z.val
  have hhs : Tendsto (fun n => matrixHSNorm (C n-B n)) atTop (nhds 0) := by
    convert! sourceFlagMatrix_HS_tendsto hD g χ hχ hL hχc hΛ hρ hη hκ hLip T using 1
  filter_upwards [hinv η hη hη₁ κ hκ δ hδ,hhs.eventually_lt_const hd] with n hn hdn
  have hi : finiteL2Norm ((1+B n)⁻¹*ᵥh n)≤C₁*η+C₂*Real.sqrt κ+δ := by
    exact hn (T n) Finset.subset_union_left
  have hθc : ∀x,L≤‖x‖ → q+ψ x=q := by
    intro x hx
    rw [hcompact x (by linarith only [hx,hKL]),add_zero]
  exact sourceSmoothFieldLaw_transportEstimate (v:=v) (η:=η) hD g (fun x => q+ψ x) χ
    hL hχc q hθc hρ hκ n d (C₁*η+C₂*Real.sqrt κ+δ) hd.le hdn.le hi

end SourceTransportConstants

section SignalTransport
open Classical MeasureTheory Filter
open scoped Topology
namespace FieldSignalData

theorem realLaw_transport_constants (S : FieldSignalData)
    {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) (g : polygonFullGroup a m) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (S.realLaw (v:=v) hD η κ n)
        ((S.realLaw (v:=v) hD η κ n).map (fieldReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) :=
  sourceSmoothFieldLaw_transport_constants hD g S.ψ S.χ S.smooth S.compact S.q S.K S.L S.Λ
    S.L_pos S.gap S.ψ_zero S.χ_range S.χ_one S.χ_zero S.Λ_nonneg S.χ_lipschitz

theorem bitLaw_transport_constants (S : FieldSignalData)
    {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) (g : polygonFullGroup a m) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (S.bitLaw (v:=v) hD η κ n)
        ((S.bitLaw (v:=v) hD η κ n).map (bitReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := S.realLaw_transport_constants (v:=v) hD g
  refine ⟨C₁,C₂,hC₁,hC₂,fun η hη hη₁ κ hκ δ d hδ hd => ?_⟩
  filter_upwards [h η hη hη₁ κ hκ δ d hδ hd] with n hn
  exact hn.threshold_transport _ _

end FieldSignalData
end SignalTransport

section SourceFieldTransport
open Classical Matrix MeasureTheory Filter
open scoped Topology

theorem sourceSmoothFieldLaw_transport {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L Λ : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0)
    (hΛ : 0≤Λ) (hLip : ∀x y,|χ x-χ y| ≤ Λ*(|x.1-y.1|+|x.2-y.2|))
    (ε : ℝ) (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,
      ObservableClose (sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n)
        ((sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n).map
          (fieldReindex (flagSitePermutation hD g))) ε := by
  obtain ⟨C₁,C₂,hC₁,hC₂,ht⟩ := sourceSmoothFieldLaw_transport_constants (v:=v) hD g ψ χ
    hψ hsψ q K L Λ hL hKL hcompact hχ hχ₁ hχc hΛ hLip
  obtain ⟨η,κ,δ,d,hη,hη₁,hκ,hδ,hd,hparameters⟩ :=
    smallTransportParameters smoothNoiseTransportConstant_pos hC₁ hC₂ hε
  refine ⟨η,κ,hη,hη₁,hκ,?_⟩
  filter_upwards [ht η hη hη₁ κ hκ δ d hδ hd] with n hn
  exact hn.mono (hparameters d (C₁*η+C₂*Real.sqrt κ+δ) hd.le le_rfl (by positivity) le_rfl).le

end SourceFieldTransport

end SimpleAmenable
end
end

end OAI
