import OAI.NumberTheory.Jacobsthal.Primes.SourceRawPrimeMass
import OAI.NumberTheory.Jacobsthal.Probability.SingletonEventMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosCofactorChoices SingletonBinSelection TwoPrimeObservableSum
attribute [local instance] Classical.propDecidable

def hardSelection {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (i : Fin n) (Cs eps : ℝ) (f : Fin n → Finset ℕ) : Prop :=
  pickedPrime f i ∈ rawHardPrimeUnion Q z R theta a (selectionProduct (eraseSelection f i)) Cs eps

theorem hardSelection_fill {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (i : Fin n) (Cs eps : ℝ) (f : Fin n → Finset ℕ) (he : f i = ∅) (p : ℕ) :
    hardSelection Q z R theta a i Cs eps (fillSelection f i p) ↔
      p ∈ rawHardPrimeUnion Q z R theta a (selectionProduct f) Cs eps := by
  unfold hardSelection
  rw [erase_fill f i p he]
  simp [pickedPrime,fillSelection]

theorem hardSelection_fibre {n : ℕ} (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ)
    (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n) (Cs eps : ℝ)
    (hPi : P i = ErdosInversePrimeBin.primeBin R theta)
    (f : Fin n → Finset ℕ) (hf : f ∈ selections P (eraseMultiplicity m i)) :
    (P i).filter (fun p => hardSelection Q z R theta a i Cs eps (fillSelection f i p)) =
      rawHardPrimeUnion Q z R theta a (selectionProduct f) Cs eps := by
  ext p
  rw [Finset.mem_filter,hardSelection_fill Q z R theta a i Cs eps f (erased_coordinate_empty P m i f hf) p,hPi]
  exact and_iff_right_of_imp (fun hp => rawHardPrimeUnion_subset Q z R theta a (selectionProduct f) Cs eps hp)

end ErdosVarianceWeighted


section

open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseCells ErdosCofactorChoices
  SingletonBinSelection CanonicalSubsetBox
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_selection_hard_mass (alpha aStar eps tau Cmin : ℝ) (F : ℕ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (a : ℕ → ℕ) (n : ℕ) (P : Fin n → Finset ℕ) (m : Fin n → ℕ) (i : Fin n),m i = 1 →
        P i = primeBin R theta →
        (∀ f ∈ selections P (eraseMultiplicity m i),Squarefree (selectionProduct f) ∧
          (∀ t ∈ (selectionProduct f).primeFactors,sourceW z < (t : ℝ)) ∧
          (∀ p ∈ P i,(selectionProduct f).Coprime p ∧
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*selectionProduct f))/Real.log (sourceW z))) →
      ∀ Q : Finset ℚ,Q.card ≤ F →
        (∑ f ∈ (selections P m).filter (hardSelection Q z R theta a i Cs eps),(selectionProduct f : ℝ)⁻¹) ≤
          tau*selectionMass P m := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_raw_hard_prime_mass alpha aStar eps tau Cmin F halpha ha heps htau
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hsource xi hxi hxib] with z hz
  intro R theta hRlo hthetal hthetau a n P m i hi hPi hgeometry Q hQ
  apply singleton_event_mass_bound P m i hi _ tau
  intro f hf
  have hg := hgeometry f hf
  rw [hPi] at hg
  rw [hardSelection_fibre Q z R theta a P m i Cs eps hPi f hf,hPi]
  exact hz R theta a (selectionProduct f) hg.1 hRlo hthetal hthetau hg.2.1 hg.2.2 Q hQ

end ErdosVarianceWeighted

end


open _root_.Filter
namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport SafeSubsetBoxGeometry
  GeometricBoxImages ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection CanonicalSubsetBox
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition LogarithmicBinMaps
  ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem geometric_selection_hard_mass (C aStar alpha eps tau Cmin : ℝ) (F : ℕ)
    (hC : 1 ≤ C) (ha : 0 < aStar) (halpha : 0 < alpha) (heps : 0 < eps) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi0 → ∀ᶠ top : ℝ in atTop,
      ∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ (K L : ℝ) (z : Node),z.side = .even → 199/100 ≤ z.ratio → Consistent z →
        z.cutoff = sourceB top → z.closed = true →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
      ∀ m ∈ geometricBoxes hw htop hxi C (sourceB top) K L alpha (1/100) z,
      ∀ i : Fin (binCount (sourceW top) top xi),m i = 1 → top^alpha ≤ lower (sourceW top) top xi i →
      ∀ (a : ℕ → ℕ) (Q : Finset ℚ),Q.card ≤ F →
        (∑ f ∈ (selections (globalBins (sourceW top) top xi) m).filter
          (hardSelection Q top (lower (sourceW top) top xi i) (width (sourceW top) top xi i) a i Cs eps),
          (selectionProduct f : ℝ)⁻¹) ≤ tau*selectionMass (globalBins (sourceW top) top xi) m := by
  obtain ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,hsource⟩ :=
    source_selection_hard_mass alpha aStar eps tau Cmin F halpha ha heps htau
  refine ⟨Cs,hCs,hCmin,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  have hBT := JacobsthalSourceScale.sourceB_tendsto.comp Real.tendsto_log_atTop
  filter_upwards [hsource xi hxi hxib,source_span_geometry,
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually,
    source_B_bounds,hBT.eventually_ge_atTop 3] with top hv hspan hscale hBounds hB3
  have hw : 1 < sourceW top := hscale.1
  have htop : sourceW top < top := hspan.2.1
  have htop0 : 0 < top := (zero_lt_one.trans hw).trans htop
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hlog : 1 ≤ Real.log (sourceW top) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hBounds.1
  have hsmall : 2*(xi/Real.log (sourceW top)) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have hspanMul : (1+xi)*sourceW top ≤ top := by
    have hh := hspan.2.2 xi hxi hxi1
    have hd : 0 < top/sourceW top := div_pos htop0 (zero_lt_one.trans hw)
    have he := (Real.log_le_log_iff (by positivity : 0 < 1+xi) hd).mp hh
    exact (le_div_iff₀ (zero_lt_one.trans hw)).mp he
  have hwidth := common_width_bounds (zero_lt_one.trans hw) htop hxi hxi1 hspanMul
  refine ⟨hw,htop,?_⟩
  intro K L z heven h199 hz hcut hclosed hroot m hm i hi hiR a Q hQ
  have hs : Valid z.side z.ratio := by rw [heven];change 198/100 ≤ z.ratio;linarith
  have hStrong := source_strong_state hB3 z heven h199 hz hcut
  have hY : 0 < sourceY top := by
    by_contra! hzero
    have he : sourceY top = 0 := by omega
    rw [he,Nat.cast_zero,Real.log_zero,zero_div] at hroot
    linarith [hStrong.1]
  have hcap : (sourceW top)^z.cutoff = top := by
    rw [hcut]
    exact (JacobsthalSourceScale.sourceW_pow_sourceB hw).trans (Real.exp_log htop0)
  have hanchor := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hgeometry := full_box_variance_fibres hw htop hxi (by linarith : 0 ≤ C) ha.le hcomp
    (sourceY top) hY z hroot hs hz hStrong hclosed hcap m hanchor i hi
  have hthetal : xi/4 ≤ width (sourceW top) top xi i := by rw [hwidth.2.2.2 i];exact hwidth.2.1
  have hthetau : width (sourceW top) top xi i ≤ xi := by rw [hwidth.2.2.2 i];exact hwidth.2.2.1
  exact hv (lower (sourceW top) top xi i) (width (sourceW top) top xi i) hiR hthetal hthetau a _
    (globalBins (sourceW top) top xi) m i hi rfl hgeometry Q hQ

end ErdosVarianceWeighted


end Erdos970

end OAI
