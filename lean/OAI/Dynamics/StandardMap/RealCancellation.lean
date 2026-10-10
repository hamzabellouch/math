import OAI.Dynamics.StandardMap.ShapeCore

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma realArray_noFastCancellation (d : DistanceArray) (hu : UnitArray d)
    (hn : ∀ s t : DyadicTime,(s:ℝ)<(t:ℝ) → ¬arrayCancellation s t d) :
    NoFastCancellation (realArray d) (1/100000000) := by
  have hc := continuous_realArray d hu
  let R : ℝ → ℝ → Prop := fun x y => ¬(x<y ∧
    (1-1/100000000:ℝ)*(y-x)/2<realArray d x ((x+y)/2) ∧
    (1-1/100000000:ℝ)*(y-x)/2<realArray d ((x+y)/2) y ∧
    realArray d x y<(1/100000000:ℝ)*(y-x)/2)
  have hcl : IsClosed {p : ℝ×ℝ | R p.1 p.2} := by
    apply IsOpen.isClosed_compl
    exact (isOpen_lt continuous_fst continuous_snd).inter
      ((isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2)
        (hc.comp (continuous_fst.prodMk ((continuous_fst.add continuous_snd).div_const 2)))).inter
        ((isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2)
          (hc.comp (((continuous_fst.add continuous_snd).div_const 2).prodMk continuous_snd))).inter
          (isOpen_lt hc (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2))))
  have hdy : ∀ s t : DyadicTime,R s t := by
    intro s t he
    apply hn s t he.1
    simpa only [arrayCancellation,←realArray_coe d hu,dyadicMid_val] using he.2
  have hall := isClosed_property2 (p := R) dyadicTime_dense hcl hdy
  intro z t ht he
  have hh := hall (z-t) (z+t)
  apply hh
  refine ⟨by linarith,?_⟩
  have hm : (z-t+(z+t))/2=z := by ring
  have hl : (z+t-(z-t))/2=t := by ring
  rw [hm]
  rcases he with ⟨he1,he2,he3⟩
  constructor
  · nlinarith
  constructor <;> nlinarith
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma noCancellation_aemulti : ∀ᵐ d ∂L.multi,NoFastCancellation (realArray d.val) (1/100000000) := by
  have hh (s t : DyadicTime) : ∀ᵐ d ∂L.multi,(s:ℝ)<(t:ℝ) → ¬arrayCancellation s t d.val := by
    by_cases hst : (s:ℝ)<(t:ℝ)
    · have he : ∀ᵐ d ∂L.multi,¬arrayCancellation s t d.val := ae_iff.mpr (by simpa using S.cancellation_null_multi L s t hst)
      filter_upwards [he] with d hd
      exact fun _ => hd
    · exact Eventually.of_forall fun d h => (hst h).elim
  filter_upwards [S.unit_aemulti L,ae_all_iff.mpr (fun s => ae_all_iff.mpr (hh s))] with d hu hn
  exact realArray_noFastCancellation d.val hu hn
lemma noCancellation_aeterminal : ∀ᵐ d ∂L.terminal,NoFastCancellation (realArray d.val) (1/100000000) := by
  have hh (s t : DyadicTime) : ∀ᵐ d ∂L.terminal,(s:ℝ)<(t:ℝ) → ¬arrayCancellation s t d.val := by
    by_cases hst : (s:ℝ)<(t:ℝ)
    · have he : ∀ᵐ d ∂L.terminal,¬arrayCancellation s t d.val := ae_iff.mpr (by simpa using S.cancellation_null_terminal L s t hst)
      filter_upwards [he] with d hd
      exact fun _ => hd
    · exact Eventually.of_forall fun d h => (hst h).elim
  filter_upwards [S.unit_aeterminal L,ae_all_iff.mpr (fun s => ae_all_iff.mpr (hh s))] with d hu hn
  exact realArray_noFastCancellation d.val hu hn
end CriticalScaleSequence
end StandardMapEntropy

end OAI
