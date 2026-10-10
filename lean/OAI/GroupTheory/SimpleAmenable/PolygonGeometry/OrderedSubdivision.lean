import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierAlgorithm

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section OrderedSubdivision
open Classical Set

theorem exists_consecutiveSubdivision (E : Finset ℝ) {L U x : ℝ}
    (hL : L∈E) (hU : U∈E) (hx : x∈Ico L U) :
    ∃s t,ConsecutiveSubdivision E s t ∧ x∈Icc s t := by
  let E₀ := E.filter (fun s => s≤x)
  have h₀ : E₀.Nonempty := ⟨L,Finset.mem_filter.mpr ⟨hL,hx.1⟩⟩
  let s := E₀.max' h₀
  have hs₀ : s∈E₀ := Finset.max'_mem E₀ h₀
  have hs := Finset.mem_filter.mp hs₀
  let E₁ := E.filter (fun t => s<t)
  have h₁ : E₁.Nonempty := ⟨U,Finset.mem_filter.mpr ⟨hU,lt_of_le_of_lt hs.2 hx.2⟩⟩
  let t := E₁.min' h₁
  have ht₁ : t∈E₁ := Finset.min'_mem E₁ h₁
  have ht := Finset.mem_filter.mp ht₁
  refine ⟨s,t,⟨hs.1,ht.1,ht.2,?_⟩,hs.2,?_⟩
  · intro r hr hsr
    exact Finset.min'_le E₁ r (Finset.mem_filter.mpr ⟨hr,hsr⟩)
  · by_contra h
    have htx : t≤x := le_of_lt (lt_of_not_ge h)
    have hts : t ≤ s := Finset.le_max' E₀ t (Finset.mem_filter.mpr ⟨ht.1,htx⟩)
    exact not_lt_of_ge hts ht.2

theorem sampledBarriers_contains_line {a m : ℕ} (ha : 0<a) (i : Fin m) {N : ℝ}
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    {j : Fin 4} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (hact : ∀z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i → cutForm a j (barrierSitePoint z)=ordinary c →
      (barrierSitePoint z=barrierIncoming a j c ∨ z∈M j) → b j z=true) :
    ∀p∈squareInterior,cutForm a j p=ordinary c → p∈sampledBarriers ha i N M b := by
  intro p hp hpc
  let x := barrierLineParameter j p
  have hpx : barrierLinePoint a j c x=p := barrierLinePoint_parameter hpc
  have hxin : x∈Ioo (barrierLineLower a j c) (barrierLineUpper a j c) := by
    apply (barrierLinePoint_interior_iff hc x).mp
    rwa [hpx]
  let E := barrierSubdivision ha i j c (M j)
  have hL : barrierLineLower a j c∈E := by simp [E,barrierSubdivision]
  have hU : barrierLineUpper a j c∈E := by simp [E,barrierSubdivision]
  obtain ⟨s,t,hst,hx⟩ := exists_consecutiveSubdivision E hL hU ⟨hxin.1.le,hxin.2⟩
  obtain ⟨z,hzt,hzp,hzm⟩ := barrierSubdivision_start_site ha i hc (M j) hst
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := by
    rw [hzp]; exact cutForm_barrierLinePoint a j c s
  have hzb : b j z=true := hact z hzt hzline (hzm.imp (fun hs => by rw [hzp,hs]; rfl) id)
  have hactivation : barrierActivation ha i j c (b j) s=true := by
    rw [barrierActivation_at_site ha i j c (b j) s z hzt hzp,hzb]
  refine ⟨⟨j,⟨c,hc⟩⟩,(s,t),?_,x,hx,hpx⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨hst.1,hst.2.1⟩,hst,hactivation⟩

theorem barrierActiveIntervals_empty {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hb : ∀z,z.val.1=i → cutForm a j (barrierSitePoint z)=ordinary c → b z=false) :
    barrierActiveIntervals ha i j c M b=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro st hst
  have hh := (Finset.mem_filter.mp hst).2
  obtain ⟨z,hzt,hzp,_⟩ := barrierSubdivision_start_site ha i hc M hh.1
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := by
    rw [hzp]; exact cutForm_barrierLinePoint a j c st.1
  rw [barrierActivation_at_site ha i j c b st.1 z hzt hzp,hb z hzt hzline] at hh
  exact Bool.false_ne_true hh.2

end OrderedSubdivision

end SimpleAmenable
end
end

end OAI
