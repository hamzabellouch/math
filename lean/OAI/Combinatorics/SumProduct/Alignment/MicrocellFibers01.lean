import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RawHarmonic01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope11
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
end
end RawSuccessInlineScope11

 

 

section RawSuccessInlineScope12
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace MicrocellConditional
open Finset RawHarmonicProbability
attribute [local instance] Classical.propDecidable

def eventMass (C:Finset ℕ) (A:Set ℕ) : ℝ := ∑ p∈C,if p∈A then (p:ℝ)⁻¹ else 0

lemma law_apply_units (X W:ℕ) (hw:0<W) (hx:4*W≤X) (A:Set ℕ) :
    (law X W hw hx:Measure ℕ).real A =
      eventMass (units X W) A/DyadicHarmonicBoundary.mass X (X^2) W := by
  unfold eventMass
  rw [law_apply,units,sum_filter]
  congr 1
  apply sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

lemma subset_event_sum (X W:ℕ) (C:Finset ℕ) (hC:C⊆units X W) (A:Set ℕ) :
    eventMass (units X W) (A∩(C:Set ℕ))=eventMass C A := by
  unfold eventMass
  symm
  calc
    _ = ∑ p∈C,if p∈A∩(C:Set ℕ) then (p:ℝ)⁻¹ else 0 := by
      apply sum_congr rfl
      intro p hp
      simp [hp]
    _ = ∑ p∈units X W,if p∈A∩(C:Set ℕ) then (p:ℝ)⁻¹ else 0 :=
      sum_subset hC (fun p hp hnot=>by simp [hnot])
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      split_ifs <;> rfl

 

theorem conditional_ratio (X W:ℕ) (hw:0<W) (hx:4*W≤X)
    (C:Finset ℕ) (hC:C⊆units X W) (A:Set ℕ) :
    (law X W hw hx:Measure ℕ).real (A∩(C:Set ℕ)) /
      (law X W hw hx:Measure ℕ).real (C:Set ℕ) =
      eventMass C A/(∑ p∈C,(p:ℝ)⁻¹) := by
  rw [law_apply_units,law_apply_units,subset_event_sum X W C hC A]
  have hd:eventMass (units X W) (C:Set ℕ)=∑ p∈C,(p:ℝ)⁻¹ := by
    have hh:=subset_event_sum X W C hC Set.univ
    rw [Set.univ_inter] at hh
    exact hh.trans (by simp [eventMass])
  rw [hd,div_div_div_cancel_right₀ (mass_pos X W hw hx).ne']

lemma cell_real_law (C:Finset ℕ) (hC:C.Nonempty) (hpos:∀ p∈C,0<p) (A:Set ℕ) :
    letI : Nonempty C:=hC.coe_sort
    (MicrocellProbability.weightedLaw (fun p:C=>(p.1:ℝ)⁻¹)
      (fun p=>inv_pos.mpr (by exact_mod_cast hpos p.1 p.2))
      Subtype.val : Measure ℕ).real A =
        eventMass C A/(∑ p∈C,(p:ℝ)⁻¹) := by
  classical
  let : Nonempty C:=hC.coe_sort
  rw [MicrocellProbability.weightedLaw_apply _ _ _ _ MeasurableSet.of_discrete]
  simp only [MicrocellHarmonic.weight]
  rw [sum_coe_sort C (fun p:ℕ=>(p:ℝ)⁻¹)]
  rw [sum_coe_sort C (fun p:ℕ=>(p:ℝ)⁻¹/(∑ q∈C,(q:ℝ)⁻¹)*(if p∈A then 1 else 0))]
  unfold eventMass
  rw [sum_div]
  apply sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

 

theorem conditional_event_error (X W:ℕ) (hw:0<W) (hx:4*W≤X)
    (C:Finset ℕ) (hC:C.Nonempty) (hsub:C⊆units X W)
    (x₀ R:ℝ) (hbase:(X:ℝ)≤x₀) (hR:0≤R)
    (hwindow:∀ p∈C,x₀≤(p:ℝ) ∧ (p:ℝ)≤x₀+R) (A:Set ℕ) :
    letI : Nonempty C:=hC.coe_sort
    |(law X W hw hx:Measure ℕ).real (A∩(C:Set ℕ)) /
      (law X W hw hx:Measure ℕ).real (C:Set ℕ) -
        (MicrocellProbability.uniformLaw (Subtype.val:C→ℕ):Measure ℕ).real A| ≤ R/X := by
  let : Nonempty C:=hC.coe_sort
  have hxp:(0:ℝ)<X:=by exact_mod_cast (show 0<X by omega)
  have hx₀:0<x₀:=hxp.trans_le hbase
  have hpos:∀ p∈C,0<p:=by
    intro p hp
    have hh:=hx₀.trans_le (hwindow p hp).1
    exact_mod_cast hh
  rw [conditional_ratio X W hw hx C hsub A,←cell_real_law C hC hpos A]
  have hh:=MicrocellProbability.harmonic_event_error (fun p:C=>(p.1:ℝ)) x₀ R hx₀ hR
    (fun p=>hwindow p.1 p.2) (Subtype.val:C→ℕ) A MeasurableSet.of_discrete
  exact hh.trans (div_le_div_of_nonneg_left hR hxp hbase)

 

theorem conditional_success (X W:ℕ) (hw:0<W) (hx:4*W≤X)
    (C:Finset ℕ) (hC:C.Nonempty) (hsub:C⊆units X W)
    (x₀ R c:ℝ) (hbase:(X:ℝ)≤x₀) (hR:0≤R)
    (hwindow:∀ p∈C,x₀≤(p:ℝ) ∧ (p:ℝ)≤x₀+R) (A:Set ℕ)
    (herr:R/X≤c/6)
    (hs:letI : Nonempty C:=hC.coe_sort
      c/2<(MicrocellProbability.uniformLaw (Subtype.val:C→ℕ):Measure ℕ).real A) :
    c/3<(law X W hw hx:Measure ℕ).real (A∩(C:Set ℕ)) /
      (law X W hw hx:Measure ℕ).real (C:Set ℕ) := by
  have hh:=conditional_event_error X W hw hx C hC hsub x₀ R hbase hR hwindow A
  have hh':=(abs_le.mp hh).1
  linarith

end MicrocellConditional
end
end RawSuccessInlineScope12

 

 

section RawSuccessInlineScope13

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MicrocellFibers
attribute [local instance] Classical.propDecidable
open Finset RawHarmonicProbability MicrocellConditional

 

def fiber (M N k r:ℕ) : Finset ℕ :=
  (Ico (M*k) (M*(k+N))).filter (fun p=>p%M=r)

def point (M k r b:ℕ) : ℕ := M*k+r+M*b

lemma point_mem (M N k r:ℕ) (_:0<M) (hr:r<M) (b:Fin N) :
    point M k r b∈fiber M N k r := by
  apply mem_filter.mpr
  constructor
  · apply mem_Ico.mpr
    constructor
    · unfold point; omega
    · unfold point
      have hb:M*(b.val+1)≤M*N:=Nat.mul_le_mul_left M (by omega)
      nlinarith
  · simp [point,Nat.add_mod,Nat.mod_eq_of_lt hr]

lemma point_injective (M k r:ℕ) (hM:0<M) : Function.Injective (point M k r) := by
  intro a b hab
  unfold point at hab
  exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hab)

lemma represent (M N k r p:ℕ) (hM:0<M) (hp:p∈fiber M N k r) :
    ∃ b:Fin N,point M k r b=p := by
  obtain ⟨hpI,hpr⟩:=mem_filter.mp hp
  obtain ⟨hlo,hhi⟩:=mem_Ico.mp hpI
  have hqlo:k≤p/M:=(Nat.le_div_iff_mul_le hM).mpr (by simpa [Nat.mul_comm] using hlo)
  have hqhi:p/M<k+N:=(Nat.div_lt_iff_lt_mul hM).mpr (by simpa [Nat.mul_comm] using hhi)
  refine ⟨⟨p/M-k,by omega⟩,?_⟩
  have hq:k+(p/M-k)=p/M:=Nat.add_sub_of_le hqlo
  dsimp [point]
  calc
    M*k+r+M*(p/M-k)=M*(k+(p/M-k))+r:=by ring
    _ = M*(p/M)+p%M:=by rw [hq,hpr]
    _ = p:=Nat.div_add_mod p M

 
def parametrization (M N k r:ℕ) (hM:0<M) (hr:r<M) : Fin N ≃ fiber M N k r :=
  Equiv.ofBijective (fun b=>⟨point M k r b,point_mem M N k r hM hr b⟩) (by
    constructor
    · intro a b hab
      apply Fin.ext
      exact point_injective M k r hM (congrArg Subtype.val hab)
    · intro p
      obtain ⟨b,hb⟩:=represent M N k r p hM p.2
      exact ⟨b,Subtype.ext hb⟩)

lemma fiber_card (M N k r:ℕ) (hM:0<M) (hr:r<M) :
    (fiber M N k r).card=N := by
  simpa only [Fintype.card_coe,Fintype.card_fin] using
    (Fintype.card_congr (parametrization M N k r hM hr)).symm

lemma fiber_nonempty (M N k r:ℕ) (hM:0<M) (hN:0<N) (hr:r<M) :
    (fiber M N k r).Nonempty := by
  rw [←card_pos,fiber_card M N k r hM hr]
  exact hN

lemma fiber_subset_units (X W M N k r:ℕ) (hWM:W∣M)
    (hr:W.Coprime r) (hlo:X≤M*k) (hhi:M*(k+N)≤X^2) :
    fiber M N k r⊆units X W := by
  intro p hp
  obtain ⟨hpI,hpr⟩:=mem_filter.mp hp
  obtain ⟨hp₀,hp₁⟩:=mem_Ico.mp hpI
  apply mem_filter.mpr
  refine ⟨mem_Ico.mpr ⟨hlo.trans hp₀,hp₁.trans_le hhi⟩,?_⟩
  have hm:W.Coprime (p%M):=hpr.symm ▸ hr
  have hmod:(p%M)%W=p%W:=Nat.mod_mod_of_dvd p hWM
  have hw:W.Coprime (p%W):=by
    rw [←hmod]
    exact (UnitIntervalCounts.coprime_mod W (p%M)).mpr hm
  exact (UnitIntervalCounts.coprime_mod W p).mp hw

 

lemma uniform_fiber (M N k r:ℕ) (hM:0<M) (hN:0<N) (hr:r<M) (A:Set ℕ) :
    letI : Nonempty (fiber M N k r):=(fiber_nonempty M N k r hM hN hr).coe_sort
    letI : Nonempty (Fin N):=Fin.pos_iff_nonempty.mp hN
    (MicrocellProbability.uniformLaw (Subtype.val : fiber M N k r→ℕ):Measure ℕ).real A =
      (MicrocellProbability.uniformLaw (fun b:Fin N=>point M k r b):Measure ℕ).real A := by
  let : Nonempty (fiber M N k r):=(fiber_nonempty M N k r hM hN hr).coe_sort
  let : Nonempty (Fin N):=Fin.pos_iff_nonempty.mp hN
  rw [MicrocellProbability.uniformLaw_apply _ _ MeasurableSet.of_discrete,
    MicrocellProbability.uniformLaw_apply _ _ MeasurableSet.of_discrete]
  unfold MicrocellHarmonic.uniform
  simp only [Fintype.card_coe,Fintype.card_fin,fiber_card M N k r hM hr]
  exact (Equiv.sum_comp (parametrization M N k r hM hr)
    (fun p:fiber M N k r=>(N:ℝ)⁻¹*(if p.1∈A then 1 else 0))).symm

 

theorem raw_fiber_success (X W M N k r:ℕ) (hW:0<W) (hX:4*W≤X)
    (hM:0<M) (hN:0<N) (hr:r<M) (hWR:W.Coprime r) (hWM:W∣M)
    (hlo:X≤M*k) (hhi:M*(k+N)≤X^2) (c:ℝ) (A:Set ℕ)
    (herr:((M*N:ℕ):ℝ)/X≤c/6)
    (hm:letI : Nonempty (Fin N):=Fin.pos_iff_nonempty.mp hN
      c/2<(MicrocellProbability.uniformLaw (fun b:Fin N=>point M k r b):Measure ℕ).real A) :
    c/3<(law X W hW hX:Measure ℕ).real (A∩(fiber M N k r:Set ℕ)) /
      (law X W hW hX:Measure ℕ).real (fiber M N k r:Set ℕ) := by
  refine conditional_success X W hW hX (fiber M N k r)
    (fiber_nonempty M N k r hM hN hr) (fiber_subset_units X W M N k r hWM hWR hlo hhi)
    (M*k) (M*N) c (by exact_mod_cast hlo) (by positivity) ?_ A (by simpa only [Nat.cast_mul] using herr) ?_
  · intro p hp
    obtain ⟨hp₀,hp₁⟩:=mem_Ico.mp (mem_filter.mp hp).1
    constructor
    · exact_mod_cast hp₀
    · have hp':p≤M*k+M*N:=by nlinarith
      exact_mod_cast hp'
  · rw [uniform_fiber M N k r hM hN hr A]
    exact hm

end MicrocellFibers
end
end RawSuccessInlineScope13

 

 

end

end OAI
