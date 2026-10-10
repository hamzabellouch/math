import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MicrocellFibers01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope14

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace RawSmallCells
attribute [local instance] Classical.propDecidable
open Finset RawHarmonicProbability MicrocellConditional DyadicHarmonicBoundary

lemma finite_event (X W:ℕ) (hW:0<W) (hX:4*W≤X) (E:Finset ℕ)
    (hE:E⊆RawHarmonicProbability.units X W) :
    (law X W hW hX:Measure ℕ).real (E:Set ℕ)=
      (∑ p∈E,(p:ℝ)⁻¹)/mass X (X^2) W := by
  rw [law_apply_units]
  congr 1
  have hh:=subset_event_sum X W E hE Set.univ
  simpa [eventMass] using hh

 

theorem cover_cost {J:Type*} [DecidableEq J] (X W R:ℕ)
    (hW:0<W) (hX:4*W≤X) (T:Finset J) (a:J→ℕ) (E:Finset ℕ)
    (hE:E⊆RawHarmonicProbability.units X W)
    (hcover:∀ p∈E,∃ j∈T,p∈UnitIntervalCounts.units (a j) R W) :
    (law X W hW hX:Measure ℕ).real (E:Set ℕ) ≤
      4*T.card*((R:ℝ)+2*W)/X := by
  have hxN:0<X:=by omega
  have hx:(0:ℝ)<X:=by exact_mod_cast hxN
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have ht:(0:ℝ)<W.totient:=by exact_mod_cast Nat.totient_pos.mpr hW
  have hxx:X+X≤X^2:=by
    have : 2≤X:=by omega
    nlinarith
  have hm:(W.totient:ℝ)/(4*W)≤ mass X (X^2) W:=
    (dyadic_lower X W hW hX).trans (mass_mono hxx)
  have hc:=UnitNeighborhoodCost.cover_count T a R W hW E (fun p hp=>mem_biUnion.mpr (hcover p hp))
  rw [finite_event X W hW hX E hE]
  calc
    _ ≤ ((E.card:ℝ)/X)/(mass X (X^2) W) := by
      apply div_le_div_of_nonneg_right ?_ (mass_nonneg _ _ _)
      calc
        _ ≤ ∑ _p∈E,(X:ℝ)⁻¹ := sum_le_sum (by
          intro p hp
          apply inv_anti₀ hx
          exact_mod_cast (mem_Ico.mp (mem_filter.mp (hE hp)).1).1)
        _ = _:=by simp;ring
    _ ≤ ((T.card:ℝ)*W.totient*((R:ℝ)/W+2)/X)/((W.totient:ℝ)/(4*W)) := by
      apply div_le_div₀ (by positivity) (div_le_div_of_nonneg_right hc hx.le) (by positivity) hm
    _ = _:=by field_simp

 

def partialCells (X W R:ℕ) : Finset ℕ := (RawHarmonicProbability.units X W).filter
  (fun p=>¬(X≤R*(p/R) ∧ R*(p/R+1)≤X^2))

lemma partial_cover (X W R p:ℕ) (hR:0<R) (hp:p∈partialCells X W R) :
    p∈UnitIntervalCounts.units X R W ∨ p∈UnitIntervalCounts.units (X^2-R) R W := by
  obtain ⟨hpU,hbad⟩:=mem_filter.mp hp
  obtain ⟨hpI,hcop⟩:=mem_filter.mp hpU
  obtain ⟨hlo,hhi⟩:=mem_Ico.mp hpI
  have hdiv:=Nat.div_add_mod p R
  have hmod:=Nat.mod_lt p hR
  by_cases hb:X≤R*(p/R)
  · right
    have hend:X^2<R*(p/R+1):=by omega
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨?_,?_⟩,hcop⟩
    · have hmul:R*(p/R+1)=R*(p/R)+R:=by ring
      omega
    · omega
  · left
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨hlo,?_⟩,hcop⟩
    omega

 

theorem partial_cost (X W R:ℕ) (hW:0<W) (hX:4*W≤X) (hR:0<R) :
    (law X W hW hX:Measure ℕ).real (partialCells X W R:Set ℕ) ≤
      8*((R:ℝ)+2*W)/X := by
  have hh:=cover_cost X W R hW hX (univ:Finset (Fin 2))
    (fun i=>if i=0 then X else X^2-R) (partialCells X W R) (filter_subset _ _) (by
      intro p hp
      rcases partial_cover X W R p hR hp with h|h
      · exact ⟨0,mem_univ _,by simpa using h⟩
      · exact ⟨1,mem_univ _,by simpa using h⟩)
  norm_num at hh ⊢
  exact hh

lemma partial_cost_simple (X W R:ℕ) (hW:0<W) (hX:4*W≤X) (hWR:W≤R) :
    (law X W hW hX:Measure ℕ).real (partialCells X W R:Set ℕ) ≤24*(R:ℝ)/X := by
  apply (partial_cost X W R hW hX (hW.trans_le hWR)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh:(W:ℝ)≤R:=by exact_mod_cast hWR
  linarith

 

theorem eventually_partial {X W R:ℕ→ℕ}
    (hbase:∀ᶠ n in atTop,0<W n ∧ 4*W n≤X n ∧ W n≤R n)
    (hr:Tendsto (fun n=>(R n:ℝ)/X n) atTop (𝓝 0)) :
    ∃ ε:ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∀ (hw:0<W n) (hx:4*W n≤X n),
        (law (X n) (W n) hw hx:Measure ℕ).real (partialCells (X n) (W n) (R n):Set ℕ)≤ε n := by
  refine ⟨fun n=>24*((R n:ℝ)/X n),by simpa using hr.const_mul 24,?_⟩
  filter_upwards [hbase] with n hn hw hx
  simpa [mul_div_assoc] using partial_cost_simple (X n) (W n) (R n) hw hx hn.2.2

end RawSmallCells
end
end RawSuccessInlineScope14

 

 

section RawSuccessInlineScope15
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace RawPartitionSuccess
attribute [local instance] Classical.propDecidable

 

theorem finite_partition {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (S : Finset α) (w : α → ℝ) (hw : ∀ x∈S,0≤w x)
    (π : α → ι) (G : Set ι) (A : Set α) (a ε : ℝ) (ha : 0≤a)
    (hZ : 0 < ∑ x∈S,w x)
    (hbad : (∑ x∈S.filter (fun x => π x∉G),w x) ≤ ε*(∑ x∈S,w x))
    (hs : ∀ i∈S.image π,i∈G →
      a*(∑ x∈S.filter (fun x => π x=i),w x) ≤
        ∑ x∈S.filter (fun x => π x=i),if x∈A then w x else 0) :
    a*(1-ε) ≤ (∑ x∈S,if x∈A then w x else 0)/(∑ x∈S,w x) := by
  classical
  let T := (S.image π).filter (·∈G)
  have hb : (∑ x∈S.filter (fun x => π x∈G),w x) +
      (∑ x∈S.filter (fun x => π x∉G),w x) = ∑ x∈S,w x := by
    exact sum_filter_add_sum_filter_not S (fun x => π x∈G) w
  have hf : S.filter (fun x => π x∈T)=S.filter (fun x => π x∈G) := by
    ext x
    simp only [mem_filter,T]
    constructor
    · rintro ⟨hx,hxT⟩;exact ⟨hx,hxT.2⟩
    · rintro ⟨hx,hxG⟩;exact ⟨hx,mem_image_of_mem π hx,hxG⟩
  have hsum : a*(∑ x∈S.filter (fun x => π x∈G),w x) ≤
      ∑ x∈S,if x∈A then w x else 0 := by
    calc
      _ = ∑ i∈T,a*(∑ x∈S.filter (fun x => π x=i),w x) := by
        rw [←mul_sum,sum_fiberwise_eq_sum_filter,hf]
      _ ≤ ∑ i∈T,∑ x∈S.filter (fun x => π x=i),if x∈A then w x else 0 :=
        sum_le_sum (fun i hi => hs i (mem_filter.mp hi).1 (mem_filter.mp hi).2)
      _ = ∑ x∈S.filter (fun x => π x∈G),if x∈A then w x else 0 := by
        rw [sum_fiberwise_eq_sum_filter,hf]
      _ ≤ ∑ x∈S,if x∈A then w x else 0 := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro x hx hnot
        split_ifs <;> simp_all
  apply (le_div_iff₀ hZ).mpr
  have hlo : (1-ε)*(∑ x∈S,w x) ≤ ∑ x∈S.filter (fun x => π x∈G),w x := by
    linarith
  have hh := mul_le_mul_of_nonneg_left hlo ha
  nlinarith

open RawHarmonicProbability MicrocellConditional

 

theorem raw_partition {ι : Type*} [DecidableEq ι]
    (X W : ℕ) (hW : 0<W) (hX : 4*W≤X) (π : ℕ→ι)
    (G : Set ι) (A : Set ℕ) (a ε : ℝ) (ha : 0≤a)
    (hbad : (law X W hW hX : Measure ℕ).real {p | π p∉G} ≤ ε)
    (hs : ∀ i∈(units X W).image π,i∈G →
      a ≤ (law X W hW hX : Measure ℕ).real
        (A∩((units X W).filter (fun p => π p=i):Set ℕ)) /
        (law X W hW hX : Measure ℕ).real
        ((units X W).filter (fun p => π p=i):Set ℕ)) :
    a*(1-ε) ≤ (law X W hW hX : Measure ℕ).real A := by
  have hZ := mass_pos X W hW hX
  rw [mass_units] at hZ
  rw [law_apply_units] at hbad ⊢
  rw [mass_units] at hbad ⊢
  apply finite_partition (units X W) (fun p => (p:ℝ)⁻¹)
    (fun p hp => by positivity) π G A a ε ha hZ
  · have hh := (div_le_iff₀ hZ).mp hbad
    have he : eventMass (units X W) {p | π p∉G} =
        ∑ p∈(units X W).filter (fun p=>π p∉G),(p:ℝ)⁻¹ := by
      unfold eventMass
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      split_ifs <;> simp_all
    rw [he] at hh
    exact hh
  · intro i hi hG
    have hcond := hs i hi hG
    rw [conditional_ratio X W hW hX _ (filter_subset _ _) A] at hcond
    have hCi : ((units X W).filter (fun p => π p=i)).Nonempty := by
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
      exact ⟨p,mem_filter.mpr ⟨hp,rfl⟩⟩
    have hCpos : 0 < ∑ p∈(units X W).filter (fun p => π p=i),(p:ℝ)⁻¹ := by
      apply sum_pos _ hCi
      intro p hp
      apply inv_pos.mpr
      exact units_pos (by omega) ⟨p,(mem_filter.mp hp).1⟩
    exact (le_div_iff₀ hCpos).mp hcond

end RawPartitionSuccess
end
end RawSuccessInlineScope15

 

 

section RawSuccessInlineScope16
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace MicrocellSaturation
open RawHarmonicProbability RawSmallCells RawPartitionSuccess MicrocellFibers
attribute [local instance] Classical.propDecidable

 

def good {J : Type*} (X R H : ℕ) (t : J→ℕ) (i : ℕ×ℕ) : Prop :=
  X≤R*i.1 ∧ R*(i.1+1)≤X^2 ∧
    ∀ j,t j*(R*i.1-R)/H=t j*(R*(i.1+1)+R)/H

def label (R M p : ℕ) : ℕ×ℕ := (p/R,p%M)

lemma quotient_window (R p : ℕ) (hR : 0<R) :
    R*(p/R)≤p ∧ p<R*(p/R+1) := by
  constructor
  · exact Nat.mul_div_le p R
  · exact Nat.lt_mul_div_succ p hR

 

lemma saturated {J : Type*} (X W R H M : ℕ) (t : J→ℕ) (hR : 0<R)
    (p : ℕ) (hp : p∈units X W)
    (hpartial : p∉partialCells X W R)
    (hstable : ∀ j,t j*(p-2*R)/H=t j*(p+2*R)/H) :
    good X R H t (label R M p) := by
  have hc : X≤R*(p/R) ∧ R*(p/R+1)≤X^2 := by
    simpa only [partialCells,mem_filter,hp,true_and,not_not] using hpartial
  refine ⟨hc.1,hc.2,?_⟩
  intro j
  have hw := quotient_window R p hR
  have hmul : R*(p/R+1) = R*(p/R)+R := by ring
  have hl : p-2*R≤R*(p/R)-R := by omega
  have hh : R*(p/R+1)+R≤p+2*R := by omega
  have hmid : R*(p/R)-R≤R*(p/R+1)+R := by omega
  have hl' := Nat.div_le_div_right (c:=H) (Nat.mul_le_mul_left (t j) hl)
  have hh' := Nat.div_le_div_right (c:=H) (Nat.mul_le_mul_left (t j) hh)
  have hm' := Nat.div_le_div_right (c:=H) (Nat.mul_le_mul_left (t j) hmid)
  have he := hstable j
  change t j*(R*(p/R)-R)/H=t j*(R*(p/R+1)+R)/H
  omega

lemma enlarged_cell_stable {J : Type*} {X R H : ℕ} {t : J→ℕ} {i : ℕ×ℕ}
    (hg : good X R H t i) (j : J) (z : ℕ)
    (hz : t j*(R*i.1-R)≤z ∧ z≤t j*(R*(i.1+1)+R)) :
    z/H=t j*(R*i.1)/H := by
  have he := hg.2.2 j
  have hlo := Nat.div_le_div_right (c:=H) hz.1
  have hhi := Nat.div_le_div_right (c:=H) hz.2
  have hl := Nat.div_le_div_right (c:=H)
    (Nat.mul_le_mul_left (t j) (Nat.sub_le (R*i.1) R))
  have hu := Nat.div_le_div_right (c:=H)
    (Nat.mul_le_mul_left (t j) (show R*i.1≤R*(i.1+1)+R by nlinarith))
  omega

lemma law_restrict_units (X W : ℕ) (hW : 0<W) (hX : 4*W≤X) (A : Set ℕ) :
    (law X W hW hX : Measure ℕ).real (A∩(units X W:Set ℕ)) =
      (law X W hW hX : Measure ℕ).real A := by
  rw [MicrocellConditional.law_apply_units,MicrocellConditional.law_apply_units]
  congr 1
  unfold MicrocellConditional.eventMass
  apply sum_congr rfl
  intro p hp
  simp [hp]

 

theorem bad_conditioning_bound {J : Type*} [Fintype J]
    (X W R H M : ℕ) (hW : 0<W) (hX : 4*W≤X) (hR : 0<R)
    (t : J→ℕ) (ε : ℝ)
    (hb : ∀ j,DyadicHarmonicBoundary.badMass X (X^2) W (t j) H (2*R) /
      DyadicHarmonicBoundary.mass X (X^2) W≤ε) :
    (law X W hW hX : Measure ℕ).real {p | ¬good X R H t (label R M p)} ≤
      8*((R:ℝ)+2*W)/X + Fintype.card J*ε := by
  rw [←law_restrict_units X W hW hX]
  have hsub : {p | ¬good X R H t (label R M p)}∩(units X W:Set ℕ) ⊆
      (partialCells X W R:Set ℕ) ∪ ⋃ j,{p | t j*(p-2*R)/H≠t j*(p+2*R)/H} := by
    intro p hp
    by_cases hc : p∈partialCells X W R
    · exact Or.inl hc
    · right
      by_contra hnot
      have hst : ∀ j,t j*(p-2*R)/H=t j*(p+2*R)/H := by
        simpa using hnot
      exact hp.1 (saturated X W R H M t hR p hp.2 hc hst)
  calc
    _ ≤ (law X W hW hX : Measure ℕ).real
        ((partialCells X W R:Set ℕ) ∪ ⋃ j,{p | t j*(p-2*R)/H≠t j*(p+2*R)/H}) :=
      measureReal_mono hsub
    _ ≤ (law X W hW hX : Measure ℕ).real (partialCells X W R:Set ℕ) +
        (law X W hW hX : Measure ℕ).real
          (⋃ j,{p | t j*(p-2*R)/H≠t j*(p+2*R)/H}) := measureReal_union_le _ _
    _ ≤ _ := add_le_add (partial_cost X W R hW hX hR)
      (finite_boundary_bound X W H (2*R) hW hX t ε hb)

 

lemma conditioned_fiber (X W M N q r : ℕ) (hM : 0<M) (hN : 0<N)
    (_ : r<M) (hWR : W.Coprime r) (hWM : W∣M)
    (hlo : X≤(M*N)*q) (hhi : (M*N)*(q+1)≤X^2) :
    (units X W).filter (fun p => label (M*N) M p=(q,r)) =
      fiber M N (N*q) r := by
  have hlo' : X≤M*(N*q) := by simpa only [mul_assoc] using hlo
  have hhi' : M*(N*q+N)≤X^2 := by nlinarith
  have hR : 0<M*N := Nat.mul_pos hM hN
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hlabel⟩ := mem_filter.mp hp
    have hq : p/(M*N)=q := congrArg Prod.fst hlabel
    have hr' : p%M=r := congrArg Prod.snd hlabel
    have hw := quotient_window (M*N) p hR
    rw [hq] at hw
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨?_,?_⟩,hr'⟩ <;> nlinarith
  · intro hp
    have hpU := fiber_subset_units X W M N (N*q) r hWM hWR hlo' hhi' hp
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
    obtain ⟨hpl,hph⟩ := mem_Ico.mp hpI
    apply mem_filter.mpr
    refine ⟨hpU,Prod.ext ?_ hpr⟩
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

lemma label_unit (X W M R : ℕ) (hM : 0<M) (hWM : W∣M) (i : ℕ×ℕ)
    (hi : i∈(units X W).image (label R M)) : i.2<M ∧ W.Coprime i.2 := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
  have hcop := (mem_filter.mp hp).2
  refine ⟨Nat.mod_lt p hM,?_⟩
  apply (UnitIntervalCounts.coprime_mod W (p%M)).mp
  rw [Nat.mod_mod_of_dvd p hWM]
  exact (UnitIntervalCounts.coprime_mod W p).mpr hcop

 

theorem global_success {J : Type*} [Fintype J]
    (X W M N H : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (hM : 0<M) (hN : 0<N) (hWM : W∣M) (t : J→ℕ)
    (c ε : ℝ) (hc : 0≤c) (A : Set ℕ)
    (herr : ((M*N:ℕ):ℝ)/X≤c/6)
    (hb : ∀ j,DyadicHarmonicBoundary.badMass X (X^2) W (t j) H (2*(M*N)) /
      DyadicHarmonicBoundary.mass X (X^2) W≤ε)
    (hs : ∀ i∈(units X W).image (label (M*N) M),good X (M*N) H t i →
      letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
      c/2<(MicrocellProbability.uniformLaw
        (fun b:Fin N => point M (N*i.1) i.2 b):Measure ℕ).real A) :
    (c/3)*(1-(8*((M*N:ℕ):ℝ)+16*W)/X-Fintype.card J*ε) ≤
      (law X W hW hX : Measure ℕ).real A := by
  have hbad := bad_conditioning_bound X W (M*N) H M hW hX (Nat.mul_pos hM hN) t ε hb
  have hp := raw_partition X W hW hX (label (M*N) M)
    {i | good X (M*N) H t i} A (c/3)
    (8*(((M*N:ℕ):ℝ)+2*W)/X+Fintype.card J*ε) (by positivity) hbad
  have hcond : ∀ i∈(units X W).image (label (M*N) M),good X (M*N) H t i →
      c/3 ≤ (law X W hW hX : Measure ℕ).real
        (A∩((units X W).filter (fun p => label (M*N) M p=i):Set ℕ)) /
        (law X W hW hX : Measure ℕ).real
        ((units X W).filter (fun p => label (M*N) M p=i):Set ℕ) := by
    intro i hi hg
    obtain ⟨hr,hWr⟩ := label_unit X W M (M*N) hM hWM i hi
    rw [show i=(i.1,i.2) from rfl,
      conditioned_fiber X W M N i.1 i.2 hM hN hr hWr hWM hg.1 hg.2.1]
    apply le_of_lt
    apply raw_fiber_success X W M N (N*i.1) i.2 hW hX hM hN hr hWr hWM
      (by simpa only [mul_assoc] using hg.1) (by nlinarith [hg.2.1]) c A herr
    exact hs i hi hg
  have hh := hp hcond
  convert hh using 1
  ring

end MicrocellSaturation

end
end RawSuccessInlineScope16
end

end OAI
