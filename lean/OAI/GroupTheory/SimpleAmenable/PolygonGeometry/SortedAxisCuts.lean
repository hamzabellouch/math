import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisCutSequences

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SortedAxisCuts
attribute [local instance] cutOrdinaryOrder

noncomputable def sortedAxisCutSequence (n k N : ℕ) (p : ℤ) (u v : CutRing)
    (S : Finset CutRing) (hu : u ∈ S) (hv : v ∈ S)
    (hbound : ∀ z ∈ S, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlabels : ∀ z ∈ S, p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hoveru : p+(N:ℤ)-k ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hoverv : p+(N:ℤ)-k ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (_hkN : k ≤ N) (_hNk : N ≤ 2*k) (hkn : k ≤ n*9/10) : AxisCutSequence n (S.card-1) := by
  classical
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨u,hu⟩
  have hcard : S.card = S.card-1+1 := by omega
  let f : Fin (S.card-1+1) ↪o CutRing := S.orderEmbOfFin hcard
  have hmem (i) : f i ∈ S := Finset.orderEmbOfFin_mem S hcard i
  have hsurj : ∀ z ∈ S, ∃ i, f i=z := by
    intro z hz
    have hh : z ∈ Set.range f := by
      change z ∈ Set.range (S.orderEmbOfFin hcard)
      rw [Finset.range_orderEmbOfFin]
      exact hz
    exact hh
  have hzero : f 0=u := by
    obtain ⟨i,hi⟩ := hsurj u hu
    apply ordinary_injective
    apply le_antisymm
    · have hh := f.monotone (Fin.zero_le i)
      change ordinary (f 0) ≤ ordinary (f i) at hh
      simpa only [hi] using hh
    · exact (hbound _ (hmem 0)).1
  have hlast : f (Fin.last (S.card-1))=v := by
    obtain ⟨i,hi⟩ := hsurj v hv
    apply ordinary_injective
    apply le_antisymm
    · exact (hbound _ (hmem _)).2
    · have hh := f.monotone (Fin.le_last i)
      change ordinary (f i) ≤ ordinary (f (Fin.last (S.card-1))) at hh
      simpa only [hi] using hh
  refine {
    cut := f
    strictMono := f.strictMono
    length := fun _ => k
    start := fun i => if endpointLabel (f i) < p+k then p else p+(N:ℤ)-k
    length_le := fun _ => hkn
    lower_label := ?_
    upper_label := ?_
    cut_label := ?_ }
  · intro i
    rw [hzero]
    split_ifs <;> have hh := hlabels u hu <;> constructor <;> omega
  · intro i
    rw [hlast]
    split_ifs <;> have hh := hlabels v hv <;> constructor <;> omega
  · intro i
    have hh := hlabels (f i) (hmem i)
    split_ifs <;> constructor <;> omega

noncomputable def labelLift (u : CutRing) (q : ℤ) : CutRing :=
  u+cutFraction ((q:CutRing)*cutTau-u)

@[simp] theorem endpointLabel_labelLift (u : CutRing) (q : ℤ) : endpointLabel (labelLift u q)=q := by
  simp [labelLift,endpointLabel_add,endpointLabel_sub]

theorem labelLift_bounds (u : CutRing) (q : ℤ) :
    ordinary u ≤ ordinary (labelLift u q) ∧ ordinary (labelLift u q) < ordinary u+1 := by
  simp only [labelLift,map_add,ordinary_cutFraction]
  have hh := Int.fract_nonneg (ordinary ((q:CutRing)*cutTau-u))
  have hh' := Int.fract_lt_one (ordinary ((q:CutRing)*cutTau-u))
  constructor <;> linarith

theorem labelLift_eq (u z : CutRing) (hz : ordinary u ≤ ordinary z ∧ ordinary z < ordinary u+1) :
    labelLift u (endpointLabel z)=z := by
  have hc : cutFraction (((endpointLabel z:CutRing)*cutTau)-u) = cutFraction (z-u) := by
    rw [cutFraction_label (((endpointLabel z:CutRing)*cutTau)-u),cutFraction_label (z-u)]
    simp only [endpointLabel_sub,endpointLabel_labelTau]
  rw [labelLift,hc,cutFraction_eq_self (z-u) (by simp only [map_sub]; constructor <;> linarith)]
  ring

noncomputable def anchorCutSet (N : ℕ) (p : ℤ) (u v : CutRing) : Finset CutRing := by
  classical
  exact insert u (insert v ((Finset.univ.image fun i : Fin N => labelLift u (p+(i.val:ℤ))).filter
    fun z => ordinary z ≤ ordinary v))

theorem anchorCutSet_lower (N : ℕ) (p : ℤ) (u v : CutRing) : u ∈ anchorCutSet N p u v := by
  classical
  simp only [anchorCutSet,Finset.mem_insert_self]

theorem anchorCutSet_upper (N : ℕ) (p : ℤ) (u v : CutRing) : v ∈ anchorCutSet N p u v := by
  classical
  simp [anchorCutSet]

theorem anchorCutSet_bounds (N : ℕ) (p : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v) :
    ∀ z ∈ anchorCutSet N p u v, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v := by
  classical
  intro z hz
  simp only [anchorCutSet,Finset.mem_insert,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with rfl | rfl | ⟨⟨i,rfl⟩,hz⟩
  · exact ⟨le_rfl,huv⟩
  · exact ⟨huv,le_rfl⟩
  · exact ⟨(labelLift_bounds u _).1,hz⟩

theorem anchorCutSet_labels (N : ℕ) (p : ℤ) (u v : CutRing)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+N)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+N) :
    ∀ z ∈ anchorCutSet N p u v, p ≤ endpointLabel z ∧ endpointLabel z < p+N := by
  classical
  intro z hz
  simp only [anchorCutSet,Finset.mem_insert,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and] at hz
  rcases hz with rfl | rfl | ⟨⟨i,rfl⟩,_⟩
  · exact hu
  · exact hv
  · rw [endpointLabel_labelLift]; constructor <;> omega

theorem mem_anchorCutSet (N : ℕ) (p : ℤ) (u v z : CutRing)
    (hl : p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hz : ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlen : ordinary v-ordinary u < 1) : z ∈ anchorCutSet N p u v := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨?_,hz.2⟩
  have hn : (endpointLabel z-p).toNat < N := by omega
  apply Finset.mem_image.mpr
  refine ⟨⟨(endpointLabel z-p).toNat,hn⟩,Finset.mem_univ _,?_⟩
  have hh : p+(((endpointLabel z-p).toNat:ℕ):ℤ) = endpointLabel z := by omega
  rw [hh]
  exact labelLift_eq u z ⟨hz.1,by linarith⟩

end SortedAxisCuts

section SortedAxisCutSpecs
attribute [local instance] cutOrdinaryOrder
variable (n k N : ℕ) (p : ℤ) (u v : CutRing)
    (S : Finset CutRing) (hu : u ∈ S) (hv : v ∈ S)
    (hbound : ∀ z ∈ S, ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlabels : ∀ z ∈ S, p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hoveru : p+(N:ℤ)-k ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hoverv : p+(N:ℤ)-k ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hkN : k ≤ N) (hNk : N ≤ 2*k) (hkn : k ≤ n*9/10)
local notation "D" => sortedAxisCutSequence n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn

theorem sortedAxisCutSequence_mem (i) : (D).cut i ∈ S := by
  exact Finset.orderEmbOfFin_mem S _ i

theorem sortedAxisCutSequence_range : Set.range (D).cut = (S : Set CutRing) := by
  exact Finset.range_orderEmbOfFin S _

theorem sortedAxisCutSequence_lower : (D).cut 0=u := by
  have hh : u ∈ Set.range (D).cut := by
    rw [sortedAxisCutSequence_range]
    exact hu
  obtain ⟨i,hi⟩ := hh
  apply ordinary_injective
  apply le_antisymm
  · have hh := ((D).ordered i).1
    simpa only [hi] using hh
  · exact (hbound _ (sortedAxisCutSequence_mem n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn 0)).1

theorem sortedAxisCutSequence_upper : (D).cut (Fin.last (S.card-1))=v := by
  have hh : v ∈ Set.range (D).cut := by
    rw [sortedAxisCutSequence_range]
    exact hv
  obtain ⟨i,hi⟩ := hh
  apply ordinary_injective
  apply le_antisymm
  · exact (hbound _ (sortedAxisCutSequence_mem n k N p u v S hu hv hbound hlabels hoveru hoverv hkN hNk hkn _)).2
  · have hh := ((D).ordered i).2
    simpa only [hi] using hh

theorem sortedAxisCutSequence_length (i) : (D).length i=k := rfl

theorem sortedAxisCutSequence_start (i) : (D).start i =
    if endpointLabel ((D).cut i)<p+k then p else p+(N:ℤ)-k := rfl

end SortedAxisCutSpecs

end SimpleAmenable
end
end

end OAI
