import OAI.Combinatorics.HoneycombChords.BoundarySystems
import OAI.Combinatorics.HoneycombChords.Bridges

namespace OAI

/-! Finite rectangle exhaustion of strict honeycomb bridges. -/

section

namespace CriticalHoneycomb
open scoped ENNReal


namespace StripExhaustion

def turn (h : ℕ) (m : ℤ) (v : Center) : Center :=
  ((h:ℤ)-1-v.2.1,m-v.1,!v.2.2)
lemma turn_injective (h : ℕ) (m : ℤ) : Function.Injective (turn h m) := by
  rintro ⟨x,y,b⟩ ⟨u,v,c⟩ he
  simp only [turn,Prod.mk.injEq] at he ⊢
  rcases he with ⟨h₁,h₂,h₃⟩
  have hb : b=c := by simpa using congrArg Bool.not h₃
  exact ⟨by omega,by omega,hb⟩
lemma turn_adj (h : ℕ) (m : ℤ) (v w : Center) :
    Adj (turn h m v) (turn h m w) ↔ Adj v w := by
  rcases v with ⟨x,y,b⟩
  rcases w with ⟨u,v,c⟩
  cases b <;> cases c <;> simp [turn,Adj] <;> omega
lemma adj_symm {v w : Center} (he : Adj v w) : Adj w v := by
  rcases v with ⟨x,y,b⟩
  rcases w with ⟨u,v,c⟩
  cases b <;> cases c <;> simp_all [Adj] <;> omega
lemma reverse_chain {p : List Center} (he : p.IsChain Adj) : p.reverse.IsChain Adj := by
  rw [List.isChain_reverse]
  exact he.imp (fun _ _ hh=>adj_symm hh)

noncomputable def reflected {h : ℕ} (m : ℤ) (γ : StrictBridge h) : List Center :=
  (γ.val.map (turn h m)).reverse
lemma reflected_injective {h : ℕ} (m : ℤ) :
    Function.Injective (reflected (h:=h) m) := by
  intro γ δ he
  apply Subtype.ext
  apply List.map_injective_iff.mpr (turn_injective h m)
  simpa [reflected] using congrArg List.reverse he
lemma reflected_length {h : ℕ} (m : ℤ) (γ : StrictBridge h) :
    (reflected m γ).length=γ.val.length := by simp [reflected]
lemma reflected_last {h : ℕ} (m : ℤ) (γ : StrictBridge h) :
    (reflected m γ).getLast?=some (down ((h:ℤ)-1) m) := by
  simp [reflected,List.head?_map,γ.property.2.1,turn,up,down]
noncomputable def terminal {h : ℕ} (γ : StrictBridge h) : ℤ := Classical.choose γ.property.2.2
lemma terminal_last {h : ℕ} (γ : StrictBridge h) :
    γ.val.getLast?=some (down (terminal γ) ((h:ℤ)-1)) := Classical.choose_spec γ.property.2.2
lemma reflected_head {h : ℕ} (m : ℤ) (γ : StrictBridge h) :
    (reflected m γ).head?=some (up 0 (m-terminal γ)) := by
  simp [reflected,List.getLast?_map,terminal_last,turn,up,down]

lemma finite_trace_bound {h : ℕ} (s : Finset (StrictBridge h)) :
    ∃ M : ℕ,∀ γ∈s,∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M := by
  classical
  let t : Finset ℕ := s.biUnion (fun γ=>γ.val.toFinset.image (fun v=>v.1.natAbs))
  refine ⟨t.sup id,?_⟩
  intro γ hγ v hv
  have ht : v.1.natAbs∈t := by
    apply Finset.mem_biUnion.mpr
    refine ⟨γ,hγ,?_⟩
    exact Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩
  have hh : v.1.natAbs≤t.sup id := Finset.le_sup (f:=id) ht
  have ha : -(v.1.natAbs:ℤ)≤v.1 ∧ v.1≤(v.1.natAbs:ℤ) :=
    by simpa only [Int.natCast_natAbs] using (abs_le.mp (le_refl |v.1|))
  omega

lemma reflected_trace {h M : ℕ} (γ : StrictBridge h)
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) :
    IsTrace {v : Center | 0≤v.1 ∧ v.1<h ∧ 0≤v.2.1 ∧ v.2.1<2*(M:ℤ)+1}
      (reflected M γ) := by
  obtain ⟨hn,hc,hp⟩ := γ.property.1
  refine ⟨?_,?_,?_⟩
  · simpa [reflected] using hn.map (turn_injective h M)
  · apply reverse_chain
    exact List.isChain_map_of_isChain _ (fun _ _ hh=>(turn_adj h M _ _).mpr hh) hc
  · intro v hv
    rw [reflected,List.mem_reverse,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    have hur := hp u hu
    have hub := hb u hu
    simp only [strip,Set.mem_ofPred_eq] at hur
    simp only [turn,Set.mem_ofPred_eq]
    omega

lemma terminal_bound {h M : ℕ} (γ : StrictBridge h)
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) :
    -(M:ℤ)≤terminal γ ∧ terminal γ≤M := by
  have hm : down (terminal γ) ((h:ℤ)-1) ∈ γ.val :=
    List.mem_of_getLast? (terminal_last γ)
  exact hb _ hm
end StripExhaustion
end CriticalHoneycomb

namespace CriticalHoneycomb.StripExhaustion
open CriticalHoneycomb.Transfer

noncomputable def exitIndex {h M : ℕ} (γ : StrictBridge (h+1))
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) : Fin (2*M+1) :=
  ⟨((M:ℤ)-terminal γ).toNat,by have hh:=terminal_bound γ hb;omega⟩
lemma exitIndex_value {h M : ℕ} (γ : StrictBridge (h+1))
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) :
    ((exitIndex γ hb).val:ℤ)=(M:ℤ)-terminal γ := by
  apply Int.toNat_of_nonneg
  have hh:=terminal_bound γ hb
  omega

noncomputable def reflectedChord {h M : ℕ} (γ : StrictBridge (h+1))
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) :
    RasterGrid.RectChord h (2*M) (exitIndex γ hb) ⟨M,by omega⟩ := by
  refine ⟨reflected M γ,?_,?_,?_⟩
  · obtain ⟨hn,hc,hp⟩ := reflected_trace γ hb
    refine ⟨hn,hc,?_⟩
    intro v hv
    apply (RasterGrid.mem_domain_iff v).mpr
    have hh := hp v hv
    simpa only [Set.mem_ofPred_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hh
  · rw [reflected_head]
    simp only [RasterGrid.westPort,RasterGrid.cellCenter,up,Fin.val_zero,Int.natCast_zero]
    rw [exitIndex_value]
  · rw [reflected_last]
    simp [RasterGrid.eastPort,RasterGrid.cellCenter,down]

theorem strip_finite_sum_le (h : ℕ) (s : Finset (StrictBridge (h+1))) :
    (∑ γ∈s,kappa^γ.val.length)≤1 := by
  classical
  obtain ⟨M,hM⟩ := finite_trace_bound s
  let B := Σ j : Fin (2*M+1),RasterGrid.RectChord h (2*M) j ⟨M,by omega⟩
  let f : {γ // γ∈s} → B := fun γ =>
    ⟨exitIndex γ.val (hM γ.val γ.property),reflectedChord γ.val (hM γ.val γ.property)⟩
  have hi : Function.Injective f := by
    intro γ δ he
    have hh : reflected M γ.val=reflected M δ.val :=
      congrArg (fun p : B=>p.2.val) he
    exact Subtype.ext (reflected_injective M hh)
  have hb : (∑ p : B,kappa^p.2.val.length)≤1 := by
    rw [Fintype.sum_sigma]
    exact FluxWard.rectangle_actual_sum_bound h (2*M) ⟨M,by omega⟩
  calc
    (∑ γ∈s,kappa^γ.val.length) = ∑ γ : {γ // γ∈s},kappa^(f γ).2.val.length := by
      simp only [f,reflectedChord,reflected_length]
      exact Finset.sum_subtype s (fun _=>Iff.rfl) _
    _ = ∑ p∈Finset.univ.image f,kappa^p.2.val.length := (Finset.sum_image (f:=fun p : B=>kappa^p.2.val.length) (s:=Finset.univ) hi.injOn).symm
    _ ≤ ∑ p : B,kappa^p.2.val.length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hn
      exact (pow_pos FiniteContinuation.kappa_positive _).le
    _ ≤ 1 := hb

lemma real_strip_summable (h : ℕ) :
    Summable (fun γ : StrictBridge (h+1)=>kappa^γ.val.length) := by
  apply summable_of_sum_le (c:=1)
  · intro γ
    exact (pow_pos FiniteContinuation.kappa_positive _).le
  · exact strip_finite_sum_le h

lemma real_strip_tsum_le (h : ℕ) :
    (∑' γ : StrictBridge (h+1),kappa^γ.val.length)≤1 := by
  apply Real.tsum_le_of_sum_le
  · intro γ
    exact (pow_pos FiniteContinuation.kappa_positive _).le
  · exact strip_finite_sum_le h

end CriticalHoneycomb.StripExhaustion
namespace CriticalHoneycomb.StripExhaustion
open scoped ENNReal

theorem bridgeMass_le_one (h : ℕ) : bridgeMass h≤1 := by
  cases h with
  | zero => simp [bridgeMass]
  | succ h =>
    simp only [bridgeMass,Nat.add_one_ne_zero,ite_false,weight]
    rw [←ENNReal.ofReal_tsum_of_nonneg]
    · exact (ENNReal.ofReal_le_ofReal (real_strip_tsum_le h)).trans (by simp)
    · intro γ
      exact (pow_pos FiniteContinuation.kappa_positive _).le
    · exact real_strip_summable h

theorem bridgeMass_finite (h : ℕ) : bridgeMass h<⊤ :=
  (bridgeMass_le_one h).trans_lt (by simp)
end CriticalHoneycomb.StripExhaustion

end

section

namespace CriticalHoneycomb.StripExhaustion
open Filter Topology
open CriticalHoneycomb.Transfer

def ConfinedAt {W : ℕ} (H k : ℕ) (γ : StrictBridge (W+1)) : Prop :=
  ∀ v∈γ.val,(k:ℤ)-(H:ℤ)≤v.1 ∧ v.1≤k

noncomputable instance confinedAtDecidable {W : ℕ} (H k : ℕ) (γ : StrictBridge (W+1)) :
    Decidable (ConfinedAt H k γ) := Classical.propDecidable _

noncomputable def placements {W : ℕ} (H : ℕ) (γ : StrictBridge (W+1)) : ℝ := by
  classical
  exact ∑ k : Fin (H+1),if ConfinedAt H k.val γ then (1:ℝ) else 0

noncomputable def placementFraction {W : ℕ} (H : ℕ) (γ : StrictBridge (W+1)) : ℝ :=
  placements H γ/(H+1:ℕ)

lemma placements_nonnegative {W H : ℕ} (γ : StrictBridge (W+1)) : 0≤placements H γ := by
  classical
  apply Finset.sum_nonneg
  intro k hk
  split_ifs <;> norm_num
lemma placements_le {W H : ℕ} (γ : StrictBridge (W+1)) : placements H γ≤(H+1:ℕ) := by
  classical
  calc
    placements H γ ≤ ∑ k : Fin (H+1),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> norm_num
    _ = (H+1:ℕ) := by simp
lemma placementFraction_nonnegative {W H : ℕ} (γ : StrictBridge (W+1)) :
    0≤placementFraction H γ := div_nonneg (placements_nonnegative γ) (by positivity)
lemma placementFraction_le_one {W H : ℕ} (γ : StrictBridge (W+1)) :
    placementFraction H γ≤1 := by
  apply (div_le_one (by positivity : (0:ℝ)<(H+1:ℕ))).mpr
  exact placements_le γ

def interiorPlacement (H M : ℕ) (k : Fin (H+1-2*M)) : Fin (H+1) :=
  ⟨k.val+M,by have hk:=k.isLt;omega⟩
lemma interiorPlacement_injective (H M : ℕ) : Function.Injective (interiorPlacement H M) := by
  intro k l he
  apply Fin.ext
  have hh:=congrArg Fin.val he
  simp only [interiorPlacement] at hh
  omega
lemma interior_confined {W H M : ℕ} (γ : StrictBridge (W+1))
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) (k : Fin (H+1-2*M)) :
    ConfinedAt H (interiorPlacement H M k).val γ := by
  intro v hv
  have hh:=hb v hv
  have hk:=k.isLt
  simp only [interiorPlacement]
  omega

lemma placements_lower {W H M : ℕ} (γ : StrictBridge (W+1))
    (hb : ∀ v∈γ.val,-(M:ℤ)≤v.1 ∧ v.1≤M) :
    ((H+1-2*M:ℕ):ℝ)≤placements H γ := by
  classical
  let f := interiorPlacement H M
  let g : Fin (H+1)→ℝ := fun k=>if ConfinedAt H k.val γ then 1 else 0
  calc
    ((H+1-2*M:ℕ):ℝ) = ∑ k : Fin (H+1-2*M),g (f k) := by
      simp only [g,f,interior_confined γ hb,ite_eq_left]
      simp
    _ = ∑ k∈Finset.univ.image f,g k :=
      (Finset.sum_image (f:=g) (s:=Finset.univ) (interiorPlacement_injective H M).injOn).symm
    _ ≤ ∑ k : Fin (H+1),g k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k hk hn
      simp only [g]
      split_ifs <;> positivity
    _ = placements H γ := rfl

lemma central_fraction_limit (M : ℕ) :
    Tendsto (fun H : ℕ=>((H+1-2*M:ℕ):ℝ)/(H+1:ℕ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun H : ℕ=>((H+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (ht.const_div_atTop (2*(M:ℝ)))
  have he : (fun H : ℕ=>((H+1-2*M:ℕ):ℝ)/(H+1:ℕ)) =ᶠ[atTop]
      (fun H : ℕ=>(1:ℝ)-2*(M:ℝ)/(H+1:ℕ)) := by
    filter_upwards [eventually_ge_atTop (2*M)] with H hH
    rw [Nat.cast_sub (by omega : 2*M≤H+1)]
    push_cast
    field_simp
  apply (show Tendsto (fun H : ℕ=>(1:ℝ)-2*(M:ℝ)/(H+1:ℕ)) atTop (𝓝 1) from by
    simpa using hh).congr' he.symm

lemma placementFraction_limit {W : ℕ} (γ : StrictBridge (W+1)) :
    Tendsto (fun H : ℕ=>placementFraction H γ) atTop (𝓝 1) := by
  classical
  obtain ⟨M,hM⟩ := finite_trace_bound ({γ} : Finset (StrictBridge (W+1)))
  have hb:=hM γ (by simp)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (central_fraction_limit M) tendsto_const_nhds
  · intro H
    exact div_le_div_of_nonneg_right (placements_lower γ hb) (by positivity)
  · intro H
    exact placementFraction_le_one γ

noncomputable def averagingMass (W H : ℕ) : ℝ :=
  ∑' γ : StrictBridge (W+1),placementFraction H γ*kappa^γ.val.length

theorem averagingMass_limit (W : ℕ) :
    Tendsto (averagingMass W) atTop
      (𝓝 (∑' γ : StrictBridge (W+1),kappa^γ.val.length)) := by
  apply tendsto_tsum_of_dominated_convergence (real_strip_summable W)
  · intro γ
    simpa using (placementFraction_limit γ).mul_const (kappa^γ.val.length)
  · apply Eventually.of_forall
    intro H γ
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (placementFraction_nonnegative γ)
      (pow_pos FiniteContinuation.kappa_positive _).le)]
    exact mul_le_of_le_one_left (pow_pos FiniteContinuation.kappa_positive _).le
      (placementFraction_le_one γ)
end CriticalHoneycomb.StripExhaustion

namespace CriticalHoneycomb.StripExhaustion
open CriticalHoneycomb.Transfer

abbrev RectAllAt (W H : ℕ) (k : Fin (H+1)) :=
  Σ j : Fin (H+1),RasterGrid.RectChord W H j k

noncomputable def unplace {W H : ℕ} {k : Fin (H+1)} (γ : RectAllAt W H k) :
    StrictBridge (W+1) := by
  refine ⟨(γ.2.val.map (turn (k.val+1) W)).reverse,⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [List.nodup_reverse] using γ.2.property.1.1.map (turn_injective (k.val+1) W)
  · apply reverse_chain
    exact List.isChain_map_of_isChain _ (fun _ _ hh=>(turn_adj (k.val+1) W _ _).mpr hh)
      γ.2.property.1.2.1
  · intro v hv
    rw [List.mem_reverse,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    have hh := (RasterGrid.mem_domain_iff u).mp (γ.2.property.1.2.2 u hu)
    simp only [strip,Set.mem_ofPred_eq,turn]
    omega
  · simp only [List.head?_reverse,List.getLast?_map,γ.2.property.2.2,Option.map_some]
    simp [RasterGrid.eastPort,RasterGrid.cellCenter,turn,up]
  · refine ⟨(k.val:ℤ)-γ.1.val,?_⟩
    simp only [List.getLast?_reverse,List.head?_map,γ.2.property.2.1,Option.map_some]
    simp [RasterGrid.westPort,RasterGrid.cellCenter,turn,down]

lemma unplace_length {W H : ℕ} {k : Fin (H+1)} (γ : RectAllAt W H k) :
    (unplace γ).val.length=γ.2.val.length := by simp [unplace]
lemma unplace_confined {W H : ℕ} {k : Fin (H+1)} (γ : RectAllAt W H k) :
    ConfinedAt H k.val (unplace γ) := by
  intro v hv
  simp only [unplace,List.mem_reverse,List.mem_map] at hv
  obtain ⟨u,hu,rfl⟩ := hv
  have hh := (RasterGrid.mem_domain_iff u).mp (γ.2.property.1.2.2 u hu)
  simp only [turn]
  omega

lemma terminal_confined {W H k : ℕ} (γ : StrictBridge (W+1)) (hb : ConfinedAt H k γ) :
    (k:ℤ)-(H:ℤ)≤terminal γ ∧ terminal γ≤k := by
  have hh:=hb _ (List.mem_of_getLast? (terminal_last γ))
  exact hh

noncomputable def exitAt {W H : ℕ} (k : Fin (H+1)) (γ : StrictBridge (W+1))
    (hb : ConfinedAt H k.val γ) : Fin (H+1) :=
  ⟨((k.val:ℤ)-terminal γ).toNat,by have hh:=terminal_confined γ hb;omega⟩
lemma exitAt_value {W H : ℕ} (k : Fin (H+1)) (γ : StrictBridge (W+1))
    (hb : ConfinedAt H k.val γ) : ((exitAt k γ hb).val:ℤ)=(k.val:ℤ)-terminal γ := by
  apply Int.toNat_of_nonneg
  have hh:=terminal_confined γ hb
  omega

noncomputable def place {W H : ℕ} (k : Fin (H+1)) (γ : StrictBridge (W+1))
    (hb : ConfinedAt H k.val γ) : RectAllAt W H k := by
  refine ⟨exitAt k γ hb,reflected k.val γ,⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [reflected,List.nodup_reverse] using γ.property.1.1.map (turn_injective (W+1) k.val)
  · apply reverse_chain
    exact List.isChain_map_of_isChain _ (fun _ _ hh=>(turn_adj (W+1) k.val _ _).mpr hh)
      γ.property.1.2.1
  · intro v hv
    rw [reflected,List.mem_reverse,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    have hh:=γ.property.1.2.2 u hu
    have hbu:=hb u hu
    apply (RasterGrid.mem_domain_iff _).mpr
    simp only [strip,Set.mem_ofPred_eq] at hh
    simp only [turn]
    omega
  · rw [reflected_head]
    simp only [RasterGrid.westPort,RasterGrid.cellCenter,up,Fin.val_zero,Int.natCast_zero]
    rw [exitAt_value]
  · rw [reflected_last]
    simp [RasterGrid.eastPort,RasterGrid.cellCenter,down]

lemma turn_turn (W k : ℕ) (v : Center) : turn (k+1) W (turn (W+1) k v)=v := by
  rcases v with ⟨x,y,b⟩
  simp [turn]

lemma unplace_place {W H : ℕ} (k : Fin (H+1)) (γ : StrictBridge (W+1))
    (hb : ConfinedAt H k.val γ) : unplace (place k γ hb)=γ := by
  apply Subtype.ext
  simp only [unplace,place,reflected,List.map_reverse,List.reverse_reverse,List.map_map]
  have he : (fun v=>turn (k.val+1) W (turn (W+1) k.val v))=id :=
    funext (turn_turn W k.val)
  change List.map _ _ = _
  simp only [show (turn (k.val+1) W ∘ turn (W+1) k.val) = id from he,List.map_id]

lemma rectAll_ext {W H : ℕ} {k : Fin (H+1)} (γ δ : RectAllAt W H k)
    (he : γ.2.val=δ.2.val) : γ=δ := by
  rcases γ with ⟨j,γ⟩;rcases δ with ⟨l,δ⟩
  have hh:=congrArg List.head? he
  rw [γ.property.2.1,δ.property.2.1] at hh
  have hj : j=l := by
    apply Fin.ext
    have hl:=congrArg (fun x : Option Center=>x.map (fun v=>v.2.1)) hh
    simpa [RasterGrid.westPort,RasterGrid.cellCenter,up] using hl
  subst l
  have hγ : γ=δ := Subtype.ext he
  subst δ
  rfl

lemma place_unplace {W H : ℕ} (k : Fin (H+1)) (γ : RectAllAt W H k) :
    place k (unplace γ) (unplace_confined γ)=γ := by
  apply rectAll_ext
  simp only [place,reflected,unplace,List.map_reverse,List.reverse_reverse,List.map_map]
  have he : (fun v=>turn (W+1) k.val (turn (k.val+1) W v))=id :=
    funext (turn_turn k.val W)
  simp only [show (turn (W+1) k.val ∘ turn (k.val+1) W) = id from he,List.map_id]

noncomputable def placementEquiv (W H : ℕ) (k : Fin (H+1)) :
    RectAllAt W H k ≃ {γ : StrictBridge (W+1)//ConfinedAt H k.val γ} where
  toFun γ := ⟨unplace γ,unplace_confined γ⟩
  invFun γ := place k γ.val γ.property
  left_inv γ := place_unplace k γ
  right_inv γ := by apply Subtype.ext;exact unplace_place k γ.val γ.property
end CriticalHoneycomb.StripExhaustion

namespace CriticalHoneycomb.StripExhaustion
open Filter Topology CriticalHoneycomb.Transfer

lemma rectangle_one_source (W H : ℕ) (k : Fin (H+1)) :
    (∑ j : Fin (H+1), ∑ γ : RasterGrid.RectChord W H j k,kappa^γ.val.length) =
    ∑' γ : StrictBridge (W+1),if ConfinedAt H k.val γ then kappa^γ.val.length else 0 := by
  classical
  have he := (placementEquiv W H k).tsum_eq
    (fun γ : {γ : StrictBridge (W+1)//ConfinedAt H k.val γ}=>kappa^γ.val.val.length)
  have hl (γ : RectAllAt W H k) : ((placementEquiv W H k γ).val.val).length =
      γ.2.val.length := unplace_length γ
  simp only [hl] at he
  rw [tsum_fintype,Fintype.sum_sigma] at he
  rw [he]
  exact tsum_subtype {γ : StrictBridge (W+1) | ConfinedAt H k.val γ}
    (fun γ : StrictBridge (W+1)=>kappa^γ.val.length)

lemma confined_summable (W H : ℕ) (k : Fin (H+1)) :
    Summable (fun γ : StrictBridge (W+1)=>
      if ConfinedAt H k.val γ then kappa^γ.val.length else 0) := by
  classical
  exact (real_strip_summable W).indicator {γ | ConfinedAt H k.val γ}

lemma rectangle_average_eq (W H : ℕ) :
    (∑ k : Fin (H+1), ∑ j : Fin (H+1),
      ∑ γ : RasterGrid.RectChord W H j k,kappa^γ.val.length)/(H+1:ℕ) =
      averagingMass W H := by
  classical
  have he : ∀ γ : StrictBridge (W+1),
      placementFraction H γ*kappa^γ.val.length =
      (∑ k : Fin (H+1),if ConfinedAt H k.val γ then kappa^γ.val.length else 0)/(H+1:ℕ) := by
    intro γ
    rw [placementFraction,placements,div_mul_eq_mul_div,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  simp only [rectangle_one_source,averagingMass,he]
  rw [tsum_div_const,(Summable.tsum_finsetSum (fun k _=>confined_summable W H k))]

theorem physical_rectangle_average_limit (W : ℕ) :
    Tendsto (fun H : ℕ=>
      (∑ k : Fin (H+1), ∑ j : Fin (H+1),
        (RasterGrid.prescribedPartition (W+1) (H+1)
          (RasterGrid.singleColumn j) (RasterGrid.singleColumn k) (fun _=>1) (fun _=>1)).re)
        /(H+1:ℕ)) atTop
      (𝓝 (∑' γ : StrictBridge (W+1),kappa^γ.val.length)) := by
  have he : ∀ H : ℕ, (∑ k : Fin (H+1), ∑ j : Fin (H+1),
        (RasterGrid.prescribedPartition (W+1) (H+1)
          (RasterGrid.singleColumn j) (RasterGrid.singleColumn k) (fun _=>1) (fun _=>1)).re)
        /(H+1:ℕ) = averagingMass W H := by
    intro H
    simp only [RasterGrid.actual_chord_sum_eq_transfer,Complex.re_sum,
      ←Complex.ofReal_pow,Complex.ofReal_re]
    exact rectangle_average_eq W H
  simpa only [he] using averagingMass_limit W
end CriticalHoneycomb.StripExhaustion

end

end OAI
