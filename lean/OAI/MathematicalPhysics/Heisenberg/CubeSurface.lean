import OAI.MathematicalPhysics.Heisenberg.PhysicalSurface

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
open SpatialFrame
variable {d ℓ : ℕ}

lemma bad_slots_le (Λ F : Finset (Site d)) :
    (Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card≤(Λ\F).card*ℓ := by
  let f : {v : Slots (B:=Fin ℓ) Λ // v.1.val∉F} → ↥(Λ\F) × Fin ℓ:=
    fun v=>(⟨v.val.1,Finset.mem_sdiff.mpr ⟨v.val.1.property,v.property⟩⟩,v.val.2)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; exact congrArg (fun v : ↥(Λ\F) × Fin ℓ=>v.1.val) h
    · exact congrArg (fun v : ↥(Λ\F) × Fin ℓ=>v.2) h
  have hc:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using hc

lemma bad_edges_le (Λ F : Finset (Site d)) :
    (Finset.univ.filter (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>
      e.val.1.1.val∉F ∨ e.val.2.1.val∉F)).card≤(4*d)*(Λ\F).card*ℓ^2 := by
  let E:={e : Edges (B:=Fin ℓ) Geometry.Step Λ // e.val.1.1.val∉F ∨ e.val.2.1.val∉F}
  let f : E → (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ):=fun e=>
    (⟨(e.val.val.1.1.val,e.val.val.2.1.val),mem_incidentEdges (nearestNeighbor_iff_step.mpr e.val.property)
      (e.property.imp (fun h=>Finset.mem_sdiff.mpr ⟨e.val.val.1.1.property,h⟩)
        (fun h=>Finset.mem_sdiff.mpr ⟨e.val.val.2.1.property,h⟩))⟩,(e.val.val.1.2,e.val.val.2.2))
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext; exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.1.val.1) h
      · exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.2.1) h
    · apply Prod.ext
      · apply Subtype.ext; exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.1.val.2) h
      · exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.2.2) h
  have hc:=Fintype.card_le_of_injective f hf
  simp only [E,Fintype.card_subtype,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at hc
  exact hc.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (ℓ*ℓ) (card_incidentEdges_le (Λ\F)))

lemma schedule_bad_eq {q : ℕ} (Λ F : Finset (Site d))
    (edge : Fin q ≃ Edges (B:=Fin ℓ) Geometry.Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
    (ha : ∀ j : Fin q,a₀ j=(edge j).val.1) (hb : ∀ j : Fin q,b₀ j=(edge j).val.2) :
    ((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card=
      (Finset.univ.filter (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>e.val.1.1.val∉F ∨ e.val.2.1.val∉F)).card := by
  have hsum := edge.sum_comp (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>if e.val.1.1.val∉F ∨ e.val.2.1.val∉F then (1:ℕ) else 0)
  rw [Finset.card_filter,Finset.card_filter,←Fin.sum_univ_eq_sum_range]
  simpa only [ha,hb] using hsum

lemma box_card (d n : ℕ) : (box d n).card=(2*n+1)^d := Geometry.card_boxFinset d n
lemma box_mem (d n : ℕ) (x : Site d) : x∈box d n ↔ ∀ j,|x j|≤(n:ℤ) := Geometry.mem_boxFinset d n x
lemma box_mono {n m : ℕ} (hnm : n≤ m) : box d n⊆box d m := by
  intro x hx
  apply (box_mem d m x).mpr
  intro j
  exact (box_mem d n x |>.mp hx j).trans (by exact_mod_cast hnm)
lemma box_nonempty (d n : ℕ) : (box d n).Nonempty:=⟨0,(box_mem d n 0).mpr (by intro j; simp)⟩

lemma box_neighbor {n : ℕ} {x y : Site d} (hx : x∈box d n) (h : Geometry.Step x y) : y∈box d (n+1) := by
  obtain ⟨i,hi,hj⟩:=h
  apply (box_mem _ _ _).mpr
  intro j
  have hxj:=(box_mem d n x).mp hx j
  by_cases hji : j=i
  · subst j
    rcases hi with hi | hi
    · rw [hi]
      exact (abs_add_le _ _).trans (by simpa only [abs_one,Nat.cast_add,Nat.cast_one,add_le_add_iff_right] using hxj)
    · rw [show y i=x i-1 by omega]
      exact (abs_sub _ _).trans (by simpa only [abs_one,Nat.cast_add,Nat.cast_one,add_le_add_iff_right] using hxj)
  · rw [hj j hji]
    exact hxj.trans (by exact_mod_cast Nat.le_succ n)

lemma box_sub_card (d n r : ℕ) : (box d (n+r)\box d n).card=(2*(n+r)+1)^d-(2*n+1)^d := by
  rw [Finset.card_sdiff_of_subset (box_mono (Nat.le_add_right n r)),box_card,box_card]

lemma box_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 1) := by
  have hx : Tendsto (fun n : ℕ=>(2*(n:ℝ)+1)/(2*((n:ℝ)+r)+1)) atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ=>(2*((n:ℝ)+r)+1)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_atTop_add_const_right _ 1
        ((tendsto_atTop_add_const_right _ (r:ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<2))
    have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (hi.const_mul (2*r:ℝ))
    convert hh using 1
    · ext n
      field_simp
      ring
    · simp
  have hh:=hx.pow d
  simpa only [box_card,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_pow,one_pow] using hh

lemma box_boundary_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d (n+r)\box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 0) := by
  have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (box_ratio_tendsto d r)
  convert hh using 1
  · ext n
    rw [Finset.card_sdiff_of_subset (box_mono (Nat.le_add_right n r)),Nat.cast_sub (Finset.card_le_card (box_mono (Nat.le_add_right n r))),sub_div,div_self]
    exact_mod_cast (Finset.card_ne_zero.mpr (box_nonempty d (n+r)))
  · norm_num

end Heisenberg
end
end

end OAI
