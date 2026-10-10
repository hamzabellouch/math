import OAI.MathematicalPhysics.Heisenberg.PhysicalTilt

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
namespace Heisenberg.Selection
open Heisenberg.Geometry SpatialFrame SlotTensor

lemma box_volume_tendsto {d : ℕ} (hd : 0<d) (r : ℕ) :
    Tendsto (fun n : ℕ=>((box d (n+r)).card:ℝ)) atTop atTop := by
  simp only [box_card,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  exact (tendsto_pow_atTop hd.ne').comp (tendsto_atTop_add_const_right _ 1
    ((tendsto_atTop_add_const_right _ (r:ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<2)))

lemma surface_exp_tendsto {d : ℕ} (hd : 0<d) (C a : ℝ) (ha : 0<a) :
    Tendsto (fun n : ℕ=>2*Real.exp (C*((box d (n+1)\box d n).card:ℝ)-a*((box d (n+1)).card:ℝ))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ=>C*(((box d (n+1)\box d n).card:ℝ)/((box d (n+1)).card:ℝ))-a) atTop (𝓝 (-a)) := by
    simpa only [mul_zero,zero_sub] using ((box_boundary_ratio_tendsto d 1).const_mul C).sub_const a
  have hmul:=(hc.neg_mul_atTop (neg_lt_zero.mpr ha) (box_volume_tendsto hd 1))
  have hexp:=(Real.tendsto_exp_atBot.comp hmul).const_mul 2
  convert hexp using 1
  · ext n
    congr 2
    have hv : ((box d (n+1)).card:ℝ)≠0:=by exact_mod_cast Finset.card_ne_zero.mpr (box_nonempty d (n+1))
    field_simp
  · norm_num

lemma cube_edges_nonempty (d ℓ n : ℕ) (hd : 0<d) [NeZero ℓ] :
    Nonempty (Edges (B:=Fin ℓ) Step (box d (n+1))) := by
  let i : Fin d:=⟨0,hd⟩
  let y : Site d:=Function.update 0 i 1
  have h0 : (0:Site d)∈box d (n+1):=(box_mem d (n+1) 0).mpr (by intro j; simp; omega)
  have hy : y∈box d (n+1) := by
    apply (box_mem d (n+1) y).mpr
    intro j
    by_cases hj : j=i
    · subst j; simp [y]
    · simp [y,Function.update_of_ne hj]; omega
  have hs : Step (0:Site d) y:=⟨i,Or.inl (by simp [y]),fun j hj=>by simp [y,Function.update_of_ne hj]⟩
  exact ⟨⟨((⟨0,h0⟩,(0:Fin ℓ)),(⟨y,hy⟩,(0:Fin ℓ))),hs⟩⟩

theorem field_ordered_cubes (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ]
    (τ : State (d+1) ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A)) :
    ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β → ∀ h : ℝ,0<h →
      ∀ᶠ n : ℕ in atTop,
        ((box (d+1) (n+1)).card:ℝ)*ℓ/8≤
          ((gibbsState τ (shiftedField (box (d+1) (n+1)) h) β).functional
            (totalZ (box (d+1) (n+1)))).re := by
  obtain ⟨s,hs,hbound⟩:=Surface.physical_surface_bound d ℓ hd
  refine ⟨4*s+1,by linarith,?_⟩
  intro β hβ h hh
  have hb : 0<β:=by linarith
  let C : ℝ:=Real.log 2*((ℓ:ℝ)+β*((4*(d+1):ℕ):ℝ)*ℓ^2)
  let a : ℝ:=β*h*ℓ/16
  have ha : 0<a:=by dsimp [a]; exact div_pos (mul_pos (mul_pos hb hh) (by exact_mod_cast NeZero.pos ℓ)) (by norm_num)
  have he :=(surface_exp_tendsto (by omega : 0<d+1) C a ha).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/11))
  filter_upwards [he] with n hn
  let Λ:=box (d+1) (n+1)
  let F:=box (d+1) n
  let E:=Edges (B:=Fin ℓ) Step Λ
  let : Nonempty E:=cube_edges_nonempty (d+1) ℓ n (by omega)
  let q:=Fintype.card E
  let : NeZero q:=⟨Fintype.card_ne_zero⟩
  let edge : Fin q ≃ E:=(Fintype.equivFin E).symm
  let a₀ : ℕ → Slots (B:=Fin ℓ) Λ:=fun j=>(edge (j:Fin q)).val.1
  let b₀ : ℕ → Slots (B:=Fin ℓ) Λ:=fun j=>(edge (j:Fin q)).val.2
  have ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1:=by intro j; simp only [a₀,Fin.cast_val_eq_self]
  have hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2:=by intro j; simp only [b₀,Fin.cast_val_eq_self]
  let Z : ℝ:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
  let J : ℝ:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
  let L : ℝ:=Real.exp (-(Real.log 2)*(Z+β*J))/2
  have htail :=hbound Λ F (box_nonempty _ _) q edge a₀ b₀ ha₀ hb₀
    (box_mono (Nat.le_succ n)) (fun z hz w hzw=>box_neighbor hz hzw) (β/2) (by linarith)
  have htail' : L*Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ))≤
      Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ)*
        Matrix.diagonal (fun k : Λ → SpinSlots.Level ℓ=>if (Λ.card:ℝ)*ℓ/4≤physicalMagnetization ℓ k then (1:ℝ) else 0)) := by
    convert htail using 1 <;> simp only [L,Z,J,nearestNeighbor_iff_step]; congr 5; ring
  apply physical_field_mean Λ τ hτ β h L (mul_pos hb hh).le (by dsimp [L]; positivity) htail'
  have hZ : Z≤((Λ\F).card:ℝ)*ℓ := by dsimp [Z]; exact_mod_cast bad_slots_le (ℓ:=ℓ) Λ F
  have hJ : J≤((4*(d+1):ℕ):ℝ)*((Λ\F).card:ℝ)*ℓ^2 := by
    dsimp [J]
    rw [schedule_bad_eq Λ F edge a₀ b₀ ha₀ hb₀]
    exact_mod_cast bad_edges_le (ℓ:=ℓ) Λ F
  have hcost : (Real.log 2)*(Z+β*J)≤C*((Λ\F).card:ℝ) := by
    have hbJ:=mul_le_mul_of_nonneg_left hJ hb.le
    have hhcost:=mul_le_mul_of_nonneg_left (add_le_add hZ hbJ) (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
    calc _ ≤ (Real.log 2)*(((Λ\F).card:ℝ)*ℓ+β*(((4*(d+1):ℕ):ℝ)*((Λ\F).card:ℝ)*ℓ^2)) := hhcost
         _ = C*((Λ\F).card:ℝ) := by dsimp [C]; ring
  calc L⁻¹*Real.exp (-((β*h)*((Λ.card:ℝ)*ℓ)/16))=
        2*Real.exp ((Real.log 2)*(Z+β*J)-a*(Λ.card:ℝ)) := by
          dsimp [L,a]
          rw [inv_div,div_eq_mul_inv,←Real.exp_neg]
          simp only [neg_mul,neg_neg]
          rw [mul_assoc,←Real.exp_add]
          congr 2
          ring
       _ ≤ 2*Real.exp (C*((Λ\F).card:ℝ)-a*(Λ.card:ℝ)) :=
         mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right hcost _)) (by norm_num)
       _ ≤ 1/11 := hn

end Heisenberg.Selection
end
end

end OAI
