import OAI.MathematicalPhysics.Heisenberg.BoundaryMesh

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance surfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return Heisenberg.LayeredExchange Heisenberg.Exposure Heisenberg.LatticeRegular Heisenberg.SpatialFrame Heisenberg.Geometry

lemma growth_singleton {X Y : Type*} [PseudoMetricSpace X] (loc : Y → X)
    (α L : ℝ) (hα : 0≤α) (hL : 1≤L) (y : Y) : localGrowth loc α L {y} := by
  intro x r hr
  have hh : (1:ℝ)≤(1+r)^α := Real.one_le_rpow (by linarith) hα
  have hc : ((({y}:Finset Y).filter fun v=>dist (loc v) x≤r).card:ℝ)≤1 := by
    exact_mod_cast (Finset.card_filter_le ({y}:Finset Y) _)
  exact hc.trans (by nlinarith)

lemma rotation_reaches_zero (n : ℕ) (t : Fin (n+1)) : ∃ k : ℕ,((finRotate (n+1))^k) t=0 := by
  have h : (finRotate (n+1)).SameCycle 0 t := by
    refine ⟨(t.val:ℤ),?_⟩
    rw [zpow_natCast,rotate_pow_zero]
    simp
  exact h.symm.exists_nat_pow_eq

lemma pinPartition_empty_trace {V Ω : Type*} [Fintype V] [Fintype Ω]
    (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    pinPartition μ π ∅=∑ ω,μ ω*Matrix.trace (SlotColor.matrix (π ω)) := by
  unfold pinPartition
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hh:=pinned_trace (π ω) ∅ (fun _=>1)
  have hcard:=card_pinnedColor (π ω) ∅
  simpa only [Set.mem_empty_iff_false,IsEmpty.forall_iff,implies_true,ite_true,
    Matrix.diagonal_one,Matrix.mul_one,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,hcard,Nat.cast_pow,Nat.cast_ofNat] using hh.symm

lemma cut_card {V : Type*} [Fintype V] (n : ℕ) :
    (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))).card=Fintype.card V := by
  rw [Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).2),Finset.card_univ]

lemma cut_spin {V : Type*} [Fintype V] (n : ℕ) (c : Fin (n+1)×V → Bool) :
    cutSpin (Finset.univ.image (fun v : V=>((0:Fin (n+1)),v))) c=SlotColor.magnetization (fun v=>c (0,v)) := by
  rw [cutSpin,Finset.sum_image (fun _ _ _ _ h=>(Prod.mk.inj h).2)]
  rfl

attribute [local irreducible] colorTail coinWiring Heisenberg.LayeredExchange.layerWeight pinDensity

theorem mesh_surface_tail (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ p s : ℝ,0<p ∧ p<1/4 ∧ 0<s ∧ s=p^(-(11/10:ℝ)) ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (N Q : ℕ) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣N+1)
          (a b : Fin (N+1) → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin (N+1),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin (N+1),q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin (N+1) → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin (N+1),j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ N+1 →
          let K:=Finset.univ.filter (fun j : Fin (N+1)=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
          let C:=Finset.univ.image (fun v : Slots (B:=B) Λ=>((0:Fin (N+1)),v))
          Real.exp (-(Real.log 2)*(((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)+2*δ*K.card))/2 ≤
            colorTail (layerWeight rates) (coinWiring (finRotate (N+1)) a b) C/
              pinPartition (layerWeight rates) (coinWiring (finRotate (N+1)) a b) ∅ := by
  obtain ⟨p,s,hp,hpq,hs,hsp,hbound⟩:=Heisenberg.Bootstrap.mesh_pin_bound d hd B (2*(d+1):ℕ) (by rfl)
  refine ⟨p,s,hp,hpq,hs,hsp,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀
  filter_upwards [hbound Λ F q edge a₀ b₀ ha₀ hb₀] with δ hδ
  intro hδpos N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom K C
  let D : Set (Slots (B:=B) Λ):={v | v.1.val∉F}
  let P : Set (Fin (N+1)×Slots (B:=B) Λ):={z | z.2∈D}
  let μ:=layerWeight rates
  let π:=coinWiring (finRotate (N+1)) a b
  have hμ:=layerWeight_nonneg rates hrates
  have hpos : 0<∑ c,μ c := by
    have hh:=layerWeight_sum rates
    with_reducible convert (show (0:ℝ)<1 by norm_num) using 1
    with_reducible convert hh using 1
    congr! 20
  have hC : C.Nonempty := by
    obtain ⟨x,hx⟩:=hΛ
    exact Finset.image_nonempty.mpr ⟨(⟨x,hx⟩,Classical.choice (inferInstance : Nonempty B)),Finset.mem_univ _⟩
  apply color_surface_tail μ π hμ hpos P C hC p hpq.le
  · intro i _
    by_cases hi : i∈P
    · simp only [hasHit_of_mem (π _) hi,not_true_eq_false,ite_false,Finset.sum_const_zero]
      exact hp.le
    · have hh:=hδ hδpos N Q hQ hqQ hdiv a b hab hsite rates hrates hrate hF hframe hroom P
        (fun z hz=>hz) {i} ?_ ?_
      · simpa only [Finset.mem_singleton,forall_eq,Finset.card_singleton,pow_one] using hh
      · refine ⟨i.1,{i.2},by simp,?_⟩
        exact growth_singleton _ _ _ (by norm_num) (by exact_mod_cast (show 1≤2*(d+1) by omega)) _
      · simpa only [Finset.coe_singleton] using Set.disjoint_singleton_right.mpr hi
  · have hK : ∀ t,t∉K → (a t∈D ↔ b t∈D) := by
      intro t ht
      by_cases hspatial : t.val%Q<q
      · have hh : (a t).1.val∈F ∧ (b t).1.val∈F := by
          simpa only [K,Finset.mem_filter,Finset.mem_univ,true_and,hspatial,true_and,not_or,not_not] using ht
        simp [D,hh.1,hh.2]
      · change ((a t).1.val∉F)↔((b t).1.val∉F)
        rw [hsite t (by omega)]
    have hh:=mean_boundary_cycles (finRotate (N+1)) a b D K hK 0 (rotation_reaches_zero N) rates hrates ∅
    have hr : (∑ t∈K,rates t)=δ/2*K.card := by
      calc _ = ∑ _t∈K,δ/2 := by
             apply Finset.sum_congr rfl
             intro t ht
             exact hrate t (Finset.mem_filter.mp ht).2.1
           _ = _ := by simp; ring
    rw [hr] at hh
    simp_rw [layerMass_pinDensity] at hh
    have he : (4:ℝ)*(δ/2*K.card)=2*δ*K.card := by ring
    rw [he] at hh
    dsimp only [μ,π,P,D]
    dsimp only [D] at hh
    with_unfolding_all convert hh using 1 <;> congr! 20
    all_goals exact Exposure.coinWiring_eq_history _ _ _

end Heisenberg.Surface
end
end

end OAI
