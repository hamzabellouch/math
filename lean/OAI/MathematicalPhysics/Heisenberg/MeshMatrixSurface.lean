import OAI.MathematicalPhysics.Heisenberg.ColorClockLimit

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance matrixSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.Cycle Pin Return LayeredExchange Exposure LatticeRegular SpatialFrame Heisenberg.Geometry

def tailProjection (V : Type) [Fintype V] : Matrix (V → Bool) (V → Bool) ℝ :=
  Matrix.diagonal (fun c=>if (Fintype.card V:ℝ)/4≤SlotColor.magnetization c then (1:ℝ) else 0)

theorem mesh_matrix_surface (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2),
        ∀ᶠ δ in 𝓝 (0:ℝ),0<δ →
        ∀ (L Q : ℕ) (_hL : 0<L) (_hQ : 0<Q) (_hqQ : q≤Q) (_hdiv : Q∣L)
          (a b : Fin L → Slots (B:=B) Λ)
          (_hab : ∀ j : Fin L,j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q))
          (_hsite : ∀ j : Fin L,q≤j.val%Q → (a j).1.val=(b j).1.val)
          (rates : Fin L → ℝ) (_hp : ∀ j,0≤rates j ∧ rates j≤1)
          (_hrate : ∀ j : Fin L,j.val%Q<q → rates j=δ/2),
          F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
          2*(⌊s/δ⌋₊+1)*Q ≤ L →
          let K:=Finset.univ.filter (fun j : Fin L=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
          let T:=Serial.product L (fun j=>colorCoin (a j) (b j) (rates j))
          Real.exp (-(Real.log 2)*(((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)+2*δ*K.card))/2 *
            Matrix.trace T ≤ Matrix.trace (T*tailProjection (Slots (B:=B) Λ)) := by
  obtain ⟨p,s,_hp,_hpq,hs,_hsp,hbound⟩:=mesh_surface_tail d hd B
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀
  filter_upwards [hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀] with δ hδ
  intro hδpos L Q hL hQ hqQ hdiv a b hab hsite rates hp hrate hF hf hroom K T
  cases L with
  | zero=>omega
  | succ N=>
    have hh:=hδ hδpos N Q hQ hqQ hdiv a b hab hsite rates hp hrate hF hf hroom
    have hsum : (∑ ω,layerWeight rates ω)=1 := by
      with_reducible convert layerWeight_sum rates using 1
      congr! 20
    have hpos:=pinPartition_pos (layerWeight rates) (coinWiring (finRotate (N+1)) a b)
      (layerWeight_nonneg rates hp) (by rw [hsum]; norm_num) ∅
    dsimp only at hh
    rw [mesh_cut_product,mesh_partition_product] at hh
    rw [mesh_partition_product] at hpos
    exact (le_div_iff₀ hpos).mp hh

end Heisenberg.Surface
end
end

end OAI
