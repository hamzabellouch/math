import OAI.MathematicalPhysics.Heisenberg.SpinField

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
attribute [instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Geometry SpatialFrame SlotTensor TensorMatrix

lemma cycleGenerator_eq {d ℓ q : ℕ} (Λ : Finset (Site d))
    (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
    (ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1) (hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2) :
    (∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))=
      clockGenerator (fun x y : Λ=>Step x.val y.val) ℓ := by
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [ha₀,hb₀]
  exact edge.sum_comp (fun e : Edges (B:=Fin ℓ) Step Λ =>
    (1/2:ℝ) • (SlotColor.matrix (Equiv.swap e.val.1 e.val.2)-1))

lemma step_ne {d : ℕ} {x y : Site d} (h : Step x y) : x≠y := by
  obtain ⟨j,hj,_⟩:=h
  intro he
  subst y
  omega

lemma spectral_tail_eq {X : Type} [Fintype X] (ℓ : ℕ) :
    tailProjection (X×Fin ℓ)=Matrix.diagonal
      (fun c : (X×Fin ℓ) → Bool=>if (Fintype.card X:ℝ)*ℓ/4≤SlotColor.magnetization c then (1:ℝ) else 0) := by
  simp only [tailProjection,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]

theorem physical_surface_bound (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • spinGenerator (fun x y : Λ=>Step x.val y.val) ℓ)
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace E≤
          Matrix.trace (E*Matrix.diagonal (fun k : Λ → SpinSlots.Level ℓ=>
            if (Λ.card:ℝ)*ℓ/4≤physicalMagnetization ℓ k then (1:ℝ) else 0)) := by
  obtain ⟨s,hs,hbound⟩:=symmetrized_surface_bound d ℓ hd
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ hF hf t ht Z J E
  have hh : Real.exp (-(Real.log 2)*(Z+2*t*J))/2*
      Matrix.trace (colorSymmetrizer Λ ℓ*NormedSpace.exp (t • ∑ j∈Finset.range q,
        (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1)))≤
      Matrix.trace (colorSymmetrizer Λ ℓ*NormedSpace.exp (t • ∑ j∈Finset.range q,
        (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
    convert hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀ hF hf t ht using 1 <;> congr! 30
  rw [cycleGenerator_eq Λ edge a₀ b₀ ha₀ hb₀,spectral_tail_eq] at hh
  have hn : ∀ x y : Λ,Step x.val y.val → x≠y := fun x y h he=>step_ne h (congrArg Subtype.val he)
  have hb:=trace_clock_spectral (fun x y : Λ=>Step x.val y.val) hn ℓ t (fun _=>1)
  simp only [Matrix.diagonal_one,Matrix.mul_one] at hb
  rw [hb] at hh
  have htail:=trace_clock_spectral (fun x y : Λ=>Step x.val y.val) hn ℓ t
    (fun m=>if (Fintype.card Λ:ℝ)*ℓ/4≤ m then (1:ℝ) else 0)
  rw [htail] at hh
  simpa only [Fintype.card_coe] using hh

end Heisenberg.Surface
end
end

end OAI
