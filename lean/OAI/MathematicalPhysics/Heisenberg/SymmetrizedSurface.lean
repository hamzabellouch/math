import OAI.MathematicalPhysics.Heisenberg.CompletionFactor

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance symSurfaceDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.Geometry LatticeRegular SpatialFrame MeshPair

def colorSymmetrizer (X : Type) [Fintype X] (ℓ : ℕ) :
    Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ :=
  (Fintype.card (X → Equiv.Perm (Fin ℓ)):ℝ)⁻¹ •
    ∑ κ : X → Equiv.Perm (Fin ℓ),SlotColor.matrix (SlotTensor.fiberPerm κ)

lemma colorSymmetrizer_reindex (X : Type) [Fintype X] (ℓ : ℕ) :
    Matrix.reindex (SlotTensor.configEquiv ℓ) (SlotTensor.configEquiv ℓ) (colorSymmetrizer X ℓ)=
      TensorMatrix.tensor (fun _ : X=>SpinSlots.basis ℓ) *
        (TensorMatrix.tensor (fun _ : X=>SpinSlots.basis ℓ)).transpose := by
  rw [← SlotTensor.symmetrizer]
  ext A B
  simp only [colorSymmetrizer,SlotTensor.matrix,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  congr! 20

theorem symmetrized_surface_bound (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))
        let P:=colorSymmetrizer Λ ℓ
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (P*E)≤
          Matrix.trace (P*E*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
  obtain ⟨s,hs,hbound⟩:=completed_surface_bound d hd (Fin ℓ)
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ hF hf t ht Z J E P
  let : Nonempty Λ:=Finset.Nonempty.coe_sort hΛ
  have hh (κ : Λ → Equiv.Perm (Fin ℓ)) :
      Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (SlotColor.matrix (SlotTensor.fiberPerm κ)*E)≤
      Matrix.trace (SlotColor.matrix (SlotTensor.fiberPerm κ)*E*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
    obtain ⟨c,u,v,huv,hp⟩:=completion_factorization (fun p : Slots (B:=Fin ℓ) Λ=>p.1.val)
      (SlotTensor.fiberPerm κ) (fun _=>rfl)
    have hh:=hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀ c u v huv hF hf t ht
    dsimp only at hh
    rw [hp] at hh
    exact hh
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun κ _=>hh κ)
  rw [←Finset.mul_sum] at hsum
  have hm:=mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Λ → Equiv.Perm (Fin ℓ))) : 0≤(Fintype.card (Λ → Equiv.Perm (Fin ℓ)):ℝ)))
  dsimp only [P,colorSymmetrizer]
  simp only [Matrix.smul_mul,Matrix.sum_mul,Matrix.trace_smul,Matrix.trace_sum,smul_eq_mul]
  with_reducible convert hm using 1 <;> (try ring_nf) <;> congr! 20

end Heisenberg.Surface
end
end

end OAI
