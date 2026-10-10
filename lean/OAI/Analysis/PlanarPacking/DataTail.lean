import OAI.Analysis.PlanarPacking.ContactData
import OAI.Analysis.PlanarPacking.AtomTail

namespace OAI

/-!
# Tails of transformed contact data

Gaussian row estimates control the tails of the summable contact sequences.
-/

namespace SharpPlanar
open IntegerBasis
lemma sharp_data_row (p : CardinalData) (n : Node) :
    |transformedJets p (n,false)|+|transformedJets p (n,true)| ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6,rowPiece j n.val)+
      |p.C| *(∑ j : Fin 7,atomRow j n.val) := by
  have h0 := sharp_moment_bound p 0 (Nat.cast_nonneg n.val)
  have h1 := sharp_moment_bound p 1 (Nat.cast_nonneg n.val)
  simp only [pow_zero,mul_one] at h0
  simp only [pow_one] at h1
  have hq := Q_pos n.val
  unfold transformedJets
  simp only [Bool.false_eq_true,ite_false,ite_true]
  calc
    _ ≤ ((1+|D n.val|)*|K p 0 n.val|+|K p 1 n.val|)/Q n.val := paired_jet_bound hq _ _ _
    _ ≤ ((1+|D n.val|)*((|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6,densityCap j*pieceL j n.val)+
        |p.C| *(∑ j : Fin 7,atomL j n.val))+
      ((|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6,densityCap j*pieceL j n.val*(Real.pi*zCap ⟨j.val,by omega⟩))+
        |p.C| *(∑ j : Fin 7,atomL j n.val*(Real.pi*zCap j))))/Q n.val := by
      exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity)) h1) hq.le
    _ = _ := by
      have hr : (∑ j : Fin 6,rowPiece j n.val)=
          ((1+|D n.val|)*(∑ j : Fin 6,densityCap j*pieceL j n.val)+
            ∑ j : Fin 6,densityCap j*pieceL j n.val*(Real.pi*zCap ⟨j.val,by omega⟩))/Q n.val := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        simp only [rowPiece,n.prop.2,ite_true,rowFactor,div_eq_mul_inv]
        ring
      have ha : (∑ j : Fin 7,atomRow j n.val)=
          ((1+|D n.val|)*(∑ j : Fin 7,atomL j n.val)+
            ∑ j : Fin 7,atomL j n.val*(Real.pi*zCap j))/Q n.val := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        simp only [atomRow,n.prop.2,ite_true,atomRowFactor,div_eq_mul_inv]
        ring
      rw [hr,ha]
      ring
lemma atom_natural_tail_summable (N : ℕ) :
    Summable (fun k : ℕ => ∑ j : Fin 7,atomRow j (N+1+k)) :=
  (hasSum_sum (fun j _ => (atomRow_tail_sum j N).1.hasSum)).summable
lemma atom_natural_tail_bound (N : ℕ) :
    (∑' k : ℕ,∑ j : Fin 7,atomRow j (N+1+k))≤atomRowTable N := by
  rw [Summable.tsum_finsetSum (fun j _ => (atomRow_tail_sum j N).1)]
  exact Finset.sum_le_sum (fun j _ => (atomRow_tail_sum j N).2)
lemma sharp_data_tail (p : CardinalData) (N : ℕ) :
    rowTailNorm (transformedJetList p) N ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*rowTable N+|p.C| *atomRowTable N := by
  let f : ℕ → ℝ := fun k => (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6,rowPiece j (N+1+k))+
    |p.C| *(∑ j : Fin 7,atomRow j (N+1+k))
  let index : {n : Node // N<n.val} → ℕ := fun n => n.val.val-(N+1)
  have hi : Function.Injective index := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have ha := a.prop; have hb := b.prop
    dsimp only [index] at hab
    omega
  have he (n : {n : Node // N<n.val}) : N+1+index n=n.val.val := by
    have hn := n.prop
    dsimp only [index]
    omega
  have hf : Summable f := ((natural_row_tail_summable N).mul_left _).add ((atom_natural_tail_summable N).mul_left _)
  have hfn : ∀ n,0≤f n := by
    intro n
    dsimp only [f]
    exact add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => rowPiece_nonneg _ _))
      (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => atomRow_nonneg _ _))
  have hfi : Summable (f ∘ index) := hf.comp_injective hi
  calc
    rowTailNorm (transformedJetList p) N ≤ ∑' n : {n : Node // N<n.val}, f (index n) := by
      apply (rowTailNorm_summable _ N).tsum_le_tsum _ hfi
      intro n
      change |transformedJets p (n.val,false)|+|transformedJets p (n.val,true)| ≤ f (index n)
      simpa only [f,he] using sharp_data_row p n.val
    _≤∑' k,f k := tsum_comp_le_tsum_of_inj hf hfn hi
    _=(|p.c₀|+|p.d₀|+‖p.x‖)*(∑' k,∑ j : Fin 6,rowPiece j (N+1+k))+
        |p.C| *(∑' k,∑ j : Fin 7,atomRow j (N+1+k)) := by
      rw [Summable.tsum_add ((natural_row_tail_summable N).mul_left _) ((atom_natural_tail_summable N).mul_left _)]
      simp only [tsum_mul_left]
    _≤_ := add_le_add (mul_le_mul_of_nonneg_left (natural_row_tail_bound N) (by positivity))
      (mul_le_mul_of_nonneg_left (atom_natural_tail_bound N) (abs_nonneg _))
end SharpPlanar

end OAI
