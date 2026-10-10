import OAI.NumberTheory.DirichletL.Reflection.DyadSelection
import OAI.NumberTheory.DirichletL.Reflection.InactiveRows

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma dependent_sum_filter_partition {α β A : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid A]
    (T : Finset α) (label : α→β) (f : T→A) :
    (∑ p : T,f p)=∑ j : β,∑ p : T.filter (fun p => label p=j),f ⟨p.val,(Finset.mem_filter.mp p.property).1⟩ := by
  let g : α→A := fun p => if hp:p∈T then f ⟨p,hp⟩ else 0
  have h := Finset.sum_fiberwise T label g
  calc
    _ = ∑ p∈T,g p := by
      symm
      rw [←Finset.sum_coe_sort T]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left p.property]
    _ = ∑ j,∑ p∈T.filter (fun p => label p=j),g p := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left (Finset.mem_filter.mp p.property).1]

theorem dependent_partition_energy {α β ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rows : Finset α) (tuples : Finset β) (rowLabel : α→ι) (slotLabel : β→κ)
    (f : rows→tuples→ℂ) :
    (∑ k : rows,‖∑ p : tuples,f k p‖^2)≤
      (Fintype.card κ:ℝ)*∑ i : ι,∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
  rw [dependent_sum_filter_partition rows rowLabel]
  calc
    _ ≤ ∑ i : ι,(Fintype.card κ:ℝ)*∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      let g := fun (j : κ) (k : rows.filter (fun k => rowLabel k=i)) =>
        ∑ p : tuples.filter (fun p => slotLabel p=j),
          f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩ ⟨p.val,(Finset.mem_filter.mp p.property).1⟩
      have he := weighted_finite_row_energy (Finset.univ : Finset κ)
        (Finset.univ : Finset (rows.filter (fun k => rowLabel k=i))) (fun _ => (1:ℂ)) g
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
      convert he using 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      exact dependent_sum_filter_partition tuples slotLabel _
    _ = _ := by rw [Finset.mul_sum]

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)
variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)

def dyadicPhysicalTerm (K : rows) (p : tuples) : ℂ :=
  if hp:IsCoprime K.val (slotTupleProduct p.val) then
    r K.val*aw p.val*mixedReflectedValue
      (dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C K p hp) s
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

lemma dyadicPhysicalTerm_at (i : Fin (columnDyadicLength Hrow+1))
    (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) :
    dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (C i j K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  unfold dyadicPhysicalTerm
  split_ifs with hp
  · rw [dyadicTupleControlled_at]
  · rfl

theorem dyadic_physical_energy (E : ℝ)
    (hE : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (∑ K : rows.filter (fun K => divisorDyadicLabel Hrow K=i),
        ‖∑ p : tuples.filter (fun p => divisorDyadicLabel Hslot (slotTupleProduct p)=j),
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
            ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
            ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2)≤E) :
    (∑ K : rows,‖∑ p : tuples,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw K p‖^2)≤
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E := by
  have he := dependent_partition_energy rows tuples (divisorDyadicLabel Hrow)
    (fun p => divisorDyadicLabel Hslot (slotTupleProduct p))
    (dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw)
  apply he.trans
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hE i j))
  apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card (Fin (columnDyadicLength Hslot+1))))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
