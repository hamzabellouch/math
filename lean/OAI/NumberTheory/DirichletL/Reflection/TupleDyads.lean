import OAI.NumberTheory.DirichletL.Reflection.FixedTuples
import OAI.NumberTheory.DirichletL.Descent.Dyadic

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def activeTupleDyad (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (i : Fin (columnDyadicLength H+1)) : Finset (σ→Ideal Eis) :=
  tuples.filter fun p => divisorDyadicLabel H (slotTupleProduct p)=i

omit [DecidableEq σ] in
lemma sum_activeTupleDyads {A : Type*} [AddCommMonoid A]
    (tuples : Finset (σ→Ideal Eis)) (H : ℝ) (f : (σ→Ideal Eis)→A) :
    (∑ p∈tuples,f p)=∑ i : Fin (columnDyadicLength H+1),∑ p∈activeTupleDyad tuples H i,f p := by
  exact (Finset.sum_fiberwise tuples (fun p => divisorDyadicLabel H (slotTupleProduct p)) f).symm

omit [DecidableEq σ] in
lemma activeTupleDyad_bounds (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (p : σ→Ideal Eis) (hp : p∈activeTupleDyad tuples H i) :
    divisorDyadicScale i.val≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨hpt,he⟩ := Finset.mem_filter.mp hp
  have hh := divisorDyadicLabel_bounds H (slotTupleProduct p) (hn p hpt).1 (hn p hpt).2
  rw [he] at hh
  constructor
  · exact max_le (hn p hpt).1 hh.1.le
  · have ht : (2:ℝ)^i.val/2≤divisorDyadicScale i.val := le_max_right _ _
    linarith [hh.2]

omit [DecidableEq σ] in
lemma activeTupleDyad_scale_le (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    divisorDyadicScale i.val≤H := by
  obtain ⟨p,hp⟩ := hi
  exact (activeTupleDyad_bounds tuples H hn i p hp).1.trans (hn p (Finset.mem_filter.mp hp).1).2

omit [DecidableEq σ] in
lemma activeTupleDyad_width (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    0≤Real.logb Z (divisorDyadicScale i.val) ∧ Real.logb Z (divisorDyadicScale i.val)≤z := by
  have hs := divisorDyadicScale_ge_one i.val
  have hp : 0<divisorDyadicScale i.val := lt_of_lt_of_le zero_lt_one hs
  constructor
  · have hh := Real.logb_le_logb_of_le hZ zero_lt_one hs
    simpa only [Real.logb_one] using hh
  · have hh := Real.logb_le_logb_of_le hZ hp ((activeTupleDyad_scale_le tuples H hn i hi).trans hH)
    rwa [Real.logb_rpow (lt_trans zero_lt_one hZ) (ne_of_gt hZ)] at hh
omit [DecidableEq σ] in
lemma slotTupleProduct_norm_bound (L : σ→Finset (Ideal Eis)) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (p : σ→Ideal Eis) (hp : ∀ i,p i∈L i) :
    1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤∏ i,H i := by
  have hn : slotTupleProduct p≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hzero i _ (hp i))
  refine ⟨QuadraticMainBoundary.norm_one_le hn,?_⟩
  change (Ideal.absNorm (∏ i,p i):ℝ)≤_
  rw [map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hH i _ (hp i))

omit [DecidableEq σ] in
lemma activeTupleDyad_energy_scale (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    2≤2*divisorDyadicScale i.val ∧
      0≤Real.logb Z ((2*divisorDyadicScale i.val)/2) ∧
      Real.logb Z ((2*divisorDyadicScale i.val)/2)≤z ∧
      ∀ p∈activeTupleDyad tuples H i,
        (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
          (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  have hw := activeTupleDyad_width tuples H Z z hZ hH hn i hi
  have hs := divisorDyadicScale_ge_one i.val
  rw [show (2*divisorDyadicScale i.val)/2=divisorDyadicScale i.val by ring]
  exact ⟨by linarith,hw.1,hw.2,activeTupleDyad_bounds tuples H hn i⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
