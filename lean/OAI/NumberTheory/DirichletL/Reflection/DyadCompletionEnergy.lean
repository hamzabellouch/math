import OAI.NumberTheory.DirichletL.Reflection.DyadReassembly

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

abbrev CellCompletion (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1)) :=
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode

variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

def cellPhysicalTerm (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j)
    (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) : ℂ :=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (D K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem physical_dyad_selection_energy (E : ℝ→ℝ) (hE : ∀ θ,0≤E θ)
    (he : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (divisorDyadicBin rows Hrow i).Nonempty → (activeTupleDyad tuples Hslot j).Nonempty →
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ) :
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : rows,‖∑ p : tuples,
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw K p‖^2)≤
          (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ := by
  have hall : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ := by
    intro i j
    by_cases hi : (divisorDyadicBin rows Hrow i).Nonempty
    · by_cases hj : (activeTupleDyad tuples Hslot j).Nonempty
      · exact he i j hi hj
      · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
          fun K p hp => (hj ⟨p.val,p.property⟩).elim
        refine ⟨D,?_⟩
        intro θ r aw hr haw
        have hzero : ∀ K : divisorDyadicBin rows Hrow i,
            (∑ p : activeTupleDyad tuples Hslot j,
              cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p)=0 := by
          intro K
          apply Finset.sum_eq_zero
          intro p hp
          exact (hj ⟨p.val,p.property⟩).elim
        simp_rw [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero]
        exact hE θ
    · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
        fun K p hp => (hi ⟨K.val,K.property⟩).elim
      refine ⟨D,?_⟩
      intro θ r aw hr haw
      have hzero : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)=0 := by
        apply Finset.sum_eq_zero
        intro K hK
        exact (hi ⟨K.val,K.property⟩).elim
      rw [hzero]
      exact hE θ
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ r aw hr haw
  apply dyadic_physical_energy G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw (E θ)
  intro i j
  have hid : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw
        ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
        ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩‖^2)=
      ∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
        cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j (D i j) θ r aw K p‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro p hp
    exact dyadicPhysicalTerm_at G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw i j K p
  exact hid.trans_le (hD i j θ r aw hr haw)
end
end SevenEighths.InverseReflectedPhase

end OAI
