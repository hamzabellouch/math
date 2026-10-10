import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Amplification

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryHitTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem visitEnvelope_column_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V) :
    Summable (fun z => q.visitEnvelope o p k z a) ∧
      (∑' z, q.visitEnvelope o p k z a) ≤ c*((k*M:ℕ)*q.successProbability p o ^ k) := by
  apply transported_column_of_row_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (q.visitEnvelope o p k) (q.visitEnvelope_nonneg o p k) _
    (fun z => (q.visitEnvelope_row_bound o p k z).1) _
    (fun z => (q.visitEnvelope_row_bound o p k z).2) a
  intro b hb x y
  obtain ⟨d,hd⟩ := hΓ hb
  exact q.visitEnvelope_covariant o p k b d hd x y

 

theorem finiteTrajectoryHit_sum_le (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Finset V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
      (fun ω (x y : ↥B) => q.mass ω x.val y.val) z A) ≤
      (A.card:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have hcol := fun a => q.visitEnvelope_column_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o p k a
  calc
    _ ≤ ∑ z : ↥B, ∑ a ∈ A, q.visitEnvelope o p k z.val a := by
      apply Finset.sum_le_sum
      intro z _
      exact (finiteTrajectoryHit_le_sum G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z A).trans
        (Finset.sum_le_sum fun a _ => q.finiteTrajectoryMass_le_envelope o Q B p k z a hQ)
    _ = ∑ a ∈ A, ∑ z : ↥B, q.visitEnvelope o p k z.val a := Finset.sum_comm
    _ ≤ ∑ _a ∈ A, c*((k*M:ℕ)*q.successProbability p o ^ k) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_coe_sort B (fun z => q.visitEnvelope o p k z a)]
      exact ((hcol a).1.sum_le_tsum B (fun z _ => q.visitEnvelope_nonneg o p k z a)).trans (hcol a).2
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end LocalEndpointRule
end TrajectoryHitTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteChoiceHit_allRuns {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : ℝ) (k : ℕ)
    (q : Set E → W → W → ℝ) (A : Finset V) :
    finiteChoiceHit G k Q p
      (fun (r : W × (Fin k → W)) _ => e ∘ oldRunVertices k r.1 r.2)
      (fun r η => oldRunWeight (fun i => q (η i)) k r.1 r.2) (A : Set V) =
      ∑ z : W, finiteTrajectoryHit G e Q p k q z A := by
  unfold finiteChoiceHit finiteTrajectoryHit
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral_sum]

noncomputable def allAmplificationVertices (B : Finset V) (k : ℕ)
    (r : ↥B × (Fin k → ↥B)) (_η : ℕ → Set E) : ℕ → V :=
  amplificationVertices B k r.1 r.2

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def allAmplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) : ℝ :=
  oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k r.1 r.2

noncomputable def allAmplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ)
    (r : ↥B × (Fin k → ↥B)) : Finset (SpliceState E) :=
  q.amplificationInputs Q B x k n r.1 r.2

theorem allAmplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) :
    0 ≤ q.allAmplificationWeight B k r η :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (η i) a.val b.val) (fun i a b => q.nonneg (η i) a.val b.val) k r.1 r.2

variable {ι : Type*} [Fintype ι]

theorem allAmplificationHit_bound (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (A : Set V) (hf : A.Finite)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A ≤
      (A.ncard:ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)) := by
  have he : finiteChoiceHit G k Q p (allAmplificationVertices B k) (q.allAmplificationWeight B k) A =
      ∑ z : ↥B, finiteTrajectoryHit G Subtype.val Q p k
        (fun ω (a b : ↥B) => q.mass ω a.val b.val) z hf.toFinset := by
    rw [← finiteChoiceHit_allRuns]
    rw [hf.coe_toFinset]
    rfl
  rw [he,Set.ncard_eq_toFinset_card A hf]
  exact q.finiteTrajectoryHit_sum_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin o Q B p k hf.toFinset hQ

end LocalEndpointRule
end AllEndpointHit

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointSeparated
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWindowMass (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (lo hi : ℕ) : ℝ :=
  finiteFieldIntegral Q p (fun ω => if (cluster G ω x).Finite ∧
    lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi then 1 else 0)

theorem finiteChoiceHit_nonneg {P : Type*} [Fintype P]
    (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : unitInterval)
    (y : P → (ℕ → Set E) → ℕ → V) (m : P → (ℕ → Set E) → ℝ)
    (hm : ∀ r η, 0 ≤ m r η) (A : Set V) : 0 ≤ finiteChoiceHit G k Q p y m A := by
  apply Finset.sum_nonneg
  intro r _
  apply finiteFamilyIntegral_nonneg
  intro η
  split_ifs
  · exact hm r η
  · exact le_refl _

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable {ι : Type*} [Fintype ι]

 

theorem amplificationSeparatedSecondMoment_le [Nonempty E] (hconn : Connected G)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n : ℕ)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) ≤
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p o ^ k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let A := q.allAmplificationInputs Q B x k n
  let y := allAmplificationVertices (E := E) B k
  let m := q.allAmplificationWeight B k
  have hA (r) : A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    q.amplificationInputs_subset Q B x k n r.1 r.2
  have hbin r s (hs : s ∈ A r) : (cluster G s.1 x).Finite ∧
      n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n := by
    have hd := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp (hA r hs)
    have hb := (q.mem_amplificationInputs Q B x k n r.1 r.2 s).mp hs
    exact ⟨cluster_finite_of_finite_edges G (Q.finite_toSet.subset hd.1) x,hb.2.2.2.1,hb.2.2.2.2.1⟩
  have hcap r s (hs : s ∈ A r) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      (cluster G (s.2 i) (y r s.2 i)).Finite ∧ (cluster G (s.2 i) (y r s.2 i)).ncard ≤ M := by
    have hd := q.amplificationInputs_chain Q B x k n r.1 r.2 s hs i hi hik
    exact ⟨hd.2.1,hd.2.2.1⟩
  have hm := q.allAmplificationWeight_nonneg B k
  have hb := finiteChoiceSeparatedPairMass_le G hloc x k n M Q p A A y y m m hm hm hA hA hbin
    (fun r s hs i hi hik => (hcap r s hs i hi hik).1) hcap
  let d : ℝ := c*((k*M:ℕ)*q.successProbability p o ^ k)
  have hd : 0 ≤ d := mul_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p o) _))
  let t : ℝ := ((2*n:ℕ):ℝ)*d
  apply hb.trans
  unfold finiteClusterWindowMass finiteFieldIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have he : t^2 * (finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then 1 else 0)) =
      finiteFieldWeight Q p ω * (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then t^2 else 0) := by
    split_ifs <;> ring
  change _ ≤ t^2 * _
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  by_cases h : (cluster G (finiteFieldSet Q ω) x).Finite ∧
      n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
      (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  · rw [ite_eq_left h,ite_eq_left h]
    have hhit := q.allAmplificationHit_bound hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
      o Q B p k (cluster G (finiteFieldSet Q ω) x) h.1 hQ
    have hc' : ((cluster G (finiteFieldSet Q ω) x).ncard:ℝ) ≤ ((2*n:ℕ):ℝ) := by exact_mod_cast h.2.2.le
    have hhit' : finiteChoiceHit G k Q p y m (cluster G (finiteFieldSet Q ω) x) ≤ t :=
      hhit.trans (mul_le_mul_of_nonneg_right hc' hd)
    simpa only [pow_two] using mul_self_le_mul_self
      (finiteChoiceHit_nonneg G k Q p y m hm _) hhit'
  · rw [ite_eq_right h,ite_eq_right h]

end LocalEndpointRule
end AllEndpointSeparated

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteRootLoad_sum {P : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset P) (f : P → SpliceState E → ℝ) (ω : FiniteField Q) :
    finiteRootLoad Q J p (fun s => ∑ z ∈ S, f z s) ω =
      ∑ z ∈ S, finiteRootLoad Q J p (f z) ω := by
  simp only [finiteRootLoad,Finset.mul_sum]
  exact Finset.sum_comm

 

theorem finiteChoiceForwardLoad_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (t : SpliceState E) :
    finiteChoiceForwardLoad G x k Q A y m t = ∑ z : P,
      finiteChoiceForwardLoad G x k Q (fun r => A (z,r)) (fun r => y (z,r))
        (fun s r => m s (z,r)) t := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma,choiceTraceOutput,choiceTraceMass,choiceTraceInput]
  rfl

 
theorem endpointRootMass_choice_prod {P R : Type*} [Fintype P] [Fintype R]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A : P × R → Finset (SpliceState E)) (y : P × R → SpliceState E → ℕ → V)
    (m : SpliceState E → P × R → ℝ) (e : P → V) (he : Function.Injective e)
    (z : P) (ω : Set E) :
    endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q A y)
      (fun a => e a.1.1) (choiceTraceMass G x k Q A y m) ω (e z) =
      ∑ a : FiniteChoiceTraceIndex G x k Q (fun r => A (z,r)) (fun r => y (z,r)),
        if (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a).1 = ω then
          auxiliaryTupleWeight Q (Finset.Icc 1 k) p
            (choiceTraceOutput G x k Q (fun r => A (z,r)) (fun r => y (z,r)) a) *
          choiceTraceMass G x k Q (fun r => A (z,r)) (fun r => y (z,r)) (fun s r => m s (z,r)) a else 0 := by
  unfold endpointRootMass
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · rw [Fintype.sum_sigma]
    simp only [choiceTraceOutput,choiceTraceMass,choiceTraceInput,and_true]
    rfl
  · intro z' _ hz'
    have hh : e z' ≠ e z := fun h => hz' (he h)
    simp only [hh,and_false,ite_false,Finset.sum_const_zero]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

abbrev AmplificationIndex (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) :=
  FiniteChoiceTraceIndex G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationOutput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceOutput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationInput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceInput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationCode (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → List (ℕ × E) :=
  choiceTraceCode G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → ℝ :=
  choiceTraceMass G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)

noncomputable def amplificationRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) : ℝ :=
  ∑ z : ↥B, q.amplificationMarginal Q B x k n z p ω

theorem amplificationRow_eq_load (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    q.amplificationRow Q B x k n p ω = finiteRootLoad Q (Finset.Icc 1 k) p
      (finiteInverseLoad (q.amplificationOutput Q B x k n) (q.amplificationMass Q B x k n))
      (restrictFiniteField Q ω) := by
  change _ = finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) _
  have hf : (finiteChoiceForwardLoad G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)) =
      (fun t => ∑ z : ↥B, finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
        (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z) t) := by
    funext t
    exact finiteChoiceForwardLoad_prod G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2) t
  rw [hf,finiteRootLoad_sum]
  rfl

theorem amplificationEndpointMass_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) (z : ↥B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) (finiteFieldSet Q ω) z.val =
      q.amplificationMarginal Q B x k n z p (finiteFieldSet Q ω) := by
  change endpointRootMass Q (Finset.Icc 1 k) p (choiceTraceOutput G x k Q _ _)
    _ (choiceTraceMass G x k Q _ _ _) _ _ = _
  rw [endpointRootMass_choice_prod G x k Q p _ _ _ Subtype.val Subtype.val_injective z]
  unfold amplificationMarginal finiteChoiceForwardLoad
  rw [restrictFiniteField_fieldSet,finiteRootLoad_eq_sum]
  · rfl
  · intro a
    exact traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n z a.1) a.2

end LocalEndpointRule
end AllEndpointMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AmplificationIndexFacts
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationOutput_mem (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    q.amplificationOutput Q B x k n a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  traceIndexOutput_mem G x k Q _ _ (q.amplificationInputs_subset Q B x k n a.1.1 a.1.2) a.2

theorem amplificationMass_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    0 ≤ q.amplificationMass Q B x k n a :=
  mul_nonneg (q.allAmplificationWeight_nonneg B k a.1 (q.amplificationInput Q B x k n a).2)
    (Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem amplificationIndex_trace (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    SpliceTrace G x (q.amplificationInput Q B x k n a).2
      (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
      (q.amplificationCode Q B x k n a) (q.amplificationOutput Q B x k n a).1 :=
  (traceIndex_valid G x k Q _ _ a.2).1

theorem amplificationIndex_execution (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    SpliceExecution G x (q.amplificationInput Q B x k n a)
      (q.amplificationCode Q B x k n a) (q.amplificationOutput Q B x k n a) :=
  (traceIndex_valid G x k Q _ _ a.2).2

theorem amplificationIndex_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) :
    x ∈ O ∧ a.1.1.val ∈ O ∧ Conn G (q.amplificationOutput Q B x k n a).1 x a.1.1.val ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).Finite ∧
      (cluster G (q.amplificationOutput Q B x k n a).1 x).ncard ≤ 2*n+k*M :=
  q.amplificationTrace_support Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property _ _
    (q.amplificationIndex_trace Q B x k n a)

theorem amplificationIndex_caps (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).Finite ∧
    (cluster G ((q.amplificationInput Q B x k n a).2 i) (amplificationVertices B k a.1.1 a.1.2 i)).ncard ≤ M := by
  have hc := q.amplificationInputs_chain Q B x k n a.1.1 a.1.2 a.2.1.val a.2.1.property i hi hik
  exact ⟨hc.2.1,hc.2.2.1⟩

theorem amplificationEndpointMass_outside (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (z : V) (hz : z ∉ B) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · exact (hz (h.2 ▸ a.1.1.property)).elim
  · rfl

 

theorem amplificationEndpointMass_bound (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E)
    (hω : ω ⊆ (Q : Set E)) (z : V) :
    endpointRootMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (fun a => a.1.1.val) (q.amplificationMass Q B x k n) ω z ≤ inverseCodeMass M L ^ k := by
  by_cases hz : z ∈ B
  · let z' : ↥B := ⟨z,hz⟩
    have hfield : finiteFieldSet Q (restrictFiniteField Q ω) = ω := by
      rw [finiteFieldSet_restrict,Set.inter_eq_left.mpr hω]
    rw [← hfield,q.amplificationEndpointMass_eq Q B x k n p _ z']
    exact (q.amplificationMarginal_bounds hL Q B x k n z' p _).2
  · rw [q.amplificationEndpointMass_outside Q B x k n p ω z hz]
    apply pow_nonneg
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)

end LocalEndpointRule
end AmplificationIndexFacts

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NoSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem SpliceExecution.nil_iff (G : BondGraph V E) (x : V) (s t : SpliceState E) :
    SpliceExecution G x s [] t ↔ s = t := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact SpliceExecution.nil s

theorem traceIndexMass_nil (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) (hc : traceIndexCode G x k Q A y a = []) :
    traceIndexMass G x k Q A y a = 1 := by
  change a.2.val = [] at hc
  simp [traceIndexMass,hc,traceContactCount]

 

theorem finiteChoiceNilLoad_le {P : Type*} [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (m : SpliceState E → P → ℝ) (hm : ∀ s r, 0 ≤ m s r) (t : SpliceState E) :
    finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t ≤
      ∑ r, if t ∈ A r then m t r else 0 := by
  let I := FiniteChoiceTraceIndex G x k Q A y
  let S : I → Prop := fun a => choiceTraceOutput G x k Q A y a = t ∧ choiceTraceCode G x k Q A y a = []
  let J := {a : I // S a}
  have hin (a : J) : choiceTraceInput G x k Q A y a.val = t := by
    have he := (traceIndex_valid G x k Q (A a.val.1) (y a.val.1) a.val.2).2
    change SpliceExecution G x (choiceTraceInput G x k Q A y a.val)
      (choiceTraceCode G x k Q A y a.val) (choiceTraceOutput G x k Q A y a.val) at he
    rw [a.property.1,a.property.2,SpliceExecution.nil_iff] at he
    exact he
  have hi : Function.Injective (fun a : J => a.val.1) := by
    intro a b hab
    apply Subtype.ext
    apply choiceTrace_injective G x k Q A y
    exact Prod.ext ((hin a).trans (hin b).symm)
      (Prod.ext hab (a.property.2.trans b.property.2.symm))
  have hm' (a : J) : choiceTraceMass G x k Q A y m a.val = m t a.val.1 := by
    unfold choiceTraceMass
    rw [hin a,traceIndexMass_nil G x k Q (A a.val.1) (y a.val.1) a.val.2 a.property.2,mul_one]
  have hA (a : J) : t ∈ A a.val.1 := (hin a) ▸ a.val.2.1.property
  have he : finiteInverseLoad (choiceTraceOutput G x k Q A y)
      (fun a => if choiceTraceCode G x k Q A y a = [] then choiceTraceMass G x k Q A y m a else 0) t =
      ∑ a : J, m t a.val.1 := by
    unfold finiteInverseLoad
    simp only [← ite_and]
    change (∑ a : I, if S a then choiceTraceMass G x k Q A y m a else 0) = _
    calc
      _ = ∑ a : J, choiceTraceMass G x k Q A y m a.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by intro a; simp) _
      _ = _ := Finset.sum_congr rfl (fun a _ => hm' a)
  rw [he]
  have hb := sum_comp_le_sum_of_injective (fun a : J => a.val.1) hi
    (fun r => if t ∈ A r then m t r else 0) (by intro r; split_ifs; exact hm t r; exact le_refl _)
  simpa only [ite_eq_left (hA _)] using hb

end NoSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointNil
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRunArrival_integral {W : Type*} [Fintype W]
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunArrival (fun i => q (η i)) k z A) =
      oldRunArrival (fun _ => finiteOldKernel Q p q) k z A := by
  unfold oldRunArrival
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : oldRunVertices k z r 0 ∈ A
  · simp only [ite_eq_left h]
    exact oldRunWeight_integral Q p k q z r
  · simp [h,finiteFamilyIntegral]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationNilRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteInverseLoad (q.amplificationOutput Q B x k n)
      (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)) ω

 

theorem amplificationNilRow_arrival_le (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) :
    q.amplificationNilRow Q B x k n p ω ≤
      if n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        ∑ z : ↥B, oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z
          (Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x) else 0 := by
  let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
  let H := n ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧ (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  have hb (η : ℕ → Set E) :
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)
        (finiteFieldSet Q ω,η) ≤
      if H then ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0 := by
    apply (finiteChoiceNilLoad_le G x k Q (q.allAmplificationInputs Q B x k n)
      (fun r s => allAmplificationVertices B k r s.2)
      (fun s r => q.allAmplificationWeight B k r s.2)
      (fun s r => q.allAmplificationWeight_nonneg B k r s.2) (finiteFieldSet Q ω,η)).trans
    rw [Fintype.sum_prod_type]
    by_cases h : H
    · rw [ite_eq_left h]
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro r _
      by_cases hs : (finiteFieldSet Q ω,η) ∈ q.allAmplificationInputs Q B x k n (z,r)
      · rw [ite_eq_left hs]
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        have ha : oldRunVertices k z r 0 ∈ A := by
          simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,amplificationVertices] using hi.2.2.2.2.2.1
        rw [ite_eq_left ha]
        exact le_rfl
      · rw [ite_eq_right hs]
        split_ifs
        · exact oldRunWeight_nonneg _ (fun i a b => q.nonneg (η i) a.val b.val) k z r
        · exact le_refl _
    · rw [ite_eq_right h]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro z _
      apply Finset.sum_eq_zero
      intro r _
      rw [ite_eq_right (by
        intro hs
        have hi := (q.mem_amplificationInputs Q B x k n z r _).mp hs
        exact h ⟨hi.2.2.2.1,hi.2.2.2.2.1⟩)]
  change _ ≤ if H then ∑ z : ↥B,
    oldRunArrival (fun _ => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)) k z A else 0
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if H then
        ∑ z : ↥B, oldRunArrival (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z A else 0) := by
      apply Finset.sum_le_sum
      intro η _
      exact mul_le_mul_of_nonneg_left (hb _) (finiteFamilyWeight_nonneg Q (Finset.Icc 1 k) p η)
    _ = _ := by
      by_cases h : H
      · simp only [ite_eq_left h,finiteFamilyIntegral_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact oldRunArrival_integral Q p k (fun η (a b : ↥B) => q.mass η a.val b.val) z A
      · simp only [ite_eq_right h,finiteFamilyIntegral,mul_zero,Finset.sum_const_zero]

end LocalEndpointRule
end AllEndpointNil

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNilBound
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationNilRow_nonneg {O : Set V} (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) :
    0 ≤ q.amplificationNilRow Q B x k n p ω := by
  apply finiteRootLoad_nonneg
  intro s _
  apply finiteInverseLoad_nonneg
  intro a
  split_ifs
  · exact q.amplificationMass_nonneg Q B x k n a
  all_goals exact le_refl _

 

theorem amplificationNilRow_bound {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    q.amplificationNilRow Q B x k n p ω ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k := by
  apply (q.amplificationNilRow_arrival_le Q B x k n p ω).trans
  split_ifs with h
  · let A : Finset ↥B := Finset.univ.filter fun a : ↥B => a.val ∈ cluster G (finiteFieldSet Q ω) x
    let K := fun (_ : ℕ) => finiteOldKernel Q p (fun η (a b : ↥B) => q.mass η a.val b.val)
    have hK (i : ℕ) (a b : ↥B) : K i a b = q.kernel p a.val b.val :=
      q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)
    have hnK (i : ℕ) (a b : ↥B) : 0 ≤ K i a b := by rw [hK i a b]; exact q.kernel_nonneg p a.val b.val
    have hc (i : ℕ) (b : ↥B) : (∑ a, K i a b) ≤ q.successProbability p (root i₀) := by
      simp only [hK]
      rw [Finset.sum_coe_sort B (fun a => q.kernel p a b.val)]
      exact ((q.summable_kernel_column p b.val).sum_le_tsum B (fun a _ => q.kernel_nonneg p a b.val)).trans
        (q.kernel_column_le_success root weight Γ htr hΓ hw i₀ hw₀ p b.val)
    have hf : (cluster G (finiteFieldSet Q ω) x).Finite := cluster_finite_of_finite_edges G
      ω.val.finite_toSet x
    have hcard : A.card ≤ 2*n := by
      have hh : A.card ≤ hf.toFinset.card := Finset.card_le_card_of_injOn Subtype.val
        (by intro a ha; exact hf.mem_toFinset.mpr (Finset.mem_filter.mp ha).2)
        (fun _ _ _ _ he => Subtype.val_injective he)
      rw [← Set.ncard_eq_toFinset_card (cluster G (finiteFieldSet Q ω) x) hf] at hh
      exact hh.trans h.2.le
    calc
      _ ≤ (A.card:ℝ) * q.successProbability p (root i₀)^k :=
        sum_oldRunArrival_le K hnK _ (q.successProbability_nonneg p (root i₀)) hc k A
      _ ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (q.successProbability_nonneg p (root i₀)) _)

end LocalEndpointRule
end AllEndpointNilBound

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNear
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationAdded (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) : Set V :=
  cluster G (q.amplificationOutput Q B x k n a).1 x \ cluster G (q.amplificationInput Q B x k n a).1 x

noncomputable def amplificationNearPairMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) : ℝ :=
  ∑ a : q.AmplificationIndex Q B x k n, ∑ b : q.AmplificationIndex Q B x k n,
    if (q.amplificationOutput Q B x k n a).1 = (q.amplificationOutput Q B x k n b).1 ∧
      q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
      ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (q.amplificationOutput Q B x k n a) (q.amplificationOutput Q B x k n b)) *
        q.amplificationMass Q B x k n a * q.amplificationMass Q B x k n b else 0

 

theorem amplificationNearPairMass_bound [Nonempty E]
    (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n d : ℕ) (p : unitInterval)
    (hdeg : ∀ a, degree G a ≤ d) :
    q.amplificationNearPairMass Q B x k n p ≤
      (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k *
        ∑ a : q.AmplificationIndex Q B x k n,
          spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
            q.amplificationMass Q B x k n a := by
  let out := q.amplificationOutput Q B x k n
  let code := q.amplificationCode Q B x k n
  let added := q.amplificationAdded Q B x k n
  let m := q.amplificationMass Q B x k n
  let e (a : q.AmplificationIndex Q B x k n) := (code a).headD (0,Classical.choice ‹Nonempty E›) |>.2
  have hfin (a : q.AmplificationIndex Q B x k n) : (cluster G (out a).1 x).Finite :=
    (q.amplificationIndex_support Q B x k n a).2.2.2.1
  have hhead (a : q.AmplificationIndex Q B x k n) (hc : code a ≠ []) :
      OpenMarkedPivotal G (out a).1 {a.1.1.val} x (e a) ∧
      hangingSide G (out a).1 x (e a) = added a ∧
      (hangingSide G (out a).1 x (e a)).ncard ≤ k*M := by
    cases hh : code a with
    | nil => exact (hc hh).elim
    | cons w rest =>
      have ht := q.amplificationIndex_trace Q B x k n a
      change SpliceTrace G x (q.amplificationInput Q B x k n a).2
        (amplificationVertices B k a.1.1 a.1.2) k 0 (q.amplificationInput Q B x k n a).1
        (code a) (out a).1 at ht
      rw [hh] at ht
      have he : e a = w.2 := by simp only [e,hh,List.headD_cons]
      rw [he]
      refine ⟨?_,ht.head_hanging G x _ _ k 0 w.1 _ _ w.2 rest,
        ht.head_hanging_cap G x _ _ k 0 w.1 M _ _ w.2 rest (q.amplificationIndex_caps Q B x k n a)⟩
      simpa only [amplificationVertices,oldRunVertices_last] using
        ht.seams_pivotal G x _ _ k 0 _ _ (w::rest) w (List.mem_cons_self)
  let S (a : q.AmplificationIndex Q B x k n) : Finset V := if code a = [] then ∅ else
    nearHangingEndpoints G hloc (out a).1 x a.1.1.val (e a) (k*M) (hfin a)
  let R (a b : q.AmplificationIndex Q B x k n) := code a ≠ [] ∧ code b ≠ [] ∧
    ¬GraphSeparated G (added a) (added b)
  have hS (a b : q.AmplificationIndex Q B x k n) (he : (out a).1 = (out b).1) (h : R a b) :
      b.1.1.val ∈ S a := by
    obtain ⟨hpa,hea,_⟩ := hhead a h.1
    obtain ⟨hpb,heb,hcb⟩ := hhead b h.2.1
    have hn := h.2.2
    rw [← hea,← heb,← he] at hn
    rw [← he] at hpb hcb
    simp only [S,ite_eq_right h.1]
    exact mem_nearHangingEndpoints_of_not_separated G hloc (out a).1 x a.1.1.val b.1.1.val
      (e a) (e b) (k*M) (hfin a) hpa hpb hcb hn
  have hN (a : q.AmplificationIndex Q B x k n) : (S a).card ≤ (k*M)+(k*M)^2+d*(k*M)^3 := by
    by_cases h : code a = []
    · simp only [S,ite_eq_left h,Finset.card_empty,Nat.zero_le]
    · simp only [S,ite_eq_right h]
      exact nearHangingEndpoints_card_le G hloc (out a).1 x a.1.1.val (e a) (k*M) d
        (hfin a) (hhead a h).2.2 hdeg
  have hC : 0 ≤ inverseCodeMass M L ^ k := pow_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => gapWeight_nonneg L (by linarith) l)) _
  simpa only [amplificationNearPairMass,out,m,R,added] using finite_near_pair_mass_le Q (Finset.Icc 1 k) (Finset.Icc 1 k) p out out m m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationMass_nonneg Q B x k n)
    (fun a => a.1.1.val) R S hS ((k*M)+(k*M)^2+d*(k*M)^3) hN _ hC
    (fun a z _ => q.amplificationEndpointMass_bound hL Q B x k n p (out a).1
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) (out a)).mp (q.amplificationOutput_mem Q B x k n a)).1 z)

end LocalEndpointRule
end AllEndpointNear

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteThreeClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def commonRootPairMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (m : I → ℝ) (P : I → I → Prop) : ℝ :=
  ∑ a, ∑ b, if (out a).1 = (out b).1 ∧ P a b then
    jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b else 0

 

theorem finiteRootLoad_three_classes_le {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (out : I → SpliceState E)
    (m : I → ℝ) (hm : ∀ a, 0 ≤ m a) (hs : ∀ a, out a ∈ finiteSpliceDomain Q J)
    (C : I → Prop) (R : I → I → Prop) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J p (finiteInverseLoad out m) ω ^ 2) ≤
      2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        finiteRootLoad Q J p (finiteInverseLoad out (fun a => if C a then m a else 0)) ω *
        finiteRootLoad Q J p (finiteInverseLoad out m) ω) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ R a b) +
      commonRootPairMass Q J p out m (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) := by
  let m₀ := fun a => if C a then m a else 0
  let row := finiteRootLoad Q J p (finiteInverseLoad out m)
  let nilrow := finiteRootLoad Q J p (finiteInverseLoad out m₀)
  have hcross : (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) =
      ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω := by
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have heq : 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) =
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) +
      (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω * nilrow ω) := by
    rw [hcross]; ring
  change _ ≤ 2 * (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω) + _ + _
  rw [heq]
  dsimp only [nilrow,row]
  simp only [pow_two,← mul_assoc]
  rw [finiteRootLoad_pair_expansion Q J J p out out m m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m₀ m hs hs,
    finiteRootLoad_pair_expansion Q J J p out out m m₀ hs hs]
  unfold commonRootPairMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hw : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) :=
    jointTupleWeight_nonneg Q J J p _
  have ht : 0 ≤ jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b :=
    mul_nonneg (mul_nonneg hw (hm a)) (hm b)
  dsimp only [m₀]
  by_cases hab : (out a).1 = (out b).1
  · simp only [hab,true_and,ite_true]
    by_cases ha : C a <;> by_cases hb : C b <;> by_cases hr : R a b <;>
      simp only [ha,hb,hr,not_true_eq_false,not_false_eq_true,and_true,and_false,
        ite_true,ite_false,mul_zero,zero_mul] <;> linarith
  · simp only [hab,false_and,ite_false,zero_add,le_refl]

end FiniteThreeClass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointMomentIdentities
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteRootLoad_inverse_mean {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p (finiteInverseLoad out m) ω) =
      ∑ a, spliceTupleWeight Q J p (out a) * m a := by
  rw [finiteRootLoad_mean]
  simp only [finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq,ite_eq_left (hs a)]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem amplificationRow_nonneg (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationRow Q B x k n p ω := by
  rw [q.amplificationRow_eq_load]
  apply finiteRootLoad_nonneg
  intro s _
  exact finiteInverseLoad_nonneg _ _ (q.amplificationMass_nonneg Q B x k n) s

theorem amplificationRow_mean_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) =
      ∑ a : q.AmplificationIndex Q B x k n,
        spliceTupleWeight Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n a) *
          q.amplificationMass Q B x k n a := by
  simp only [finiteFieldIntegral,q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  exact finiteRootLoad_inverse_mean Q (Finset.Icc 1 k) p _ _ (q.amplificationOutput_mem Q B x k n)

 

theorem amplificationSeparated_class_eq (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) :
    commonRootPairMass Q (Finset.Icc 1 k) p (q.amplificationOutput Q B x k n)
      (q.amplificationMass Q B x k n) (fun a b =>
        q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
        GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)) =
    finiteChoiceSeparatedPairMass G x k Q p
      (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
      (allAmplificationVertices B k) (allAmplificationVertices B k)
      (q.allAmplificationWeight B k) (q.allAmplificationWeight B k) := by
  unfold commonRootPairMass finiteChoiceSeparatedPairMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with ha hb hb
  · rfl
  · exfalso
    apply hb
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput] at ha
    rcases ha with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · exfalso
    apply ha
    dsimp only [amplificationAdded,amplificationOutput,amplificationCode,amplificationInput]
    rcases hb with ⟨he,hca,hcb,hsep⟩
    refine ⟨he,hca,hcb,?_⟩
    simpa only [he] using hsep
  · rfl

end LocalEndpointRule
end AllEndpointMomentIdentities

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationRow_second_moment_le [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x : V) (k n d : ℕ)
    (hdeg : ∀ a, degree G a ≤ d)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a (max q.radius M)).toFinset ⊆ Q) :
    finiteFieldIntegral Q p (fun ω => q.amplificationRow Q B x k n p ω ^ 2) ≤
      (((4*n:ℕ):ℝ) * q.successProbability p (root i₀)^k +
        (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) * inverseCodeMass M L ^ k) *
          finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) +
      (((2*n:ℕ):ℝ) * (c*((k*M:ℕ)*q.successProbability p (root i₀)^k)))^2 *
        finiteClusterWindowMass G Q p x (n-k*M) (2*n) := by
  let out := q.amplificationOutput Q B x k n
  let m := q.amplificationMass Q B x k n
  let C := fun a => q.amplificationCode Q B x k n a = []
  let R := fun a b => ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
  let row := finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out m)
  let nilrow := q.amplificationNilRow Q B x k n p
  let b₀ := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω
  let bnil := ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * nilrow ω * row ω
  let S := finiteChoiceSeparatedPairMass G x k Q p
    (q.allAmplificationInputs Q B x k n) (q.allAmplificationInputs Q B x k n)
    (allAmplificationVertices B k) (allAmplificationVertices B k)
    (q.allAmplificationWeight B k) (q.allAmplificationWeight B k)
  have hrow (ω : FiniteField Q) : q.amplificationRow Q B x k n p (finiteFieldSet Q ω) = row ω := by
    rw [q.amplificationRow_eq_load,restrictFiniteField_fieldSet]
  have hmean : finiteFieldIntegral Q p (q.amplificationRow Q B x k n p) = b₀ := by
    simp only [finiteFieldIntegral,hrow,b₀]
  have hpart := finiteRootLoad_three_classes_le Q (Finset.Icc 1 k) p out m
    (q.amplificationMass_nonneg Q B x k n) (q.amplificationOutput_mem Q B x k n) C R
  have hnear_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ R a b) = q.amplificationNearPairMass Q B x k n p := by
    simp only [commonRootPairMass,amplificationNearPairMass,C,R,out,m]
  have hsep_eq : commonRootPairMass Q (Finset.Icc 1 k) p out m
      (fun a b => ¬C a ∧ ¬C b ∧ ¬R a b) = S := by
    simpa only [C,R,not_not] using q.amplificationSeparated_class_eq Q B x k n p
  rw [hnear_eq,hsep_eq] at hpart
  have hnilfun : finiteInverseLoad out (fun a => @ite ℝ (C a) (Classical.propDecidable _) (m a) 0) =
      finiteInverseLoad (q.amplificationOutput Q B x k n)
        (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0) := by
    apply congrArg (finiteInverseLoad out)
    funext a
    dsimp only [C,m]
    split_ifs <;> rfl
  rw [hnilfun] at hpart
  change (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * row ω ^ 2) ≤
    2*bnil + q.amplificationNearPairMass Q B x k n p + S at hpart
  have hnil : bnil ≤ ((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k * b₀ := by
    dsimp only [bnil,b₀]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    have hr : 0 ≤ row ω := by rw [← hrow]; exact q.amplificationRow_nonneg Q B x k n p _
    have hn := q.amplificationNilRow_bound root weight Γ htr (fun a ha => hΓ ha) hw i₀ hw₀ Q B x k n p ω
      (fun a ha => (incidentSupport_ball_mono G hloc a (le_max_left _ _)).trans (hQ a ha))
    calc
      _ ≤ finiteFieldWeight Q p ω * (((2*n:ℕ):ℝ) * q.successProbability p (root i₀)^k) * row ω :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (finiteFieldWeight_nonneg Q p ω)) hr
      _ = _ := by ring
  have hnear := q.amplificationNearPairMass_bound hL Q B x k n d p hdeg
  rw [← q.amplificationRow_mean_eq Q B x k n p,hmean] at hnear
  have hsep := q.amplificationSeparatedSecondMoment_le hconn root weight Γ hΓ htr hcov hw hw1 c hc hmin
    (root i₀) Q B p x k n hQ
  have hfinal := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hnil (show (0:ℝ) ≤ 2 by norm_num)) hnear) hsep
  rw [hmean]
  simp only [finiteFieldIntegral,hrow]
  apply hpart.trans
  convert hfinal using 1
  push_cast
  ring

end LocalEndpointRule
end AllEndpointSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (b ⁻¹' ω) x = a ⁻¹' cluster G ω (a x) := by
  ext y
  exact conn_aut_iff G hab ω x y

theorem exchangeOn_preimage (b : E ≃ E) (mask ω η : Set E) :
    exchangeOn (b ⁻¹' mask) (b ⁻¹' ω) (b ⁻¹' η) = b ⁻¹' exchangeOn mask ω η := by
  rfl

theorem spliceMask_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) :
    spliceMask G (a ⁻¹' S) (a ⁻¹' B) e = b ⁻¹' spliceMask G S B (b e) := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq,Set.mem_preimage,b.injective.eq_iff]
  apply or_congr_right
  have hi : internalEdges G (a ⁻¹' S)ᶜ = b ⁻¹' internalEdges G Sᶜ :=
    internalEdges_aut_preimage G hab Sᶜ
  rw [hi]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨v,hv,hvf⟩
    refine ⟨a v,hv,?_⟩
    rw [hab f]
    exact Sym2.mem_map.mpr ⟨v,hvf,rfl⟩
  · rintro ⟨v,hv,hvf⟩
    rw [hab f] at hvf
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hvf
    exact ⟨w,hv,hw⟩

theorem spliceField_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) (ω η : Set E) :
    spliceField G (a ⁻¹' S) (a ⁻¹' B) e (b ⁻¹' ω) (b ⁻¹' η) =
      b ⁻¹' spliceField G S B (b e) ω η := by
  rw [spliceField,spliceMask_aut_preimage G hab,exchangeOn_preimage]
  rfl

theorem seamContactCount_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => b ⁻¹' η j) y (b ⁻¹' ωf) x i e =
      seamContactCount G η (fun j => a (y j)) ωf (a x) i (b e) := by
  have he : (b ⁻¹' ωf) \ {e} = b ⁻¹' (ωf \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  unfold seamContactCount
  rw [he,cluster_aut_preimage G hab]
  rw [show (a ⁻¹' cluster G (ωf \ {b e}) (a x))ᶜ =
    a ⁻¹' (cluster G (ωf \ {b e}) (a x))ᶜ from rfl]
  rw [internalEdges_aut_preimage G hab,← Set.preimage_inter,cluster_aut_preimage G hab,
    contactSet_aut_preimage G hab,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun f _ => b.surjective f

theorem traceContactCount_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V)
    (c : List (ℕ × E)) (i : ℕ) :
    traceContactCount G (fun j => b ⁻¹' η j) y (b ⁻¹' ωf) x c i =
      traceContactCount G η (fun j => a (y j)) ωf (a x) (c.map (Prod.map id b)) i := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨j,e⟩
    simp only [traceContactCount,List.map_cons,Prod.map_apply,id_eq]
    split_ifs
    · exact seamContactCount_aut_preimage G hab η y ωf x j e
    · exact ih

end SpliceCovarianceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

def edgeFieldEquiv (b : E ≃ E) : Set E ≃ Set E where
  toFun ω := b.symm ⁻¹' ω
  invFun ω := b ⁻¹' ω
  left_inv ω := by ext e; simp
  right_inv ω := by ext e; simp

def spliceStateEquiv (b : E ≃ E) : SpliceState E ≃ SpliceState E :=
  (edgeFieldEquiv b).prodCongr (Equiv.piCongrRight fun _ => edgeFieldEquiv b)

def spliceCodeEquiv (b : E ≃ E) : List (ℕ × E) ≃ List (ℕ × E) :=
  Equiv.listEquivOfEquiv ((Equiv.refl ℕ).prodCongr b)

@[simp] theorem edgeFieldEquiv_apply (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b ω = b.symm ⁻¹' ω := rfl

@[simp] theorem spliceCodeEquiv_apply (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c = c.map (Prod.map id b) := rfl

theorem cluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (edgeFieldEquiv b ω) (a x) = a.symm ⁻¹' cluster G ω x := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    cluster_aut_preimage G (isAut_symm G hab) ω (a x)

theorem slitCluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) :
    cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y) =
      a.symm ⁻¹' cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y := by
  rw [cluster_edgeFieldEquiv G hab]
  rw [show (a.symm ⁻¹' cluster G ω x)ᶜ = a.symm ⁻¹' (cluster G ω x)ᶜ from rfl]
  rw [internalEdges_aut_preimage G (isAut_symm G hab),edgeFieldEquiv_apply,← Set.preimage_inter,
    cluster_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]

theorem spliceStep_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceField G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) (edgeFieldEquiv b ω) (edgeFieldEquiv b η) =
    edgeFieldEquiv b (spliceField G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e ω η) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab]
  rw [edgeFieldEquiv_apply,edgeFieldEquiv_apply,
    spliceField_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

 

theorem SpliceTrace.aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) (ht : SpliceTrace G x η y k j ω c ωf) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) := by
  induction ht with
  | stop j ω hs =>
    apply SpliceTrace.stop
    simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hs
  | step j i ω e v w rest ωf hn hji hik hmax hy he hev hv hw ht ih =>
    change SpliceTrace G (a x) _ _ k j _ ((i,b e)::spliceCodeEquiv b rest) _
    refine SpliceTrace.step j i _ (b e) (a v) (a w) _ _ ?_ hji hik ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hn
    · intro l hil hlk
      rw [cluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
        Set.disjoint_preimage_iff a.symm.surjective]
      exact hmax l hil hlk
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hy
    · simpa only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_apply_apply] using he
    · rw [hab e,hev,Sym2.map_mk]
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hv
    · simpa only [slitCluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hw
    · rw [spliceStep_edgeFieldEquiv G hab]
      exact ih

end SpliceCovarianceTrace

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceReplay
attribute [local instance] Classical.propDecidable Classical.decEq

theorem spliceStepMask_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceMask G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) =
    edgeFieldEquiv b (spliceMask G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
    spliceMask_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

theorem exchangeState_aut_map (b : E ≃ E) (mask : Set E) (i : ℕ) (s : SpliceState E) :
    exchangeState (edgeFieldEquiv b mask) i (spliceStateEquiv b s) =
      spliceStateEquiv b (exchangeState mask i s) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases hji : j = i
    · subst j
      rw [exchangeState_at]
      change _ = edgeFieldEquiv b ((exchangeState mask i s).2 i)
      rw [exchangeState_at]
      rfl
    · rw [exchangeState_away _ _ _ _ hji]
      change edgeFieldEquiv b (s.2 j) = edgeFieldEquiv b ((exchangeState mask i s).2 j)
      rw [exchangeState_away _ _ _ _ hji]

theorem replaySplice_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replaySplice G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    edgeFieldEquiv b (replaySplice G x η y c ω) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    change replaySplice G (a x) _ _ (spliceCodeEquiv b c) _ = _
    rw [spliceStep_edgeFieldEquiv G hab,ih]
    rfl

theorem replayMasks_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replayMasks G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    (replayMasks G x η y c ω).map (Prod.map id (edgeFieldEquiv b)) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,replayMasks]
    rw [spliceStepMask_edgeFieldEquiv G hab,spliceStep_edgeFieldEquiv G hab]
    exact congrArg (List.cons _) (ih _)

theorem runMasks_aut_map (b : E ≃ E) (c : List (ℕ × Set E)) (s : SpliceState E) :
    runMasks (c.map (Prod.map id (edgeFieldEquiv b))) (spliceStateEquiv b s) =
      spliceStateEquiv b (runMasks c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,mask⟩
    simp only [List.map_cons,Prod.map_apply,id_eq,runMasks]
    rw [exchangeState_aut_map,ih]

theorem seamContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) i (b e) = seamContactCount G η y ωf x i e := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    seamContactCount_aut_preimage G (isAut_symm G hab) η (fun j => a (y j)) ωf (a x) i (b e)

theorem traceContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V)
    (c : List (ℕ × E)) (i : ℕ) :
    traceContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) (spliceCodeEquiv b c) i =
      traceContactCount G η y ωf x c i := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨j,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,traceContactCount]
    split_ifs
    · exact seamContactCount_aut_map G hab η y ωf x j e
    · exact ih

end SpliceCovarianceReplay

end Percolation

end OAI
