import Mathlib
import OAI.Probability.UnimodularPercolation.Transport.EndpointKernels

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def restrictFiniteField (Q : Finset E) (ω : Set E) : FiniteField Q :=
  ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩

@[simp] theorem finiteFieldSet_restrict (Q : Finset E) (ω : Set E) :
    finiteFieldSet Q (restrictFiniteField Q ω) = ω ∩ (Q : Set E) := by
  ext e
  simp [restrictFiniteField,domainBits,finiteFieldSet,and_comm]

@[simp] theorem restrictFiniteField_fieldSet (Q : Finset E) (ω : FiniteField Q) :
    restrictFiniteField Q (finiteFieldSet Q ω) = ω := by
  apply Subtype.ext
  exact domainBits_finiteFieldSet Q ω

theorem cluster_restrict_of_cap (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (C : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x C).toFinset ⊆ Q)
    (hf : (cluster G (ω ∩ (Q : Set E)) x).Finite)
    (hC : (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ C) :
    cluster G (ω ∩ (Q : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have ha := finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hf C hC ih
      have heQ := hQ ((mem_incidentSupport G hloc _ e).mpr
        ⟨a,by simpa only [Set.Finite.mem_toFinset] using ha,by simp [hab]⟩)
      exact ih.tail ⟨e,⟨he,heQ⟩,hab⟩

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

noncomputable def amplificationMarginal (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
      (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z)) (restrictFiniteField Q ω)

theorem amplificationMarginal_local (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q B x k n z p ω =
      q.amplificationMarginal Q B x k n z p (ω ∩ (Q : Set E)) := by
  unfold amplificationMarginal
  congr 1
  apply (finiteFieldSet_injective Q)
  simp only [finiteFieldSet_restrict,Set.inter_assoc,Set.inter_self]

theorem amplificationMarginal_bounds (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationMarginal Q B x k n z p ω ∧
      q.amplificationMarginal Q B x k n z p ω ≤ inverseCodeMass M L ^ k := by
  have hb := finiteChoiceForwardLoad_bounds G hloc x z.val k M L hL Q
    (q.amplificationInputs Q B x k n z) (fun r _ => amplificationVertices B k z r)
    (q.amplificationWeight B k z) (q.amplificationWeight_nonneg B k z)
    (q.amplificationWeight_row B k z) (q.amplificationInputs_subset Q B x k n z)
    (fun _ _ _ => congrArg Subtype.val (oldRunVertices_last ..))
    (fun r s hs i hi hik => (q.amplificationInputs_chain Q B x k n z r s hs i hi hik).2)
  exact ⟨finiteRootLoad_nonneg _ _ p _ (fun s _ => (hb s).1) _,
    finiteRootLoad_le _ _ p _ _ (fun s _ => (hb s).2) _⟩

theorem amplificationMarginal_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G (ω ∩ (Q : Set E)) x z.val ∧
      (cluster G (ω ∩ (Q : Set E)) x).Finite ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ 2*n+k*M := by
  let A := q.amplificationInputs Q B x k n z
  let y := fun r (_ : SpliceState E) => amplificationVertices B k z r
  let I := FiniteChoiceTraceIndex G x k Q A y
  let out := choiceTraceOutput G x k Q A y
  have ho (a : I) : out a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    traceIndexOutput_mem G x k Q (A a.1) (y a.1) (q.amplificationInputs_subset Q B x k n z a.1) a.2
  have he := finiteRootLoad_eq_sum Q (Finset.Icc 1 k) p out
    (choiceTraceMass G x k Q A y (q.amplificationWeight B k z)) ho (restrictFiniteField Q ω)
  have ha : ∃ a : I, (out a).1 = ω ∩ (Q : Set E) := by
    by_contra hn
    push Not at hn
    apply h
    change finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out _) _ = 0
    rw [he,finiteFieldSet_restrict]
    simp only [hn,ite_false,Finset.sum_const_zero]
  obtain ⟨a,ha⟩ := ha
  have ht := (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1
  have hs := q.amplificationTrace_support Q B x k n z a.1 a.2.1.val a.2.1.property
    (choiceTraceCode G x k Q A y a) (out a).1 ht
  rwa [ha] at hs

theorem amplificationMarginal_physical_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n+k*M)).toFinset ⊆ Q)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ω x z.val ∧ (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ 2*n+k*M := by
  obtain ⟨hx,hz,hc,hf,hcap⟩ := q.amplificationMarginal_support Q B x k n z p ω h
  have he := cluster_restrict_of_cap G hloc Q ω x (2*n+k*M) hQ hf hcap
  exact ⟨hx,hz,conn_mono G Set.inter_subset_left hc,he ▸ hf,he ▸ hcap⟩

 

theorem amplificationMarginal_mean [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r, ∑ s ∈ q.amplificationInputs Q B x k n z r,
        spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r := by
  rw [integral_finite_local Q p _ (q.amplificationMarginal_local Q B x k n z p)]
  simp only [amplificationMarginal,restrictFiniteField_fieldSet]
  rw [finiteRootLoad_mean]
  apply finiteChoiceForwardLoad_mean G hloc x k M Q p
  · exact q.amplificationInputs_subset Q B x k n z
  · intro r s hs
    exact ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.1
  · intro r s hs i hi
    exact (q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1
  · intro r s hs i hi
    have hc := q.amplificationInputs_chain Q B x k n z r s hs i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
    exact ⟨hc.2.1,hc.2.2.1⟩

end LocalEndpointRule
end AmplificationMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMeanKernel
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finiteSpliceDomain_integral_factor (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : Set E → ℝ) (g : (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s.1 * g s.2) =
      finiteFieldIntegral Q p f * finiteFamilyIntegral Q J p g := by
  have hh := finiteRootLoad_mean Q J p (fun s => f s.1 * g s.2)
  simp only [← mul_assoc] at hh
  rw [← hh]
  simp only [finiteRootLoad,finiteFieldIntegral,finiteFamilyIntegral,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

 
noncomputable def finiteBinConnection (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (n : ℕ) (y : V) : ℝ := finiteFieldIntegral Q p (fun ω =>
      if n ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < 2*n ∧ y ∈ cluster G ω x then 1 else 0)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem finiteOldKernel_eq_kernel (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (p : unitInterval) (a b : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    finiteOldKernel Q p q.mass a b = q.kernel p a b := by
  symm
  exact integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.locality · a b))

 

theorem amplificationMarginal_mean_kernel [Nonempty E] (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ O) (hz : z.val ∈ O)
    (hQ : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) =
      ∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
        oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r := by
  rw [q.amplificationMarginal_mean Q B x k n z p]
  apply Finset.sum_congr rfl
  intro r _
  let f : Set E → ℝ := fun ω => if n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ amplificationVertices B k z r 0 ∈ cluster G ω x then 1 else 0
  let g : (ℕ → Set E) → ℝ := fun η =>
    oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k z r
  have he : (∑ s ∈ q.amplificationInputs Q B x k n z r,
      spliceTupleWeight Q (Finset.Icc 1 k) p s * q.amplificationWeight B k z s r) =
      ∑ s ∈ finiteSpliceDomain Q (Finset.Icc 1 k), spliceTupleWeight Q (Finset.Icc 1 k) p s * f s.1 * g s.2 := by
    rw [amplificationInputs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    change (if _ then _ else _) = _
    by_cases hw : q.amplificationWeight B k z s r = 0
    · have hg : g s.2 = 0 := hw
      simp [hx,hz,hw,hg]
    · simp only [hx,hz,true_and,hw,ne_eq,not_false_eq_true,and_true]
      by_cases hbin : n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
          amplificationVertices B k z r 0 ∈ cluster G s.1 x
      · simp [f,hbin,g,amplificationWeight]
      · simp only [hbin,ite_false,f,mul_zero,zero_mul]
  rw [he,finiteSpliceDomain_integral_factor]
  dsimp only [g]
  rw [oldRunWeight_integral Q p k (fun ω (a b : ↥B) => q.mass ω a.val b.val) z r]
  change finiteBinConnection G Q p x n _ * _ = _
  congr 1
  apply congrArg (fun K : ℕ → ↥B → ↥B → ℝ => oldRunWeight K k z r)
  funext i a b
  exact q.finiteOldKernel_eq_kernel Q p a.val b.val (hQ a.val a.property)

end LocalEndpointRule
end AmplificationMeanKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def binConnectionMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  if (cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n ∧ Conn G ω x y then 1 else 0

theorem binConnectionMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    0 ≤ binConnectionMass G n ω x y := by unfold binConnectionMass; split_ifs <;> norm_num

theorem binConnectionMass_symm (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n ω x y = binConnectionMass G n ω y x := by
  by_cases hc : Conn G ω x y
  · have he := cluster_eq_of_conn G ω hc
    simp only [binConnectionMass,hc,conn_symm G ω hc,and_true,he]
  · have hc' : ¬Conn G ω y x := fun h => hc (conn_symm G ω h)
    simp only [binConnectionMass,hc,hc',and_false,ite_false]

theorem binConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binConnectionMass G n ω x y = binConnectionMass G n (ω ∩ (Q : Set E)) x y := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
  have hp : ((cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
      (cluster G ω x).ncard < 2*n ∧ Conn G ω x y) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard < 2*n ∧ Conn G (ω ∩ (Q : Set E)) x y) := by
    constructor
    · rintro ⟨hf,hn,hN,hc⟩
      have hs : cluster G ω x ⊆ (finite_reachBall hloc x (2*n)).toFinset := by
        simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf (2*n) hN.le
      have he := cluster_restrict_incident_of_full G hloc _ ω x hs
      change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
      refine ⟨he.symm ▸ hf,he.symm ▸ hn,he.symm ▸ hN,?_⟩
      change y ∈ cluster G (ω ∩ (Q : Set E)) x
      rw [he]
      exact hc
    · rintro ⟨hf,hn,hN,hc⟩
      have he := cluster_restrict_of_cap G hloc Q ω x (2*n) (Finset.Subset.refl _) hf hN.le
      exact ⟨he ▸ hf,he ▸ hn,he ▸ hN,conn_mono G Set.inter_subset_left hc⟩
  exact if_congr hp rfl rfl

theorem binConnectionMass_support (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (h : binConnectionMass G n ω x y ≠ 0) :
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard < 2*n ∧ Conn G ω x y := by
  unfold binConnectionMass at h
  split_ifs at h with hp
  · exact ⟨hp.1,hp.2.2.1,hp.2.2.2⟩
  · exact (h rfl).elim

theorem binConnectionMass_outside (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnectionMass G n ω x y = 0 := by
  by_contra h
  obtain ⟨hf,hN,hc⟩ := binConnectionMass_support G n ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hf (2*n) hN.le hc)

theorem binConnectionMass_row (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) :
    (∑' y, binConnectionMass G n ω x y) ≤ 2*n := by
  by_cases hb : (cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < 2*n
  · have hs : (∑' y, binConnectionMass G n ω x y) = (cluster G ω x).ncard := by
      rw [tsum_eq_sum (s := hb.1.toFinset) (fun y hy => by
        have hc : ¬Conn G ω x y := fun h => hy (hb.1.mem_toFinset.mpr h)
        simp only [binConnectionMass,hc,and_false,ite_false])]
      have he : (∑ y ∈ hb.1.toFinset, binConnectionMass G n ω x y) =
          ∑ _y ∈ hb.1.toFinset, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact ite_eq_left ⟨hb.1,hb.2.1,hb.2.2,hb.1.mem_toFinset.mp hy⟩
      rw [he]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
      exact_mod_cast (Set.ncard_eq_toFinset_card _ hb.1).symm
    rw [hs]
    exact_mod_cast hb.2.2.le
  · have hz (y : V) : binConnectionMass G n ω x y = 0 := by
      apply ite_eq_right
      exact fun h => hb ⟨h.1,h.2.1,h.2.2.1⟩
    simp only [hz,tsum_zero]
    positivity

noncomputable def binConnection (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binConnectionMass G n ω x y ∂law p

theorem binConnection_nonneg (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    0 ≤ binConnection G p n x y := integral_nonneg fun ω => binConnectionMass_nonneg G n ω x y

theorem binConnection_symm (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) :
    binConnection G p n x y = binConnection G p n y x :=
  integral_congr_ae (ae_of_all _ fun ω => binConnectionMass_symm G n ω x y)

theorem binConnection_outside (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binConnection G p n x y = 0 := by
  simp only [binConnection,fun ω => binConnectionMass_outside G n ω x y hy,integral_zero]

theorem binConnection_row (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x : V) : (∑' y, binConnection G p n x y) ≤ 2*n := by
  let B := (finite_reachBall hloc x (2*n)).toFinset
  let Q := incidentSupport G hloc B
  have hi (y : V) : Integrable (fun ω => binConnectionMass G n ω x y) (law p) :=
    integrable_finite_local Q p _ (fun ω => binConnectionMass_local G hloc n ω x y)
  have he (ω : Set E) : (∑' y, binConnectionMass G n ω x y) = ∑ y ∈ B, binConnectionMass G n ω x y :=
    tsum_eq_sum fun y hy => binConnectionMass_outside G n ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have hs : (∑' y, binConnection G p n x y) = ∑ y ∈ B, binConnection G p n x y :=
    tsum_eq_sum fun y hy => binConnection_outside G p n x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  rw [hs]
  simp only [binConnection]
  rw [← integral_finsetSum B (fun y _ => hi y)]
  calc
    _ ≤ ∫ _ω, (2*n : ℝ) ∂law p := integral_mono (integrable_finsetSum B (fun y _ => hi y))
      (integrable_const _) (fun ω => (he ω).symm ▸ binConnectionMass_row G n ω x)
    _ = 2*n := by simp

 

theorem exists_binConnection_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ 2*n ∧
      ∀ x y, A (lp.single 2 y (1:ℂ)) x = (binConnection G p n x y : ℂ) := by
  have hs (x : V) : Summable (binConnection G p n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
    intro y hy
    exact binConnection_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, binConnection G p n x y) ≤ 2*n :=
    ((hs x).sum_le_tsum S (fun y _ => binConnection_nonneg G p n x y)).trans (binConnection_row G hloc p n x)
  apply exists_operator_of_row_column_bound (binConnection G p n) (2*n) (by positivity) (binConnection_nonneg G p n) hr
  intro y S
  simpa only [binConnection_symm G p n] using hr y S

end BinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteBinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteBinConnection_eq_binConnection (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (n : ℕ) (y : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q) :
    finiteBinConnection G Q p x n y = binConnection G p n x y := by
  rw [binConnection, integral_finite_local Q p _
    (finite_local_of_subset _ Q hQ _ (fun ω => binConnectionMass_local G hloc n ω x y))]
  unfold finiteBinConnection finiteFieldIntegral
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hf : (cluster G (finiteFieldSet Q ω) x).Finite :=
    cluster_finite_of_finite_edges G ω.val.finite_toSet x
  unfold cluster at hf
  simp only [binConnectionMass,cluster,Set.mem_ofPred_eq,hf,true_and]
  exact if_congr Iff.rfl rfl rfl

end FiniteBinConnection

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 
def PositiveRealMatrix (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (matrixCoeff A x y).im = 0 ∧ 0 ≤ (matrixCoeff A x y).re

namespace PositiveRealMatrix
variable {A H : Hilbert V →L[ℂ] Hilbert V}

theorem real (hA : PositiveRealMatrix A) (x y : V) :
    matrixCoeff A x y = ((matrixCoeff A x y).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (hA x y).1

theorem mul_hasSum (hA : PositiveRealMatrix A) (H : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    HasSum (fun z => (matrixCoeff A x z).re * (matrixCoeff H z y).re)
      (matrixCoeff (A*H) x y).re := by
  have h := Complex.reCLM.hasSum (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x)
  change HasSum (fun z => (matrixCoeff A x z * matrixCoeff H z y).re)
    (matrixCoeff (A*H) x y).re at h
  simpa only [Complex.mul_re,(hA _ _).1,zero_mul,sub_zero] using h

theorem mul (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H) :
    PositiveRealMatrix (A*H) := by
  intro x y
  constructor
  · have hs := (operator_kernel_hasSum A (H (lp.single 2 y (1:ℂ))) x).summable
    change Summable (fun z => matrixCoeff A x z * matrixCoeff H z y) at hs
    rw [matrixCoeff_mul,Complex.im_tsum hs]
    simp only [Complex.mul_im,(hA _ _).1,(hH _ _).1,mul_zero,zero_mul,add_zero,tsum_zero]
  · rw [← (hA.mul_hasSum H x y).tsum_eq]
    exact tsum_nonneg fun z => mul_nonneg (hA x z).2 (hH z y).2

theorem one : PositiveRealMatrix (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro x y
  simp only [matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply]
  split_ifs <;> norm_num

theorem pow (hA : PositiveRealMatrix A) (k : ℕ) : PositiveRealMatrix (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (V := V))
  | succ k ih => rw [pow_succ]; exact ih.mul hA

theorem star (hA : PositiveRealMatrix A) : PositiveRealMatrix (star A) := by
  intro x y
  simpa only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_im,Complex.conj_re,neg_eq_zero] using hA y x

end PositiveRealMatrix

 

theorem oldRun_test_succ {W : Type*} [Fintype W]
    (K : ℕ → W → W → ℝ) (F : W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, oldRunWeight K (k+1) z r * F (oldRunVertices (k+1) z r 0)) =
      ∑ a : W, K (k+1) z a *
        ∑ r : Fin k → W, oldRunWeight K k a r * F (oldRunVertices k a r 0) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * oldRunWeight K k r.1 r.2 * F (oldRunVertices k r.1 r.2 0))
      (by intro r; simp only [oldRunWeight,oldRunConsEquiv,Equiv.coe_fn_mk,
        oldRunVertices_succ_of_le k z r 0 (Nat.zero_le k)]), Fintype.sum_prod_type]
  simp only [Finset.mul_sum,mul_assoc]

 

theorem finite_oldRun_operator_domination (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hH : PositiveRealMatrix H)
    (B : Finset V) (k : ℕ) (z : ↥B) (x : V) :
    (∑ r : Fin k → ↥B,
      oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
        (matrixCoeff H (oldRunVertices k z r 0).val x).re) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  induction k generalizing z with
  | zero => simp [oldRunWeight,oldRunVertices]
  | succ k ih =>
    rw [oldRun_test_succ (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re)
      (fun a : ↥B => (matrixCoeff H a.val x).re) k z]
    calc
      _ ≤ ∑ a : ↥B, (matrixCoeff A z.val a.val).re * (matrixCoeff (A^k*H) a.val x).re :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih a) (hA z.val a.val).2
      _ ≤ ∑' a, (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re := by
        rw [Finset.sum_coe_sort B (fun a => (matrixCoeff A z.val a).re * (matrixCoeff (A^k*H) a x).re)]
        exact (hA.mul_hasSum (A^k*H) z.val x).summable.sum_le_tsum B
          (fun a _ => mul_nonneg (hA z.val a).2 (((hA.pow k).mul hH) a x).2)
      _ = (matrixCoeff (A^(k+1)*H) z.val x).re := by
        rw [(hA.mul_hasSum (A^k*H) z.val x).tsum_eq,pow_succ',mul_assoc]

end PositivePathOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitBinOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem isAut_trans (G : BondGraph V E) {a c : V ≃ V} {b d : E ≃ E}
    (hab : IsAut G a b) (hcd : IsAut G c d) : IsAut G (a.trans c) (b.trans d) := by
  intro e
  change G (d (b e)) = (G e).map (c ∘ a)
  rw [hcd,hab,Sym2.map_map]

theorem mem_vertexOrbit_aut_iff (G : BondGraph V E) (o : V) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) : a x ∈ vertexOrbit G o ↔ x ∈ vertexOrbit G o := by
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G hab),?_⟩
    simp only [Equiv.trans_apply,hc,Equiv.symm_apply_apply]
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd hab,rfl⟩

theorem binConnectionMass_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (n : ℕ) (ω : Set E) (x y : V) :
    binConnectionMass G n (b ⁻¹' ω) x y = binConnectionMass G n ω (a x) (a y) := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [binConnectionMass,hf,hn,conn_aut_iff G hab]

theorem binConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    binConnection G p n (a x) (a y) = binConnection G p n x y := by
  have hm : Measurable (fun ω => binConnectionMass G n ω x y) :=
    measurable_finite_local _ _ (fun ω => binConnectionMass_local G hloc n ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binConnection,binConnectionMass_covariant G hab] using h.symm

 
noncomputable def orbitBinConnection (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : ℝ :=
  if x ∈ vertexOrbit G o ∧ y ∈ vertexOrbit G o then binConnection G p n x y else 0

theorem orbitBinConnection_nonneg (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : 0 ≤ orbitBinConnection G p o n x y := by
  unfold orbitBinConnection
  split_ifs
  · exact binConnection_nonneg G p n x y
  · exact le_rfl

theorem orbitBinConnection_symm (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : orbitBinConnection G p o n x y = orbitBinConnection G p o n y x := by
  simp only [orbitBinConnection,and_comm,binConnection_symm G p n]

theorem orbitBinConnection_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    orbitBinConnection G p o n (a x) (a y) = orbitBinConnection G p o n x y := by
  simp only [orbitBinConnection,mem_vertexOrbit_aut_iff G o hab,binConnection_covariant G hloc p hab n]

theorem orbitBinConnection_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) : Summable (orbitBinConnection G p o n x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
  intro y hy
  have hz := binConnection_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  simp only [orbitBinConnection,hz,ite_self]

noncomputable def binOrbitRow (G : BondGraph V E) (p : unitInterval) (o : V) (n : ℕ) : ℝ :=
  ∑' y, orbitBinConnection G p o n o y

theorem orbitBinConnection_row (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) (hx : x ∈ vertexOrbit G o) :
    (∑' y, orbitBinConnection G p o n x y) = binOrbitRow G p o n := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  rw [← a.tsum_eq (fun y => orbitBinConnection G p o n (a o) y)]
  exact tsum_congr (fun y => orbitBinConnection_covariant G hloc p o hab n o y)

theorem orbitBinConnection_row_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (x : V) :
    (∑' y, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (orbitBinConnection_row G hloc p o n x hx).le
  · simp only [orbitBinConnection,hx,false_and,ite_false,tsum_zero]
    exact tsum_nonneg (orbitBinConnection_nonneg G p o n o)

 

theorem exists_orbitBinConnection_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) :
    ∃ H : Hilbert V →L[ℂ] Hilbert V, ‖H‖ ≤ binOrbitRow G p o n ∧
      ∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ) := by
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, orbitBinConnection G p o n x y) ≤ binOrbitRow G p o n :=
    ((orbitBinConnection_summable G hloc p o n x).sum_le_tsum S
      (fun y _ => orbitBinConnection_nonneg G p o n x y)).trans (orbitBinConnection_row_le G hloc p o n x)
  exact exists_operator_of_row_column_bound (orbitBinConnection G p o n) (binOrbitRow G p o n)
    (tsum_nonneg (orbitBinConnection_nonneg G p o n o)) (orbitBinConnection_nonneg G p o n) hr
    (fun y S => by simpa only [orbitBinConnection_symm G p o n] using hr y S)

end OrbitBinOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open MeasureTheory
section AmplificationOperatorDomination
attribute [local instance] Classical.propDecidable Classical.decEq

theorem oldRun_endpoint_mem {W : Type*} (P : W → Prop) (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, K i a b ≠ 0 → P b) (k : ℕ) (z : W) (hz : P z)
    (r : Fin k → W) (hr : oldRunWeight K k z r ≠ 0) : P (oldRunVertices k z r 0) := by
  induction k generalizing z with
  | zero => exact hz
  | succ k ih =>
    have hm := mul_ne_zero_iff.mp hr
    rw [oldRunVertices_succ_of_le _ _ _ _ (Nat.zero_le k)]
    exact ih (r 0) (hK _ _ _ hm.1) (Fin.tail r) hm.2

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_operator_le [Nonempty E] (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval)
    (hx : x ∈ vertexOrbit G o) (hz : z.val ∈ vertexOrbit G o)
    (hroot : incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset ⊆ Q)
    (hquery : ∀ a ∈ B, incidentSupport G hloc (finite_reachBall hloc a q.radius).toFinset ⊆ Q)
    (A H : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ a b, matrixCoeff A a b = (q.kernel p a b : ℂ))
    (hH : ∀ a b, matrixCoeff H a b = (orbitBinConnection G p o n a b : ℂ)) :
    (∫ ω, q.amplificationMarginal Q B x k n z p ω ∂law p) ≤
      (matrixCoeff (A^k*H) z.val x).re := by
  have hposA : PositiveRealMatrix A := fun a b => by
    rw [hA a b]
    exact ⟨rfl,q.kernel_nonneg p a b⟩
  have hposH : PositiveRealMatrix H := fun a b => by
    rw [hH a b]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n a b⟩
  rw [q.amplificationMarginal_mean_kernel Q B x k n z p hx hz hquery]
  have he : (∑ r : Fin k → ↥B, finiteBinConnection G Q p x n (amplificationVertices B k z r 0) *
      oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r) =
      ∑ r : Fin k → ↥B,
        oldRunWeight (fun _ (a b : ↥B) => (matrixCoeff A a.val b.val).re) k z r *
          (matrixCoeff H (oldRunVertices k z r 0).val x).re := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [hA,hH,Complex.ofReal_re,
      finiteBinConnection_eq_binConnection G hloc Q p x n _ hroot]
    by_cases hr : oldRunWeight (fun _ (a b : ↥B) => q.kernel p a.val b.val) k z r = 0
    · simp only [hr,mul_zero,zero_mul]
    · have hy : (oldRunVertices k z r 0).val ∈ vertexOrbit G o :=
        oldRun_endpoint_mem (fun a : ↥B => a.val ∈ vertexOrbit G o)
          (fun _ (a b : ↥B) => q.kernel p a.val b.val)
          (fun _ a b hab => by
            by_contra hb
            exact hab (q.kernel_zero_of_end_not_mem p a.val b.val hb)) k z hz r hr
      rw [orbitBinConnection,ite_eq_left ⟨hy,hx⟩,binConnection_symm G p n]
      exact mul_comm _ _
  rw [he]
  exact finite_oldRun_operator_domination A H hposA hposH B k z x

end LocalEndpointRule

 

theorem exists_operator_of_amplification_domination
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (o : V) (n k : ℕ)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A)
    (F : V → V → ℝ) (hF : ∀ x z, 0 ≤ F x z)
    (hdom : ∀ (H : Hilbert V →L[ℂ] Hilbert V),
      (∀ x y, matrixCoeff H x y = (orbitBinConnection G p o n x y : ℂ)) →
      ∀ x z, F x z ≤ (matrixCoeff (A^k*H) z x).re) :
    ∃ T : Hilbert V →L[ℂ] Hilbert V, ‖T‖ ≤ binOrbitRow G p o n * ‖A‖^k ∧
      ∀ x z, matrixCoeff T x z = (F x z : ℂ) := by
  obtain ⟨H,hHnorm,hH⟩ := exists_orbitBinConnection_operator G hloc p o n
  have hposH : PositiveRealMatrix H := fun x y => by
    rw [hH x y]
    exact ⟨rfl,orbitBinConnection_nonneg G p o n x y⟩
  have hpos := ((hA.pow k).mul hposH).star
  have htr (x z : V) : (matrixCoeff (star (A^k*H)) x z).re = (matrixCoeff (A^k*H) z x).re := by
    simp only [matrixCoeff_adjoint,Complex.star_def,Complex.conj_re]
  obtain ⟨T,hTnorm,hT⟩ := exists_operator_of_matrix_domination
    (fun x z => (matrixCoeff (star (A^k*H)) x z).re) F (fun x z => (hpos x z).2)
    (fun x z => by rw [abs_of_nonneg (hF x z),htr]; exact hdom H hH x z)
    (star (A^k*H)) (fun x z => hpos.real x z)
  refine ⟨T,hTnorm.trans ?_,hT⟩
  have hpow : ∀ j : ℕ, ‖A^j‖ ≤ ‖A‖^j := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  calc
    ‖star (A^k*H)‖ = ‖A^k*H‖ := by
      change ‖ContinuousLinearMap.adjoint (A^k*H)‖ = _
      exact LinearIsometryEquiv.norm_map _ _
    _ ≤ ‖A^k‖ * ‖H‖ := norm_mul_le _ _
    _ ≤ ‖A‖^k * binOrbitRow G p o n := mul_le_mul (hpow k) hHnorm
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = binOrbitRow G p o n * ‖A‖^k := mul_comm _ _

end AmplificationOperatorDomination

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterVisitKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def conditionalSuccess (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y

theorem conditionalSuccess_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    0 ≤ q.conditionalSuccess ω x := tsum_nonneg (q.nonneg ω x)

theorem conditionalSuccess_support (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V)
    (h : q.conditionalSuccess ω x ≠ 0) :
    x ∈ O ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  have he : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (by simp only [conditionalSuccess,hn,tsum_zero])
  obtain ⟨y,hy⟩ := he
  obtain ⟨hx,_,_,hf,hc,_⟩ := q.support ω x y hy
  exact ⟨hx,hf,hc⟩

theorem conditionalSuccess_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    q.conditionalSuccess ω x = q.conditionalSuccess
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem conditionalSuccess_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.conditionalSuccess ω x) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.conditionalSuccess_local ω x)

theorem conditionalSuccess_mean (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∫ ω, q.conditionalSuccess ω x ∂law p) = q.successProbability p x :=
  (q.kernel_row_integral p x).symm

theorem conditionalSuccess_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x : V) :
    q.conditionalSuccess (b ⁻¹' ω) x = q.conditionalSuccess ω (a x) := by
  unfold conditionalSuccess
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _

 

noncomputable def clusterVisitMass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) : ℝ :=
  if a ∈ cluster G ω x then q.conditionalSuccess ω x else 0

theorem clusterVisitMass_nonneg (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    0 ≤ q.clusterVisitMass ω x a := by
  unfold clusterVisitMass
  split_ifs
  · exact q.conditionalSuccess_nonneg ω x
  · exact le_refl _

theorem clusterVisitMass_outside (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitMass ω x a = 0 := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    exact ite_eq_right (fun hmem => ha (finite_cluster_subset_reachBall G ω x hf M hc hmem))

theorem clusterVisitMass_local (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q : Set E)) x a := by
  dsimp only
  let Q := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
  change q.clusterVisitMass ω x a = q.clusterVisitMass (ω ∩ (Q:Set E)) x a
  have he := finite_local_of_subset _ Q
    (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
    (fun ω => q.conditionalSuccess ω x) (fun ω => q.conditionalSuccess_local ω x) ω
  by_cases h : q.conditionalSuccess ω x = 0
  · have h' : q.conditionalSuccess (ω ∩ (Q:Set E)) x = 0 := he.symm.trans h
    simp only [clusterVisitMass,h,h',ite_self]
  · obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x (max q.radius M)).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G ω x hf _ (hc.trans (le_max_right _ _))
    have hc' := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q:Set E)) x = cluster G ω x at hc'
    change (if a ∈ cluster G ω x then _ else _) = (if a ∈ cluster G (ω ∩ (Q:Set E)) x then _ else _)
    rw [hc',he]

theorem clusterVisitMass_integrable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    Integrable (fun ω => q.clusterVisitMass ω x a) (law p) :=
  integrable_finite_local _ p _ (fun ω => q.clusterVisitMass_local ω x a)

theorem clusterVisitMass_covariant (q : LocalEndpointRule G hloc O M L)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.clusterVisitMass (b ⁻¹' ω) x y = q.clusterVisitMass ω (a x) (a y) := by
  have hc : y ∈ cluster G (b ⁻¹' ω) x ↔ a y ∈ cluster G ω (a x) := by
    rw [← cluster_aut G hab ω x]
    constructor
    · intro hy; exact ⟨y,hy,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact (a.injective he) ▸ hz
  simp only [clusterVisitMass,hc,q.conditionalSuccess_covariant a b hab]

theorem clusterVisitMass_row_le (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    (∑' a, q.clusterVisitMass ω x a) ≤ M * q.conditionalSuccess ω x := by
  by_cases h : q.conditionalSuccess ω x = 0
  · simp only [clusterVisitMass,h,ite_self,tsum_zero,mul_zero,le_refl]
  obtain ⟨_,hf,hc⟩ := q.conditionalSuccess_support ω x h
  rw [tsum_eq_sum (f := q.clusterVisitMass ω x) (s := hf.toFinset) (fun a ha => ite_eq_right (by simpa only [Set.Finite.mem_toFinset] using ha))]
  have he : (∑ a ∈ hf.toFinset, q.clusterVisitMass ω x a) =
      (hf.toFinset.card:ℝ) * q.conditionalSuccess ω x := by
    calc
      _ = ∑ _a ∈ hf.toFinset, q.conditionalSuccess ω x := Finset.sum_congr rfl (fun a ha => ite_eq_left (hf.mem_toFinset.mp ha))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (q.conditionalSuccess_nonneg ω x)
  exact_mod_cast (by simpa only [← Set.ncard_eq_toFinset_card _ hf] using hc)

noncomputable def clusterVisitKernel (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x a : V) : ℝ := ∫ ω, q.clusterVisitMass ω x a ∂law p

theorem clusterVisitKernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V) :
    0 ≤ q.clusterVisitKernel p x a := integral_nonneg (fun ω => q.clusterVisitMass_nonneg ω x a)

theorem clusterVisitKernel_outside (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x a : V)
    (ha : a ∉ reachBall G x M) : q.clusterVisitKernel p x a = 0 := by
  simp only [clusterVisitKernel,q.clusterVisitMass_outside _ x a ha,integral_zero]

theorem clusterVisitKernel_summable (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.clusterVisitKernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro a ha
  exact q.clusterVisitKernel_outside p x a (by simpa only [Set.Finite.mem_toFinset] using ha)

theorem clusterVisitKernel_row_le (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' a, q.clusterVisitKernel p x a) ≤ M * q.successProbability p x := by
  let B := (finite_reachBall hloc x M).toFinset
  have he (ω : Set E) : (∑' a, q.clusterVisitMass ω x a) = ∑ a ∈ B, q.clusterVisitMass ω x a :=
    tsum_eq_sum (fun a ha => q.clusterVisitMass_outside ω x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))
  rw [tsum_eq_sum (s := B) (fun a ha => q.clusterVisitKernel_outside p x a (by simpa only [B,Set.Finite.mem_toFinset] using ha))]
  simp only [clusterVisitKernel]
  rw [← integral_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a)]
  calc
    _ ≤ ∫ ω, (M:ℝ) * q.conditionalSuccess ω x ∂law p :=
      integral_mono (integrable_finsetSum B (fun a _ => q.clusterVisitMass_integrable p x a))
        ((q.conditionalSuccess_integrable p x).const_mul _) (fun ω => by rw [← he]; exact q.clusterVisitMass_row_le ω x)
    _ = _ := by rw [integral_const_mul,q.conditionalSuccess_mean]

theorem clusterVisitKernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.clusterVisitKernel p (a x) (a y) = q.clusterVisitKernel p x y := by
  have hm : Measurable (fun ω => q.clusterVisitMass ω x y) :=
    measurable_finite_local _ _ (fun ω => q.clusterVisitMass_local ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [clusterVisitKernel,q.clusterVisitMass_covariant a b hab] using h.symm

end LocalEndpointRule
end ClusterVisitKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section VisitEnvelope
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

noncomputable def visitEnvelope (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) : ℕ → V → V → ℝ
  | 0, _, _ => 0
  | k+1, x, a => q.successProbability p o ^ k * q.clusterVisitKernel p x a +
      ∑' y, q.kernel p x y * q.visitEnvelope o p k y a

theorem visitEnvelope_nonneg (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x a : V) : 0 ≤ q.visitEnvelope o p k x a := by
  induction k generalizing x with
  | zero => exact le_refl _
  | succ k ih =>
    exact add_nonneg (mul_nonneg (pow_nonneg (q.successProbability_nonneg p o) _) (q.clusterVisitKernel_nonneg p x a))
      (tsum_nonneg (fun y => mul_nonneg (q.kernel_nonneg p x y) (ih y)))

theorem visitEnvelope_covariant (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x y : V) :
    q.visitEnvelope o p k (a x) (a y) = q.visitEnvelope o p k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [visitEnvelope,q.clusterVisitKernel_covariant p a b hab]
    congr 1
    rw [← a.tsum_eq (fun z => q.kernel p (a x) z * q.visitEnvelope o p k z (a y))]
    exact tsum_congr fun z => by rw [q.kernel_covariant p a b hab,ih]

 

theorem visitEnvelope_row_bound (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (k : ℕ) (x : V) :
    Summable (q.visitEnvelope o p k x) ∧
      (∑' a, q.visitEnvelope o p k x a) ≤ (k*M:ℕ) * q.successProbability p o ^ k := by
  let u := q.successProbability p o
  have hu : 0 ≤ u := q.successProbability_nonneg p o
  induction k generalizing x with
  | zero => simp only [visitEnvelope,zero_mul,Nat.cast_zero,pow_zero,mul_one,tsum_zero,le_refl,and_true]; exact summable_zero
  | succ k ih =>
    let B := (finite_reachBall hloc x M).toFinset
    have he (a : V) : (∑' y, q.kernel p x y * q.visitEnvelope o p k y a) =
        ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a :=
      tsum_eq_sum (fun y hy => by
        rw [q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul])
    have ht (a : V) : q.visitEnvelope o p (k+1) x a =
        u^k * q.clusterVisitKernel p x a + ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a := by
      exact congrArg (_ + ·) (he a)
    have hsum : Summable (fun a => ∑ y ∈ B, q.kernel p x y * q.visitEnvelope o p k y a) :=
      summable_sum (s := B) (fun y _ => (ih y).1.mul_left _)
    have hs := ((q.clusterVisitKernel_summable p x).mul_left (u^k)).add hsum
    have hs' : Summable (q.visitEnvelope o p (k+1) x) := by
      change Summable (fun a => q.visitEnvelope o p (k+1) x a)
      simpa only [ht] using hs
    refine ⟨hs',?_⟩
    simp_rw [ht]
    rw [Summable.tsum_add ((q.clusterVisitKernel_summable p x).mul_left _) hsum,tsum_mul_left,
      Summable.tsum_finsetSum (fun y _ => (ih y).1.mul_left _)]
    simp_rw [tsum_mul_left]
    have hr : (∑ y ∈ B, q.kernel p x y) ≤ u :=
      ((q.summable_kernel p x).sum_le_tsum B (fun y _ => q.kernel_nonneg p x y)).trans
        (q.kernel_row_le_success o p x)
    calc
      _ ≤ u^k * (M*u) + ∑ y ∈ B, q.kernel p x y * ((k*M:ℕ)*u^k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
          exact (q.clusterVisitKernel_row_le p x).trans
            (mul_le_mul_of_nonneg_left (q.kernel_row_le_success o p x) (Nat.cast_nonneg _))
        · exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (q.kernel_nonneg p x y)
      _ ≤ u^k * (M*u) + u*((k*M:ℕ)*u^k) := by
        rw [← Finset.sum_mul]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _)))
      _ = ((k+1)*M:ℕ) * q.successProbability p o ^ (k+1) := by
        change _ = ((k+1)*M:ℕ) * u^(k+1)
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        ring

end LocalEndpointRule
end VisitEnvelope

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MarkedOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

theorem oldRunWeight_congr (K K' : ℕ → W → W → ℝ) (k : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → ∀ a b, K i a b = K' i a b) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = oldRunWeight K' k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight]
    rw [h (k+1) (by omega) (by omega),ih (fun i hi hik => h i hi (by omega))]

theorem oldRunWeight_prod (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K k z r = ∏ i ∈ Finset.Icc 1 k,
      K i (oldRunVertices k z r i) (oldRunVertices k z r (i-1)) := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k, K i (oldRunVertices (k+1) z r i)
        (oldRunVertices (k+1) z r (i-1))) = oldRunWeight K k (r 0) (Fin.tail r) := by
      rw [ih]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he,oldRunVertices_last,Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _),oldRunVertices_last]
    exact mul_comm _ _

 

noncomputable def markedOldRun (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, oldRunWeight (fun j a b => if j = i then C j a b else K j a b) k z r

theorem markedOldRun_nonneg (K C : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (hC : ∀ i a b, 0 ≤ C i a b)
    (k : ℕ) (z : W) (r : Fin k → W) : 0 ≤ markedOldRun K C k z r := by
  apply Finset.sum_nonneg
  intro i _
  apply oldRunWeight_nonneg
  intro j a b
  split_ifs
  · exact hC j a b
  · exact hK j a b

theorem markedOldRun_succ (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin (k+1) → W) :
    markedOldRun K C (k+1) z r =
      K (k+1) z (r 0) * markedOldRun K C k (r 0) (Fin.tail r) +
      C (k+1) z (r 0) * oldRunWeight K k (r 0) (Fin.tail r) := by
  unfold markedOldRun
  rw [Finset.sum_Icc_succ_top (by omega),Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hne : k+1 ≠ i := by have := Finset.mem_Icc.mp hi; omega
    simp only [oldRunWeight,ite_eq_right hne]
  · simp only [oldRunWeight,ite_true]
    congr 1
    apply oldRunWeight_congr
    intro i hi hik a b
    exact ite_eq_right (by omega)

theorem sum_markedOldRun_succ [Fintype W] (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ r : Fin (k+1) → W, markedOldRun K C (k+1) z r) =
      ∑ b : W, (K (k+1) z b * (∑ r : Fin k → W, markedOldRun K C k b r) +
        C (k+1) z b * (∑ r : Fin k → W, oldRunWeight K k b r)) := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun r => K (k+1) z r.1 * markedOldRun K C k r.1 r.2 + C (k+1) z r.1 * oldRunWeight K k r.1 r.2)
      (by intro r; exact markedOldRun_succ K C k z r),Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib,Finset.mul_sum]

 
theorem oldRunWeight_integral_indexed (Q : Finset E) (p : ℝ)
    (q : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => oldRunWeight (fun i => q i (η i)) k z r) =
      oldRunWeight (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b)) k z r := by
  calc
    _ = finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
        ∏ i : ↥(Finset.Icc 1 k), q i (η i) (oldRunVertices k z r i)
          (oldRunVertices k z r (i.val-1))) := by
      congr 1
      funext η
      rw [oldRunWeight_prod]
      exact (Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q i (η i) (oldRunVertices k z r i) (oldRunVertices k z r (i-1)))).symm
    _ = ∏ i : ↥(Finset.Icc 1 k), finiteFieldIntegral Q p (fun ω =>
        q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1))) :=
      finiteFamilyIntegral_prod Q (Finset.Icc 1 k) p
        (fun i ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i.val-1)))
    _ = _ := by
      rw [oldRunWeight_prod]
      exact Finset.prod_coe_sort (Finset.Icc 1 k) (fun i => finiteFieldIntegral Q p
        (fun ω => q i ω (oldRunVertices k z r i) (oldRunVertices k z r (i-1))))

theorem markedOldRun_integral (Q : Finset E) (p : ℝ)
    (q c : ℕ → Set E → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) :
    finiteFamilyIntegral Q (Finset.Icc 1 k) p
      (fun η => markedOldRun (fun i => q i (η i)) (fun i => c i (η i)) k z r) =
      markedOldRun (fun i a b => finiteFieldIntegral Q p (fun ω => q i ω a b))
        (fun i a b => finiteFieldIntegral Q p (fun ω => c i ω a b)) k z r := by
  unfold markedOldRun
  rw [finiteFamilyIntegral_sum]
  apply Finset.sum_congr rfl
  intro i _
  change finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
      oldRunWeight (fun j => (fun ω a b => if j=i then c j ω a b else q j ω a b) (η j)) k z r) = _
  rw [oldRunWeight_integral_indexed Q p (fun j ω a b => if j=i then c j ω a b else q j ω a b) k z r]
  congr 1
  funext j a b
  by_cases h : j = i <;> simp only [h,ite_true,ite_false]

 

theorem trajectory_indicator_le_marked (G : BondGraph V E) (e : W → V)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y)
    (k : ℕ) (η : ℕ → Set E) (z : W) (r : Fin k → W) (a : V) :
    (if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k then
      oldRunWeight (fun i => q (η i)) k z r else 0) ≤
      markedOldRun (fun i => q (η i))
        (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r := by
  have hC : ∀ i x y, 0 ≤ (if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) := by
    intro i x y; split_ifs; exact hq _ _ _; exact le_refl _
  by_cases ha : a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z r) k
  · rw [ite_eq_left ha]
    obtain ⟨i,hi,hik,hai⟩ := (mem_trajectoryUnion G η (e ∘ oldRunVertices k z r) k a).mp ha
    have he : oldRunWeight (fun j x y => if j=i then
        (if a ∈ cluster G (η j) (e x) then q (η j) x y else 0) else q (η j) x y) k z r =
        oldRunWeight (fun j => q (η j)) k z r := by
      simp_rw [oldRunWeight_prod]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [ite_true,Function.comp_apply] at hai ⊢
        exact ite_eq_left hai
      · exact ite_eq_right hji
    rw [← he]
    unfold markedOldRun
    apply Finset.single_le_sum _ (Finset.mem_Icc.mpr ⟨hi,hik⟩)
    intro j _
    apply oldRunWeight_nonneg
    intro l x y
    split_ifs
    · exact hq _ _ _
    · exact le_refl _
    · exact hq _ _ _
  · rw [ite_eq_right ha]
    exact markedOldRun_nonneg _ _ (fun _ => hq _) hC k z r

end MarkedOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryEnvelopeDomination
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteTrajectoryMass_le_marked {W : Type*} [Fintype W]
    (G : BondGraph V E) (e : W → V) (Q : Finset E) (p : unitInterval) (k : ℕ)
    (q : Set E → W → W → ℝ) (hq : ∀ ω x y, 0 ≤ q ω x y) (z : W) (a : V) :
    finiteTrajectoryMass G e Q p k q z a ≤
      ∑ r : Fin k → W, markedOldRun (fun _ => finiteOldKernel Q p q)
        (fun _ x y => finiteFieldIntegral Q p (fun ω => if a ∈ cluster G ω (e x) then q ω x y else 0)) k z r := by
  unfold finiteTrajectoryMass
  calc
    _ ≤ finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => ∑ r : Fin k → W,
        markedOldRun (fun i => q (η i))
          (fun i x y => if a ∈ cluster G (η i) (e x) then q (η i) x y else 0) k z r) :=
      finiteFamilyIntegral_mono Q (Finset.Icc 1 k) p _ _ (fun η => Finset.sum_le_sum (fun r _ =>
        trajectory_indicator_le_marked G e q hq k η z r a))
    _ = _ := by
      rw [finiteFamilyIntegral_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact markedOldRun_integral Q p (fun _ => q)
        (fun _ ω x y => if a ∈ cluster G ω (e x) then q ω x y else 0) k z r

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem finite_marked_step_row_le (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (x a : V)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ y : ↥B, finiteFieldIntegral Q p (fun ω =>
      if a ∈ cluster G ω x then q.mass ω x y.val else 0)) ≤ q.clusterVisitKernel p x a := by
  rw [← finiteFieldIntegral_sum]
  have he : q.clusterVisitKernel p x a = finiteFieldIntegral Q p (fun ω => q.clusterVisitMass ω x a) :=
    integral_finite_local Q p _ (finite_local_of_subset _ Q hQ _ (q.clusterVisitMass_local · x a))
  rw [he]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (finiteFieldWeight_nonneg Q p ω)
  dsimp only
  by_cases ha : a ∈ cluster G (finiteFieldSet Q ω) x
  · simp only [ha,ite_true,clusterVisitMass]
    rw [Finset.sum_coe_sort B (fun y => q.mass (finiteFieldSet Q ω) x y)]
    exact (q.summable_mass _ x).sum_le_tsum B (fun y _ => q.nonneg _ x y)
  · simp only [ha,ite_false,clusterVisitMass,Finset.sum_const_zero,le_refl]

 

theorem sum_markedOldRun_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    (∑ r : Fin k → ↥B, markedOldRun
      (fun _ => finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val))
      (fun _ (x y : ↥B) => finiteFieldIntegral Q p (fun ω =>
        if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)) k z r) ≤
      q.visitEnvelope o p k z.val a := by
  let u := q.successProbability p o
  let K : ↥B → ↥B → ℝ := finiteOldKernel Q p (fun ω (x y : ↥B) => q.mass ω x.val y.val)
  let C : ↥B → ↥B → ℝ := fun x y => finiteFieldIntegral Q p (fun ω =>
    if a ∈ cluster G ω x.val then q.mass ω x.val y.val else 0)
  have hK (x y : ↥B) : K x y = q.kernel p x.val y.val :=
    q.finiteOldKernel_eq_kernel Q p x.val y.val
      ((incidentSupport_ball_mono G hloc x.val (le_max_left _ _)).trans (hQ x.val x.property))
  have hKn (x y : ↥B) : 0 ≤ K x y := by rw [hK]; exact q.kernel_nonneg p _ _
  have hCn (x y : ↥B) : 0 ≤ C x y := by
    apply finiteFieldIntegral_nonneg
    intro ω; split_ifs; exact q.nonneg ω _ _; exact le_refl _
  have hKr (x : ↥B) : (∑ y, K x y) ≤ u := by
    simp only [hK]
    rw [Finset.sum_coe_sort B (fun y => q.kernel p x.val y)]
    exact ((q.summable_kernel p x.val).sum_le_tsum B (fun y _ => q.kernel_nonneg p x.val y)).trans
      (q.kernel_row_le_success o p x.val)
  have hCr (x : ↥B) : (∑ y, C x y) ≤ q.clusterVisitKernel p x.val a :=
    q.finite_marked_step_row_le o Q B p x.val a (hQ x.val x.property)
  change (∑ r : Fin k → ↥B, markedOldRun (fun _ => K) (fun _ => C) k z r) ≤ _
  induction k generalizing z with
  | zero => simp [markedOldRun,visitEnvelope]
  | succ k ih =>
    rw [sum_markedOldRun_succ]
    have hs : Summable (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc z.val M).toFinset)
      intro y hy
      rw [q.kernel_outside_ball_zero p z.val y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]
    calc
      _ ≤ ∑ y : ↥B, (K z y * q.visitEnvelope o p k y.val a + C z y * u^k) :=
        Finset.sum_le_sum fun y _ => add_le_add
          (mul_le_mul_of_nonneg_left (ih y) (hKn z y))
          (mul_le_mul_of_nonneg_left (sum_oldRunWeight_le (fun _ => K) (fun _ => hKn)
            u (q.successProbability_nonneg p o) (fun _ => hKr) k y) (hCn z y))
      _ = (∑ y : ↥B, K z y * q.visitEnvelope o p k y.val a) + (∑ y : ↥B, C z y)*u^k := by
        rw [Finset.sum_add_distrib,Finset.sum_mul]
      _ ≤ (∑' y, q.kernel p z.val y * q.visitEnvelope o p k y a) + q.clusterVisitKernel p z.val a * u^k := by
        apply add_le_add
        · simp only [hK]
          rw [Finset.sum_coe_sort B (fun y => q.kernel p z.val y * q.visitEnvelope o p k y a)]
          exact hs.sum_le_tsum B (fun y _ => mul_nonneg (q.kernel_nonneg p z.val y) (q.visitEnvelope_nonneg o p k y a))
        · exact mul_le_mul_of_nonneg_right (hCr z) (pow_nonneg (q.successProbability_nonneg p o) _)
      _ = q.visitEnvelope o p (k+1) z.val a := by rw [visitEnvelope]; ring

theorem finiteTrajectoryMass_le_envelope (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (Q : Finset E) (B : Finset V) (p : unitInterval) (k : ℕ) (z : ↥B) (a : V)
    (hQ : ∀ x ∈ B, incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset ⊆ Q) :
    finiteTrajectoryMass G Subtype.val Q p k (fun ω (x y : ↥B) => q.mass ω x.val y.val) z a ≤
      q.visitEnvelope o p k z.val a :=
  (finiteTrajectoryMass_le_marked G Subtype.val Q p k _ (fun ω x y => q.nonneg ω x.val y.val) z a).trans
    (q.sum_markedOldRun_le_envelope o Q B p k z a hQ)

end LocalEndpointRule
end TrajectoryEnvelopeDomination

end Percolation

end OAI
