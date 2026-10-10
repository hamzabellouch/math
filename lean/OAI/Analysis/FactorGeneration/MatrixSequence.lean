import OAI.Analysis.FactorGeneration.MatrixRefinement

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure FiniteMatrixStage (N : VonNeumannAlgebra H) where
  size : ℕ
  positive : 0 < size
  units : MatrixUnitSystem (Fin size) N.toStarSubalgebra

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

def commutant (E : FiniteMatrixStage N) (hNM : N ≤ M) : VonNeumannAlgebra H :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann

theorem commutant_le (E : FiniteMatrixStage N) (hNM : N ≤ M) : E.commutant hNM ≤ M :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann_le

def energy (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : ℝ :=
  τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x)^2

theorem energy_nonneg (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) : 0 ≤ E.energy τ hNM x := sq_nonneg _

theorem commutant_antitone (E F : FiniteMatrixStage N) (hNM : N ≤ M)
    (hEF : E.units.algebra ≤ F.units.algebra) : F.commutant hNM ≤ E.commutant hNM :=
  (E.units.map (coordinateInclusion hNM)).relative_antitone _
    (E.units.map_algebra_mono F.units hEF (coordinateInclusion hNM))

theorem energy_antitone (E F : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (hEF : E.units.algebra ≤ F.units.algebra) (x : M.toStarSubalgebra) :
    F.energy τ hNM x ≤ E.energy τ hNM x := by
  have h := conditionalExpectation_nested_energy τ (F.commutant_le hNM) (E.commutant_le hNM)
    (E.commutant_antitone F hNM hEF) x
  dsimp [energy]
  nlinarith [sq_nonneg (τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x-
    conditionalExpectation τ (F.commutant_le hNM) x))]

theorem exists_refinement_descent (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      F.energy τ hNM x ≤ (15/16 : ℝ)*E.energy τ hNM x := by
  by_cases hz : conditionalExpectation τ (E.commutant_le hNM) x=0
  · refine ⟨E,le_rfl,?_⟩
    simp [energy,hz]
  · obtain ⟨k,n,hn,F,hc,hEF,hdesc⟩ := exists_compatible_matrix_energy_descent τ hNM
      hfactor hdiff hirr E.units ⟨0,E.positive⟩ x ht hz
    let G := E.units.product F hc
    let e := (Fintype.equivFin (Fin E.size × Fin n)).symm
    let S : FiniteMatrixStage N := ⟨Fintype.card (Fin E.size × Fin n),by
      simp only [Fintype.card_prod,Fintype.card_fin]
      rw [hn]
      exact Nat.mul_pos E.positive (by positivity),G.reindex e⟩
    refine ⟨S,?_,?_⟩
    · change E.units.algebra ≤ (G.reindex e).algebra
      rw [G.reindex_algebra]
      exact hEF
    · change τ.norm₂ (conditionalExpectation τ
        ((G.reindex e).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤ _
      simp only [G.mapped_reindex_relative e (coordinateInclusion hNM)]
      exact hdesc

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/
namespace FiniteMatrixStage

section
open scoped BigOperators
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hfactor hdiff hirr

theorem exists_finite_family_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)*E.energy τ hNM (x s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E,le_rfl,by simp⟩
  | @insert s S hs ih =>
    obtain ⟨F,hEF,hF⟩ := ih (fun t ht' => ht t (Finset.mem_insert_of_mem ht'))
    obtain ⟨G,hFG,hG⟩ := F.exists_refinement_descent τ hNM hfactor hdiff hirr (x s)
      (ht s (Finset.mem_insert_self s S))
    refine ⟨G,hEF.trans hFG,?_⟩
    intro t ht'
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact hG.trans (mul_le_mul_of_nonneg_left (E.energy_antitone F τ hNM hEF _) (by norm_num))
    · exact (F.energy_antitone G τ hNM hFG _).trans (hF t ht')

theorem exists_iterated_energy_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (r : ℕ) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)^r*E.energy τ hNM (x s) := by
  induction r with
  | zero => exact ⟨E,le_rfl,by simp⟩
  | succ r ih =>
    obtain ⟨F,hEF,hF⟩ := ih
    obtain ⟨G,hFG,hG⟩ := exists_finite_family_descent τ hNM hfactor hdiff hirr S x ht F
    refine ⟨G,hEF.trans hFG,?_⟩
    intro s hs
    calc G.energy τ hNM (x s) ≤ (15/16 : ℝ)*F.energy τ hNM (x s) := hG s hs
      _ ≤ (15/16 : ℝ)*((15/16 : ℝ)^r*E.energy τ hNM (x s)) :=
        mul_le_mul_of_nonneg_left (hF s hs) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem exists_finite_matrix_energy_budget {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      (∑ s ∈ S,F.energy τ hNM (x s)) < ε := by
  let A := ∑ s ∈ S,E.energy τ hNM (x s)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun s _ => E.energy_nonneg τ hNM (x s))
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε/(A+1) from div_pos hε (by positivity)) (by norm_num : (15/16 : ℝ) < 1)
  obtain ⟨F,hEF,hF⟩ := exists_iterated_energy_descent τ hNM hfactor hdiff hirr S x ht E r
  refine ⟨F,hEF,?_⟩
  have hbound : (∑ s ∈ S,F.energy τ hNM (x s)) ≤ (15/16 : ℝ)^r*A := by
    calc (∑ s ∈ S,F.energy τ hNM (x s)) ≤
        ∑ s ∈ S,(15/16 : ℝ)^r*E.energy τ hNM (x s) :=
          Finset.sum_le_sum (fun s hs => hF s hs)
      _ = _ := (Finset.mul_sum S _ _).symm
  have hsmall := (lt_div_iff₀ (by positivity : 0 < A+1)).mp hr
  have hp : 0 ≤ (15/16 : ℝ)^r := by positivity
  nlinarith

end

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_countable_matrix_refinement (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : ℕ → M.toStarSubalgebra) (ht : ∀ s,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      Monotone (fun n => (A n).units.algebra) ∧
      (∀ n,(∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n) ∧
      ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0) := by
  have hex (n : ℕ) (F : FiniteMatrixStage N) := exists_finite_matrix_energy_budget τ hNM
    hfactor hdiff hirr (Finset.range (n+1)) x (fun s _ => ht s) F
    ((1/2 : ℝ)^(n+1)) (by positivity)
  let next (n : ℕ) (F : FiniteMatrixStage N) := (hex n F).choose
  let A : ℕ → FiniteMatrixStage N := fun n => Nat.rec E (fun n F => next n F) n
  have hstep (n : ℕ) : (A n).units.algebra ≤ (A (n+1)).units.algebra ∧
      (∑ s ∈ Finset.range (n+1),(A (n+1)).energy τ hNM (x s)) < (1/2 : ℝ)^(n+1) :=
    (hex n (A n)).choose_spec
  have hbudget (n : ℕ) :
      (∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n := by
    cases n with
    | zero => simp
    | succ n => exact (hstep n).2
  refine ⟨A,rfl,monotone_nat_of_le_succ (fun n => (hstep n).1),hbudget,?_⟩
  intro s
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => (A n).energy_nonneg τ hNM (x s)))
    ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  filter_upwards [eventually_ge_atTop (s+1)] with n hn
  exact (Finset.single_le_sum (fun t _ => (A n).energy_nonneg τ hNM (x t))
    (Finset.mem_range.mpr (by omega))).trans (hbudget n).le

end FiniteMatrixStage

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/
section
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_countable_norm₂_dense (S : Set M.toStarSubalgebra)
    (hne : S.Nonempty) (hsep : TopologicalSpace.IsSeparable (baseVector τ '' S)) :
    ∃ a : ℕ → M.toStarSubalgebra,(∀ n,a n ∈ S) ∧
      ∀ b ∈ S,∀ ε : ℝ,0 < ε → ∃ n,τ.norm₂ (b-a n) < ε := by
  let T := baseVector τ '' S
  let : TopologicalSpace.SeparableSpace T := hsep.separableSpace
  let : Nonempty T := ⟨⟨baseVector τ hne.choose,Set.mem_image_of_mem _ hne.choose_spec⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := T)
  have hex (n : ℕ) : ∃ a ∈ S,baseVector τ a=(v n).val := (v n).property
  choose a ha he using hex
  refine ⟨a,ha,?_⟩
  intro b hb ε hε
  let z : T := ⟨baseVector τ b,Set.mem_image_of_mem _ hb⟩
  obtain ⟨w,⟨n,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (hv z) ε hε
  refine ⟨n,?_⟩
  change ‖baseVector τ (b-a n)‖ < ε
  rw [map_sub,he n]
  simpa only [Subtype.dist_eq,dist_eq_norm] using hw

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem scalar_common_commutant_of_dense_energy_decay (τ : TracialRepresentation M) (hNM : N ≤ M)
    (A : ℕ → FiniteMatrixStage N) (x : ℕ → M.toStarSubalgebra)
    (hdense : ∀ b : M.toStarSubalgebra,τ.trace b=0 → ∀ ε : ℝ,0 < ε →
      ∃ s,τ.norm₂ (b-x s) < ε)
    (hlim : ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n,c.val ∈ (A n).commutant hNM) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let y := c-τ.trace c • (1 : M.toStarSubalgebra)
  have hyt : τ.trace y=0 := by
    dsimp [y]
    rw [trace_sub,cornerTrace_smul,τ.trace_one,mul_one,sub_self]
  have hym (n : ℕ) : y.val ∈ (A n).commutant hNM :=
    ((A n).commutant hNM).sub_mem (hc n)
      (((A n).commutant hNM).smul_mem ((A n).commutant hNM).one_mem _)
  suffices y=0 from sub_eq_zero.mp this
  by_contra hy
  have hp : 0 < τ.norm₂ y := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hy ((τ.norm₂_eq_zero_iff y).mp h.symm))
  obtain ⟨s,hs⟩ := hdense y hyt (τ.norm₂ y/4) (by positivity)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp (hlim s)).2 ((τ.norm₂ y/4)^2) (by positivity)).exists
  let hDM := (A n).commutant_le hNM
  let z := conditionalExpectation τ hDM (x s)
  have hz : τ.norm₂ z < τ.norm₂ y/4 := by
    change τ.norm₂ z^2 < (τ.norm₂ y/4)^2 at hn
    nlinarith [show 0 ≤ τ.norm₂ z from norm_nonneg _]
  have hdiff : τ.norm₂ (y-z) ≤ τ.norm₂ (y-x s) := by
    have he : conditionalExpectation τ hDM (y-x s)=y-z := by
      change conditionalExpectationCLM τ hDM (y-x s)=y-z
      rw [map_sub]
      change conditionalExpectation τ hDM y-z=y-z
      rw [conditionalExpectation_fixed τ hDM y (hym n)]
    rw [← he]
    exact conditionalExpectation_norm₂_le τ hDM _
  have hadd := τ.norm₂_add_le (y-z) z
  rw [sub_add_cancel] at hadd
  linarith

theorem exists_irreducible_matrix_sequence (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      Monotone (fun n => (A n).units.algebra) ∧
      ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let S : Set M.toStarSubalgebra := {b | τ.trace b=0}
  obtain ⟨x,hx,hdense⟩ := exists_countable_norm₂_dense τ S ⟨0,by change τ.trace 0=0; simp [TracialRepresentation.trace]⟩
    (hsep.mono (Set.image_subset_range _ _))
  obtain ⟨A,hA,hmono,_,hlim⟩ := exists_countable_matrix_refinement τ hNM hfactor hdiff hirr x hx E
  exact ⟨A,hA,hmono,scalar_common_commutant_of_dense_energy_decay τ hNM A x hdense hlim⟩

end FiniteMatrixStage

end

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_wotClosed (M : VonNeumannAlgebra H) : WOTClosed M.toStarSubalgebra := by
  change IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ (M : Set (H →L[ℂ] H))}
  rw [← M.centralizer_centralizer]
  change IsClosed {T : H →WOT[ℂ] H |
    ∀ S ∈ Set.centralizer (M : Set (H →L[ℂ] H)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : H →WOT[ℂ] H | S*T.toCLM=T.toCLM*S} =
      {T : H →WOT[ℂ] H |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (H →WOT[ℂ] H) ≃ (H →L[ℂ] H) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generated (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  wstar (⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)))

theorem generated_closed (A : ℕ → FiniteMatrixStage N) : WOTClosed (generated A) := wstar_closed _

theorem stage_le_generated (A : ℕ → FiniteMatrixStage N) (n : ℕ) :
    (A n).units.concreteAlgebra ≤ generated A := by
  intro x hx
  exact subset_wstar _ (Set.mem_iUnion.mpr ⟨n,hx⟩)

theorem generated_le (A : ℕ → FiniteMatrixStage N) : generated A ≤ N.toStarSubalgebra := by
  apply wstar_le (vonNeumann_wotClosed N)
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact (A n).units.concreteAlgebra_le hn

theorem generated_minimal (A : ℕ → FiniteMatrixStage N)
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (hR : WOTClosed R)
    (h : ∀ n,(A n).units.concreteAlgebra ≤ R) : generated A ≤ R := by
  apply wstar_le hR
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact h n hn

theorem generated_relative_scalar (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : generated A,a.val*c.val=c.val*a.val) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  apply hirr c
  intro n
  apply (((A n).units.map (coordinateInclusion hNM)).relativeStar_mem c.val).mpr
  refine ⟨c.property,?_⟩
  intro i j
  have hi : ((A n).units.entry i j).val ∈ (A n).units.concreteAlgebra := by
    exact ((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)
  exact hc ⟨((A n).units.entry i j).val,stage_le_generated A n hi⟩

theorem concrete_stage_monotone (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.algebra)) :
    Monotone (fun n => (A n).units.concreteAlgebra) := by
  intro i j hij x hx
  let a : N.toStarSubalgebra := ⟨x,(A i).units.concreteAlgebra_le hx⟩
  exact ((A j).units.mem_concreteAlgebra a).mpr
    (hA hij (((A i).units.mem_concreteAlgebra a).mp hx))

def scalarStage (N : VonNeumannAlgebra H) : FiniteMatrixStage N where
  size := 1
  positive := by norm_num
  units := {
    entry := fun _ _ => 1
    star_entry := by intros; simp
    mul_entry := by
      intro i j k l
      rw [ite_eq_left (Subsingleton.elim j k),one_mul]
    total := by simp }

theorem exists_irreducible_matrix_generated_algebra
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      WOTClosed (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  obtain ⟨A,hA,hmono,hscalar⟩ := exists_irreducible_matrix_sequence τ hNM hfactor hdiff hirr hsep (scalarStage N)
  exact ⟨A,hA,concrete_stage_monotone A hmono,fun n => (A n).units.concrete_finiteDimensional,
    generated_closed A,generated_le A,generated_relative_scalar A τ hNM hscalar⟩

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_isII1 (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) : IsII1Factor P.toStarSubalgebra where
  nonzero := tracial_nonzero τ
  weaklyClosed := vonNeumann_wotClosed P
  factor c hc := by
    obtain ⟨z,hz⟩ := hirr (coordinateInclusion hPM c) (fun a => by
      simpa only [map_mul] using congrArg (coordinateInclusion hPM) (hc a))
    refine ⟨z,?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val) hz
  finite := tracial_isometry_coisometry (restrictedTrace τ hPM)
  diffuse := irreducible_subalgebra_diffuse τ hPM hdiff hirr

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generatedVonNeumann (A : ℕ → FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (generated A) (generated_closed A)

theorem generatedVonNeumann_le (A : ℕ → FiniteMatrixStage N) : generatedVonNeumann A ≤ N :=
  generated_le A

def generatedTrace (A : ℕ → FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TracialRepresentation (generatedVonNeumann A) :=
  restrictedTrace τ ((generatedVonNeumann_le A).trans hNM)

theorem generated_isII1 (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra)) : IsII1Factor (generated A) := by
  apply irreducible_subalgebra_isII1 (restrictedTrace τ hNM) (generatedVonNeumann_le A) hdiff
  intro c hc
  have h := hirr (coordinateInclusion hNM c) (fun a =>
    congrArg (fun b : N.toStarSubalgebra => b.val) (hc a))
  refine ⟨τ.trace (coordinateInclusion hNM c),?_⟩
  exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)

theorem exists_irreducible_matrix_generated_II1
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      IsII1Factor (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  obtain ⟨A,hA,hmono,hfd,_,hAN,hscalar⟩ :=
    exists_irreducible_matrix_generated_algebra τ hNM hfactor hdiff hirr hsep
  exact ⟨A,hA,hmono,hfd,generated_isII1 A τ hNM hdiff hscalar,hAN,hscalar⟩

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def bicommutantStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))

theorem bicommutantStar_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantStar S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  unfold bicommutantStar
  rw [StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

def bicommutantVonNeumann (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := bicommutantStar S
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (bicommutantStar S : Set (H →L[ℂ] H)))=
      (bicommutantStar S : Set (H →L[ℂ] H))
    rw [bicommutantStar_coe,Set.centralizer_centralizer_centralizer]

theorem bicommutantVonNeumann_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantVonNeumann S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  exact bicommutantStar_coe S

theorem wstar_starAlgebra_eq_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    wstar (S : Set (H →L[ℂ] H))=(bicommutantVonNeumann S).toStarSubalgebra := by
  apply le_antisymm
  · apply wstar_le (Tracial.vonNeumann_wotClosed _)
    intro a ha
    change a ∈ (bicommutantVonNeumann S : Set (H →L[ℂ] H))
    rw [bicommutantVonNeumann_coe]
    exact fun b hb => (hb a ha).symm
  · intro a ha
    have hb : a ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      rwa [← bicommutantVonNeumann_coe]
    rw [← SetLike.mem_coe,← wotClosed_bicommutant _ (wstar_closed _)]
    exact fun b hb' => hb b (fun c hc => hb' c (subset_wstar _ hc))

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {N M : VonNeumannAlgebra H}

def stageUnion (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  ⨆ n,(A n).units.concreteAlgebra

theorem stageUnion_coe (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    (stageUnion A : Set (H →L[ℂ] H))=⋃ n,((A n).units.concreteAlgebra : Set (H →L[ℂ] H)) :=
  StarSubalgebra.coe_iSup_of_directed hA.directed_le

theorem generated_eq_wstar_union (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    generated A=wstar (stageUnion A : Set (H →L[ℂ] H)) := by
  rw [stageUnion_coe A hA]
  rfl

theorem exists_stage_strong_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) (T : generated A)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ a : (A n).units.concreteAlgebra,∀ x ∈ s,‖T.val x-a.val x‖ < ε := by
  have hT : T.val ∈ Set.centralizer (Set.centralizer (stageUnion A : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    change T.val ∈ (bicommutantVonNeumann (stageUnion A)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,← generated_eq_wstar_union A hA]
    exact T.property
  obtain ⟨a,ha⟩ := bicommutant_finite_strong_approximation (stageUnion A) T.val hT s ε hε
  have hm := a.property
  rw [← SetLike.mem_coe,stageUnion_coe A hA] at hm
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm
  exact ⟨n,⟨a.val,hn⟩,ha⟩

theorem exists_stage_norm₂_approximation (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : M.toStarSubalgebra)
    (hx : x.val ∈ generated A) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ a : M.toStarSubalgebra,a.val ∈ (A n).units.concreteAlgebra ∧ τ.norm₂ (x-a) < ε := by
  classical
  obtain ⟨n,a,ha⟩ := exists_stage_strong_approximation A hA ⟨x.val,hx⟩ {τ.vector} ε hε
  exact ⟨n,⟨a.val,hNM ((A n).units.concreteAlgebra_le a.property)⟩,a.property,
    ha τ.vector (Finset.mem_singleton_self _)⟩

end FiniteMatrixStage

end Generator

end

end OAI
