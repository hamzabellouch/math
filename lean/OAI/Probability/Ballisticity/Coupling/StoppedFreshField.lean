import Mathlib
import OAI.Probability.Ballisticity.Estimates.GlobalProfile
import OAI.Probability.Ballisticity.Estimates.StoppedSplice

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stoppedRowsEvent_mono {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (A : Set (Environment d)) (hA : StoppedRowsEvent S τ A) : StoppedRowsEvent S σ A := by
  intro n
  have he : A∩{ω | σ ω=n}=
      (⋃ k : Fin (n+1), A∩{ω | τ ω=k.val})∩{ω | σ ω=n} := by
    ext ω
    constructor
    · rintro ⟨ha,hs⟩
      refine ⟨Set.mem_iUnion.mpr ⟨⟨τ ω,by have hh := hτσ ω; change σ ω = n at hs; omega⟩,ha,rfl⟩,hs⟩
    · rintro ⟨hk,hs⟩
      obtain ⟨k,ha,_⟩ := Set.mem_iUnion.mp hk
      exact ⟨ha,hs⟩
  rw [he]
  have hAk (k : Fin (n+1)) : MeasurableSet[rowSigma (S n)] (A∩{ω | τ ω=k.val}) := by
    have hk : k.val≤n := Nat.le_of_lt_succ k.isLt
    exact (rowSigma_mono (hS hk)) _ (hA k.val)
  exact (MeasurableSet.iUnion hAk).inter (hσ n)

lemma stoppedRowsEvent_measurable {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (A : Set (Environment d)) (hA : StoppedRowsEvent S τ A) : MeasurableSet A := by
  have he : A=⋃ n, A∩{ω | τ ω=n} := by ext ω; simp
  rw [he]
  exact MeasurableSet.iUnion fun n => (rowSigma_le _) _ (hA n)

theorem stopped_fresh_joint_map {d : ℕ} {D F : Type*} [MeasurableSpace D] [MeasurableSpace F]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (U : Environment d → D) (hUm : Measurable U)
    (hU : ∀ B, MeasurableSet B → StoppedRowsEvent S τ (U ⁻¹' B))
    (V : ℕ → Environment d → F)
    (hV : ∀ n, @Measurable _ _ (rowSigma (S n)ᶜ) _ (V n))
    (R : Measure F) [IsProbabilityMeasure R]
    (hR : ∀ n, (environmentLaw ν).map (V n)=R) :
    (environmentLaw ν).map (fun ω => (U ω,V (τ ω) ω))=((environmentLaw ν).map U).prod R := by
  have hVm (n : ℕ) : Measurable (V n) := (hV n).mono (rowSigma_le _) le_rfl
  have hVm' : Measurable (fun p : Environment d×ℕ => V p.2 p.1) :=
    measurable_from_prod_countable_left hVm
  have hmap : Measurable (fun ω => (U ω,V (τ ω) ω)) :=
    hUm.prodMk (hVm'.comp (measurable_id.prodMk (measurable_of_stop_events S τ hτ)))
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hmap (hA.prod hB),Measure.prod_prod,Measure.map_apply hUm hA]
  let E (n : ℕ) := (U ⁻¹' A)∩{ω | τ ω=n}
  let K (n : ℕ) := E n∩(V n ⁻¹' B)
  have hE (n : ℕ) : MeasurableSet[rowSigma (S n)] (E n) := hU A hA n
  have hEm (n : ℕ) : MeasurableSet (E n) := (rowSigma_le _) _ (hE n)
  have hK (n : ℕ) : MeasurableSet (K n) := (hEm n).inter (hB.preimage (hVm n))
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro n m hnm
    exact Set.disjoint_left.mpr fun ω hn hm => hnm (hn.2.symm.trans hm.2)
  have hKd : Pairwise (Function.onFun Disjoint K) := by
    intro n m hnm
    exact (hEd hnm).mono Set.inter_subset_left Set.inter_subset_left
  have he : (fun ω => (U ω,V (τ ω) ω)) ⁻¹' (A ×ˢ B)=⋃ n, K n := by
    ext ω
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨τ ω,⟨ha,rfl⟩,hb⟩
    · intro h
      obtain ⟨n,⟨ha,hn⟩,hb⟩ := Set.mem_iUnion.mp h
      refine ⟨ha,?_⟩
      change τ ω=n at hn
      change V n ω∈B at hb
      simpa only [hn] using hb
  rw [he,measure_iUnion hKd hK]
  have hfactor (n : ℕ) : environmentLaw ν (K n)=environmentLaw ν (E n)*R B := by
    have hind := (Indep_iff _ _ _).mp (environment_indep_rows ν (S:=S n)
      (T:=(S n)ᶜ) disjoint_compl_right) (E n) (V n ⁻¹' B) (hE n) ((hV n) hB)
    rw [←Measure.map_apply (hVm n) hB,hR n] at hind
    exact hind
  simp_rw [hfactor]
  rw [ENNReal.tsum_mul_right,←measure_iUnion hEd hEm]
  have he' : (⋃ n, E n)=U ⁻¹' A := by ext ω; simp [E]
  rw [he']

noncomputable def upperField {d : ℕ} (e : Direction d) (n : ℕ) (ω : Environment d) :
    (ℕ×HorizontalSpace e) → Row d := fun p => ω (horizontalLift e (n+p.1) p.2)

lemma upperField_index_injective {d : ℕ} (e : Direction d) (n : ℕ) :
    Function.Injective (fun p : ℕ×HorizontalSpace e => horizontalLift e (n+p.1) p.2) := by
  intro p q h
  have hh := congrArg (signedHeight e) h
  have hz := congrArg (horizontalProjection e) h
  rw [signedHeight_horizontalLift,signedHeight_horizontalLift] at hh
  rw [horizontalProjection_lift,horizontalProjection_lift] at hz
  exact Prod.ext (by exact_mod_cast (add_left_cancel hh)) hz

lemma upperField_measurable_rows {d : ℕ} (e : Direction d) (n : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) n)ᶜ) _ (upperField e n) := by
  apply @Measurable.of_eval (Environment d) (ℕ×HorizontalSpace e) (fun _ => Row d)
    (rowSigma (BelowHeight (realPosition (step e)) n)ᶜ) (fun _ => inferInstance)
  intro p
  apply measurable_row_on
  change ¬ dot (realPosition (horizontalLift e (n+p.1) p.2)) (realPosition (step e))<n
  rw [signedHeight_projection,signedHeight_horizontalLift]
  push_cast
  linarith [Nat.cast_nonneg (α:=ℝ) p.1]

lemma upperField_map {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (n : ℕ) : (environmentLaw ν).map (upperField e n)=
      Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν) :=
  Measure.map_infinitePi_infinitePi_of_inj (upperField_index_injective e n)

end DirectionalTransience

end

end OAI
