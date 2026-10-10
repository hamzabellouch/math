import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Zero-one laws for invariant Bernoulli events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory ProbabilityTheory
open scoped ENNReal symmDiff
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_aut_disjoint_edges [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (F : Finset E) : ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ Disjoint F (F.image b) := by
  classical
  let B : Finset V := F.biUnion (fun e => (G e).toFinset)
  let x : V := Classical.arbitrary V
  obtain ⟨n,hn⟩ := exists_transportCut G hconn x B
  have hfin : (⋃ z ∈ (B : Set V), reachBall G z n).Finite :=
    B.finite_toSet.biUnion (fun z _ => finite_reachBall hloc z n)
  obtain ⟨y,⟨a,b,hab,hax⟩,hy⟩ :=
    (vertexOrbit_infinite G hconn hloc hqt x).exists_notMem_finite hfin
  refine ⟨a,b,hab,Finset.disjoint_left.mpr ?_⟩
  intro e he heb
  obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp heb
  have hm : ∃ z, z ∈ G e' := Sym2.inductionOn (G e') (fun z w => ⟨z,by simp⟩)
  obtain ⟨z,hz⟩ := hm
  have hzB : z ∈ B := Finset.mem_biUnion.mpr ⟨e',he',by simpa using hz⟩
  have hazB : a z ∈ B := by
    apply Finset.mem_biUnion.mpr
    refine ⟨b e',he,?_⟩
    rw [Sym2.mem_toFinset,hab]
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  apply hy
  simp only [Set.mem_iUnion]
  refine ⟨a z,hazB,?_⟩
  rw [←hax]
  exact mem_reachBall_aut G hab (hn z hzB).1

theorem label_cylinder_independent (F : Finset E) (b : E ≃ E)
    (hd : Disjoint F (F.image b)) (S : Set (F → unitInterval)) (hS : MeasurableSet S) :
    (labelLaw : Measure (E → unitInterval))
      (cylinder F S ∩ (fun l : E → unitInterval => l ∘ b) ⁻¹' cylinder F S) =
      labelLaw (cylinder F S) * labelLaw (cylinder F S) := by
  classical
  have hi : iIndepFun (fun e (l : E → unitInterval) => l e) labelLaw :=
    iIndepFun_infinitePi (X := fun (_ : E) (x : unitInterval) => x) (fun _ => measurable_id)
  have h := hi.indepFun_finset F (F.image b) hd (fun e => measurable_pi_apply e)
  let r : ((F.image b) → unitInterval) → (F → unitInterval) :=
    fun l e => l ⟨b e,Finset.mem_image.mpr ⟨e,e.property,rfl⟩⟩
  have hr : Measurable r := Measurable.of_eval (fun _ => measurable_pi_apply _)
  have h' := h.comp measurable_id hr
  have he := h'.meas_inter (s := cylinder F S)
    (t := (fun l : E → unitInterval => l ∘ b) ⁻¹' cylinder F S)
    ⟨S,hS,rfl⟩ ⟨S,hS,rfl⟩
  have hm : Measurable (fun l : E → unitInterval => l ∘ b) :=
    Measurable.of_eval fun e => measurable_pi_apply (b e)
  rw [←Measure.map_apply hm hS.cylinder,labelLaw_map_precomp] at he
  exact he

theorem label_invariant_zero_one [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (A : Set (E → unitInterval)) (hA : MeasurableSet A)
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b →
      (fun l : E → unitInterval => l ∘ b) ⁻¹' A = A) :
    labelLaw A = 0 ∨ labelLaw A = 1 := by
  classical
  let μ : Measure (E → unitInterval) := labelLaw
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
    (isSetAlgebra_measurableCylinders (α := fun _ : E => unitInterval))
    generateFrom_measurableCylinders.symm
  have heq : μ.real A ≤ (μ.real A)^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨B,hB,hAB⟩ := hd.approx A hA (measure_ne_top _ _) (ε/4) (by positivity)
    obtain ⟨F,S,hS,rfl⟩ := (mem_measurableCylinders B).mp hB
    let B : Set (E → unitInterval) := cylinder F S
    have hBm : MeasurableSet B := hS.cylinder
    have hABr : μ.real (A ∆ B) < ε/4 := by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hAB |>.trans_le
        (by rw [ENNReal.toReal_ofReal (by positivity)])
    obtain ⟨a,b,hab,habF⟩ := exists_aut_disjoint_edges G hconn hloc hqt F
    let φ : (E → unitInterval) → (E → unitInterval) := fun l => l ∘ b
    have hφ : Measurable φ := Measurable.of_eval fun e => measurable_pi_apply (b e)
    have hφμ : μ.map φ = μ := labelLaw_map_precomp b
    have hφA : φ ⁻¹' A = A := hinv a b hab
    have hφAB : μ.real (A ∆ (φ ⁻¹' B)) = μ.real (A ∆ B) := by
      conv_lhs => rw [←hφA,←Set.preimage_symmDiff]
      change (μ (φ ⁻¹' (A ∆ B))).toReal = _
      rw [←Measure.map_apply hφ (hA.symmDiff hBm),hφμ]
      rfl
    have hC : MeasurableSet (B ∩ φ ⁻¹' B) := hBm.inter (hBm.preimage hφ)
    have hsub : A ∆ (B ∩ φ ⁻¹' B) ⊆ (A ∆ B) ∪ (A ∆ (φ ⁻¹' B)) := by
      intro l hl
      simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_union] at hl ⊢
      tauto
    have hAC : μ.real (A ∆ (B ∩ φ ⁻¹' B)) < ε/2 := by
      calc
        _ ≤ μ.real ((A ∆ B) ∪ (A ∆ (φ ⁻¹' B))) := measureReal_mono hsub
        _ ≤ μ.real (A ∆ B) + μ.real (A ∆ (φ ⁻¹' B)) := measureReal_union_le _ _
        _ < ε/2 := by rw [hφAB]; linarith
    have hprod : μ.real (B ∩ φ ⁻¹' B) = (μ.real B)^2 := by
      change (labelLaw (B ∩ φ ⁻¹' B)).toReal = _
      rw [label_cylinder_independent F b habF S hS,ENNReal.toReal_mul,pow_two]
      rfl
    have h1 := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) hA.nullMeasurableSet hC.nullMeasurableSet
    have h2 := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) hA.nullMeasurableSet hBm.nullMeasurableSet
    have h1' : μ.real A - (μ.real B)^2 < ε/2 := by
      rw [hprod] at h1
      exact lt_of_le_of_lt (le_trans (le_abs_self (μ.real A - (μ.real B)^2)) h1) hAC
    have h2' : μ.real B - μ.real A < ε/4 := by
      have hh := (neg_le_abs (μ.real A - μ.real B)).trans h2 |>.trans_lt hABr
      linarith
    have hA0 : 0 ≤ μ.real A := measureReal_nonneg
    have hB0 : 0 ≤ μ.real B := measureReal_nonneg
    have hA1 : μ.real A ≤ 1 := measureReal_le_one
    have hB1 : μ.real B ≤ 1 := measureReal_le_one
    have hsq : (μ.real B)^2 ≤ (μ.real A)^2 + ε/2 := by
      by_cases hle : μ.real B ≤ μ.real A
      · nlinarith [sq_nonneg (μ.real A-μ.real B)]
      · have hp := mul_le_mul (le_of_lt h2') (show μ.real B+μ.real A ≤ 2 by linarith)
          (show 0 ≤ μ.real B+μ.real A by positivity) (show 0 ≤ ε/4 by positivity)
        nlinarith
    linarith
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  have hA1 : μ.real A ≤ 1 := measureReal_le_one
  have he : μ.real A = 0 ∨ μ.real A = 1 := by
    have : μ.real A * (μ.real A-1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases he with h | h
  · left
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top _ _)
  · right
    exact (ENNReal.toReal_eq_one_iff _).mp h

end Percolation

end OAI
