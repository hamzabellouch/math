import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FourierObstruction01
import OAI.Combinatorics.SumProduct.Alignment.PolynomialDephasing01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
 
namespace TorusLeibman
open scoped BigOperators
open PolynomialWeyl WeylCoefficients FourierObstruction MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def polynomialOrbit (p : ι → Polynomial ℝ) (n : ℕ) : UnitAddTorus ι :=
  fun i => (((p i).eval (n : ℝ) : ℝ) : UnitAddCircle)

def characterPolynomial (k : ι → ℤ) (p : ι → Polynomial ℝ) : Polynomial ℝ :=
  ∑ i, (k i : ℝ) • p i

theorem characterPolynomial_coeff (k : ι → ℤ) (p : ι → Polynomial ℝ) (j : ℕ) :
    (characterPolynomial k p).coeff j = ∑ i, (k i : ℝ) * (p i).coeff j := by
  simp [characterPolynomial]

theorem characterPolynomial_degree (k : ι → ℤ) (p : ι → Polynomial ℝ) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) : (characterPolynomial k p).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [characterPolynomial_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by exact (hp i).trans_lt hj), mul_zero]

theorem phase_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    phase (∑ a ∈ s, f a) = ∏ a ∈ s, phase (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | @insert a s ha ih => simp [Finset.sum_insert, Finset.prod_insert, ha, ih]

theorem character_polynomialOrbit (k : ι → ℤ) (p : ι → Polynomial ℝ) :
    (fun n => UnitAddTorus.mFourier k (polynomialOrbit p n)) =
      polynomialPhase (characterPolynomial k p) := by
  funext n
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, polynomialOrbit,
    fourier_coe_apply, Complex.ofReal_one, div_one,
    polynomialPhase, characterPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, phase_sum]
  apply Finset.prod_congr rfl
  intro i _
  unfold phase
  congr 1
  push_cast
  ring

 

theorem quantitative_torus_leibman (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ N : ℕ, 0 < N → ∀ p : ι → Polynomial ℝ,
      (∀ i, (p i).natDegree ≤ d) →
      (∃ f : C(UnitAddTorus ι, ℂ), LipschitzWith 1 f ∧ ‖f‖ ≤ 1 ∧
        δ ≤ ‖mean N (fun n => f (polynomialOrbit p n)) - ∫ t, f t ∂torusHaar ι‖) →
      ∃ k : ι → ℤ, k ≠ 0 ∧ (∀ i, |(k i : ℝ)| ≤ A) ∧ ∃ m : ℕ → ℤ,
        ∀ j : ℕ, 0 < j → j ≤ d →
          |(∑ i, (k i : ℝ) * (p i).coeff j) - m j| ≤ (A : ℝ) / (N : ℝ) ^ j := by
  classical
  obtain ⟨S, η, hη, htest⟩ := torus_character_obstruction ι δ hδ
  obtain ⟨B, hB, hinv⟩ := coefficient_inverse d η hη
  let M := ∑ k ∈ S, ∑ i, (k i).natAbs
  let A := B * (M + 1)
  have hBA : B ≤ A := by dsimp [A]; nlinarith
  have hA : 0 < A := hB.trans_le hBA
  refine ⟨A, hA, ?_⟩
  intro N hN p hp hlarge
  obtain ⟨k, hk, hk₀, hcorr⟩ := htest N hN (polynomialOrbit p) hlarge
  rw [character_polynomialOrbit] at hcorr
  obtain ⟨q, hq, hqB, m, hm⟩ := hinv N hN (characterPolynomial k p)
    (characterPolynomial_degree k p d hp) hcorr
  let k' : ι → ℤ := fun i => (q : ℤ) * k i
  have hk' : k' ≠ 0 := by
    intro he
    apply hk₀
    funext i
    have := congrFun he i
    simp only [k', Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at this
    exact this.resolve_left (Nat.ne_of_gt hq)
  refine ⟨k', hk', ?_, m, ?_⟩
  · intro i
    have hki : (k i).natAbs ≤ M := by
      have h₁ : (k i).natAbs ≤ ∑ x, (k x).natAbs :=
        Finset.single_le_sum (f := fun x => (k x).natAbs) (fun x _ => Nat.zero_le _) (Finset.mem_univ i)
      have h₂ : (∑ x, (k x).natAbs) ≤ M :=
        Finset.single_le_sum (f := fun x : ι → ℤ => ∑ i, (x i).natAbs) (fun x (_ : x ∈ S) => Nat.zero_le _) hk
      exact h₁.trans h₂
    have hkM : |(k i : ℝ)| ≤ (M : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le.mpr hki : ((k i).natAbs : ℝ) ≤ M)
    have hq₀ : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    simp only [k', Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg hq₀]
    have h := mul_le_mul (Nat.cast_le.mpr hqB : (q : ℝ) ≤ B) hkM
      (abs_nonneg _) (Nat.cast_nonneg B)
    have hMA : (B : ℝ) * M ≤ A := by
      dsimp [A]
      push_cast
      nlinarith [(show (0 : ℝ) ≤ B from Nat.cast_nonneg B)]
    exact h.trans hMA
  · intro j hj hjd
    have he : (∑ i, (k' i : ℝ) * (p i).coeff j) =
        (q : ℝ) * (characterPolynomial k p).coeff j := by
      simp only [k', Int.cast_mul, Int.cast_natCast, characterPolynomial_coeff,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact (hm j hj hjd).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hBA)
      (by positivity))

end
end TorusLeibman
end
 

 
section
noncomputable section
open scoped BigOperators
namespace AbelianMalcevTorus
open RationalLattice RationalQuotientFunctions
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

 

def torusProjection (g : G) : UnitAddTorus (Fin n) := fun i => (c.coord g i : UnitAddCircle)

include hadd in
lemma torusProjection_mul (g h : G) :
    torusProjection c (g*h)=torusProjection c g+torusProjection c h := by
  ext i
  simp only [torusProjection,hadd,AddCircle.coe_add,Pi.add_apply]

lemma torusProjection_one : torusProjection c (1:G)=0 := by
  ext i
  simp [torusProjection,c.one_coord]

include hΓ in
lemma torusProjection_eq_zero (g : G) : torusProjection c g=0 ↔ g∈Γ := by
  rw [hΓ]
  constructor
  · intro h i
    have hi : (c.coord g i : UnitAddCircle)=0 := congrFun h i
    obtain ⟨z,hz⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hi
    exact ⟨z,by simpa using hz.symm⟩
  · intro h
    ext i
    obtain ⟨z,hz⟩ := h i
    exact (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨z,by simpa using hz.symm⟩

lemma torusProjection_surjective : Function.Surjective (torusProjection c) := by
  intro t
  have hh (i : Fin n) : ∃ x : ℝ, (x : UnitAddCircle)=t i :=
    QuotientAddGroup.mk_surjective (t i)
  choose x hx using hh
  exact ⟨c.coord.symm x,by ext i; simpa [torusProjection] using hx i⟩

lemma continuous_torusProjection : Continuous (torusProjection c) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1:ℝ)).comp ((continuous_apply i).comp c.coord.continuous)

 
def quotientTorus : C(G⧸Γ,UnitAddTorus (Fin n)) :=
  ⟨cosetLift Γ (torusProjection c) (by
      intro g a ha
      rw [torusProjection_mul c hadd, (torusProjection_eq_zero c Γ hΓ a).mpr ha,add_zero]),
    continuous_cosetLift _ _ _ (continuous_torusProjection c)⟩

@[simp] lemma quotientTorus_mk (g : G) :
    quotientTorus c hadd Γ hΓ (QuotientGroup.mk g)=torusProjection c g := rfl

lemma quotientTorus_bijective : Function.Bijective (quotientTorus c hadd Γ hΓ) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with | h g =>
      induction y using Quotient.inductionOn with | h a =>
        apply QuotientGroup.eq.mpr
        apply (torusProjection_eq_zero c Γ hΓ (g⁻¹*a)).mp
        have hm := torusProjection_mul c hadd g⁻¹ g
        rw [inv_mul_cancel,torusProjection_one] at hm
        rw [torusProjection_mul c hadd]
        change torusProjection c g=torusProjection c a at h
        rw [← h]
        exact hm.symm
  · intro y
    obtain ⟨g,hg⟩ := torusProjection_surjective c y
    exact ⟨QuotientGroup.mk g,hg⟩

include c hΓ in
lemma quotient_compact : CompactSpace (G⧸Γ) := by
  obtain ⟨K,hK,hrep⟩ := compact_reps_of_integerCoordinates c Γ hΓ
  exact (show CompactGroupProducts.HasCompactReps ⊤ Γ from
    ⟨K,hK,Set.subset_univ _,fun g _ => hrep g⟩).quotient_compactSpace

 

def quotientHomeomorph : (G⧸Γ) ≃ₜ UnitAddTorus (Fin n) := by
  letI := quotient_compact c Γ hΓ
  let e := Equiv.ofBijective (quotientTorus c hadd Γ hΓ) (quotientTorus_bijective c hadd Γ hΓ)
  exact Continuous.homeoOfEquivCompactToT2 (f:=e) (quotientTorus c hadd Γ hΓ).continuous

@[simp] lemma quotientHomeomorph_mk (g : G) :
    quotientHomeomorph c hadd Γ hΓ (QuotientGroup.mk g)=torusProjection c g := rfl

lemma quotientHomeomorph_smul (g : G) (x : G⧸Γ) :
    quotientHomeomorph c hadd Γ hΓ (g • x)=
      torusProjection c g+quotientHomeomorph c hadd Γ hΓ x := by
  induction x using Quotient.inductionOn with | h a =>
    exact torusProjection_mul c hadd g a

end AbelianMalcevTorus
end
end
 

 
section
noncomputable section
namespace AbelianMalcevTorus
open MeasureTheory RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

 

theorem coordinateHaar_map (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (G⧸Γ) μ] :
    Measure.map (quotientHomeomorph c hadd Γ hΓ) μ = FourierObstruction.torusHaar (Fin n) := by
  let e := quotientHomeomorph c hadd Γ hΓ
  let ν := Measure.map e μ
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).mpr inferInstance
  have hinv : ν.IsAddLeftInvariant := by
    constructor
    intro t
    obtain ⟨g,rfl⟩ := torusProjection_surjective c t
    change Measure.map (fun x => torusProjection c g+x) (Measure.map e μ)=Measure.map e μ
    rw [Measure.map_map (by fun_prop) e.measurable]
    have he : (fun x => torusProjection c g+x) ∘ e=e ∘ (fun x : G⧸Γ => g • x) := by
      funext x
      exact (quotientHomeomorph_smul c hadd Γ hΓ g x).symm
    rw [he,← Measure.map_map e.measurable (by fun_prop),MeasureTheory.map_smul g μ]
  let := hinv
  let : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν Set.univ
    isCompact_univ (by simp) (by simp) (by simp)
  let : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  let : (FourierObstruction.torusHaar (Fin n)).IsAddHaarMeasure := by
    change (volume : Measure (UnitAddTorus (Fin n))).IsAddHaarMeasure
    infer_instance
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure ν (FourierObstruction.torusHaar (Fin n))

end AbelianMalcevTorus

end
end
end
end
end

end OAI
