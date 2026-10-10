import OAI.Probability.RadialTransition.ProductFock

namespace OAI

universe uX uM uIndex uY

noncomputable section


open MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section MultisetEnergy
variable {X : Type uX}

def multisetPairing (v : X → X → ℝ) (s t : Multiset X) : ℝ :=
  (s.map (fun x => (t.map (v x)).sum)).sum

def multisetDiagonal (v : X → X → ℝ) (s : Multiset X) : ℝ :=
  (s.map (fun x => v x x)).sum

def multisetEnergy (v : X → X → ℝ) (s : Multiset X) : ℝ :=
  (1/2:ℝ) * (multisetPairing v s s - multisetDiagonal v s)

@[simp] lemma multisetPairing_zero_left (v : X → X → ℝ) (s : Multiset X) :
    multisetPairing v 0 s = 0 := by simp [multisetPairing]
@[simp] lemma multisetPairing_zero_right (v : X → X → ℝ) (s : Multiset X) :
    multisetPairing v s 0 = 0 := by simp [multisetPairing]
@[simp] lemma multisetPairing_add_left (v : X → X → ℝ) (s t u : Multiset X) :
    multisetPairing v (s+t) u = multisetPairing v s u + multisetPairing v t u := by
  simp [multisetPairing]
@[simp] lemma multisetPairing_add_right (v : X → X → ℝ) (s t u : Multiset X) :
    multisetPairing v s (t+u) = multisetPairing v s t + multisetPairing v s u := by
  simp [multisetPairing, Multiset.sum_map_add]
@[simp] lemma multisetDiagonal_add (v : X → X → ℝ) (s t : Multiset X) :
    multisetDiagonal v (s+t) = multisetDiagonal v s + multisetDiagonal v t := by
  simp [multisetDiagonal]
@[simp] lemma multisetDiagonal_zero (v : X → X → ℝ) : multisetDiagonal v 0 = 0 := by simp [multisetDiagonal]

lemma multisetPairing_symm {v : X → X → ℝ} (hv : ∀ x y, v x y = v y x) (s t : Multiset X) :
    multisetPairing v s t = multisetPairing v t s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [multisetPairing, Multiset.map_cons, Multiset.sum_cons] at *
    simp_rw [Multiset.sum_map_add, hv a]
    rw [ih]

lemma multisetEnergy_add {v : X → X → ℝ} (hv : ∀ x y, v x y = v y x) (s t : Multiset X) :
    multisetEnergy v (s+t) = multisetEnergy v s + multisetEnergy v t + multisetPairing v s t := by
  simp only [multisetEnergy, multisetPairing_add_left, multisetPairing_add_right, multisetDiagonal_add]
  rw [multisetPairing_symm hv t s]
  ring

lemma sum_map_configuration {ι : Type} [Fintype ι] {M : Type uM} [AddCommMonoid M]
    (f : X → M) (x : ι → X) : ((configurationMultiset x).map f).sum = ∑ i, f (x i) := by
  unfold configurationMultiset
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp [Multiset.sum_sum]

lemma multisetPairing_configuration {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : X → X → ℝ) (x : ι → X) (y : κ → X) :
    multisetPairing v (configurationMultiset x) (configurationMultiset y) = ∑ i, ∑ j, v (x i) (y j) := by
  simp only [multisetPairing, sum_map_configuration]

lemma multisetDiagonal_configuration {ι : Type} [Fintype ι] (v : X → X → ℝ) (x : ι → X) :
    multisetDiagonal v (configurationMultiset x) = ∑ i, v (x i) (x i) := by
  simp only [multisetDiagonal, sum_map_configuration]

lemma multisetEnergy_particle (v : X → X → ℝ) (s : ParticleState X) :
    multisetEnergy v (particleMultiset s) = pairWithin v s := by
  classical
  simp only [multisetEnergy, particleMultiset, multisetPairing_configuration, multisetDiagonal_configuration,
    pairWithin]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hh : (∑ j : Fin s.1, v (s.2 i) (s.2 j)) =
      v (s.2 i) (s.2 i) + ∑ j : Fin s.1, if i = j then 0 else v (s.2 i) (s.2 j) := by
    conv_lhs =>
      arg 2; ext j
      rw [show v (s.2 i) (s.2 j) = (if i = j then v (s.2 i) (s.2 j) else 0) +
        (if i = j then 0 else v (s.2 i) (s.2 j)) by split_ifs <;> simp]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  linarith

lemma multisetPairing_fin_sum_left {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) (t : Multiset X) :
    multisetPairing v (∑ i ∈ T, s i) t = ∑ i ∈ T, multisetPairing v (s i) t := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetPairing_fin_sum_right {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) (t : Multiset X) :
    multisetPairing v t (∑ i ∈ T, s i) = ∑ i ∈ T, multisetPairing v t (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetDiagonal_fin_sum {ι : Type uIndex} (v : X → X → ℝ) (T : Finset ι)
    (s : ι → Multiset X) :
    multisetDiagonal v (∑ i ∈ T, s i) = ∑ i ∈ T, multisetDiagonal v (s i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih => simp [hi, ih]

lemma multisetEnergy_sum {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (v : X → X → ℝ) (s : ι → Multiset X) :
    multisetEnergy v (∑ i, s i) = ∑ i, multisetEnergy v (s i) +
      (1/2:ℝ) * ∑ i, ∑ j, if i = j then 0 else multisetPairing v (s i) (s j) := by
  have hh (i : ι) : (∑ j, multisetPairing v (s i) (s j)) =
      multisetPairing v (s i) (s i) + ∑ j, if i = j then 0 else multisetPairing v (s i) (s j) := by
    conv_lhs =>
      arg 2; ext j
      rw [show multisetPairing v (s i) (s j) =
        (if i = j then multisetPairing v (s i) (s j) else 0) +
        (if i = j then 0 else multisetPairing v (s i) (s j)) by split_ifs <;> simp]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [multisetEnergy, multisetPairing_fin_sum_left, multisetDiagonal_fin_sum]
  simp_rw [multisetPairing_fin_sum_right, hh]
  simp only [multisetEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma multisetEnergy_mappedMulti {I : Type} [Fintype I] [DecidableEq I] (Y : I → Type uY)
    (pos : ∀ i, Y i → X) (v : X → X → ℝ) (x : ∀ i, ParticleState (Y i)) :
    multisetEnergy v (mappedMultiParticleMultiset Y pos x) =
      pairCellEnergy (fun i j a b => v (pos i a) (pos j b)) x := by
  unfold mappedMultiParticleMultiset pairCellEnergy cellHamiltonian
  rw [multisetEnergy_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [multisetEnergy_particle]
    rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rfl
    · exact multisetPairing_configuration v _ _

section Continuity
variable [TopologicalSpace X]

lemma continuous_multisetPairing_right {v : X → X → ℝ}
    (hv : Continuous (Function.uncurry v)) (s : Multiset X)
    {ι : Type} [Fintype ι] : Continuous (fun x : ι → X => multisetPairing v s (configurationMultiset x)) := by
  induction s using Multiset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : ι → X => (0:ℝ)))
  | @cons a s ih =>
    simp only [multisetPairing, Multiset.map_cons, Multiset.sum_cons, sum_map_configuration] at *
    exact (continuous_finsetSum _ (fun i _ => hv.comp (continuous_const.prodMk (continuous_apply i)))).add ih

lemma continuous_multisetEnergy_configuration {v : X → X → ℝ}
    (hv : Continuous (Function.uncurry v)) {ι : Type} [Fintype ι] :
    Continuous (fun x : ι → X => multisetEnergy v (configurationMultiset x)) := by
  simp only [multisetEnergy, multisetPairing_configuration, multisetDiagonal_configuration]
  apply continuous_const.mul
  apply Continuous.sub
  · exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => hv.comp (show Continuous (fun x : ι → X => (x i, x j)) from (continuous_apply i).prodMk (continuous_apply j))))
  · exact continuous_finsetSum _ (fun i _ => hv.comp (show Continuous (fun x : ι → X => (x i, x i)) from (continuous_apply i).prodMk (continuous_apply i)))

lemma continuousConfiguration_boltzmann {v : X → X → ℝ}
    (hv : Continuous (Function.uncurry v)) (hsym : ∀ x y, v x y = v y x) (β : ℝ) :
    ContinuousConfiguration (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy v s))) := by
  intro s ι _
  simp only [multisetEnergy_add hsym]
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul ((continuous_const.add (continuous_multisetEnergy_configuration hv)).add
      (continuous_multisetPairing_right hv s))))

end Continuity

end MultisetEnergy

def radialPair (φ : Potential) (x y : Position) : ℝ := φ (nndist x y)

lemma continuous_radialPair {φ : Potential} (hφ : Continuous φ) :
    Continuous (Function.uncurry (radialPair φ)) :=
  hφ.comp (continuous_fst.nndist continuous_snd)

lemma radialPair_symm (φ : Potential) (x y : Position) : radialPair φ x y = radialPair φ y x := by
  simp only [radialPair, nndist_comm]

lemma pairWithin_radial (φ : Potential) (s : ParticleState Position) :
    pairWithin (radialPair φ) s = orderedEnergy φ s.2 := by
  classical
  unfold pairWithin orderedEnergy
  have hh : (∑ i : Fin s.1, ∑ j : Fin s.1, if i = j then 0 else radialPair φ (s.2 i) (s.2 j)) =
      ∑ i : Fin s.1, ∑ j : Fin s.1, if i ≠ j then φ (nndist (s.2 i) (s.2 j)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij, radialPair]
  rw [hh]
  ring_nf

lemma multisetEnergy_radial (φ : Potential) (s : ParticleState Position) :
    multisetEnergy (radialPair φ) (particleMultiset s) = orderedEnergy φ s.2 := by
  rw [multisetEnergy_particle, pairWithin_radial]

lemma measurable_particleBoltzmann {φ : Potential} (hφ : Continuous φ) (β : ℝ) :
    Measurable (fun s : ParticleState Position => Real.exp (-β * orderedEnergy φ s.2)) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro n
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_orderedEnergy hφ))

lemma lintegral_grandOn {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) {A : Set Position}
    (hAfin : volume A ≠ ⊤) (z : ℝ) :
    (∫⁻ s : ParticleState Position, ENNReal.ofReal (Real.exp (-β * orderedEnergy φ s.2))
      ∂particleBase (volume.restrict A) z) = ENNReal.ofReal (grandOn φ A β z) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  rw [lintegral_particleBase _ _ (measurable_particleBoltzmann hφ β).ennreal_ofReal,
    grandOn, ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A n β))
      (grandOn_summable hφ hb hstable hβ hAfin z)]
  apply tsum_congr
  intro n
  have hi := integrable_orderedBoltzmann (ι := Fin n) hφ hb β (Measure.pi (fun _ => volume.restrict A))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => (Real.exp_pos _).le)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [partitionOn, rawPartition, div_eq_mul_inv]
  ring

lemma continuous_radialPair_comp {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {φ : Potential} (hφ : Continuous φ) {f : X → Position} {g : Y → Position}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => radialPair φ (f p.1) (g p.2)) := by
  change Continuous (fun p : X × Y => φ (nndist (f p.1) (g p.2)))
  exact hφ.comp ((hf.comp continuous_fst).nndist (hg.comp continuous_snd))

theorem grandOn_cell_factorization {I : Type} [Fintype I] [DecidableEq I]
    (Y : I → Type uY) [∀ i, TopologicalSpace (Y i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, BorelSpace (Y i)] [∀ i, SecondCountableTopology (Y i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, IsFiniteMeasure (ν i)]
    (pos : ∀ i, Y i → Position) (hpos : ∀ i, Continuous (pos i))
    {A : Set Position} (hAfin : volume A ≠ ⊤)
    (hdecomp : volume.restrict A = ∑ i, Measure.map (pos i) (ν i))
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) {B β : ℝ}
    (hstable : StableWith φ B) (hβ : 0 ≤ β) (z : ℝ) :
    let μ := Measure.pi (fun i => particleBase (ν i) z)
    let E := fun x => β * pairCellEnergy (fun i j a b => radialPair φ (pos i a) (pos j b)) x
    Integrable (fun x => Real.exp (-E x)) μ ∧ boltzmannPartition μ E = grandOn φ A β z := by
  dsimp only
  let v : ∀ i j, Y i → Y j → ℝ := fun i j a b => radialPair φ (pos i a) (pos j b)
  have hv (i j : I) : Continuous (Function.uncurry (v i j)) := by
    change Continuous (fun p : Y i × Y j => radialPair φ (pos i p.1) (pos j p.2))
    exact continuous_radialPair_comp hφ (hpos i) (hpos j)

  have hE : Measurable (fun x => Real.exp (-(β * pairCellEnergy v x))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_pairCellEnergy v hv)).neg).measurable
  have heq : (∫⁻ x, ENNReal.ofReal (Real.exp (-(β * pairCellEnergy v x)))
      ∂Measure.pi (fun i => particleBase (ν i) z)) = ENNReal.ofReal (grandOn φ A β z) := by
    have hh := particleBase_sum_map_observable Y
      (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy (radialPair φ) s)))
      (continuousConfiguration_boltzmann (continuous_radialPair hφ) (radialPair_symm φ) β)
      ν pos (fun i => (hpos i).measurable) z 0
    simp only [zero_add, multisetEnergy_radial, multisetEnergy_mappedMulti] at hh
    rw [← hdecomp, lintegral_grandOn hφ hb hstable hβ hAfin z] at hh
    simpa only [neg_mul, v] using hh.symm
  have hi : Integrable (fun x => Real.exp (-(β * pairCellEnergy v x)))
      (Measure.pi (fun i => particleBase (ν i) z)) := by
    refine ⟨hE.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (Real.exp_pos _).le]
    rw [heq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [boltzmannPartition, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hi.aestronglyMeasurable, heq,
    ENNReal.toReal_ofReal (zero_le_one.trans (grandOn_bounds hφ hb hstable hβ hAfin z).1)]

end RadialTransition

end

end OAI
