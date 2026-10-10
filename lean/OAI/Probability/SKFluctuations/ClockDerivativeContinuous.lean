import Mathlib
import OAI.Probability.SKFluctuations.PotentialHeatTrace

namespace OAI

/-! Clock Derivative Continuous. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem clockDerivative_continuous {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i)) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => clockDerivative m F G H p.1 p.2) := by
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by simpa only [pow_two] using (hG i).mul (hG i)
  exact ((continuous_finsetSum _ fun i _ => clockTest_continuous hF (hH i) m).add
    ((continuous_finsetSum _ fun i _ => clockTest_continuous hF (hGs i) m).const_mul m)).const_mul (1/2:ℝ)

 theorem clockDerivative_absBounded {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i)) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => clockDerivative m F G H p.1 p.2) := by
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by simpa only [pow_two] using (hG i).mul (hG i)
  exact ((AbsBounded.sum fun i => clockTest_absBounded hF (hH i) m).add
    ((AbsBounded.sum fun i => clockTest_absBounded hF (hGs i) m).const_mul m)).const_mul (1/2:ℝ)

 theorem clockDerivative_eq_generator {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} (m t : ℝ) (x : Fin (n+1) → ℝ) :
    clockDerivative m F G H t x = (1/2:ℝ)*∑ i,
      (clockGradient m F (G i) (G i) (H i) t x+m*(clockTest m F (G i) t x)^2) := by
  unfold clockDerivative
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [clockGradient]
  simp only [pow_two]
  ring

 theorem hasDerivAt_clockContinuation {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v)) (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1)) (H i (x+t • Pi.single i 1)) t)
    {m t : ℝ} (hm : 0 < m) (ht : 0 < t) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => clockContinuation m F s x) (clockDerivative m F G H t x) t := by
  obtain ⟨K,hK⟩ := parametric_clock hF hG hH hd hd₁ hm
  exact (hK (t+1)).derivative t ⟨ht,by linarith⟩ x

 theorem clockTest_bddSmooth {ι : Type*} [Fintype ι] {k : ℕ} {F A : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hA : BddSmooth k A) (m t : ℝ) : BddSmooth k (clockTest m F A t) := by
  obtain ⟨C,hC⟩ := hF.1
  exact hA.shiftedMean hF (fun x =>
    (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hC m x)

 theorem clockContinuation_regular {ι : Type*} [Fintype ι] {k : ℕ} {F : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) {m : ℝ} (hm : 0 < m) (t : ℝ) : PotentialRegularity k (clockContinuation m F t) := by
  obtain ⟨C,hC⟩ := hF.1
  exact hF.shiftedContinuation hm (fun x =>
    (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hC m x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

structure HeatJet (n : ℕ) where
  F : (Fin (n+1) → ℝ) → ℝ
  A : (Fin (n+1) → ℝ) → ℝ
  G : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ
  H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ
  A₁ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ
  A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ
  C : ℝ≥0
  lipschitz : LipschitzWith C F
  smoothA : BddSmooth 0 A
  smoothG : ∀ i, BddSmooth 0 (G i)
  smoothH : ∀ i, BddSmooth 0 (H i)
  smoothA₁ : ∀ i, BddSmooth 0 (A₁ i)
  smoothA₂ : ∀ i, BddSmooth 0 (A₂ i)
  derivF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v)) (∑ i, v i*G i (x+t • v)) t
  derivG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1)) (H i (x+t • Pi.single i 1)) t
  derivA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v)) (∑ i, v i*A₁ i (x+t • v)) t
  derivA₁ : ∀ i x t, HasDerivAt (fun s : ℝ => A₁ i (x+s • Pi.single i 1)) (A₂ i (x+t • Pi.single i 1)) t

 theorem HeatJet.regular {n : ℕ} (J : HeatJet n) : PotentialRegularity 0 J.F := by
  refine ⟨⟨J.C,J.lipschitz⟩,fun v => ?_⟩
  exact ⟨fun y => ∑ i, v i*J.G i y,BddSmooth.sum Finset.univ (fun i _ => (J.smoothG i).const_mul (v i)),fun x t => J.derivF x v t⟩

 theorem hasDerivAt_clockContinuation_source_vector {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : m ≠ 0)
    (t : ℝ) (x v : Fin (n+1) → ℝ) (s : ℝ) :
    HasDerivAt (fun r => clockContinuation m J.F t (x+r • v))
      (∑ i, v i*clockTest m J.F (J.G i) t (x+s • v)) s := by
  have hb : ∀ i, BddSmooth 0 (fun y => v i*J.G i y) := fun i => (J.smoothG i).const_mul (v i)
  have h := hasDerivAt_clockContinuation_source J.lipschitz
    (BddSmooth.sum Finset.univ fun i _ => hb i) (fun y r => J.derivF y v r) hm t x s
  rw [clockTest_sum J.lipschitz hb] at h
  simpa only [clockTest_const_mul] using h

 theorem HeatJet.derivF_coord {n : ℕ} (J : HeatJet n) (i : Fin (n+1)) (x : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => J.F (x+s • Pi.single i 1)) (J.G i (x+t • Pi.single i 1)) t := by
  simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
    J.derivF x (Pi.single i 1) t

 theorem HeatJet.derivA_coord {n : ℕ} (J : HeatJet n) (i : Fin (n+1)) (x : Fin (n+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => J.A (x+s • Pi.single i 1)) (J.A₁ i (x+t • Pi.single i 1)) t := by
  simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
    J.derivA x (Pi.single i 1) t

 
def HeatJet.evolve {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m) (t : ℝ) : HeatJet n where
  F := clockContinuation m J.F t
  A := clockTest m J.F J.A t
  G i := clockTest m J.F (J.G i) t
  H i := clockGradient m J.F (J.G i) (J.G i) (J.H i) t
  A₁ i := clockGradient m J.F (J.G i) J.A (J.A₁ i) t
  A₂ i := clockSecond m J.F (J.G i) (J.H i) J.A (J.A₁ i) (J.A₂ i) t
  C := J.C
  lipschitz := lipschitzWith_shiftedContinuation J.lipschitz hm (fun x =>
    (exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift J.lipschitz m x)
  smoothA := clockTest_bddSmooth J.regular J.smoothA m t
  smoothG i := clockTest_bddSmooth J.regular (J.smoothG i) m t
  smoothH i := clockGradient_bddSmooth J.regular (J.smoothG i) (J.smoothG i) (J.smoothH i) m t
  smoothA₁ i := clockGradient_bddSmooth J.regular (J.smoothG i) J.smoothA (J.smoothA₁ i) m t
  smoothA₂ i := clockSecond_bddSmooth J.regular (J.smoothG i) (J.smoothH i) J.smoothA (J.smoothA₁ i) (J.smoothA₂ i) m t
  derivF := hasDerivAt_clockContinuation_source_vector J hm.ne' t
  derivG i := hasDerivAt_clockTest_source J.lipschitz (J.smoothG i) (J.smoothG i) (J.smoothH i)
    (J.derivF_coord i) (J.derivG i) m t
  derivA := hasDerivAt_clockTest_source_vector J.lipschitz J.smoothA J.smoothG J.smoothA₁
    J.derivF J.derivA m t
  derivA₁ i := hasDerivAt_clockGradient_source J.lipschitz (J.smoothG i) (J.smoothH i) J.smoothA
    (J.smoothA₁ i) (J.smoothA₂ i) (J.derivF_coord i) (J.derivG i) (J.derivA_coord i) (J.derivA₁ i) m t

 theorem HeatJet.evolve_time_F {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    {t : ℝ} (ht : 0 < t) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => (J.evolve hm s).F x)
      ((1/2:ℝ)*∑ i, ((J.evolve hm t).H i x+m*((J.evolve hm t).G i x)^2)) t := by
  dsimp only [HeatJet.evolve]
  rw [← clockDerivative_eq_generator]
  exact hasDerivAt_clockContinuation J.lipschitz J.smoothG J.smoothH J.derivF J.derivG hm ht x

 theorem HeatJet.evolve_time_A {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m)
    {t : ℝ} (ht : 0 < t) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => (J.evolve hm s).A x)
      ((1/2:ℝ)*∑ i, ((J.evolve hm t).A₂ i x+2*m*(J.evolve hm t).A₁ i x*(J.evolve hm t).G i x)) t := by
  dsimp only [HeatJet.evolve]
  rw [← clockTestDerivative_eq_generator J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂]
  exact (hasDerivWithinAt_clockTest J.lipschitz J.smoothA J.smoothG J.smoothH J.smoothA₁ J.smoothA₂
    J.derivF J.derivG J.derivA J.derivA₁ m x ht.le).hasDerivAt (Ici_mem_nhds ht)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.square {n : ℕ} (J : HeatJet n) : HeatJet n where
  F := J.F
  A := fun y => (J.A y)^2
  G := J.G
  H := J.H
  A₁ i y := 2*(J.A y*J.A₁ i y)
  A₂ i y := 2*((J.A₁ i y)^2+J.A y*J.A₂ i y)
  C := J.C
  lipschitz := J.lipschitz
  smoothA := by simpa only [pow_two] using J.smoothA.mul J.smoothA
  smoothG := J.smoothG
  smoothH := J.smoothH
  smoothA₁ i := (J.smoothA.mul (J.smoothA₁ i)).const_mul 2
  smoothA₂ i := by simpa only [pow_two] using
    (((J.smoothA₁ i).mul (J.smoothA₁ i)).add (J.smoothA.mul (J.smoothA₂ i))).const_mul 2
  derivF := J.derivF
  derivG := J.derivG
  derivA x v t := by
    apply ((J.derivA x v t).pow 2).congr_deriv
    simp only [Nat.cast_ofNat,pow_one,Nat.reduceSub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  derivA₁ i x t := by
    apply (((J.derivA_coord i x t).mul (J.derivA₁ i x t)).const_mul 2).congr_deriv
    ring

structure HeatJetFamily (n : ℕ) where
  J : ℝ → HeatJet n
  C : ℝ≥0
  lipschitz : ∀ t, LipschitzWith C (J t).F
  continuousF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).F p.2)
  continuousA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A p.2)
  continuousG : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).G i p.2)
  continuousH : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).H i p.2)
  continuousA₁ : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A₁ i p.2)
  continuousA₂ : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A₂ i p.2)
  boundedA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A p.2)
  boundedG : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).G i p.2)
  boundedH : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).H i p.2)
  boundedA₁ : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A₁ i p.2)
  boundedA₂ : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A₂ i p.2)

 def HeatJet.family {n : ℕ} (J : HeatJet n) {m : ℝ} (hm : 0 < m) : HeatJetFamily n where
  J := J.evolve hm
  C := J.C
  lipschitz t := (J.evolve hm t).lipschitz
  continuousF := clockContinuation_continuous J.lipschitz m
  continuousA := clockTest_continuous J.lipschitz J.smoothA m
  continuousG i := clockTest_continuous J.lipschitz (J.smoothG i) m
  continuousH i := clockGradient_continuous J.lipschitz (J.smoothG i) (J.smoothG i) (J.smoothH i) m
  continuousA₁ i := clockGradient_continuous J.lipschitz (J.smoothG i) J.smoothA (J.smoothA₁ i) m
  continuousA₂ i := clockSecond_continuous J.lipschitz (J.smoothG i) (J.smoothH i) J.smoothA (J.smoothA₁ i) (J.smoothA₂ i) m
  boundedA := clockTest_absBounded J.lipschitz J.smoothA m
  boundedG i := clockTest_absBounded J.lipschitz (J.smoothG i) m
  boundedH i := clockGradient_absBounded J.lipschitz (J.smoothG i) (J.smoothG i) (J.smoothH i) m
  boundedA₁ i := clockGradient_absBounded J.lipschitz (J.smoothG i) J.smoothA (J.smoothA₁ i) m
  boundedA₂ i := clockSecond_absBounded J.lipschitz (J.smoothG i) (J.smoothH i) J.smoothA (J.smoothA₁ i) (J.smoothA₂ i) m

 def HeatJetFamily.square {n : ℕ} (V : HeatJetFamily n) : HeatJetFamily n where
  J t := (V.J t).square
  C := V.C
  lipschitz := V.lipschitz
  continuousF := V.continuousF
  continuousA := V.continuousA.pow 2
  continuousG := V.continuousG
  continuousH := V.continuousH
  continuousA₁ i := (V.continuousA.mul (V.continuousA₁ i)).const_mul 2
  continuousA₂ i := (((V.continuousA₁ i).pow 2).add (V.continuousA.mul (V.continuousA₂ i))).const_mul 2
  boundedA := by simpa only [HeatJet.square,pow_two] using V.boundedA.mul V.boundedA
  boundedG := V.boundedG
  boundedH := V.boundedH
  boundedA₁ i := (V.boundedA.mul (V.boundedA₁ i)).const_mul 2
  boundedA₂ i := by simpa only [HeatJet.square,pow_two] using
    (((V.boundedA₁ i).mul (V.boundedA₁ i)).add (V.boundedA.mul (V.boundedA₂ i))).const_mul 2

 theorem HeatJetFamily.continuousP {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => potentialHeatTrace m (V.J p.1).G (V.J p.1).H p.2) := by
  exact continuous_finsetSum _ fun i _ =>
    ((V.continuousH i).const_mul m).add (((V.continuousG i).pow 2).const_mul (m^2))

 theorem HeatJetFamily.continuousW {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => testedHeatTrace m (V.J p.1).G (V.J p.1).H
      (V.J p.1).A (V.J p.1).A₁ (V.J p.1).A₂ p.2) := by
  exact continuous_finsetSum _ fun i _ =>
    ((V.continuousA₂ i).add (((V.continuousA₁ i).const_mul (2*m)).mul (V.continuousG i))).add
      (V.continuousA.mul (((V.continuousH i).const_mul m).add (((V.continuousG i).pow 2).const_mul (m^2))))

 theorem HeatJetFamily.boundedP {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => potentialHeatTrace m (V.J p.1).G (V.J p.1).H p.2) := by
  apply AbsBounded.sum
  intro i
  simpa only [pow_two] using ((V.boundedH i).const_mul m).add
    (((V.boundedG i).mul (V.boundedG i)).const_mul (m*m))

 theorem HeatJetFamily.boundedW {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => testedHeatTrace m (V.J p.1).G (V.J p.1).H
      (V.J p.1).A (V.J p.1).A₁ (V.J p.1).A₂ p.2) := by
  apply AbsBounded.sum
  intro i
  have hP : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => m*(V.J p.1).H i p.2+m^2*((V.J p.1).G i p.2)^2) := by
    simpa only [pow_two] using ((V.boundedH i).const_mul m).add
      (((V.boundedG i).mul (V.boundedG i)).const_mul (m*m))
  exact ((V.boundedA₂ i).add (((V.boundedA₁ i).const_mul (2*m)).mul (V.boundedG i))).add (V.boundedA.mul hP)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
 

theorem local_exponential_domination {F D : ℝ → Ω → ℝ} {l r t C : ℝ}
    (ht : t ∈ Ioo l r) (hC : 0 ≤ C)
    (hd : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => F q z) (D s z) s)
    (hb : ∀ s ∈ Ioo l r, ∀ z, |D s z| ≤ C) (m : ℝ) :
    ∃ ρ > 0, Metric.ball t ρ ⊆ Ioo l r ∧ ∀ s ∈ Metric.ball t ρ, ∀ z,
      Real.exp (m*F s z) ≤ Real.exp (|m| *C)*Real.exp (m*F t z) := by
  let ρ := min 1 (min (t-l) (r-t)) / 2
  have hρ : 0 < ρ := by
    have hl : 0 < t-l := sub_pos.mpr ht.1
    have hr : 0 < r-t := sub_pos.mpr ht.2
    dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; have := min_le_left (1:ℝ) (min (t-l) (r-t)); linarith
  have hball : Metric.ball t ρ ⊆ Ioo l r := by
    intro s hs
    have hs' : |s-t| < ρ := Metric.mem_ball.mp hs
    have hρl : ρ ≤ t-l := by dsimp [ρ]; have := (min_le_right (1:ℝ) (min (t-l) (r-t))).trans (min_le_left _ _); linarith [ht.1]
    have hρr : ρ ≤ r-t := by dsimp [ρ]; have := (min_le_right (1:ℝ) (min (t-l) (r-t))).trans (min_le_right _ _); linarith [ht.2]
    have hs'' := abs_lt.mp hs'
    constructor <;> linarith
  refine ⟨ρ,hρ,hball,?_⟩
  intro s hs z
  have hL : LipschitzOnWith ⟨C,hC⟩ (fun q => F q z) (Ioo l r) :=
    (convex_Ioo l r).lipschitzOnWith_of_nnnorm_deriv_le
      (fun q hq => (hd q hq z).differentiableAt)
      (fun q hq => by
        change ‖deriv (fun q => F q z) q‖ ≤ C
        rw [(hd q hq z).deriv, Real.norm_eq_abs]
        exact hb q hq z)
  have hh := hL.dist_le_mul s (hball hs) t ht
  change |F s z-F t z| ≤ C*|s-t| at hh
  have hst : |s-t| ≤ 1 := (Metric.mem_ball.mp hs).le.trans hρ1
  have hLip : |F s z-F t z| ≤ C := hh.trans (by simpa using mul_le_mul_of_nonneg_left hst hC)
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left hLip (abs_nonneg m)
  have h' := le_abs_self (m*(F s z-F t z))
  rw [abs_mul] at h'
  nlinarith

 theorem hasDerivAt_tested_integral_local {F D A B : ℝ → Ω → ℝ} {l r t C K : ℝ}
    (ht : t ∈ Ioo l r) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Ioo l r, Measurable (F s)) (hD : Measurable (D t))
    (hA : ∀ s ∈ Ioo l r, Measurable (A s)) (hB : Measurable (B t))
    (hdF : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => F q z) (D s z) s)
    (hdA : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => A q z) (B s z) s)
    (hbF : ∀ s ∈ Ioo l r, ∀ z, |D s z| ≤ C)
    (hbA : ∀ s ∈ Ioo l r, ∀ z, |A s z| ≤ K)
    (hbB : ∀ s ∈ Ioo l r, ∀ z, |B s z| ≤ K) (m : ℝ)
    (hi : Integrable (fun z => Real.exp (m*F t z)) μ) :
    HasDerivAt (fun s => ∫ z, A s z*Real.exp (m*F s z) ∂μ)
      (∫ z, (B t z+m*A t z*D t z)*Real.exp (m*F t z) ∂μ) t := by
  obtain ⟨ρ,hρ,hball,he⟩ := local_exponential_domination ht hC hdF hbF m
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t ρ) (bound := fun z => ((K+|m| *K*C)*Real.exp (|m| *C))*Real.exp (m*F t z)))
    (Metric.ball_mem_nhds t hρ) _ (integrable_weighted hi (hA t ht) (hbA t ht)) _ _ (hi.const_mul _) _ |>.2
  · filter_upwards [Metric.ball_mem_nhds t hρ] with s hs
    exact ((hA s (hball hs)).mul (((hF s (hball hs)).const_mul m).exp)).aestronglyMeasurable
  · exact ((hB.add (((hA t ht).const_mul m).mul hD)).mul (((hF t ht).const_mul m).exp)).aestronglyMeasurable
  · exact Eventually.of_forall fun z s hs => by
      have hcoef : |B s z+m*A s z*D s z| ≤ K+|m| *K*C := by
        apply (abs_add_le _ _).trans
        rw [abs_mul,abs_mul]
        exact add_le_add (hbB s (hball hs) z)
          (mul_le_mul (mul_le_mul_of_nonneg_left (hbA s (hball hs) z) (abs_nonneg m))
            (hbF s (hball hs) z) (abs_nonneg _) (mul_nonneg (abs_nonneg m) hK))
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (K+|m| *K*C)*(Real.exp (|m| *C)*Real.exp (m*F t z)) :=
          mul_le_mul hcoef (he s hs z) (Real.exp_nonneg _) (by positivity)
        _ = _ := by ring
  · exact Eventually.of_forall fun z s hs => ((hdA s (hball hs) z).mul
      (((hdF s (hball hs) z).const_mul m).exp)).congr_deriv (by ring)

 theorem hasDerivAt_tiltedMean_local [IsProbabilityMeasure μ]
    {F D A B : ℝ → Ω → ℝ} {l r t C K : ℝ}
    (ht : t ∈ Ioo l r) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Ioo l r, Measurable (F s)) (hD : Measurable (D t))
    (hA : ∀ s ∈ Ioo l r, Measurable (A s)) (hB : Measurable (B t))
    (hdF : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => F q z) (D s z) s)
    (hdA : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => A q z) (B s z) s)
    (hbF : ∀ s ∈ Ioo l r, ∀ z, |D s z| ≤ C)
    (hbA : ∀ s ∈ Ioo l r, ∀ z, |A s z| ≤ K)
    (hbB : ∀ s ∈ Ioo l r, ∀ z, |B s z| ≤ K) (m : ℝ)
    (hi : Integrable (fun z => Real.exp (m*F t z)) μ) :
    HasDerivAt (fun s => tiltedMean μ m (F s) (A s))
      (tiltedMean μ m (F t) (B t)+m*(tiltedMean μ m (F t) (fun z => A t z*D t z)-
        tiltedMean μ m (F t) (A t)*tiltedMean μ m (F t) (D t))) t := by
  have hP := hasDerivAt_tested_integral_local ht hC (K := 1) (by norm_num) hF hD
    (fun _ _ => measurable_const) measurable_const hdF (fun s _ _ => hasDerivAt_const s (1:ℝ))
    hbF (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) m hi
  simp only [one_mul,mul_one,zero_add,mul_assoc,integral_const_mul] at hP
  have hd := (hasDerivAt_tested_integral_local ht hC hK hF hD hA hB hdF hdA hbF hbA hbB m hi).div hP
    (partition_pos m hi).ne'
  have h1 := integrable_weighted hi hB (hbB t ht)
  have h2 : Integrable (fun z => (A t z*D t z)*Real.exp (m*F t z)) μ :=
    integrable_weighted hi ((hA t ht).mul hD) (fun z => show |A t z*D t z| ≤ K*C by
    rw [abs_mul]; exact mul_le_mul (hbA t ht z) (hbF t ht z) (abs_nonneg _) hK)
  have he : (∫ z, (B t z+m*A t z*D t z)*Real.exp (m*F t z) ∂μ) =
      (∫ z, B t z*Real.exp (m*F t z) ∂μ)+m*(∫ z, (A t z*D t z)*Real.exp (m*F t z) ∂μ) := by
    rw [← integral_const_mul,← integral_add h1 (h2.const_mul m)]
    congr 1; funext z; ring
  apply hd.congr_deriv
  rw [he]
  dsimp [tiltedMean]
  field_simp
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 

theorem dynamic_testedPartition_continuous {F A : ℝ → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ z, A p.2 (x+Real.sqrt p.1 • z)*Real.exp (m*F p.2 (x+Real.sqrt p.1 • z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := |F p.2 x|+1
  let Q := Real.sqrt p.1+1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcbase : Continuous (fun q : ℝ × ℝ => F q.2 x) := hcF.comp (continuous_snd.prodMk continuous_const)
  have hbase : ∀ᶠ q in 𝓝 p, |F q.2 x| < B := hcbase.abs.continuousAt.eventually
    (eventually_lt_nhds (by dsimp [B]; linarith))
  have hscale : ∀ᶠ q in 𝓝 p, Real.sqrt q.1 < Q :=
    (Real.continuous_sqrt.comp continuous_fst).continuousAt.eventually
      (eventually_lt_nhds (by dsimp [Q]; linarith))
  apply continuousAt_of_dominated
    (bound := fun z => K*Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖))
  · exact Eventually.of_forall fun q => by
      have hmap : Continuous (fun z : ι → ℝ => (q.2,x+Real.sqrt q.1 • z)) := by fun_prop
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).aestronglyMeasurable
  · filter_upwards [hbase,hscale] with q hq hq'
    exact Eventually.of_forall fun z => by
      have hK : 0 ≤ K := (abs_nonneg (A q.2 x)).trans (hb q.2 x)
      have hdiff : |F q.2 (x+Real.sqrt q.1 • z)-F q.2 x| ≤ (C:ℝ)*Real.sqrt q.1*‖z‖ := by
        simpa only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using (hF q.2).dist_le_mul (x+Real.sqrt q.1 • z) x
      have hale : |F q.2 (x+Real.sqrt q.1 • z)| ≤ B+(C:ℝ)*Q*‖z‖ := by
        have hh := abs_add_le (F q.2 (x+Real.sqrt q.1 • z)-F q.2 x) (F q.2 x)
        rw [sub_add_cancel] at hh
        have hcomp : (C:ℝ)*Real.sqrt q.1*‖z‖ ≤ (C:ℝ)*Q*‖z‖ := by gcongr
        linarith
      have hexp : Real.exp (m*F q.2 (x+Real.sqrt q.1 • z)) ≤
          Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖) := by
        rw [← Real.exp_add,Real.exp_le_exp]
        have h1 := (le_abs_self (m*F q.2 (x+Real.sqrt q.1 • z))).trans_eq (abs_mul m _)
        have h2 := mul_le_mul_of_nonneg_left hale (abs_nonneg m)
        nlinarith
      change |A q.2 (x+Real.sqrt q.1 • z)*Real.exp (m*F q.2 (x+Real.sqrt q.1 • z))| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (hb q.2 _) hexp (Real.exp_nonneg _) hK).trans_eq (by ring)
  · exact (hν (|m| *C*Q)).const_mul _
  · exact Eventually.of_forall fun z => by
      have hmap : Continuous (fun q : ℝ × ℝ => (q.2,x+Real.sqrt q.1 • z)) :=
        continuous_snd.prodMk (continuous_const.add ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).continuousAt

 theorem dynamic_clockTest_continuous {F A : ℝ → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ r y, |A r y| ≤ K) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × ℝ => clockTest m (F p.2) (A p.2) p.1 x) := by
  have hn := dynamic_testedPartition_continuous hF hcF hcA hb m x
  have hd := dynamic_testedPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m x
  simp only [one_mul] at hd
  have hh := hn.div hd (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p.2) m).affine_integrable (exponentialIncrement_gaussian (fun _ : ι => 1)) x _)).ne')
  exact hh.congr fun p => (clockTest_eq_all (hF p.2).continuous
    (hcA.comp (continuous_const.prodMk continuous_id)) m p.1 x).symm

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem dynamic_clockGradient_continuous {ι : Type*} [Fintype ι]
    {F G A B : ℝ → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ r, LipschitzWith C (F r))
    (hcF : Continuous (fun p : ℝ × (ι → ℝ) => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × (ι → ℝ) => G p.1 p.2))
    (hcA : Continuous (fun p : ℝ × (ι → ℝ) => A p.1 p.2))
    (hcB : Continuous (fun p : ℝ × (ι → ℝ) => B p.1 p.2))
    (hbG : AbsBounded (fun p : ℝ × (ι → ℝ) => G p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (ι → ℝ) => A p.1 p.2))
    (hbB : AbsBounded (fun p : ℝ × (ι → ℝ) => B p.1 p.2)) (m : ℝ) (x : ι → ℝ) :
    Continuous (fun p : ℝ × ℝ => clockGradient m (F p.2) (G p.2) (A p.2) (B p.2) p.1 x) := by
  have hbM := hbA.mul hbG
  obtain ⟨KA,_,bA⟩ := hbA
  obtain ⟨KG,_,bG⟩ := hbG
  obtain ⟨KB,_,bB⟩ := hbB
  obtain ⟨KM,_,bM⟩ := hbM
  exact (dynamic_clockTest_continuous hF hcF hcB (fun r y => bB (r,y)) m x).add
    (((dynamic_clockTest_continuous hF hcF (hcA.mul hcG) (fun r y => bM (r,y)) m x).sub
      ((dynamic_clockTest_continuous hF hcF hcA (fun r y => bA (r,y)) m x).mul
        (dynamic_clockTest_continuous hF hcF hcG (fun r y => bG (r,y)) m x))).const_mul m)

 

theorem hasDerivAt_dynamic_clockTest {n : ℕ} (J : ℝ → HeatJet n)
    {D B : ℝ → (Fin (n+1) → ℝ) → ℝ} {l r : ℝ} {C : ℝ≥0} (m : ℝ)
    (hF : ∀ s, LipschitzWith C (J s).F)
    (hcF : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).F p.2))
    (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A p.2))
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hcB : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (J p.1).A p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbB : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hcP : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => potentialHeatTrace m (J p.1).G (J p.1).H p.2))
    (hcW : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => testedHeatTrace m (J p.1).G (J p.1).H (J p.1).A (J p.1).A₁ (J p.1).A₂ p.2))
    (hbP : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => potentialHeatTrace m (J p.1).G (J p.1).H p.2))
    (hbW : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => testedHeatTrace m (J p.1).G (J p.1).H (J p.1).A (J p.1).A₁ (J p.1).A₂ p.2))
    (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (J q).F y) (D s y) s)
    (hdA : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (J q).A y) (B s y) s)
    (x : Fin (n+1) → ℝ) {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha₀ : 0 < a t) (hbt : b t ∈ Ioo l r) :
    HasDerivAt (fun s => clockTest m (J (b s)).F (J (b s)).A (a s) x)
      (clockTestDerivative m (J (b t)).F (J (b t)).G (J (b t)).H (J (b t)).A (J (b t)).A₁ (J (b t)).A₂ (a t) x*a'+
       clockGradient m (J (b t)).F (D (b t)) (J (b t)).A (B (b t)) (a t) x*b') t := by
  have hcg := dynamic_clockGradient_continuous (F := fun s => (J s).F)
    (G := D) (A := fun s => (J s).A) (B := B) hF hcF hcD hcA hcB hbD hbA hbB m x
  obtain ⟨KA,hKA,bA⟩ := hbA
  obtain ⟨KD,hKD,bD⟩ := hbD
  obtain ⟨KB,hKB,bB⟩ := hbB
  obtain ⟨KP,_,bP⟩ := hbP
  obtain ⟨KW,_,bW⟩ := hbW
  have hct : Continuous (fun p : ℝ × ℝ =>
      clockTestDerivative m (J p.2).F (J p.2).G (J p.2).H (J p.2).A (J p.2).A₁ (J p.2).A₂ p.1 x) :=
    ((dynamic_clockTest_continuous hF hcF hcW (fun s y => bW (s,y)) m x).sub
      ((dynamic_clockTest_continuous hF hcF hcA (fun s y => bA (s,y)) m x).mul
        (dynamic_clockTest_continuous hF hcF hcP (fun s y => bP (s,y)) m x))).const_mul (1/2:ℝ)
  apply hasDerivAt_bivariate_chain
    (f := fun q s => clockTest m (J s).F (J s).A q x)
    (f₁ := fun q s => clockTestDerivative m (J s).F (J s).G (J s).H (J s).A (J s).A₁ (J s).A₂ q x)
    (f₂ := fun q s => clockGradient m (J s).F (D s) (J s).A (B s) q x)
    ?_ ?_ hct.continuousAt
    hcg.continuousAt ha hb
  · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ha₀)] with p hp
    exact (hasDerivWithinAt_clockTest (J p.2).lipschitz (J p.2).smoothA (J p.2).smoothG (J p.2).smoothH
      (J p.2).smoothA₁ (J p.2).smoothA₂ (J p.2).derivF (J p.2).derivG (J p.2).derivA (J p.2).derivA₁ m x hp.le).hasDerivAt
        (Ici_mem_nhds hp)
  · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hbt)] with p hp
    apply hasDerivAt_tiltedMean_local hp hKD (K := max KA KB) (hKA.trans (le_max_left _ _))
      (fun s _ => ((J s).lipschitz.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s _ => ((J s).smoothA.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcB.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s hs z => hdA s hs (x+z))
      (fun s _ z => bD (s,x+z))
      (fun s _ z => (bA (s,x+z)).trans (le_max_left _ _))
      (fun s _ z => (bB (s,x+z)).trans (le_max_right _ _)) m
      ((exponentialIncrement_gaussian (fun _ : Fin (n+1) => Real.toNNReal p.1)).integrable_shift (J p.2).lipschitz m x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 def HeatJet.potentialRate {n : ℕ} (J : HeatJet n) (m : ℝ) (y : Fin (n+1) → ℝ) : ℝ :=
  (1/2:ℝ)*∑ i, (J.H i y+m*(J.G i y)^2)
 def HeatJet.testRate {n : ℕ} (J : HeatJet n) (m : ℝ) (y : Fin (n+1) → ℝ) : ℝ :=
  (1/2:ℝ)*∑ i, (J.A₂ i y+2*m*J.A₁ i y*J.G i y)
 def HeatJet.energy {n : ℕ} (J : HeatJet n) (y : Fin (n+1) → ℝ) : ℝ :=
  ∑ i, (J.A₁ i y)^2

 theorem HeatJet.smoothPotentialRate {n : ℕ} (J : HeatJet n) (m : ℝ) : BddSmooth 0 (J.potentialRate m) := by
  apply (BddSmooth.sum Finset.univ fun i _ => ?_).const_mul
  simpa only [pow_two] using (J.smoothH i).add (((J.smoothG i).mul (J.smoothG i)).const_mul m)
 theorem HeatJet.smoothTestRate {n : ℕ} (J : HeatJet n) (m : ℝ) : BddSmooth 0 (J.testRate m) := by
  apply (BddSmooth.sum Finset.univ fun i _ => ?_).const_mul
  exact (J.smoothA₂ i).add (((J.smoothA₁ i).const_mul (2*m)).mul (J.smoothG i))
 theorem HeatJet.smoothEnergy {n : ℕ} (J : HeatJet n) : BddSmooth 0 J.energy := by
  apply BddSmooth.sum Finset.univ
  intro i _
  simpa only [pow_two] using (J.smoothA₁ i).mul (J.smoothA₁ i)
 theorem HeatJet.energy_nonneg {n : ℕ} (J : HeatJet n) (y : Fin (n+1) → ℝ) : 0 ≤ J.energy y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

 theorem HeatJet.trace_eq_rate {n : ℕ} (J : HeatJet n) (m : ℝ) :
    potentialHeatTrace m J.G J.H = fun y => (2*m)*J.potentialRate m y := by
  funext y
  unfold potentialHeatTrace HeatJet.potentialRate
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
 theorem HeatJet.square_trace {n : ℕ} (J : HeatJet n) (m : ℝ) :
    testedHeatTrace m J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ =
      fun y => 2*J.energy y+2*(2*(J.A y*J.testRate m y))+(2*m)*((J.A y)^2*J.potentialRate m y) := by
  funext y
  unfold testedHeatTrace HeatJet.square HeatJet.energy HeatJet.testRate HeatJet.potentialRate
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 

 theorem HeatJet.square_cancellation {n : ℕ} (J : HeatJet n) (m t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTestDerivative m J.square.F J.square.G J.square.H J.square.A J.square.A₁ J.square.A₂ t x-
      clockGradient m J.F (J.potentialRate m) J.square.A (fun y => 2*(J.A y*J.testRate m y)) t x =
        clockTest m J.F J.energy t x := by
  have hs := J.square.smoothA
  have hB := (J.smoothA.mul (J.smoothTestRate m)).const_mul 2
  have hAD := hs.mul (J.smoothPotentialRate m)
  unfold clockTestDerivative clockGradient
  rw [J.square_trace, J.square.trace_eq_rate]
  change (1/2:ℝ)*(clockTest m J.F
    (fun y => 2*J.energy y+2*(2*(J.A y*J.testRate m y))+(2*m)*((J.A y)^2*J.potentialRate m y)) t x-
      clockTest m J.F J.square.A t x*clockTest m J.F (fun y => (2*m)*J.potentialRate m y) t x)-
    (clockTest m J.F (fun y => 2*(J.A y*J.testRate m y)) t x+
      m*(clockTest m J.F (fun y => J.square.A y*J.potentialRate m y) t x-
        clockTest m J.F J.square.A t x*clockTest m J.F (J.potentialRate m) t x)) = _
  dsimp only [HeatJet.square] at hs hAD ⊢
  rw [clockTest_add_test J.lipschitz ((J.smoothEnergy.const_mul 2).add (hB.const_mul 2)) (hAD.const_mul (2*m)),
    clockTest_add_test J.lipschitz (J.smoothEnergy.const_mul 2) (hB.const_mul 2)]
  simp only [clockTest_const_mul]
  ring

 theorem HeatJetFamily.continuousPotentialRate {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialRate m p.2) := by
  exact (continuous_finsetSum _ fun i _ => (V.continuousH i).add (((V.continuousG i).pow 2).const_mul m)).const_mul (1/2:ℝ)
 theorem HeatJetFamily.continuousTestRate {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).testRate m p.2) := by
  exact (continuous_finsetSum _ fun i _ => (V.continuousA₂ i).add
    (((V.continuousA₁ i).const_mul (2*m)).mul (V.continuousG i))).const_mul (1/2:ℝ)
 theorem HeatJetFamily.boundedPotentialRate {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialRate m p.2) := by
  apply (AbsBounded.sum fun i => ?_).const_mul
  simpa only [pow_two] using (V.boundedH i).add (((V.boundedG i).mul (V.boundedG i)).const_mul m)
 theorem HeatJetFamily.boundedTestRate {n : ℕ} (V : HeatJetFamily n) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).testRate m p.2) := by
  apply (AbsBounded.sum fun i => ?_).const_mul
  exact (V.boundedA₂ i).add (((V.boundedA₁ i).const_mul (2*m)).mul (V.boundedG i))

end SKFluctuations.Hierarchy

end

end OAI
