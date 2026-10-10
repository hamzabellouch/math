import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeParameter01
import OAI.Combinatorics.SumProduct.Alignment.DenseBoolean01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI


section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeConstant
open CubeParameter CubeCoefficients BooleanRough RealPolynomialDegree DenseBooleanCubes
open Combinatorics

theorem constant_thinning (n q : ℕ) :
    ∃ N : ℕ, ∀ f : (Fin N → ℝ) → ℝ, HasDegree f q →
      ∃ l : Subspace (Fin n) Bool (Fin N),
      ∃ m : (Fin n → ℝ) → ℝ, HasDegree m q ∧
        ∀ z, m (realVertex z) = (⌊f (realVertex (l z))⌋ : ℤ) := by
  let K : ℕ := 2^(n+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨N, hN⟩ := colored_subcube n (Fin K)
  refine ⟨N, ?_⟩
  intro f hf
  let color : (Fin N → Bool) → Fin K := fun z =>
    ⟨⌊(K : ℝ)*Int.fract (f (realVertex z))⌋₊, (Nat.floor_lt
      (mul_nonneg hKr.le (Int.fract_nonneg _))).mpr (by
        simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (f (realVertex z))) hKr)⟩
  obtain ⟨l, c, hc⟩ := hN color
  let f' : (Fin n → ℝ) → ℝ := fun z => f (parameterLift l z)
  have hf' : HasDegree f' q := degree_parameterLift l hf
  obtain ⟨θ, hθ, hθeval⟩ := realVertex_degree f' q hf'
  have hθS (S : Finset (Fin n)) : Eval θ S = f (realVertex (l (fun i => decide (i ∈ S)))) := by
    simpa only [vertexSet_decide, f', parameterLift_vertex] using hθeval (fun i => decide (i ∈ S))
  have hspread (S : Finset (Fin n)) : |Int.fract (Eval θ S)-(c.val : ℝ)/(K : ℝ)| ≤ 1/(K : ℝ) := by
    have hh := congrArg Fin.val (hc (fun i => decide (i ∈ S)))
    change ⌊(K : ℝ)*Int.fract (f (realVertex (l (fun i => decide (i ∈ S)))))⌋₊ = c.val at hh
    simpa only [hθS, hh] using ConstantCoefficientRationalization.fractional_cell_bound hK
      (f (realVertex (l (fun i => decide (i ∈ S)))))
  have hsmall : (2 : ℝ)^(Fintype.card (Fin n))*(1/(K : ℝ)) < 1 := by
    rw [Fintype.card_fin, mul_one_div, div_lt_one hKr]
    dsimp [K]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  obtain ⟨a, ha, hea⟩ := constant_rounding q θ hθ (c.val / (K : ℝ)) (1/(K : ℝ)) (by positivity) hsmall hspread
  let aq : Finset (Fin n) → ℚ := fun S => a S
  have haq : DegreeLE q aq := by intro S hS; simp [aq, ha S hS]
  obtain ⟨m, hm, hem⟩ := realize_boolean_rational aq haq
  refine ⟨l, m, hm, ?_⟩
  intro z
  rw [hem]
  have haev (S : Finset (Fin n)) : Eval aq S = ((Eval a S : ℤ) : ℚ) := by
    simp only [Eval, aq, Int.cast_sum]
  rw [haev, hea, Rat.cast_intCast, hθeval]
  simp only [f', parameterLift_vertex]

end CubeConstant

end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace RoughCubeBlock
open RationalLattice RealPolynomialDegree RoughScales
open FinitePieceAverages RoughSamplingWeights DenseBooleanCubes CubeParameter
open Combinatorics

 
def time {n : ℕ} (a m : ℤ) (h : Fin n → ℕ) (z : Fin n → Bool) : ℤ :=
  a+m*(∑ i, if z i then h i else 0 : ℕ)

lemma time_subspace {n N : ℕ} (l : Subspace (Fin n) Bool (Fin N))
    (a m : ℤ) (h : Fin N → ℕ) (z : Fin n → Bool) :
    time (a+m*(CubeSubspace.offset l h : ℕ)) m (CubeSubspace.weight l h) z = time a m h (l z) := by
  unfold time
  rw [CubeSubspace.value]
  push_cast
  ring

variable {G : Type*} [Group G] [TopologicalSpace G] {r : ℕ}
variable (c : RealCoordinates G r) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

structure Block (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ) (w : ℕ) (S Z : ℝ)
    (n K : ℕ) where
  start : ℤ
  step : ℤ
  positive : 0 < step
  smooth : Smooth w step
  weight : Fin n → ℕ
  weight_pos : ∀ i, 0 < weight i
  weight_bound : ∀ i, weight i ≤ K
  scales : ∀ z, S ≤ (time start step weight z : ℝ) ∧ (time start step weight z : ℝ) < 2*S
  rough : ∀ z, Rough w (time start step weight z)
  P : (Fin (n+v) → ℝ) → G
  degree : ∀ i, HasDegree (fun y => canonicalLog c (P y) i) D
  lo : (Fin n → Bool) → Fin v → ℝ
  hi : (Fin n → Bool) → Fin v → ℝ
  res : (Fin n → Bool) → Fin v → ℤ
  test : (Fin n → Bool) → (G⧸Γ) → ℂ
  side : ∀ z i, c₀*Z ≤ hi z i-lo z i
  box : ∀ z i, -C₀*Z ≤ lo z i ∧ hi z i ≤ C₀*Z
  lip : ∀ z, LipschitzWith B (test z)
  bound : ∀ z y, ‖test z y‖ ≤ B
  bad : ∀ z, η ≤ ‖mean (boxIndices (lo z) (hi z) (fun _ => 0) 1)
      (fun x => test z (QuotientGroup.mk (P (Fin.append (realVertex z) (fun i => (x i : ℝ)))))) -
    mean (physicalResidueBox (lo z) (hi z) (res z) (time start step weight z).natAbs)
      (fun x => test z (QuotientGroup.mk (P (Fin.append (realVertex z) (fun i => (x i : ℝ))))))‖

namespace Block
variable {c Γ} {v D n N K : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η : ℝ} {w : ℕ} {S Z : ℝ}
variable (b : Block c Γ v D c₀ C₀ B η w S Z N K)

 

def subspace (l : Subspace (Fin n) Bool (Fin N)) : Block c Γ v D c₀ C₀ B η w S Z n (N*K) where
  start := b.start+b.step*(CubeSubspace.offset l b.weight : ℕ)
  step := b.step
  positive := b.positive
  smooth := b.smooth
  weight := CubeSubspace.weight l b.weight
  weight_pos := CubeSubspace.weight_pos l b.weight b.weight_pos
  weight_bound := CubeSubspace.weight_le l b.weight K b.weight_bound
  scales := by intro z; simpa only [time_subspace] using b.scales (l z)
  rough := by intro z; simpa only [time_subspace] using b.rough (l z)
  P := fun y => b.P (CubeParameter.lift l y)
  degree := fun i => degree_lift l (b.degree i)
  lo := fun z => b.lo (l z)
  hi := fun z => b.hi (l z)
  res := fun z => b.res (l z)
  test := fun z => b.test (l z)
  side := fun z => b.side (l z)
  box := fun z => b.box (l z)
  lip := fun z => b.lip (l z)
  bound := fun z => b.bound (l z)
  bad := by
    intro z
    simpa only [time_subspace, lift_vertex] using b.bad (l z)

end Block

 
def initial (n N : ℕ) (h : n ≤ N) : Subspace (Fin n) Bool (Fin N) where
  idxFun i := if hi : i.val < n then Sum.inr ⟨i.val, hi⟩ else Sum.inl false
  proper j := by
    refine ⟨⟨j.val, j.isLt.trans_le h⟩, ?_⟩
    simp [j.isLt]

namespace Block
variable {c Γ} {v D n N K : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η : ℝ} {w : ℕ} {S Z : ℝ}
variable (b : Block c Γ v D c₀ C₀ B η w S Z N K)

def restrict (h : n ≤ N) : Block c Γ v D c₀ C₀ B η w S Z n (N*K) := b.subspace (initial n N h)

end Block

end RoughCubeBlock

end

end
 

section
 
 

noncomputable section
open scoped BigOperators
namespace CubeCharacter
open RationalLattice MalcevCharacters RealPolynomialDegree RoughPolynomialDegree
open CubeParameter CubeCoefficients RoughCubeBlock RoughAnalyticExtraction
open RoughDyadicFiltration RoughLogPolynomialAdaptation PolynomialLineCoefficients
open CorrectedBoxLeibman MeasureTheory AbelianMalcevTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {r : ℕ}
variable (c : RealCoordinates G r) (hsk : SecondKind c) (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk in
omit [IsTopologicalGroup G] in
lemma degree_character {n q : ℕ} (P : (Fin n → ℝ) → G)
    (hP : ∀ i, HasDegree (fun y => c.coord (P y) i) q)
    (ξ : G →* Multiplicative ℝ) (hξ : Continuous ξ) :
    HasDegree (fun y => (ξ (P y)).toAdd) q := by
  have he : (fun y => (ξ (P y)).toAdd) =
      (fun y => ∑ i, c.coord (P y) i * (ξ (axis c i 1)).toAdd) :=
    funext (fun y => character_coordinates c hsk ξ hξ (P y))
  rw [he]
  apply finite_sum
  intro i _
  simpa only [mul_comm] using RealPolynomialDegree.scale (hP i) ((ξ (axis c i 1)).toAdd)

def coefficients {n v s : ℕ} (P : (Fin (n+v) → ℝ) → G) (ξ : G →* Multiplicative ℝ) :
    PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ :=
  CubeCoefficients.coefficients (fun y => (ξ (P y)).toAdd)

include hsk hΓ htop in
 

theorem character_tools (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 0 < B) (hη : 0 < η) :
    ∃ q s : ℕ, ∃ U : Finset (G →* Multiplicative ℝ), ∃ A T : ℝ, 0 < A ∧ 1 ≤ T ∧
      (∀ n : ℕ, ∀ P : (Fin (n+v) → ℝ) → G,
        (∀ i, HasDegree (fun y => canonicalLog c (P y) i) D) →
        ∀ ξ : G →* Multiplicative ℝ, Continuous ξ →
          (∀ I, HasDegree (coefficients (s:=s) P ξ I) q) ∧
          ∀ z : Fin n → ℝ, ∀ x : Fin v → ℝ,
            gridEval (fun I => coefficients (s:=s) P ξ I z) x = (ξ (P (Fin.append z x))).toAdd) ∧
      ∀ n K w : ℕ, ∀ S Z : ℝ, ∀ b : Block c Γ v D c₀ C₀ B η w S Z n K,
        (∀ z, 0 < (time b.start b.step b.weight z).natAbs ∧
          T ≤ Z/(time b.start b.step b.weight z).natAbs) →
        ∀ z, ∃ p : ℕ, ∃ u : Fin v → ℤ,
          (p=1 ∨ p=(time b.start b.step b.weight z).natAbs) ∧
          (∀ i, 0 ≤ u i ∧ u i < p) ∧
          ∃ ξ ∈ U, CharacterObstruction (s:=s) Γ
            (fun x => b.P (Fin.append (realVertex z) (fun i => (x i : ℝ)))) ξ u p Z A := by
  classical
  let : MeasurableSpace (G⧸Γ) := borel (G⧸Γ)
  let : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance := by
    rw [← htop]
    exact ⟨rfl⟩
  let : BorelSpace (G⧸Γ) := by
    change @BorelSpace (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace inferInstance
    exact ⟨rfl⟩
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : Group.IsNilpotent G := nilpotent_of_coordinates c
  let : ContinuousConstSMul G (G⧸Γ) := by
    change @ContinuousConstSMul G (G⧸Γ) mtr.toUniformSpace.toTopologicalSpace inferInstance
    rw [htop]
    infer_instance
  obtain ⟨μ, hinv⟩ := SolvableInvariantMeasure.exists_invariant_measure (G:=G) (X:=G⧸Γ)
  let := hinv
  obtain ⟨E, hE, hcoord⟩ := coord_degree_bound c
  obtain ⟨C, hC, hadapt⟩ := RoughDyadicFiltration.logarithmic_adapted c hsk
  let H := RoughDyadicFiltration.filtration c (max 1 (C*D))
  let s := max 1 (C*D)*2^r
  obtain ⟨h0, h1, hs, hqb, hq, hpoly⟩ := hadapt v D
  obtain ⟨U, A, T, hA, hT, hdetect⟩ := discrepancy_character (t:=r) (d:=0)
    c hsk H h0 h1 s hs (cutoff r (max 1 (C*D))) hqb hq Γ hΓ htop
    (μ : Measure (G⧸Γ)) v c₀ C₀ B η hc₀ hC₀ hB hη
  refine ⟨E*D, s, U, A, T, hA, hT, ?_, ?_⟩
  · intro n P hP ξ hξ
    have hscalar := degree_character c hsk P (hcoord (n+v) D P hP) ξ hξ
    refine ⟨fun I => coefficients_degree hscalar I, ?_⟩
    intro z x
    apply coefficients_grid_real _ hscalar z
    have hslice : ∀ i, HasDegree (fun x => canonicalLog c (P (Fin.append z x)) i) D :=
      fun i => degree_space_restrict (hP i) z
    have hPf := (hpoly (fun x => P (Fin.append z x)) hslice).2
    intro x q
    exact LeibmanSquare.character_polynomial H s hs
      (LeibmanSquare.polynomial_integer_line H hPf x q) ξ
  · intro n K w S Z b hscale z
    let Pz : (Fin v → ℝ) → G := fun x => b.P (Fin.append (realVertex z) x)
    have hPz : ∀ i, HasDegree (fun x => canonicalLog c (Pz x) i) D :=
      fun i => degree_space_restrict (b.degree i) _
    have hf := (hpoly Pz hPz).2
    let F : C(G⧸Γ, ℂ) := ⟨b.test z, (b.lip z).continuous⟩
    have hFN : ‖F‖ ≤ B := (ContinuousMap.norm_le F B.coe_nonneg).mpr (b.bound z)
    exact hdetect Z (time b.start b.step b.weight z).natAbs (hscale z).1 (hscale z).2
      (b.lo z) (b.hi z) (b.res z) (b.side z) (b.box z) _ hf
      ⟨F, b.lip z, hFN, b.bad z⟩

end CubeCharacter

end
end

end OAI
