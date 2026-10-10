import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughCube01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
open scoped BigOperators
end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeRationalization
open BooleanRough BooleanPeeling CubeParameter CubeCoefficients
open RealPolynomialDegree PolynomialLineCoefficients RoughCoefficientDescentBridge
open RoughJointCoefficients CoefficientPeeling CorrectedBoxLeibman

def bound (v s : ℕ) (A : ℝ) : ℝ :=
  (max 1 (A+(Fintype.card (PositiveGrid v s) : ℝ)*((2:ℝ)^s)^v))^(v*s)

lemma one_le_bound (v s : ℕ) (A : ℝ) : 1 ≤ bound v s A :=
  one_le_pow₀ (le_max_left _ _)

 

theorem peel_coefficients {n v s q M : ℕ}
    (θ : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ)
    (hθ : ∀ I, HasDegree (θ I) q)
    (m₀ : (Fin n → ℝ) → ℝ) (hm₀ : HasDegree m₀ q)
    (hmfloor : ∀ z, m₀ (realVertex z) = (⌊θ 0 (realVertex z)⌋ : ℤ))
    (hdim : 2*(q+v*s) < n) (a : ℤ) (b : Fin n → ℤ)
    (htpos : ∀ S : Finset (Fin n), 0 < a+∑ i ∈ S, b i)
    (htbound : ∀ S : Finset (Fin n), a+∑ i ∈ S, b i ≤ (M : ℤ))
    (hrough : ∀ p : ℕ, p.Prime → (∃ S : Finset (Fin n), (p:ℤ) ∣ a+∑ i ∈ S, b i) →
      n < p ∧ ∀ i, ¬ (p:ℤ) ∣ b i)
    (Z A : ℝ) (hZ : 0 < Z) (hMZ : (M:ℝ) ≤ Z) (hA : 0 < A)
    (p : (Fin n → Bool) → ℕ) (u : (Fin n → Bool) → Fin v → ℤ)
    (hp : ∀ z, p z = 1 ∨ p z = (a+∑ i ∈ vertexSet z, b i).natAbs)
    (hu : ∀ z i, 0 ≤ u z i ∧ u z i < p z)
    (hobs : ∀ z I, 0 < totalDegree I →
      TriangularLatticeRecovery.circleNorm (gridDilate (p z)
        (gridTranslate (fun I => θ I (realVertex z)) (u z)) I) ≤ A*((p z:ℝ)/Z)^totalDegree I)
    (hsmall : (1+(M:ℝ)^(v*s)*(2^n:ℝ)^2)*(bound v s A*((M:ℝ)/Z))*
      (M:ℝ)^(v*s*2^n) < 1) :
    ∃ m : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ,
      (∀ I, HasDegree (m I) q) ∧
      (∀ I z, ∃ k : ℤ, m I (realVertex z) = k) ∧
      ∀ I z, |θ I (realVertex z)-m I (realVertex z)| *Z^totalDegree I ≤ bound v s A := by
  classical
  choose c hc hce using fun I : PositiveGrid v s => realVertex_degree (θ I.val) q (hθ I.val)
  let zS : Finset (Fin n) → (Fin n → Bool) := fun S i => decide (i ∈ S)
  have hceS (I : PositiveGrid v s) (S : Finset (Fin n)) :
      Eval (c I) S = θ I.val (realVertex (zS S)) := by
    simpa only [zS, vertexSet_decide] using hce I (zS S)
  have hps (S : Finset (Fin n)) : p (zS S) = 1 ∨ p (zS S) = (a+∑ i ∈ S, b i).natAbs := by
    simpa only [zS, vertexSet_decide] using hp (zS S)
  have hpPos (S : Finset (Fin n)) : 0 < p (zS S) := by
    rcases hps S with he | he
    · omega
    · rw [he]
      exact Int.natAbs_pos.mpr (htpos S).ne'
  have hcBound (I J : PositiveGrid v s) (S : Finset (Fin n))
      (hIJ : totalDegree I.val < totalDegree J.val) :=
    translationMatrix_degree_bound (u (zS S)) (p (zS S)) (hpPos S) (hu (zS S)) I.val J.val hIJ
  have hnear (I : PositiveGrid v s) (S : Finset (Fin n)) :
      NearInteger ((p (zS S):ℝ)^totalDegree I.val * (Eval (c I) S +
        ∑ J ∈ univ.filter (fun J : PositiveGrid v s => totalDegree I.val < totalDegree J.val),
          (translationMatrix (u (zS S)) I.val J.val:ℝ)*Eval (c J) S))
        (A*((p (zS S):ℝ)/Z)^totalDegree I.val) := by
    simpa only [gridDilate, positive_peeling, hceS] using
      circleNorm_nearInteger (hobs (zS S) I.val I.property)
  obtain ⟨f, hf⟩ := peel_cube (fun I : PositiveGrid v s => totalDegree I.val) (v*s) q M
    (fun I => ⟨I.property, RoughCoefficientDescentBridge.totalDegree_le I.val⟩)
    (by simpa using hdim) a b c hc htpos htbound (by simpa using hrough)
    Z A (((2:ℝ)^s)^v) hZ hMZ hA (by positivity) (fun S => p (zS S)) hps
    (fun I J S => translationMatrix (u (zS S)) I.val J.val) hcBound hnear
    (by simpa only [Fintype.card_fin, bound] using hsmall)
  choose m hm hem using fun I : PositiveGrid v s => realize_boolean_rational (f I) (hf I).1
  let m' : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ := fun I =>
    if hI : 0 < totalDegree I then m ⟨I,hI⟩ else m₀
  refine ⟨m', ?_, ?_, ?_⟩
  · intro I
    dsimp only [m']
    split_ifs with hI
    · exact hm _
    · exact hm₀
  · intro I z
    dsimp only [m']
    split_ifs with hI
    · obtain ⟨k, hk⟩ := eval_integral_of_coeffs (f ⟨I,hI⟩) (hf ⟨I,hI⟩).2.1 (vertexSet z)
      refine ⟨k, ?_⟩
      rw [hem]
      exact_mod_cast hk
    · have hI0 : I = 0 := (DenseBoxComplete.degree_eq_zero I).mp (by omega)
      subst I
      exact ⟨_, hmfloor z⟩
  · intro I z
    dsimp only [m']
    split_ifs with hI
    · rw [hem, ← hce ⟨I,hI⟩]
      exact (hf ⟨I,hI⟩).2.2 (vertexSet z)
    · have hI0 : I = 0 := (DenseBoxComplete.degree_eq_zero I).mp (by omega)
      subst I
      rw [hmfloor, show totalDegree (0 : PolynomialLineCoefficients.Grid v s)=0 by simp [totalDegree], pow_zero, mul_one]
      change |Int.fract (θ 0 (realVertex z))| ≤ bound v s A
      rw [abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le.trans (one_le_bound v s A)

end CubeRationalization

end

end
 

section
 
 

noncomputable section
open Filter
open scoped Topology
namespace CubeRoundingScales

theorem eventual_small (d n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    {S Z : ℕ → ℝ} (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun j => Z j/S j^k) atTop atTop) :
    ∀ᶠ j in atTop, 1 ≤ S j ∧ 0 < Z j ∧ (⌈2*S j⌉₊ : ℝ) ≤ Z j ∧
      (1+(⌈2*S j⌉₊ : ℝ)^d*(2^n:ℝ)^2)*(B*((⌈2*S j⌉₊ : ℝ)/Z j))*
        (⌈2*S j⌉₊ : ℝ)^(d*2^n) < 1 := by
  let e := d+1+d*2^n
  let C : ℝ := (1+(2^n:ℝ)^2)*B*3^e
  have hlim : Tendsto (fun j => C*(S j^e/Z j)) atTop (𝓝 0) := by
    simpa using (RoughScales.inverse_ratio_tendsto (hZ e)).const_mul C
  have hsmall : ∀ᶠ j in atTop, C*(S j^e/Z j) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ j in atTop, 3 ≤ Z j/S j := by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop 3)
  filter_upwards [hS.eventually (eventually_ge_atTop 1), hlarge, hsmall] with j hs hz hh
  have hspos : 0 < S j := by linarith
  have hz3 : 3*S j ≤ Z j := (le_div_iff₀ hspos).mp hz
  have hzpos : 0 < Z j := (by positivity : 0 < 3*S j).trans_le hz3
  have hM : (⌈2*S j⌉₊ : ℝ) ≤ 3*S j := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 2*S j)
    linarith
  refine ⟨hs, hzpos, hM.trans hz3, lt_of_le_of_lt ?_ hh⟩
  have hp : 1 ≤ (3*S j)^d := one_le_pow₀ (by linarith)
  have hfirst : 1+(⌈2*S j⌉₊ : ℝ)^d*(2^n:ℝ)^2 ≤ (1+(2^n:ℝ)^2)*(3*S j)^d := by
    calc
      _ ≤ (3*S j)^d+(3*S j)^d*(2^n:ℝ)^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ((1+(2^n:ℝ)^2)*(3*S j)^d)*(B*((3*S j)/Z j))*(3*S j)^(d*2^n) := by
      gcongr
    _ = C*(S j^e/Z j) := by
      dsimp [C, e]
      simp only [pow_add, pow_succ, mul_pow]
      ring

end CubeRoundingScales

end

end
 

section
 
noncomputable section
open Finset
open scoped BigOperators
namespace CubeArithmetic
open RoughCubeBlock RoughScales CubeParameter

lemma time_set {n : ℕ} (a m : ℤ) (h : Fin n → ℕ) (z : Fin n → Bool) :
    time a m h z = a+∑ i ∈ vertexSet z, m*(h i:ℤ) := by
  simp only [time, vertexSet, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  cases z i <;> simp

variable {G : Type*} [Group G] [TopologicalSpace G] {r : ℕ}
variable {c : RationalLattice.RealCoordinates G r} {Γ : Subgroup G} [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace
variable {v D n K w : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η S Z : ℝ}

lemma block_prime_slopes (b : Block c Γ v D c₀ C₀ B η w S Z n K)
    (hn : n ≤ w) (hK : K ≤ w) :
    ∀ p : ℕ, p.Prime →
      (∃ E : Finset (Fin n), (p:ℤ) ∣ b.start+∑ i ∈ E, b.step*(b.weight i:ℤ)) →
      n < p ∧ ∀ i, ¬ (p:ℤ) ∣ b.step*(b.weight i:ℤ) := by
  intro p hp ⟨E, hE⟩
  have ht : (p:ℤ) ∣ time b.start b.step b.weight (fun i => decide (i ∈ E)) := by
    simpa only [time_set, vertexSet_decide] using hE
  have hpw : w < p := Nat.lt_of_not_ge (fun h => b.rough _ p hp h ht)
  refine ⟨hn.trans_lt hpw, ?_⟩
  intro i hi
  have hh : Smooth w (b.weight i:ℤ) := smooth_of_abs_le (by exact_mod_cast (b.weight_pos i).ne')
    (by simpa using (b.weight_bound i).trans hK)
  have hm : Smooth w (b.step*(b.weight i:ℤ)) := RoughRationalBlock.smooth_mul b.smooth hh
  exact (not_le_of_gt hpw) (hm p hp hi)

lemma block_time_bounds (b : Block c Γ v D c₀ C₀ B η w S Z n K) (hS : 0 < S) :
    (∀ E : Finset (Fin n), 0 < b.start+∑ i ∈ E, b.step*(b.weight i:ℤ)) ∧
    (∀ E : Finset (Fin n), b.start+∑ i ∈ E, b.step*(b.weight i:ℤ) ≤ (⌈2*S⌉₊ : ℤ)) := by
  have he (E : Finset (Fin n)) : time b.start b.step b.weight (fun i => decide (i ∈ E)) =
      b.start+∑ i ∈ E, b.step*(b.weight i:ℤ) := by simp only [time_set, vertexSet_decide]
  constructor
  · intro E
    rw [← he]
    exact_mod_cast hS.trans_le (b.scales _).1
  · intro E
    rw [← he]
    exact_mod_cast (b.scales _).2.le.trans (Nat.le_ceil (2*S))

end CubeArithmetic

end

end
 

section
 
 

noncomputable section
open Finset Filter
open scoped BigOperators Topology
namespace CubeSplitProducer
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales
open CubeParameter CubeCoefficients RoughCubeBlock CubeRationalization CubeArithmetic
open DenseBooleanCubes Combinatorics PolynomialLineCoefficients CorrectedBoxLeibman
open RoughAnalyticExtraction

variable {G : Type} [Group G] [TopologicalSpace G] {r : ℕ}

def GoodCharacter (Γ : Subgroup G) (ξ : G →* Multiplicative ℝ) : Prop :=
  ξ ≠ 1 ∧ Continuous ξ ∧ ∀ g ∈ Γ, ∃ z : ℤ, (ξ g).toAdd = z

def Split {n v : ℕ} (q s : ℕ) (P : (Fin (n+v) → ℝ) → G)
    (ξ : G →* Multiplicative ℝ) (Z B : ℝ) : Prop :=
  ∃ θ m : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ,
    (∀ I, HasDegree (θ I) q) ∧ (∀ I, HasDegree (m I) q) ∧
    (∀ z x, gridEval (fun I => θ I z) x = (ξ (P (Fin.append z x))).toAdd) ∧
    (∀ I z, ∃ k : ℤ, m I (realVertex z) = k) ∧
    ∀ I z, |θ I (realVertex z)-m I (realVertex z)| *Z^totalDegree I ≤ B

variable [IsTopologicalGroup G]
variable (c : RealCoordinates G r) (hsk : SecondKind c) (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk hΓ htop in
theorem split_producer (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 0 < B) (hη : 0 < η)
    {w : ℕ → ℕ} {S Z : ℕ → ℝ} (hw : Tendsto w atTop atTop)
    (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun j => Z j/S j^k) atTop atTop) :
    ∃ q s : ℕ, ∃ U : Finset (G →* Multiplicative ℝ),
      (∀ ξ ∈ U, GoodCharacter Γ ξ) ∧ ∃ A : ℝ, 1 ≤ A ∧
      ∀ n : ℕ, 2*(q+v*s) < n → ∃ N L : ℕ, ∀ K : ℕ, ∀ᶠ j in atTop,
        ∀ _ : Block c Γ v D c₀ C₀ B η (w j) (S j) (Z j) N K,
          ∃ b' : Block c Γ v D c₀ C₀ B η (w j) (S j) (Z j) n (L*(N*K)),
            ∃ ξ ∈ U, Split q s b'.P ξ (Z j) A := by
  classical
  obtain ⟨q,s,U,A,T,hA,hT,hcoeff,hdetect⟩ := CubeCharacter.character_tools c hsk Γ hΓ htop
    v D c₀ C₀ B η hc₀ hC₀ hB hη
  let V := U.filter (GoodCharacter Γ)
  have hV (ξ) (hξ : ξ ∈ V) : GoodCharacter Γ ξ := (mem_filter.mp hξ).2
  refine ⟨q,s,V,hV,bound v s A,one_le_bound v s A,?_⟩
  intro n hn
  obtain ⟨N₀,hN₀⟩ := CubeConstant.constant_thinning n q
  obtain ⟨N₁,hN₁⟩ := colored_subcube N₀ {ξ // ξ ∈ V}
  refine ⟨N₁,N₀,fun K => ?_⟩
  have hlarge : ∀ᶠ j in atTop, 2*T ≤ Z j/S j := by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop (2*T))
  filter_upwards [CubeRoundingScales.eventual_small (v*s) n (bound v s A)
      (zero_le_one.trans (one_le_bound v s A)) hS hZ,
    hw.eventually (eventually_ge_atTop (max n (N₀*(N₁*K)))), hlarge]
    with j hj hwj hlargej
  intro b
  have hSj : 0 < S j := zero_lt_one.trans_le hj.1
  have hscale (z : Fin N₁ → Bool) : 0 < (time b.start b.step b.weight z).natAbs ∧
      T ≤ Z j/(time b.start b.step b.weight z).natAbs := by
    have ht : 0 < time b.start b.step b.weight z := by exact_mod_cast hSj.trans_le (b.scales z).1
    have habs : ((time b.start b.step b.weight z).natAbs:ℝ) = (time b.start b.step b.weight z:ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast ht)]
    refine ⟨Int.natAbs_pos.mpr ht.ne', ?_⟩
    apply (le_div_iff₀ (by exact_mod_cast Int.natAbs_pos.mpr ht.ne')).mpr
    rw [habs]
    calc
      _ ≤ T*(2*S j) := mul_le_mul_of_nonneg_left (b.scales z).2.le (zero_le_one.trans hT)
      _ ≤ Z j := by have hh := (le_div_iff₀ hSj).mp hlargej; nlinarith
  choose p u hp hu ξ hξ hobs using hdetect N₁ K (w j) (S j) (Z j) b hscale
  have hξV (z) : ξ z ∈ V := mem_filter.mpr ⟨hξ z, (hobs z).1, (hobs z).2.1, (hobs z).2.2.1⟩
  obtain ⟨l,χ,hχ⟩ := hN₁ (fun z => (⟨ξ z,hξV z⟩ : {ξ // ξ ∈ V}))
  have hχeq (z) : ξ (l z) = χ.val := congrArg Subtype.val (hχ z)
  let b₀ := b.subspace l
  let θ : PolynomialLineCoefficients.Grid v s → (Fin N₀ → ℝ) → ℝ := CubeCharacter.coefficients b₀.P χ.val
  obtain ⟨hθ,heθ⟩ := hcoeff N₀ b₀.P b₀.degree χ.val (hV χ.val χ.property).2.1
  obtain ⟨l₀,m₀,hm₀,hmfloor⟩ := hN₀ (θ 0) (hθ 0)
  let b₁ := b₀.subspace l₀
  let θ' : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ := fun I z => θ I (parameterLift l₀ z)
  have hθ' (I) : HasDegree (θ' I) q := degree_parameterLift l₀ (hθ I)
  have heθ' (z : Fin n → ℝ) (x : Fin v → ℝ) :
      gridEval (fun I => θ' I z) x = (χ.val (b₁.P (Fin.append z x))).toAdd := by
    simpa only [θ', b₁, Block.subspace, lift_append] using heθ (parameterLift l₀ z) x
  have hobs₁ (z : Fin n → Bool) : CharacterObstruction (s:=s) Γ
      (fun x => b₁.P (Fin.append (realVertex z) (fun i => (x i:ℝ)))) χ.val
      (u (l (l₀ z))) (p (l (l₀ z))) (Z j) A := by
    simpa only [b₁, b₀, Block.subspace, lift_vertex, hχeq] using hobs (l (l₀ z))
  have hcoeffobs (z : Fin n → Bool) (I : PolynomialLineCoefficients.Grid v s) (hI : 0 < totalDegree I) :
      TriangularLatticeRecovery.circleNorm (gridDilate (p (l (l₀ z)))
        (gridTranslate (fun I => θ' I (realVertex z)) (u (l (l₀ z)))) I) ≤
          A*((p (l (l₀ z)):ℝ)/Z j)^totalDegree I := by
    obtain ⟨_,_,_,a,ha,_,ho⟩ := hobs₁ z
    have he : a = fun I => θ' I (realVertex z) := gridEval_integer_injective
      (fun x => (ha x).trans (heθ' (realVertex z) (fun i => (x i:ℝ))).symm)
    simpa only [he] using ho I hI
  obtain ⟨htpos,htbound⟩ := block_time_bounds b₁ hSj
  have hprime := block_prime_slopes b₁ ((le_max_left _ _).trans hwj) ((le_max_right _ _).trans hwj)
  have hp₁ (z : Fin n → Bool) : p (l (l₀ z)) = 1 ∨
      p (l (l₀ z)) = (b₁.start+∑ i ∈ vertexSet z, b₁.step*(b₁.weight i:ℤ)).natAbs := by
    simpa only [← time_set, b₁, b₀, Block.subspace, time_subspace] using hp (l (l₀ z))
  obtain ⟨m,hm,hmi,hmerr⟩ := peel_coefficients θ' hθ' m₀ hm₀
    (fun z => by simpa only [θ', parameterLift_vertex] using hmfloor z)
    hn b₁.start (fun i => b₁.step*(b₁.weight i:ℤ)) htpos htbound hprime
    (Z j) A hj.2.1 hj.2.2.1 hA (fun z => p (l (l₀ z))) (fun z => u (l (l₀ z)))
    hp₁ (fun z => hu (l (l₀ z))) hcoeffobs hj.2.2.2
  have hfinal : ∃ b' : Block c Γ v D c₀ C₀ B η (w j) (S j) (Z j) n (N₀*(N₁*K)),
      ∃ ξ ∈ V, Split q s b'.P ξ (Z j) (bound v s A) :=
    ⟨b₁,χ.val,χ.property,θ',m,hθ',hm,heθ',hmi,hmerr⟩
  exact hfinal

end CubeSplitProducer

end
end

end OAI
