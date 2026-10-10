import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeRationalization01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
open Finset Filter
open scoped BigOperators Topology
end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeKernel
open CubeSplitProducer CubeCoefficients CubeParameter RealPolynomialDegree RoughPolynomialDegree
open RationalLattice MalcevCharacters RoughKernelFactorization PolynomialLineCoefficients CorrectedBoxLeibman

lemma value_sub {n v s : ℕ} (θ m : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ)
    (y : Fin (n+v) → ℝ) :
    value (fun I z => θ I z-m I z) y = value θ y-value m y := by
  simp only [value, gridEval, sub_mul, sum_sub_distrib]

lemma integer_spatial {n v s : ℕ} (m : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ)
    (z : Fin n → Bool) (hm : ∀ I, ∃ k : ℤ, m I (realVertex z) = k) :
    ∃ p : MvPolynomial (Fin v) ℤ, ∀ x : Fin v → ℤ,
      ((MvPolynomial.eval x p:ℤ):ℝ) = value m (Fin.append (realVertex z) (fun i => (x i:ℝ))) := by
  classical
  choose a ha using hm
  let p : MvPolynomial (Fin v) ℤ := ∑ I, MvPolynomial.monomial (gridExponent I) (a I)
  refine ⟨p, ?_⟩
  intro x
  simp only [p, MvPolynomial.eval_sum, MvPolynomial.eval_monomial, Int.cast_sum, value_append, gridEval]
  apply sum_congr rfl
  intro I _
  rw [ha]
  push_cast
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  rfl

lemma spatial_affine {n v d : ℕ} {f : (Fin (n+v) → ℝ) → ℝ} (hf : HasDegree f d)
    (u : Fin v → ℝ) (K : ℝ) :
    HasDegree (fun y : Fin (n+v) → ℝ =>
      f (Fin.append (fun i => y (i.castAdd v)) (fun i => u i+K*y (i.natAdd n)))) d := by
  have hT (i : Fin (n+v)) : HasDegree (fun y : Fin (n+v) → ℝ =>
      Fin.append (fun i => y (i.castAdd v)) (fun i => u i+K*y (i.natAdd n)) i) 1 := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using coordinate (j.castAdd v)
    · intro j
      simpa only [Fin.append_right, max_self] using RealPolynomialDegree.add
        (RealPolynomialDegree.const (σ:=Fin (n+v)) (u j) 1)
        (RealPolynomialDegree.scale (coordinate (j.natAdd n)) K)
  simpa only [one_mul] using compose hf _ hT

lemma split_subspace {G : Type} [Group G] {n N v q s : ℕ}
    {P : (Fin (N+v) → ℝ) → G} {ξ : G →* Multiplicative ℝ} {Z B : ℝ}
    (h : Split q s P ξ Z B) (l : Combinatorics.Subspace (Fin n) Bool (Fin N)) :
    Split q s (fun y => P (lift l y)) ξ Z B := by
  obtain ⟨θ,m,hθ,hm,he,hi,herr⟩ := h
  refine ⟨fun I z => θ I (parameterLift l z), fun I z => m I (parameterLift l z),
    fun I => degree_parameterLift l (hθ I), fun I => degree_parameterLift l (hm I), ?_, ?_, ?_⟩
  · intro z x
    simpa only [lift_append] using he (parameterLift l z) x
  · intro I z
    simpa only [parameterLift_vertex] using hi I (l z)
  · intro I z
    simpa only [parameterLift_vertex] using herr I (l z)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r : ℕ} (c : RealCoordinates G (r+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)

 
theorem kernel_polynomial : ∃ E : ℕ, 0 < E ∧ ∀ n v D q s : ℕ,
    ∀ P : (Fin (n+v) → ℝ) → G,
    ∀ θ m : PolynomialLineCoefficients.Grid v s → (Fin n → ℝ) → ℝ,
    (∀ i, HasDegree (fun y => canonicalLog c (P y) i) D) →
    (∀ I, HasDegree (θ I) q) → (∀ I, HasDegree (m I) q) →
    (∀ z x, gridEval (fun I => θ I z) x = (χ (P (Fin.append z x))).toAdd) →
    ∃ Q : (Fin (n+v) → ℝ) → χ.ker,
      (∀ y, P y = R.flow c hsk χ Γ (Multiplicative.ofAdd (value (fun I z => θ I z-m I z) y))*
        (Q y).val*R.flow c hsk χ Γ (Multiplicative.ofAdd (value m y))) ∧
      ∀ i, HasDegree (fun y => canonicalLog (R.chart c hsk χ Γ) (Q y) i)
        (E*max D (q+v*s)) := by
  obtain ⟨E,hE,hfactor⟩ := R.logarithmic_factorization c hsk χ Γ
  refine ⟨E,hE,?_⟩
  intro n v D q s P θ m hP hθ hm he
  apply hfactor (n+v) (max D (q+v*s)) P (value (fun I z => θ I z-m I z)) (value m)
  · intro y
    rw [value_sub, sub_add_cancel]
    simpa only [value, Fin.append_castAdd_natAdd] using
      (he (fun i => y (i.castAdd v)) (fun i => y (i.natAdd n))).symm
  · exact fun i => RealPolynomialDegree.mono (hP i) (le_max_left _ _)
  · apply RealPolynomialDegree.mono _ (le_max_right _ _)
    apply value_degree
    intro I
    simpa only [max_self, sub_eq_add_neg] using RealPolynomialDegree.add (hθ I) (RealPolynomialDegree.neg (hm I))
  · exact RealPolynomialDegree.mono (value_degree m hm) (le_max_right _ _)

end CubeKernel

end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace CubeReduction
open RationalLattice MalcevCharacters RoughKernelFactorization RealPolynomialDegree
open RoughCubeBlock CubeSplitProducer CubeKernel CubeParameter CubeCoefficients
open RoughScales RoughCommonKernelDiscrepancy RoughCommonKernelCover
open RoughSamplingWeights FinitePieceAverages PolynomialLineCoefficients CorrectedBoxLeibman
open DenseBooleanCubes Combinatorics
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r : ℕ} (c : RealCoordinates G (r+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (Γ : Subgroup G) (R : Reduction c hsk χ Γ)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (hcont : Continuous χ) (hZint : ∀ g ∈ Γ, ∃ z : ℤ, (χ g).toAdd=z)
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

private def metricIdentity :
    @Homeomorph (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) mtr.toUniformSpace.toTopologicalSpace := by
  refine @Homeomorph.mk _ _ (QuotientGroup.instTopologicalSpace Γ) mtr.toUniformSpace.toTopologicalSpace
    (Equiv.refl _) ?_ ?_
  · rw [htop]; exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
  · rw [htop]; exact @continuous_id (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)

include hΓ hcont hZint htop in
theorem reduce_split_cubes (v D q s : ℕ) (c₀ C₀ A : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ Λ : Subgroup χ.ker, ∃ d : RealCoordinates χ.ker r, SecondKind d ∧
      ∃ hΛ : ∀ g : χ.ker, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, d.coord g i=z,
      ∃ D' : ℕ, ∃ c' : ℝ, 0 < c' ∧ ∃ B' : NNReal, 0 < B' ∧ ∃ δ : ℝ, 0 < δ ∧
      letI := coordinateQuotientMetric d Λ hΛ
      ∀ H : ℕ, ∃ N : ℕ, ∀ (w K : ℕ) (S Z : ℝ), R.period ≤ w →
        0 < S → (R.period:ℝ) ≤ Z → 1+2*S ≤ δ*Z →
        ∀ b : Block c Γ v D c₀ C₀ B η w S Z N K, Split q s b.P χ Z A →
          Nonempty (Block d Λ v D' c' (C₀+1) B' (η/2) w S (Z/R.period) H (N*K)) := by
  classical
  obtain ⟨Λ,d,hd,hΛ,hle,E,hE,hdegree⟩ := common_kernel_cover c hsk χ Γ R hΓ
  let := coordinateQuotientMetric d Λ hΛ
  obtain ⟨J,hJ,hkernel⟩ := CubeKernel.kernel_polynomial c hsk χ Γ R
  let ε : ℝ := η/14
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨M₀,hM₀,B',hB',δ,hδ,hdisc⟩ := source_common_kernel_discrepancy c hsk χ Γ R hΓ hcont hZint
    Λ d hΛ hle (metricIdentity Γ htop) (fun (I : PolynomialLineCoefficients.Grid v s) i => (I i).val)
    A C₀ c₀ (B:ℝ) hA hC₀.le hc₀ B.coe_nonneg B ε hε
  let D' := E*(J*max D (q+v*s))
  refine ⟨Λ,d,hd,hΛ,D',c₀/(M₀:ℝ),div_pos hc₀ (by exact_mod_cast hM₀),B',hB',δ,hδ,?_⟩
  intro H
  obtain ⟨N,hN⟩ := colored_subcube H (Fin v → Fin R.period)
  refine ⟨N,?_⟩
  intro w K S Z hwp hS hZ hsmall b hsplit
  obtain ⟨θ,m,hθ,hm,he,hmi,hmerr⟩ := hsplit
  obtain ⟨Q,hQP,hQdeg⟩ := hkernel N v D q s b.P θ m b.degree hθ hm he
  have hQd : ∀ i, HasDegree (fun y => canonicalLog d (Q y) i) D' :=
    hdegree (N+v) _ Q hQdeg
  have hfib (z : Fin N → Bool) :
      ∃ u : Fin v → Fin R.period, ∃ (lo hi : Fin v → ℝ) (res : Fin v → ℤ) (f : (χ.ker⧸Λ) → ℂ),
        LipschitzWith B' f ∧ (∀ y, ‖f y‖ ≤ B') ∧
        (∀ i, -(C₀+1)*(Z/R.period) ≤ lo i ∧ hi i ≤ (C₀+1)*(Z/R.period)) ∧
        (∀ i, (c₀/M₀)*(Z/R.period) ≤ hi i-lo i) ∧
        η/2 ≤ ‖mean (boxIndices lo hi (fun _ => 0) 1)
          (fun y => f (QuotientGroup.mk (Q (Fin.append (realVertex z)
            (fun i => ((integerAffine (fun i => ((u i).val:ℤ)) R.period y i:ℤ):ℝ)))))) -
          mean (physicalResidueBox lo hi res (time b.start b.step b.weight z).natAbs)
          (fun y => f (QuotientGroup.mk (Q (Fin.append (realVertex z)
            (fun i => ((integerAffine (fun i => ((u i).val:ℤ)) R.period y i:ℤ):ℝ))))))‖ := by
    have htpos : 0 < time b.start b.step b.weight z := by exact_mod_cast hS.trans_le (b.scales z).1
    have hcast : ((time b.start b.step b.weight z).natAbs:ℝ) = (time b.start b.step b.weight z:ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast htpos)]
    have htK : (time b.start b.step b.weight z).natAbs.Coprime R.period :=
      (RoughSamplingWeights.period_coprime_of_rough w R.period _ R.period_pos hwp
        ((rough_iff_coprime w _).mp (b.rough z))).symm
    obtain ⟨p,hp⟩ := integer_spatial m z (fun I => hmi I z)
    have hfactor (x : Fin v → ℤ) : b.P (Fin.append (realVertex z) (fun i => (x i:ℝ))) =
        R.flow c hsk χ Γ (Multiplicative.ofAdd (UniformSlowPolynomials.form
          (fun (I : PolynomialLineCoefficients.Grid v s) i => (I i).val)
          (fun I => θ I (realVertex z)-m I (realVertex z)) (fun i => (x i:ℝ)))) *
        (Q (Fin.append (realVertex z) (fun i => (x i:ℝ)))).val *
        R.flow c hsk χ Γ (Multiplicative.ofAdd ((MvPolynomial.eval x p:ℤ):ℝ)) := by
      rw [hp]
      simpa only [value_append, UniformSlowPolynomials.form, gridEval] using hQP (Fin.append (realVertex z) (fun i => (x i:ℝ)))
    obtain ⟨u,lo,hi,res,f,hf,hfB,hbox,hside,hbad⟩ := hdisc Z hZ
      (fun I => θ I (realVertex z)-m I (realVertex z)) (fun I => hmerr I z)
      (b.lo z) (b.hi z) (by simpa only [neg_mul] using b.box z) (b.side z)
      (b.res z) _ (Int.natAbs_pos.mpr htpos.ne') htK (by rw [hcast]; linarith [(b.scales z).2])
      (b.test z) (b.lip z) (b.bound z)
      (fun x => b.P (Fin.append (realVertex z) (fun i => (x i:ℝ))))
      (fun x => Q (Fin.append (realVertex z) (fun i => (x i:ℝ)))) p hfactor η (b.bad z)
    refine ⟨u,lo,hi,res,f,hf,hfB,hbox,hside,?_⟩
    convert hbad using 1
    dsimp [ε]
    ring
  choose u lo hi res f hf hfB hbox hside hbad using hfib
  obtain ⟨l,u₀,hu⟩ := hN u
  let b₁ := b.subspace l
  let Q' : (Fin (N+v) → ℝ) → χ.ker := fun y =>
    Q (Fin.append (fun i => y (i.castAdd v)) (fun i => ((u₀ i).val:ℝ)+(R.period:ℝ)*y (i.natAdd N)))
  let P' : (Fin (H+v) → ℝ) → χ.ker := fun y => Q' (lift l y)
  have hP' (i) : HasDegree (fun y => canonicalLog d (P' y) i) D' :=
    degree_lift l (spatial_affine (hQd i) (fun i => ((u₀ i).val:ℝ)) R.period)
  refine ⟨{
    start := b₁.start
    step := b₁.step
    positive := b₁.positive
    smooth := b₁.smooth
    weight := b₁.weight
    weight_pos := b₁.weight_pos
    weight_bound := b₁.weight_bound
    scales := b₁.scales
    rough := b₁.rough
    P := P'
    degree := hP'
    lo := fun z => lo (l z)
    hi := fun z => hi (l z)
    res := fun z => res (l z)
    test := fun z => f (l z)
    side := fun z => hside _
    box := fun z => hbox _
    lip := fun z => hf _
    bound := fun z => hfB _
    bad := ?_ }⟩
  intro z
  simpa only [P', Q', lift_vertex, Fin.append_left, Fin.append_right, integerAffine,
    hu z, Int.cast_add, Int.cast_mul, Int.cast_natCast, b₁, Block.subspace, time_subspace]
    using hbad (l z)

end CubeReduction

end

end
 

section
 
noncomputable section
namespace CubeZero
open RationalLattice RoughCubeBlock RoughSamplingWeights FinitePieceAverages Filter
variable {G : Type} [Group G] [TopologicalSpace G]
variable (c : RealCoordinates G 0) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

theorem no_cube_at (v D w n K : ℕ) (c₀ C₀ S Z η : ℝ) (B : NNReal)
    (hη : 0 < η) (hS : 1 ≤ S) (hZ : 8*S ≤ c₀*Z) :
    IsEmpty (Block c Γ v D c₀ C₀ B η w S Z n K) := by
  classical
  let : Subsingleton G := ⟨fun g h => c.coord.injective (Subsingleton.elim _ _)⟩
  let : Subsingleton (G⧸Γ) := inferInstance
  refine ⟨fun b => ?_⟩
  let z : Fin n → Bool := fun _ => false
  let t := time b.start b.step b.weight z
  have hscale := b.scales z
  have ht0 : 0 < t := by exact_mod_cast (show (0:ℝ) < t by exact zero_lt_one.trans_le (hS.trans hscale.1))
  have ht : 0 < t.natAbs := Int.natAbs_pos.mpr ht0.ne'
  have hcast : (t.natAbs:ℝ) = (t:ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast ht0)]
  have hside (i) : 4*(t.natAbs:ℝ) ≤ b.hi z i-b.lo z i := by
    rw [hcast]
    have hh := b.side z i
    dsimp only [t]
    linarith
  have hlarge (i) : 4*(1:ℝ) ≤ b.hi z i-b.lo z i := by
    have hh : (1:ℝ) ≤ t.natAbs := by exact_mod_cast ht
    linarith [hside i]
  have h₁ := box_nonempty (b.lo z) (b.hi z) (fun _ => 0) 1 zero_lt_one hlarge
  have h₂ := RoughZeroDimension.physical_nonempty (b.lo z) (b.hi z) (b.res z) t.natAbs ht hside
  have hF : (fun x : Fin v → ℤ => b.test z (QuotientGroup.mk
      (b.P (Fin.append (CubeParameter.realVertex z) (fun i => (x i:ℝ)))))) =
      (fun _ => b.test z (QuotientGroup.mk (1:G))) := by
    funext x
    exact congrArg (b.test z) (Subsingleton.elim _ _)
  have hb := b.bad z
  rw [hF, RoughZeroDimension.constant_mean _ h₁, RoughZeroDimension.constant_mean _ h₂,
    sub_self, norm_zero] at hb
  exact (not_le_of_gt hη) hb

theorem eventually_no_zero_cubes (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hη : 0 < η) {w : ℕ → ℕ} {S Z : ℕ → ℝ}
    (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun j => Z j/S j^k) atTop atTop) :
    ∀ᶠ j in atTop, ∀ n K : ℕ, IsEmpty (Block c Γ v D c₀ C₀ B η (w j) (S j) (Z j) n K) := by
  have hr : ∀ᶠ j in atTop, 8/c₀ ≤ Z j/S j := by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop (8/c₀))
  filter_upwards [hS.eventually (eventually_ge_atTop 1),hr] with j hj hjZ
  intro n K
  apply no_cube_at c Γ v D (w j) n K c₀ C₀ (S j) (Z j) η B hη hj
  have hh : (8/c₀)*S j ≤ Z j := (le_div_iff₀ (by linarith)).mp hjZ
  have hhh := mul_le_mul_of_nonneg_left hh hc₀.le
  field_simp at hhh
  nlinarith

end CubeZero

end
end

end OAI
