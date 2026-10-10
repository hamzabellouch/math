import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ConstantCoefficient01
import OAI.Combinatorics.SumProduct.Alignment.RoughJoint01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughCharacterThinning
open RoughAnalyticExtraction RoughJointCoefficients
open FinitePieceAverages RoughSamplingWeights ComparableBoxLeibman
open CorrectedBoxLeibman PolynomialLineCoefficients TriangularLatticeRecovery
open _root_.Polynomial _root_.OAI.Polynomial

def progressionIndex {N H : ℕ} (a b : ℕ) (h : a+b*H ≤ N) (j : Fin (H+1)) : Fin (N+1) :=
  ⟨a+b*j.val,Nat.lt_succ_of_le
    ((Nat.add_le_add_left (Nat.mul_le_mul_left b (Nat.le_of_lt_succ j.isLt)) a).trans h)⟩

@[simp] lemma progressionIndex_val {N H : ℕ} (a b : ℕ) (h : a+b*H≤N) (j : Fin (H+1)) :
    (progressionIndex a b h j).val = a+b*j.val := rfl

section Nilmanifold
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1) = ⊥)
variable (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g ∈ H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i = 0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
variable [MeasurableSpace (G⧸Γ)]
variable [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem common_character_from_discrepancies
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G →* Multiplicative ℝ), ∃ A T : ℝ, 0<A ∧ 1≤T ∧
      ∀ Hlen : ℕ, ∃ N : ℕ, ∀ (Z : ℝ) (k : Fin (N+1) → ℕ),
      (∀ n,0<k n) → (∀ n,T≤Z/(k n)) →
      ∀ f : (Fin (v+1) → ℤ) → G, LeibmanSquare.Polynomial H 0 f →
      ∀ (lo hi : Fin (N+1) → Fin v → ℝ) (res : Fin (N+1) → Fin v → ℤ)
        (F : Fin (N+1) → C(G⧸Γ,ℂ)),
      (∀ n i,c₀*Z≤hi n i-lo n i) →
      (∀ n i,-C₀*Z≤lo n i ∧ hi n i≤C₀*Z) →
      (∀ n,LipschitzWith B (F n) ∧ ‖F n‖≤B) →
      (∀ n,η≤‖mean (boxIndices (lo n) (hi n) (fun _=>0) 1)
          (fun x=>F n (QuotientGroup.mk (f (Fin.cons (n.val:ℤ) x)))) -
        mean (physicalResidueBox (lo n) (hi n) (res n) (k n))
          (fun x=>F n (QuotientGroup.mk (f (Fin.cons (n.val:ℤ) x))))‖) →
      ∃ a b : ℕ, 0<b ∧ ∃ hbound : a+b*Hlen≤N,
        ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ θ : PolynomialLineCoefficients.Grid v s → ℝ[X],
          (∀ I,(θ I).natDegree ≤ s) ∧
          (∀ z : ℤ,∀ x : Fin v → ℤ,
            gridEval (fun I=>(θ I).eval (z:ℝ)) (fun i=>(x i:ℝ)) =
              (ξ (f (Fin.cons ((a:ℤ)+(b:ℤ)*z) x))).toAdd) ∧
          ∀ j : Fin (Hlen+1),∃ p : ℕ,∃ u : Fin v → ℤ,
            (p=1 ∨ p=k (progressionIndex a b hbound j)) ∧
            (∀ i,0≤u i ∧ u i<p) ∧
            ∀ I,0<totalDegree I →
              circleNorm (gridDilate p (gridTranslate (fun I=>(θ I).eval (j.val:ℝ)) u) I)
                ≤ A*((p:ℝ)/Z)^totalDegree I := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,T,hA,hT,hprod⟩ := discrepancy_character c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop
    μ v c₀ C₀ B η hc₀ hC₀ hB hη
  refine ⟨U,A,T,hA,hT,?_⟩
  intro Hlen
  obtain ⟨N,hN⟩ := ConstantCoefficientRationalization.finite_van_der_waerden (Fintype.card U) Hlen
  refine ⟨N,?_⟩
  intro Z k hk hscale f hf lo hi res F hside hbox hF hbad
  have hex (n : Fin (N+1)) := hprod Z (k n) (hk n) (hscale n) (lo n) (hi n) (res n)
    (hside n) (hbox n) (fun x=>f (Fin.cons (n.val:ℤ) x)) (fibre_polynomial H hf (n.val:ℤ))
    ⟨F n,(hF n).1,(hF n).2,hbad n⟩
  choose p u hp hu ξ hξ hobs using hex
  let χ : Fin (N+1) → U := fun n=>⟨ξ n,hξ n⟩
  let e := Fintype.equivFin U
  obtain ⟨a,b,hb,hbound,hmono⟩ := hN (fun n=>e (χ n))
  let n₀ : Fin (N+1) := ⟨a,Nat.lt_succ_of_le ((Nat.le_add_right _ _).trans hbound)⟩
  have hcommon (j : Fin (Hlen+1)) : ξ (progressionIndex a b hbound j)=ξ n₀ := by
    exact congrArg Subtype.val (e.injective (hmono j))
  obtain ⟨θ,hθdeg,hθ⟩ := joint_character_coefficients H s hs hf (ξ n₀)
  let θ' : PolynomialLineCoefficients.Grid v s → ℝ[X] :=
    fun I=>(θ I).comp (C (a:ℝ)+C (b:ℝ)*X)
  have hθ'deg (I) : (θ' I).natDegree ≤ s := by
    have hlin : (C (a:ℝ)+C (b:ℝ)*X).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hθdeg I))
  have heval (z : ℤ) (I) : (θ' I).eval (z:ℝ)=(θ I).eval (((a:ℤ)+(b:ℤ)*z):ℝ) := by
    simp [θ']
  refine ⟨a,b,hb,hbound,ξ n₀,hξ n₀,(hobs n₀).1,(hobs n₀).2.1,(hobs n₀).2.2.1,
    θ',hθ'deg,?_,?_⟩
  · intro z x
    simp only [heval]
    simpa only [Int.cast_add, Int.cast_mul] using hθ ((a:ℤ)+(b:ℤ)*z) x
  · intro j
    let n := progressionIndex a b hbound j
    refine ⟨p n,u n,hp n,hu n,?_⟩
    have hobs' : CharacterObstruction (s:=s) Γ (fun x=>f (Fin.cons (n.val:ℤ) x))
        (ξ n₀) (u n) (p n) Z A := by
      simpa only [n,hcommon j] using hobs n
    apply obstruction_on_coefficients hobs' (fun I=>(θ' I).eval (j.val:ℝ))
    intro x
    have he (I) : (θ' I).eval (j.val:ℝ)=(θ I).eval (n.val:ℝ) := by
      simp only [θ',eval_comp,eval_add,eval_C,eval_mul,eval_X,n,progressionIndex_val,
        Nat.cast_add,Nat.cast_mul]
    simp only [he]
    exact hθ (n.val:ℤ) x

end Nilmanifold
end RoughCharacterThinning

end
 
end

section
 

 

open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators

namespace LagrangeBounds

variable {ι : Type*} [DecidableEq ι]

 
def nodes (N q : ℕ) (i : Fin (q + 1)) : ℤ := (N / q : ℕ) * i.val

lemma nodes_mem {N q : ℕ} (i : Fin (q + 1)) :
    (nodes N q i : ℝ) ∈ Set.Icc 0 (N : ℝ) := by
  have hv : N / q * i.val ≤ N :=
    (Nat.mul_le_mul_left _ (by omega : i.val ≤ q)).trans (Nat.div_mul_le_self N q)
  constructor
  · simp only [nodes, Int.cast_mul, Int.cast_natCast]; positivity
  · simp only [nodes, Int.cast_mul, Int.cast_natCast]
    exact_mod_cast hv

lemma nodes_separated {N q : ℕ} (hq : 0 < q) (hN : 2 * q ≤ N)
    (i j : Fin (q + 1)) (hji : j ≠ i) :
    (N : ℝ) / (2 * q) ≤ |(nodes N q i : ℝ) - nodes N q j| := by
  have hd : 1 ≤ N / q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
  have hbound : N ≤ 2 * (N / q * q) := by
    have := Nat.lt_mul_div_succ N hq
    nlinarith
  have hbound' : (N : ℝ) / (2 * q) ≤ (N / q : ℕ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
    exact_mod_cast (show N ≤ N / q * (2 * q) by nlinarith [hbound])
  have hdiff : (1 : ℝ) ≤ |(i.val : ℝ) - j.val| := by
    have hne : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    rcases lt_or_gt_of_ne hne with hij | hij
    · have hh : i.val + 1 ≤ j.val := hij
      have hh' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hh
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : j.val + 1 ≤ i.val := hij
      have hh' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hh
      rw [abs_of_nonneg (by linarith)]
      linarith
  simp only [nodes, Int.cast_mul, Int.cast_natCast, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (N / q : ℕ) by positivity)]
  exact hbound'.trans (by nlinarith [show (0 : ℝ) ≤ (N / q : ℕ) by positivity])

lemma nodes_injective {N q : ℕ} (hq : 0 < q) (hN : 2 * q ≤ N) :
    Function.Injective (fun i => (nodes N q i : ℝ)) := by
  intro i j hij
  by_contra hne
  have hh := nodes_separated hq hN i j (Ne.symm hne)
  change (nodes N q i : ℝ) = nodes N q j at hij
  rw [hij, sub_self, abs_zero] at hh
  have : (0 : ℝ) < (N : ℝ) / (2 * q) := by
    have hN' : 0 < N := by omega
    positivity
  linarith

 
theorem uniform_integer_interpolation {N q : ℕ} (hq : 0 < q) (hN : 2 * q ≤ N)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (r : Fin (q + 1) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hr : ∀ i, |r i - T.eval (nodes N q i : ℝ)| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (N : ℝ)) :
    |(Lagrange.interpolate univ (fun i => (nodes N q i : ℝ)) r).eval x - T.eval x| ≤
      (q + 1 : ℝ) * (2 * q) ^ q * ε := by
  have hNpos : 0 < N := by omega
  have hdeg : T.degree < ((univ : Finset (Fin (q + 1))).card : WithBot ℕ) := by
    simp only [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree.trans (show (T.natDegree : WithBot ℕ) ≤ (q : WithBot ℕ) by exact_mod_cast hT))
      (by exact_mod_cast Nat.lt_succ_self q)
  have h := interpolate_error univ (fun i => (nodes N q i : ℝ))
    (nodes_injective hq hN).injOn
    (by positivity : (0 : ℝ) < (N : ℝ) / (2 * q)) hε
    (fun i _ => nodes_mem i)
    (fun i _ j _ hji => nodes_separated hq hN i j hji) hx T hdeg r (fun i _ => hr i)
  have heq : ((N : ℝ) - 0) / ((N : ℝ) / (2 * q)) = 2 * q := by
    rw [sub_zero]
    field_simp
  rw [heq] at h
  simpa only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] using h

def coefficientBound (p : ℝ[X]) (q : ℕ) : ℝ :=
  ∑ k ∈ range (q + 1), |p.coeff k|

lemma coefficientBound_nonneg (p : ℝ[X]) (q : ℕ) : 0 ≤ coefficientBound p q := by
  exact sum_nonneg (fun _ _ => abs_nonneg _)

lemma polynomial_growth (p : ℝ[X]) {q : ℕ} (hq : p.natDegree ≤ q) (x : ℝ) :
    |p.eval x| ≤ coefficientBound p q * (1 + |x|) ^ q := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
  calc
    |∑ k ∈ range (q + 1), p.coeff k * x ^ k| ≤
        ∑ k ∈ range (q + 1), |p.coeff k| * (1 + |x|) ^ q := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith) k).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by simpa using mem_range.mp hk))
    _ = _ := by rw [coefficientBound, sum_mul]

 
theorem derivative_interpolation_error (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) {q : ℕ} (hcard : s.card - 1 ≤ q)
    (T : ℝ[X]) (hT : T.degree < s.card) (r : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hr : ∀ i ∈ s, |r i - T.eval (v i)| ≤ ε)
    (j : ℕ) (x : ℝ) :
    |(derivative^[j] (Lagrange.interpolate s v r - T)).eval x| ≤
      ε * (∑ i ∈ s, coefficientBound (derivative^[j] (Lagrange.basis s v i)) q) *
        (1 + |x|) ^ q := by
  have heq := Lagrange.eq_interpolate hv hT
  have hinterp : Lagrange.interpolate s v r - T =
      Lagrange.interpolate s v (fun i => r i - T.eval (v i)) := by
    conv_lhs => rw [heq]
    exact (map_sub (Lagrange.interpolate s v) _ _).symm
  rw [hinterp, Lagrange.interpolate_apply, iterate_derivative_sum, eval_finsetSum]
  calc
    |∑ i ∈ s, eval x (derivative^[j] (C (r i - T.eval (v i)) * Lagrange.basis s v i))| ≤
        ∑ i ∈ s, ε * coefficientBound (derivative^[j] (Lagrange.basis s v i)) q *
          (1 + |x|) ^ q := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i hi
      rw [iterate_derivative_C_mul, eval_mul, eval_C, abs_mul]
      exact (mul_le_mul (hr i hi)
        (polynomial_growth _ ((natDegree_iterate_derivative _ _).trans
          ((Nat.sub_le _ _).trans (by rw [Lagrange.natDegree_basis hv hi]; exact hcard))) x)
        (abs_nonneg _) hε).trans_eq (mul_assoc _ _ _).symm
    _ = _ := by rw [← sum_mul, ← mul_sum]

end LagrangeBounds

 

end
end

end OAI
