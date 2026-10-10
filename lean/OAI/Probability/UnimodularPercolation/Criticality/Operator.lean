import Mathlib
import OAI.Probability.UnimodularPercolation.Criticality.Finiteness
import OAI.Probability.UnimodularPercolation.Criticality.ScaleLimits
import OAI.Probability.UnimodularPercolation.Deformation.FiniteScale
import OAI.Probability.UnimodularPercolation.Graph.Automorphisms

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Filter
open scoped Topology

 
noncomputable def criticalApproach (q : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)),by
    have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hq := q.2
    have hp := Real.exp_pos (-(n:ℝ))
    constructor <;> nlinarith only [he,hq.1,hq.2,hp]⟩

theorem criticalApproach_half (q : unitInterval) (n : ℕ) :
    (q:ℝ)/2 ≤ (criticalApproach q n : ℝ) := by
  have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  change _ ≤ (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))
  nlinarith only [he,q.2.1]

theorem criticalApproach_lt (q : unitInterval) (hq : 0 < (q:ℝ)) (n : ℕ) :
    criticalApproach q n < q := by
  change (q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ)) < q
  exact sub_lt_self _ (mul_pos (half_pos hq) (Real.exp_pos _))

theorem criticalApproach_gap (q : unitInterval) (n : ℕ) :
    (q:ℝ)-(criticalApproach q n:ℝ) = (q:ℝ)/2*Real.exp (-(n:ℝ)) := by
  change (q:ℝ)-((q:ℝ)-(q:ℝ)/2*Real.exp (-(n:ℝ))) = _
  ring

 

theorem log_sublinear_of_geometric_gap (f : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, f n ≤ K*(p₀*Real.exp (-(n:ℝ)))^(-η)) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply log_sublinear_of_subexp f hf
  intro η hη
  obtain ⟨K,hK,hbK⟩ := hb η hη
  refine ⟨K*p₀^(-η),mul_pos hK (Real.rpow_pos_of_pos hp₀ _),fun n => ?_⟩
  have he : (p₀*Real.exp (-(n:ℝ)))^(-η) = p₀^(-η)*Real.exp (η*(n:ℝ)) := by
    rw [Real.mul_rpow hp₀.le (Real.exp_pos _).le,←Real.exp_mul]
    congr 2
    ring
  simpa only [he,mul_assoc] using hbK n

universe u v
variable {V : Type u} {E : Type v}
section AnalyticCritical
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V] [Nonempty E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 

theorem critical_bounded_of_fixed_data
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  by_contra hu
  obtain ⟨C,hC,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,_,hbad⟩ :=
    exists_finite_scale_obstruction G hG hconn hloc hqt a ha root weight htr hcov hw hw1 c hc hmin
      P hpos hsym hP hdiag hρ d hd hpcrit hpcrit₁
  let p := criticalApproach (pc G)
  have hpnear (n) : (pc G:ℝ)/2 ≤ (p n:ℝ) := criticalApproach_half (pc G) n
  have hp (n) : p n < pc G := criticalApproach_lt (pc G) hpcrit n
  have hpzero (n) : 0 < (p n:ℝ) := (half_pos hpcrit).trans_le (hpnear n)
  let A := fun n => Classical.choose (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  have hA (n) : HasKernel G (p n) (A n) := Classical.choose_spec (operatorBounded_of_lt_pc G hloc hqt (p n) (hp n))
  let m := fun n => ‖A n‖
  let R := fun n => maxSusceptibility G (p n)/m n
  let Q := fun n => rootTriangle G root weight (p n:ℝ)
  have hR (n) : 1 ≤ R n := (one_le_div (zero_lt_one.trans_le ((hA n).norm_one_le G (p n) (A n)))).mpr
    ((hA n).norm_le_maxSusceptibility G hloc hqt (p n) (hp n) (A n))
  have hQ (n) : 1 ≤ Q n := rootTriangle_one_le G hloc hqt root weight (fun i => (hw i).le) hw1 (p n) (hp n)
  have hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap R ((pc G:ℝ)/2) (half_pos hpcrit) hR
    intro η hη
    obtain ⟨K,hK,hRK⟩ := critical_normRatio_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin hu η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using (hRK (p n) (hpnear n) (hp n) (A n) (hA n)).2
  have hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0) := by
    apply log_sublinear_of_geometric_gap Q ((pc G:ℝ)/2) (half_pos hpcrit) hQ
    intro η hη
    obtain ⟨K,hK,hQK⟩ := critical_rootTriangle_subpower G hloc hconn hqt hh root weight (vertexAut G)
      (Set.Subset.refl _) htr hcov hw hw1 hpcrit hpcrit₁ hfin η hη
    refine ⟨K,hK,fun n => ?_⟩
    simpa only [p,criticalApproach_gap] using hQK (p n) (hpnear n) (hp n)
  obtain ⟨cm,hcm,hm⟩ := critical_norm_inverse_lower G hloc hqt hpcrit₁ hu
  have hmlower (n : ℕ) : (cm/((pc G:ℝ)/2))*Real.exp (n:ℝ) ≤ m n := by
    have hh := hm (p n) (hpzero n) (hp n) (A n) (hA n)
    rw [show (pc G:ℝ)-(p n:ℝ) = (pc G:ℝ)/2*Real.exp (-(n:ℝ)) from criticalApproach_gap (pc G) n,
      Real.exp_neg,div_mul_eq_div_div,div_inv_eq_mul] at hh
    exact hh
  have hρpos : 0 < ‖P‖ := by
    let x : V := Classical.arbitrary V
    have hh := (hdiag x).trans ((Complex.re_le_norm _).trans (matrixCoeff_norm_le P x x))
    linarith only [hh]
  obtain ⟨n,k,B,hk,hB,hsmall,htime,herror,hlarge⟩ := exists_corridor_scales
    ‖P‖ ((pc G:ℝ)/2) C C₁ ε M (cm/((pc G:ℝ)/2)) J k₀ hρpos hρ (half_pos hpcrit) hC hC₁ hε
    (div_pos hcm (half_pos hpcrit)) hJ m R Q hR hQ hmlower hlogR hlogQ
  exact hbad (p n) (hpnear n) (hp n) (A n) (hA n) k hk B hB hsmall htime herror hlarge

end AnalyticCritical

 

theorem nonempty_bonds_of_connected [Infinite V] (G : BondGraph V E) (hconn : Connected G) : Nonempty E := by
  classical
  by_contra he
  let : IsEmpty E := not_nonempty_iff.mp he
  obtain ⟨x,y,hxy⟩ := exists_pair_ne V
  have hh := conn_univ_of_connected G hconn x y
  have heq : (Set.univ : Set E) = ∅ := Set.eq_empty_of_isEmpty _
  rw [heq,conn_empty_iff] at hh
  exact hxy hh

 

theorem critical_bounded_of_transport_finiteness [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite) :
    OperatorBounded G (pc G) := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  let : Nonempty E := nonempty_bonds_of_connected G hconn
  let : Nonempty ι := ⟨(hcov (Classical.arbitrary V)).choose⟩
  let c := ∑ i, (weight i)⁻¹
  have hc : 0 < c := Finset.sum_pos (fun i _ => inv_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i) : 1 ≤ c*weight i := by
    have hi : (weight i)⁻¹ ≤ c := Finset.single_le_sum
      (fun j _ => (inv_pos.mpr (hw j)).le) (Finset.mem_univ i)
    simpa only [inv_mul_cancel₀ (hw i).ne'] using mul_le_mul_of_nonneg_right hi (hw i).le
  obtain ⟨d,P,hdpos,hd,hρ,hPs,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  let a := (1:ℝ)/(2*d)
  have hdr : (0:ℝ) < d := Nat.cast_pos.mpr hdpos
  have ha : 0 < a := by dsimp [a]; positivity
  have had : a*d = 1/2 := by dsimp [a]; field_simp
  have hPe : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ) := hP
  have hPpos : PositiveRealMatrix P := by
    intro x y
    rw [hPe]
    refine ⟨rfl,?_⟩
    exact walkKernel_nonneg G hloc d hd a ha.le (by rw [had]; norm_num) x y
  have hdiag (x) : 1/2 ≤ (matrixCoeff P x x).re := by
    rw [hPe,Complex.ofReal_re]
    exact walkKernel_lazy G hloc d hd a ha.le had.le x
  exact critical_bounded_of_fixed_data G hG hconn hloc hqt hh a ha root weight htr hcov hw hw1 c hc hmin
    P hPpos hPs.isSelfAdjoint hPe hdiag hρ d hd (pc_pos G hloc hqt)
    (pc_lt_one_of_nonamenable G hconn hloc hqt hh) hfin

end Percolation

 

 

namespace Percolation
open MeasureTheory
universe u v
variable {V : Type u} {E : Type v}

 

noncomputable def AutUnimodular [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) : Prop :=
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  (graphHaar G hG hconn hloc).IsMulRightInvariant

 

theorem critical_bounded_of_unimodular_finiteness [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (huni : AutUnimodular G hG hconn hloc)
    (hfin : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    OperatorBounded G (pc G) := by
  classical
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  let : Countable V := countable_vertices hloc hconn
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  obtain ⟨ι,hι,hn,root,weight,htr,hcov,hw,hw1⟩ :=
    exists_rootData_of_unimodular G hG hconn hloc hqt huni
  let : Fintype ι := hι
  exact critical_bounded_of_transport_finiteness G hG hconn hloc hqt hh
    root weight htr hcov hw hw1 (fun i => hfin (root i))

 

theorem critical_finite_of_unimodular [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (huni : AutUnimodular G hG hconn hloc) :
    ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  classical
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  obtain ⟨ι,hι,hn,root,weight,htr,hcov,hw,hw1⟩ :=
    exists_rootData_of_unimodular G hG hconn hloc hqt huni
  let : Fintype ι := hι
  exact critical_finite_of_transport G hconn hloc hqt hh root weight
    (vertexAut G) (Set.Subset.refl _) htr hcov hw hw1

 

theorem critical_bounded_of_unimodular [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (huni : AutUnimodular G hG hconn hloc) :
    OperatorBounded G (pc G) := by
  exact critical_bounded_of_unimodular_finiteness G hG hconn hloc hqt hh huni
    (critical_finite_of_unimodular G hG hconn hloc hqt hh huni)

end Percolation

 

namespace Percolation
open MeasureTheory
universe u v
variable {V : Type u} {E : Type v}

 

theorem critical_operator [Infinite V]
    (G : BondGraph V E) (hG : Function.Injective G)
    (_hloop : ∀ e x, G e ≠ s(x,x))
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (huni : AutUnimodular G hG hconn hloc) :
    operatorNorm G (pc G) < ⊤
 := by
  exact (operatorNorm_lt_top_iff G (pc G)).mpr
    (critical_bounded_of_unimodular G hG hconn hloc hqt hh huni)

end Percolation

end OAI
