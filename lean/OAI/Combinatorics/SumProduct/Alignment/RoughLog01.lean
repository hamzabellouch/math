import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CoefficientPeeling01
import OAI.Geometry.NilpotentCharts.Filtrations
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Filter
open scoped Topology
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughCoefficientDescentBridge
open _root_.Polynomial _root_.OAI.Polynomial Finset Filter
open PolynomialLineCoefficients TriangularLatticeRecovery
open RoughJointCoefficients CorrectedBoxLeibman
open RoughScales CoefficientPeeling PositiveCoefficientDescent

abbrev PositiveGrid (v s : ℕ) := {I : PolynomialLineCoefficients.Grid v s // 0 < totalDegree I}

lemma totalDegree_le {v s : ℕ} (I : PolynomialLineCoefficients.Grid v s) :
    totalDegree I ≤ v*s := by
  calc
    ∑ i, (I i).val ≤ ∑ _ : Fin v,s := Finset.sum_le_sum (fun i _=>Nat.le_of_lt_succ (I i).isLt)
    _ = v*s := by simp

lemma circleNorm_nearInteger {x ε : ℝ} (h : circleNorm x ≤ ε) : NearInteger x ε := by
  exact ⟨round x,by simpa only [circleNorm,UnitAddCircle.norm_eq] using h⟩

lemma positive_peeling {v s : ℕ} (u : Fin v → ℤ)
    (a : PolynomialLineCoefficients.Grid v s → ℝ) (I : PositiveGrid v s) :
    gridTranslate a u I.val = a I.val +
      ∑ J ∈ (Finset.univ : Finset (PositiveGrid v s)).filter
        (fun J=>totalDegree I.val < totalDegree J.val),
        (translationMatrix u I.val J.val:ℝ)*a J.val := by
  classical
  rw [gridTranslate_peeling]
  congr 1
  simp only [Finset.sum_filter]
  have hpos : ∑ J ∈ Finset.univ.filter (fun J : PolynomialLineCoefficients.Grid v s=>0<totalDegree J),
      (if totalDegree I.val < totalDegree J then (translationMatrix u I.val J:ℝ)*a J else 0) =
      ∑ J : PositiveGrid v s, if totalDegree I.val < totalDegree J.val then
        (translationMatrix u I.val J.val:ℝ)*a J.val else 0 :=
    Finset.sum_subtype _ (by simp) _
  rw [← hpos,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h : totalDegree I.val < totalDegree J
  · simp [h,lt_trans I.property h]
  · simp [h]

 

def descentInput {v s N w : ℕ} {S Z α A : ℝ}
    (E : Finset ℤ) (hE : ∀ z∈E,0≤z ∧ z≤N)
    (hcard : 2*((v+1)*s+1)≤E.card) (hdens : α*N≤E.card)
    (a b : ℤ) (hb : 0<b) (hbsm : Smooth w b)
    (hscale : ∀ z : ℤ,0≤z→z≤N→ S≤((a+b*z:ℤ):ℝ) ∧ ((a+b*z:ℤ):ℝ)<2*S)
    (hrough : ∀ z∈E,Rough w (a+b*z))
    (θ : PolynomialLineCoefficients.Grid v s → ℝ[X]) (hθ : ∀ I,(θ I).natDegree ≤ s)
    (p : ℤ → ℕ) (u : ℤ → Fin v → ℤ)
    (hp : ∀ z∈E,0<p z)
    (hsteps : ∀ z∈E,p z=1 ∨ p z=(a+b*z).natAbs)
    (hu : ∀ z∈E,∀ i,0≤u z i ∧ u z i<p z)
    (hobs : ∀ z∈E,∀ I,0<totalDegree I→
      circleNorm (gridDilate (p z) (gridTranslate (fun I=>(θ I).eval (z:ℝ)) (u z)) I)
        ≤ A*((p z:ℝ)/Z)^totalDegree I) :
    Input (fun I : PositiveGrid v s=>totalDegree I.val) N ((v+1)*s) w S Z α A (((2:ℝ)^s)^v) where
  E := E
  in_interval := hE
  enough_nodes := hcard
  dense := hdens
  a := a
  b := b
  positive_step := hb
  smooth_step := hbsm
  scale := hscale
  rough := hrough
  θ := fun I=>θ I.val
  polynomial_degree I := by
    have hlin : (C (a:ℝ)+C (b:ℝ)*X).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
    have hpow : ((C (a:ℝ)+C (b:ℝ)*X)^totalDegree I.val).natDegree ≤ totalDegree I.val :=
      natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (totalDegree I.val) hlin)
    exact natDegree_mul_le.trans ((Nat.add_le_add hpow (hθ I.val)).trans (by
      simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add_right (totalDegree_le I.val) s))
  p := p
  steps := hsteps
  c := fun I J z=>translationMatrix (u z) I.val J.val
  residue_bound I J z hz hij := translationMatrix_degree_bound (u z) (p z) (hp z hz)
    (hu z hz) I.val J.val hij
  obstruction I z hz := by
    have h := circleNorm_nearInteger (hobs z hz I.val I.property)
    simpa only [gridDilate,positive_peeling] using h

 

theorem eventual_multivariate_coefficients (v s : ℕ) {α A : ℝ}
    (hα : 0<α) (hA : 0<A) {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,0<N→
      ∀ᶠ n in atTop,∀ (E : Finset ℤ) (_ : ∀ z∈E,0≤z ∧ z≤N)
        (_ : 2*((v+1)*s+1)≤E.card) (_ : α*N≤E.card)
        (a b : ℤ) (_ : 0<b) (_ : Smooth (w n) b)
        (_ : ∀ z : ℤ,0≤z→z≤N→S n≤((a+b*z:ℤ):ℝ) ∧ ((a+b*z:ℤ):ℝ)<2*S n)
        (_ : ∀ z∈E,Rough (w n) (a+b*z))
        (θ : PolynomialLineCoefficients.Grid v s → ℝ[X]) (_ : ∀ I,(θ I).natDegree ≤ s)
        (p : ℤ→ℕ) (u : ℤ→Fin v→ℤ)
        (_ : ∀ z∈E,0<p z) (_ : ∀ z∈E,p z=1 ∨ p z=(a+b*z).natAbs)
        (_ : ∀ z∈E,∀ i,0≤u z i ∧ u z i<p z)
        (_ : ∀ z∈E,∀ I,0<totalDegree I→
          circleNorm (gridDilate (p z) (gridTranslate (fun I=>(θ I).eval (z:ℝ)) (u z)) I)
            ≤ A*((p z:ℝ)/Z n)^totalDegree I),
        ∃ M : PositiveGrid v s → ℚ[X],∀ I,
          Controlled ((v+1)*s) (w n) (totalDegree I.val) N E (Z n) B (θ I.val) (M I) := by
  classical
  obtain ⟨B,hB,hprod⟩ := eventual_rational_coefficients
    (fun I : PositiveGrid v s=>totalDegree I.val) (v*s) ((v+1)*s)
    (C₀ := ((2:ℝ)^s)^v)
    (fun I=>⟨I.property,totalDegree_le I.val⟩) (by simp only [Nat.add_mul,Nat.one_mul]; omega) hα hA (by positivity) hw hS hZ
  refine ⟨B,hB,?_⟩
  intro N hN
  filter_upwards [hprod N hN] with n hn
  intro E hE hc hd a b hb hsm hsc hr θ hθ p u hp hst hu ho
  exact hn (descentInput E hE hc hd a b hb hsm hsc hr θ hθ p u hp hst hu ho)

end RoughCoefficientDescentBridge

end
 
end

section
 

 

namespace StretchedFiltration
open Subgroup
variable {G : Type*} [Group G]

 

end StretchedFiltration

 
end

section
 

 

noncomputable section
namespace RoughLogPolynomialAdaptation
open RationalLattice MalcevCharacters RealPolynomialDegree
open CubeFaces CubePolynomials LeibmanSquare

 

def filtration {G : Type*} [Group G] (D : ℕ) (hD : 0<D) : Filtration G where
  level := StretchedFiltration.stretch D
  antitone := StretchedFiltration.stretch_antitone D
  commutator_le := StretchedFiltration.stretch_bracket hD

@[simp] lemma level_zero {G : Type*} [Group G] (D : ℕ) (hD : 0<D) :
    (filtration (G:=G) D hD).level 0=⊤ := StretchedFiltration.stretch_zero D
@[simp] lemma level_one {G : Type*} [Group G] (D : ℕ) (hD : 0<D) :
    (filtration (G:=G) D hD).level 1=⊤ := StretchedFiltration.stretch_one D

instance level_normal {G : Type*} [Group G] (D : ℕ) (hD : 0<D) (i : ℕ) :
    ((filtration (G:=G) D hD).level i).Normal :=
  LeibmanSquare.level_normal _ (level_zero D hD) i

lemma level_terminal {G : Type*} [Group G] {D s : ℕ} (hD : 0<D)
    (hs : (⊤ : Subgroup G).lowerCentralSeries s=⊥) :
    (filtration (G:=G) D hD).level (s*D+1)=⊥ :=
  StretchedFiltration.stretch_terminal hD hs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)

include hsk in
 

omit [IsTopologicalGroup G] in
theorem coordinate_adapted {v D : ℕ} (hD : 0<D) (P : (Fin v→ℝ)→G)
    (hP : ∀ i,HasDegree (fun x=>c.coord (P x) i) D) :
    LeibmanSquare.Polynomial (filtration D hD) 0 P := by
  classical
  have haxis (i : Fin n) : LeibmanSquare.Polynomial (filtration D hD) 0
      (fun x=>axis c i (c.coord (P x) i)) := by
    obtain ⟨p,hp,he⟩:=hP i
    have hdiff : ScalarDifferenceDegree.DegreeAtMost D (fun x=>c.coord (P x) i) := by
      simp_rw [he]
      exact ScalarDifferenceDegree.eval_polynomial p hp
    exact ScalarDifferenceDegree.polynomial_power (filtration D hD)
      (MalcevTailSection.axisHom c hsk i) D (by
        intro r
        change _∈StretchedFiltration.stretch D D
        rw [StretchedFiltration.stretch_eq_top hD le_rfl]
        trivial) hdiff
  have hp:=CubeTaylorExpansion.polynomial_list_prod (filtration D hD)
    (List.finRange n) (fun i x=>axis c i (c.coord (P x) i)) (fun i _=>haxis i)
  convert hp using 1
  funext x
  simp only [← List.ofFn_eq_map]
  exact hsk.ordered (P x)

def intCastVector (v : ℕ) : (Fin v→ℤ)→+(Fin v→ℝ) where
  toFun x i := (x i:ℝ)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma restrict_integer {v : ℕ} (H : Filtration G) (P : (Fin v→ℝ)→G)
    (hP : LeibmanSquare.Polynomial H 0 P) :
    LeibmanSquare.Polynomial H 0 (fun x : Fin v→ℤ=>P (fun i=>(x i:ℝ))) := by
  simpa only [intCastVector,AddMonoidHom.coe_mk,ZeroHom.coe_mk,zero_add] using
    (LeibmanSquare.polynomial_affine H hP (intCastVector v) 0)

include hsk in
 

omit [IsTopologicalGroup G] in
theorem logarithmic_adapted : ∃ C : ℕ,0<C ∧ ∀ (v d : ℕ),
    ∀ P : (Fin v→ℝ)→G,
      (∀ i,HasDegree (fun x=>canonicalLog c (P x) i) d) →
      LeibmanSquare.Polynomial
        (filtration (max 1 (C*d)) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))) 0 P ∧
      LeibmanSquare.Polynomial
        (filtration (max 1 (C*d)) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))) 0
        (fun x : Fin v→ℤ=>P (fun i=>(x i:ℝ))) := by
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound c
  refine ⟨C,hC,fun v d P hP=>?_⟩
  have hp:=coordinate_adapted c hsk
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 (C*d))) P
    (fun i=>RealPolynomialDegree.mono (hcoord v d P hP i) (le_max_right _ _))
  exact ⟨hp,restrict_integer _ P hp⟩

end RoughLogPolynomialAdaptation

end
end
end

end OAI
