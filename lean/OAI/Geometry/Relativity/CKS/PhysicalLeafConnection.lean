import OAI.Geometry.Relativity.CKS.PhysicalLeafTrace

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def angularLowerConnection (γ : PhysicalPoint → Mat) (x : PhysicalPoint)
    (i j k : Fin 2) : ℝ :=
  (D (CKSRealizedRound.basis i.succ) (fun y => γ y j k) x +
   D (CKSRealizedRound.basis j.succ) (fun y => γ y i k) x -
   D (CKSRealizedRound.basis k.succ) (fun y => γ y i j) x)/2

lemma foliation_lower_angular (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) (i j k : Fin 2) :
    lowerKoszul (actualMetricFirstJet (fun y => foliationMetric (U y) (γ y) (s y)) x)
      i.succ j.succ k.succ = angularLowerConnection γ x i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

lemma tangential_sum_pair (A : AmbientMat) (v w : PhysicalPoint)
    (hv : v 0 = 0) (hw : w 0 = 0) :
    (∑ k : Fin 3, (∑ l : Fin 3, v l*A l k)*w k) =
      ∑ k : Fin 2, (∑ l : Fin 2, v l.succ*A l.succ k.succ)*w k.succ := by
  rw [Fin.sum_univ_succ]
  simp only [hw,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_succ,hv,zero_mul,zero_add]

lemma tangential_sum_triple (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (e v w : PhysicalPoint) (he : e 0=0) (hv : v 0=0) (hw : w 0=0) :
    (∑ k : Fin 3, (∑ i : Fin 3, ∑ j : Fin 3, e i*v j*C i j k)*w k)=
      ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
        e i.succ*v j.succ*C i.succ j.succ k.succ)*w k.succ := by
  rw [Fin.sum_univ_succ]
  simp only [hw,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [he,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [hv,mul_zero,zero_mul,zero_add]

lemma foliationMetric_angular (U : ℝ) (γ : Mat) (s : Point) (i j : Fin 2) :
    foliationMetric U γ s i.succ j.succ=γ i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma source_tangential_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hp : (γ x).PosDef) (h0 : U x ≠ 0) (e w : PhysicalPoint)
    (V : PhysicalPoint → PhysicalPoint) (he : e 0=0) (hw : w 0=0)
    (hV : ∀ y, V y 0=0) :
    metricPair (foliationMetric (U x) (γ x) (s x))
      (covariantVector (fun y => foliationMetric (U y) (γ y) (s y)) e V x) w =
      (∑ k : Fin 2, (∑ l : Fin 2, D e (fun y => V y l.succ) x*γ x l k)*w k.succ) +
      ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
        e i.succ*V x j.succ*angularLowerConnection γ x i j k)*w k.succ := by
  have hz : D e (fun y => V y 0) x=0 := by
    have hh : (fun y => V y 0)=(fun _ => (0:ℝ)) := funext hV
    rw [hh,D_const]
  have hg : PosDef ((fun y => foliationMetric (U y) (γ y) (s y)) x) :=
    foliationMetric_posDef h0 hp (s x)
  have hr := metricPair_covariant (G := fun y => foliationMetric (U y) (γ y) (s y)) (x := x) hg e w V
  change metricPair (foliationMetric (U x) (γ x) (s x))
    (covariantVector (fun y => foliationMetric (U y) (γ y) (s y)) e V x) w = _ at hr
  rw [hr,tangential_sum_pair _ _ _ hz hw,
    tangential_sum_triple _ _ _ _ he (hV x) hw]
  simp only [foliationMetric_angular,foliation_lower_angular]

def inducedFrameCoefficient (U : PhysicalPoint → ℝ) (γ : PhysicalPoint → Mat)
    (s : PhysicalPoint → Point) (x : PhysicalPoint) (a b c : Fin 2) : ℝ :=
  (∑ k : Fin 2, (∑ l : Fin 2,
    D (adaptedFrame (U x) (γ x) (s x) a.succ)
      (fun y => angularFrame (U y) (γ y) (s y) b l) x * γ x l k) *
      angularFrame (U x) (γ x) (s x) c k) +
  ∑ k : Fin 2, (∑ i : Fin 2, ∑ j : Fin 2,
    angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j *
      angularLowerConnection γ x i j k) * angularFrame (U x) (γ x) (s x) c k

theorem physical_leaf_connection {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hp : (γ x).PosDef) (h0 : U x ≠ 0) (a b c : Fin 2) :
    frameCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ c.succ =
      inducedFrameCoefficient U γ s x a b c := by
  exact source_tangential_connection hp h0 _ _ _
    (adaptedFrame_radial _ _ _ a) (adaptedFrame_radial _ _ _ c)
    (fun y => adaptedFrame_radial _ _ _ b)

end
end CKSAngularGeometry

end

end OAI
