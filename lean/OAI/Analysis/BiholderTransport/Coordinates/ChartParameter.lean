import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumRow
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartFirstMatrix

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartParameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.parameter_nonnegative {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    {ι : Type} [Fintype ι] (pj : ι → TangentSpace 𝓘(ℝ,Model n) R.q.1.1) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hb : ∑ i,w i • pj i=R.q.1.2)
    (ha : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1) :
    1/4096+4*b/bplus≤Bc ((v (riemannianExp R.q.1.1 R.q.1.2)-α)/D)-
      ∑ i,w i*Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D) := by
  classical
  let κ := {i : ι // 0<w i}
  have H := positive_barycentric_restriction pj w hw hs
  let : Nonempty κ := H.1
  have HP := R.parameter κ (fun i=>pj i) (fun i=>w i) (fun i=>i.2)
    H.2.1 (H.2.2.1.trans hb) (fun i=>ha i)
  rw [H.2.2.2 (fun i=>Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D))] at HP
  exact HP

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.chart_first_limit_parameter {v G : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {a z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {q : ℕ → subgradientGraph (n := n) (cTransform (modifiedDatum v α D b Bo))}
    (J : ChartFixedPrefixLimit a (modifiedDatum v α D b Bo) G t q R.q) :
    let x := graphBaseCoordinate a R.q.1
    1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D) := by
  let x := graphBaseCoordinate a R.q.1
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ R.q.1.1
  have hre := graph_coordinate_reconstruction ha
  have hbase : (extChartAt 𝓘(ℝ,Model n) a).symm x=R.q.1.1 :=
    congrArg Bundle.TotalSpace.proj hre
  have hvel : A (graphVelocityCoordinate a R.q.1)=R.q.1.2 := by
    have H := congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>show Model n from w.2) hre
    change chartFiberInverse a x (graphVelocityCoordinate a R.q.1)=R.q.1.2 at H
    unfold chartFiberInverse at H
    rw [hbase] at H
    exact H
  let pj : Fin (Module.finrank ℝ (Model n)+1) → TangentSpace 𝓘(ℝ,Model n) R.q.1.1 :=
    fun i=>A (J.pj₀ i)
  have hbar : ∑ i,J.w₀ i • pj i=R.q.1.2 := by
    calc
      _=A (∑ i,J.w₀ i • J.pj₀ i) := by simp [pj]
      _=R.q.1.2 := by rw [J.baryLimit]; exact hvel
  have hactive : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1 := by
    intro i
    have HH := J.activeLimit i
    change chartFiberInverse a x (J.pj₀ i)∈activeLogs _ ((extChartAt 𝓘(ℝ,Model n) a).symm x) at HH
    unfold chartFiberInverse at HH
    rw [hbase] at HH
    exact HH
  have HP := R.parameter_nonnegative pj J.w₀ J.nonnegLimit J.totalLimit hbar hactive
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target := (extChartAt 𝓘(ℝ,Model n) a).map_source ha
  have he (p : Model n) : movingNormal a (x,p)=riemannianExp R.q.1.1 (A p) := by
    rw [movingNormal_eq hx,hbase]
  change 1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D)
  simp only [he,hvel]
  exact HP

end ChartParameter
end WeakMTWTransport

end
end

end OAI
