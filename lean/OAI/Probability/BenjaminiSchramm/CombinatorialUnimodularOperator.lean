import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness
import OAI.Probability.UnimodularPercolation.Criticality.Operator
import OAI.Probability.CriticalPercolation.Modular.UnimodularGeometric

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma tendsto_vertexBall_tsum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (f : V → ℝ) (hf : Summable f) (x : V) :
    Tendsto (fun n : ℕ => ∑' y, if y ∈ G.vertexBall x n then f y else 0)
      atTop (𝓝 (∑' y, f y)) := by
  let S (n : ℕ) := (G.vertexBall_finite hl x n).toFinset
  have hmono : Monotone S := by
    intro n m hnm y hy
    exact (G.vertexBall_finite hl x m).mem_toFinset.mpr
      (G.vertexBall_mono x hnm ((G.vertexBall_finite hl x n).mem_toFinset.mp hy))
  have hcover : ∀ y, ∃ n, y ∈ S n := by
    intro y
    obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc x y)
    exact ⟨n,(G.vertexBall_finite hl x n).mem_toFinset.mpr hn⟩
  have ht := hf.hasSum.comp (hmono.tendsto_atTop_finset hcover)
  have he (n : ℕ) : (∑' y, if y ∈ G.vertexBall x n then f y else 0)=∑ y ∈ S n, f y := by
    rw [tsum_eq_sum (s := S n) (fun y hy =>
      ite_eq_right (fun h => hy ((G.vertexBall_finite hl x n).mem_toFinset.mpr h)))]
    exact Finset.sum_congr rfl (fun y hy => ite_eq_left ((G.vertexBall_finite hl x n).mem_toFinset.mp hy))
  simpa only [he,Function.comp_def] using ht

lemma UnimodularRoot.balance_summable (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) u v, F (φ.vertex u) (φ.vertex v)=F u v)
    (hrow : ∀ u, Summable (F u)) (hcol : ∀ v, Summable (fun u => F u v)) :
    (∑ u ∈ R.roots, R.weight u*∑' v, F u v)=
      ∑ v ∈ R.roots, R.weight v*∑' u, F u v := by
  let Fn (n : ℕ) (u v : V) := if v ∈ G.vertexBall u n then F u v else 0
  have hFn (n : ℕ) (φ : G.Aut) (u v : V) : Fn n (φ.vertex u) (φ.vertex v)=Fn n u v := by
    simp only [Fn,Aut.vertexBall_mem,hF]
  have hrowfin (n : ℕ) (u : V) : (Function.support (Fn n u)).Finite := by
    apply (G.vertexBall_finite hl u n).subset
    intro v hv
    by_contra hn
    exact hv (by simp only [Fn,ite_eq_right hn])
  have hcolfin (n : ℕ) (v : V) : (Function.support (fun u => Fn n u v)).Finite := by
    apply (G.vertexBall_finite hl v n).subset
    intro u hu
    by_contra hn
    have hnu : v ∉ G.vertexBall u n := fun h => hn (G.vertexBall_comm.mp h)
    exact hu (by simp only [Fn,ite_eq_right hnu])
  have hbal (n : ℕ) := R.balance (Fn n) (hFn n) (hrowfin n) (hcolfin n)
  have htrow (u : V) : Tendsto (fun n : ℕ => ∑' v, Fn n u v) atTop (𝓝 (∑' v, F u v)) :=
    G.tendsto_vertexBall_tsum hc hl (F u) (hrow u) u
  have htcol (v : V) : Tendsto (fun n : ℕ => ∑' u, Fn n u v) atTop (𝓝 (∑' u, F u v)) := by
    have he (n : ℕ) : (∑' u, Fn n u v)=∑' u, if u ∈ G.vertexBall v n then F u v else 0 := by
      apply tsum_congr
      intro u
      dsimp [Fn]
      rw [G.vertexBall_comm]
    simpa only [he] using G.tendsto_vertexBall_tsum hc hl (fun u => F u v) (hcol v) v
  have htout : Tendsto (fun n => ∑ u ∈ R.roots, R.weight u*∑' v, Fn n u v)
      atTop (𝓝 (∑ u ∈ R.roots, R.weight u*∑' v, F u v)) :=
    tendsto_finsetSum _ (fun u _ => tendsto_const_nhds.mul (htrow u))
  have htin : Tendsto (fun n => ∑ v ∈ R.roots, R.weight v*∑' u, Fn n u v)
      atTop (𝓝 (∑ v ∈ R.roots, R.weight v*∑' u, F u v)) :=
    tendsto_finsetSum _ (fun v _ => tendsto_const_nhds.mul (htcol v))
  exact tendsto_nhds_unique htout (by simpa only [hbal] using htin)

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma criticalModel_unimodularRoot_transport [Nonempty V]
    (hc : Connected G) (hl : LocallyFinite G)
    (R : (criticalModel G).UnimodularRoot) :
    RootTransport (fun r : {x // x ∈ R.roots} => (r : V))
      (fun r => R.weight r) (vertexAut G) := by
  intro m hm hrow hcol
  have hHc := criticalModel_connected G hc
  have hma (φ : (criticalModel G).Aut) (x y : V) :
      m (φ.vertex x) (φ.vertex y)=m x y := hm φ.vertex ⟨φ.edge,φ.preserves⟩ x y
  have hre := R.balance_summable (criticalModel G) hHc hl
    (fun x y => (m x y).re) (fun φ x y => congrArg Complex.re (hma φ x y))
    (fun x => Complex.reCLM.summable (hrow x)) (fun y => Complex.reCLM.summable (hcol y))
  have him := R.balance_summable (criticalModel G) hHc hl
    (fun x y => (m x y).im) (fun φ x y => congrArg Complex.im (hma φ x y))
    (fun x => Complex.imCLM.summable (hrow x)) (fun y => Complex.imCLM.summable (hcol y))
  dsimp only
  rw [Finset.sum_coe_sort R.roots (fun x => (R.weight x : ℂ)*∑' y, m x y),
    Finset.sum_coe_sort R.roots (fun y => (R.weight y : ℂ)*∑' x, m x y)]
  have hsumre (s : Finset V) (f : V → ℂ) : (∑ v ∈ s, f v).re=∑ v ∈ s, (f v).re := by
    simpa only [Complex.reCLM_apply] using map_sum Complex.reCLM f s
  have hsumim (s : Finset V) (f : V → ℂ) : (∑ v ∈ s, f v).im=∑ v ∈ s, (f v).im := by
    simpa only [Complex.imCLM_apply] using map_sum Complex.imCLM f s
  apply Complex.ext
  · simpa only [hsumre,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.re_tsum (hrow _),Complex.re_tsum (hcol _)] using hre
  · simpa only [hsumim,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      Complex.im_tsum (hrow _),Complex.im_tsum (hcol _)] using him

theorem critical_bounded_of_combinatorial_unimodular [Infinite V]
    (hG : Function.Injective G) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G)
    (hu : (criticalModel G).CombinatoriallyUnimodular) :
    OperatorBounded G (pc G) := by
  let H := criticalModel G
  let R := CriticalPercolation.BondGraph.CombinatoriallyUnimodular.unimodularRoot H hu
    (criticalModel_connected G hc) hl (criticalModel_quasiTransitive G hq) (Classical.arbitrary V)
  have htr := criticalModel_unimodularRoot_transport G hc hl R
  have hcov : ∀ x, ∃ r : {x // x ∈ R.roots}, ∃ g ∈ vertexAut G, g (r : V)=x := by
    intro x
    obtain ⟨r,hr,φ,hφ⟩ := R.cover x
    exact ⟨⟨r,hr⟩,φ.vertex,⟨φ.edge,φ.preserves⟩,hφ⟩
  have hw : ∀ r : {x // x ∈ R.roots}, 0 < R.weight r := fun r => R.positive r r.property
  have hw1 : (∑ r : {x // x ∈ R.roots}, R.weight r)=1 := by
    rw [Finset.sum_coe_sort]
    exact R.normalized
  exact critical_bounded_of_transport_finiteness G hG hc hl hq hh
    (fun r : {x // x ∈ R.roots} => (r : V)) (fun r => R.weight r) htr hcov hw hw1
    (fun r => critical_finite_general G hc hl hq (pc_lt_one_of_nonamenable G hc hl hq hh) r)

end Percolation.BenjaminiSchramm

end

end OAI
