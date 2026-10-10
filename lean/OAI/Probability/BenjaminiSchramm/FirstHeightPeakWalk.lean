import OAI.Probability.BenjaminiSchramm.SlabCrossing
import OAI.Probability.BenjaminiSchramm.UniformHeightAscent

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V : Type*} {H : SimpleGraph V}

lemma first_height_peak_walk (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v-f u| ≤ R)
    {x y : V} (p : H.Walk x y) (a b : ℝ)
    (ha : a ≤ f x) (hb : f x ≤ b) (hend : b ≤ f y)
    (hlow : ∀ z ∈ p.support, a ≤ f z) :
    ∃ z, ∃ q : H.Walk x z, q.length ≤ p.length ∧
      b ≤ f z ∧ f z ≤ b+R ∧ ∀ v ∈ q.support, a ≤ f v ∧ f v ≤ f z := by
  induction p with
  | @nil u =>
    refine ⟨u,.nil,le_rfl,hend,by linarith,?_⟩
    intro v hv
    have hv' : v=u := List.mem_singleton.mp hv
    subst v
    exact ⟨ha,le_rfl⟩
  | @cons x v y huv p ih =>
    by_cases hx : b ≤ f x
    · refine ⟨x,.nil,Nat.zero_le _,hx,by linarith,?_⟩
      intro z hz
      have hz' : z=x := List.mem_singleton.mp hz
      subst z
      exact ⟨ha,le_rfl⟩
    have hav : a ≤ f v := hlow v (by simp)
    by_cases hv : b ≤ f v
    · have hvu := (abs_le.mp (hjump huv)).2
      refine ⟨v,.cons huv .nil,by simp,hv,by linarith,?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨ha,by linarith⟩
      · exact ⟨hav,le_rfl⟩
    · obtain ⟨z,q,hq,hz,hzR,hbound⟩ := ih hav (le_of_not_ge hv) hend
        (fun z hz => hlow z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz))
      refine ⟨z,.cons huv q,Nat.succ_le_succ hq,hz,hzR,?_⟩
      intro w hw
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨ha,by linarith⟩
      · exact hbound w hw

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_ascent_to_level
    [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → ∀ x,
      ∃ y, ∃ w : G.fullGraph.Walk x y, (w.length : ℝ) ≤ A*c+B ∧
        c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ c+R ∧
        ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤
            G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_ascent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  refine ⟨(L : ℝ)/ε+1,L,by positivity,Nat.cast_nonneg _,fun c hc0 x => ?_⟩
  let n := ⌈c/ε⌉₊
  have hn : c ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (c/ε))
  have hn' : (n : ℝ) ≤ c/ε+1 := (Nat.ceil_lt_add_one (div_nonneg hc0 hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_ascent_iterate hc hl a ε hε.le L hstep n x
  have hj : ∀ {u v}, G.fullGraph.Adj u v →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
    intro u v huv
    have huv' : (Percolation.openSimpleGraph G.ends Set.univ).Adj u v := by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact huv
    obtain ⟨e,_he,he⟩ := huv'.2
    have hv := hjump e u v (by rw [he]; simp) (by rw [he]; simp)
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    simpa only [add_sub_cancel_left] using hv
  obtain ⟨z,q,hq,hz,hzR,hbound⟩ := first_height_peak_walk
    (G.orbitAdjustedHeight a x) R hR hj w 0 c (by simp) (by simpa using hc0) (hn.trans hwy) hw
  refine ⟨z,q,?_,hz,hzR,hbound⟩
  have hqn : q.length ≤ n*L := hq.trans hwlen
  have hqn' : (q.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hqn
  have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  calc
    _ ≤ (n : ℝ)*L := hqn'
    _ ≤ (c/ε+1)*L := hm
    _ = ((L : ℝ)/ε+1)*c+L-c := by ring
    _ ≤ ((L : ℝ)/ε+1)*c+L := by linarith

end CriticalPercolation.BondGraph

end

end OAI
