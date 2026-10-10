import Mathlib.Tactic.FinCases
import OAI.Geometry.NodalSets.Charts.MetricFrameOps

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : Type*} [TopologicalSpace T]

theorem continue_two_axes (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hs : ∀ t u v, g t u v = g t v u) (p q : T → E) (hp : Continuous p) (hq : Continuous q)
    (hpp : ∀ t, g t (p t) (p t) = 1) (hqq : ∀ t, g t (q t) (q t) = 1)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T) (seed : Fin 4 → E)
    (hseed : ∀ i j, g t0 (seed i) (seed j) = if i = j then 1 else 0)
    (hs0 : seed 0 = p t0) (hs1 : seed 1 = q t0) :
    ∃ (U : Set T) (e : T → Fin 4 → E), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = p t ∧ e t 1 = q t) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  let a : T → Fin 2 → E := fun t ↦ ![p t, q t]
  have hac (i : Fin 2) : Continuous (fun t ↦ a t i) := by fin_cases i; exact hp; exact hq
  have ha (t) (i j : Fin 2) : g t (a t i) (a t j) = if i = j then 1 else 0 := by
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    fin_cases i <;> fin_cases j <;> simp [a, hpp, hqq, hpq, hqp]
  let z2 := fun t ↦ removeFrame (g t) (a t) (seed 2)
  have hz2 : Continuous z2 := removeFrame_continuous g a (fun _ ↦ seed 2) hg hac continuous_const
  have hz20 : z2 t0 = seed 2 := by
    apply removeFrame_fixed
    intro i
    fin_cases i
    · simpa [a, ← hs0] using hseed 0 2
    · simpa [a, ← hs1] using hseed 1 2
  have hz2pos : 0 < g t0 (z2 t0) (z2 t0) := by rw [hz20, hseed]; norm_num
  let e2 := fun t ↦ metricNormalize (g t) (z2 t)
  have he20 : e2 t0 = seed 2 := by
    dsimp [e2]
    rw [hz20, metricNormalize_fixed _ _ (by simpa using hseed 2 2)]
  have he2c {t : T} (ht : 0 < g t (z2 t) (z2 t)) : ContinuousAt e2 t :=
    metricNormalize_continuousAt g z2 hg.continuousAt hz2.continuousAt ht
  have he2orth (t : T) (i : Fin 2) : g t (a t i) (e2 t) = 0 :=
    metricNormalize_orthogonal (g t) (a t i) (z2 t) (removeFrame_orthogonal (g t) (a t) (ha t) (seed 2) i)
  let b : T → Fin 3 → E := fun t ↦ ![p t, q t, e2 t]
  have hbc {t : T} (ht : 0 < g t (z2 t) (z2 t)) (i : Fin 3) :
      ContinuousAt (fun s ↦ b s i) t := by
    fin_cases i
    · exact hp.continuousAt
    · exact hq.continuousAt
    · exact he2c ht
  have hb {t : T} (ht : 0 < g t (z2 t) (z2 t)) (i j : Fin 3) :
      g t (b t i) (b t j) = if i = j then 1 else 0 := by
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    have hp2 : g t (p t) (e2 t) = 0 := he2orth t 0
    have hq2 : g t (q t) (e2 t) = 0 := he2orth t 1
    have h2p : g t (e2 t) (p t) = 0 := by rw [hs t, hp2]
    have h2q : g t (e2 t) (q t) = 0 := by rw [hs t, hq2]
    have h22 : g t (e2 t) (e2 t) = 1 := metricNormalize_unit _ _ ht
    fin_cases i <;> fin_cases j <;> simp [b, hpp, hqq, hpq, hqp, hp2, hq2, h2p, h2q, h22]
  let z3 := fun t ↦ removeFrame (g t) (b t) (seed 3)
  have hz3c {t : T} (ht : 0 < g t (z2 t) (z2 t)) : ContinuousAt z3 t :=
    removeFrame_continuousAt g b (fun _ ↦ seed 3) hg.continuousAt (hbc ht) continuousAt_const
  have hz30 : z3 t0 = seed 3 := by
    apply removeFrame_fixed
    intro i
    fin_cases i
    · simpa [b, ← hs0] using hseed 0 3
    · simpa [b, ← hs1] using hseed 1 3
    · simpa [b, he20] using hseed 2 3
  have hz3pos : 0 < g t0 (z3 t0) (z3 t0) := by rw [hz30, hseed]; norm_num
  let e3 := fun t ↦ metricNormalize (g t) (z3 t)
  let U : Set T := {t | 0 < g t (z2 t) (z2 t)} ∩ {t | 0 < g t (z3 t) (z3 t)}
  have hU : U ∈ 𝓝 t0 := by
    apply inter_mem
    · exact (isOpen_lt continuous_const ((hg.clm_apply hz2).clm_apply hz2)).mem_nhds hz2pos
    · exact ((hg.continuousAt.clm_apply (hz3c hz2pos)).clm_apply (hz3c hz2pos)).preimage_mem_nhds
        (Ioi_mem_nhds hz3pos)
  let e : T → Fin 4 → E := fun t ↦ ![p t, q t, e2 t, e3 t]
  refine ⟨U, e, hU, ?_, fun t ↦ ⟨rfl, rfl⟩, ?_⟩
  · intro i t ht
    apply ContinuousAt.continuousWithinAt
    fin_cases i
    · exact hp.continuousAt
    · exact hq.continuousAt
    · exact he2c ht.1
    · exact metricNormalize_continuousAt g z3 hg.continuousAt (hz3c ht.1) ht.2
  · intro t ht i j
    have he3orth (i : Fin 3) : g t (b t i) (e3 t) = 0 :=
      metricNormalize_orthogonal _ _ _ (removeFrame_orthogonal (g t) (b t) (hb ht.1) (seed 3) i)
    have hqp : g t (q t) (p t) = 0 := by rw [hs t, hpq]
    have hp2 : g t (p t) (e2 t) = 0 := he2orth t 0
    have hq2 : g t (q t) (e2 t) = 0 := he2orth t 1
    have h2p : g t (e2 t) (p t) = 0 := by rw [hs t, hp2]
    have h2q : g t (e2 t) (q t) = 0 := by rw [hs t, hq2]
    have h22 : g t (e2 t) (e2 t) = 1 := metricNormalize_unit _ _ ht.1
    have hp3 : g t (p t) (e3 t) = 0 := he3orth 0
    have hq3 : g t (q t) (e3 t) = 0 := he3orth 1
    have h23 : g t (e2 t) (e3 t) = 0 := he3orth 2
    have h3p : g t (e3 t) (p t) = 0 := by rw [hs t, hp3]
    have h3q : g t (e3 t) (q t) = 0 := by rw [hs t, hq3]
    have h32 : g t (e3 t) (e2 t) = 0 := by rw [hs t, h23]
    have h33 : g t (e3 t) (e3 t) = 1 := metricNormalize_unit _ _ ht.2
    fin_cases i <;> fin_cases j <;>
      simp [e, hpp, hqq, hpq, hqp, hp2, hq2, h2p, h2q, h22, hp3, hq3, h23, h3p, h3q, h32, h33]

end
end Yau.Geometry

end OAI
