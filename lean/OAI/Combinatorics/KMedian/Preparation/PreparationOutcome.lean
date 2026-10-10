import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Preparation.PreparationClientAssignments
import OAI.Combinatorics.KMedian.Probability.Conditioning

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T J X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [Nonempty J] [PseudoMetricSpace X]

theorem preparation_outcome (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
    (s : T → X) (j : J → X) (i : I → X) (V : T → ℝ) (v : J → ℝ) (rep : J → T)
    {M δ T₁ g γ : ℝ} {Δ : ℕ}
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
    (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (hfail : failureFactor γ g < 1)
    (hsunit : ∀ t, ∑ a ∈ F t, y a=1)
    (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hscost : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
    (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (j c) (i a)=v c)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    (hsep : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u))
    (hrepV : ∀ c, V (rep c) ≤ v c) (hrepD : ∀ c, dist (j c) (s (rep c)) ≤ M*v c) :
    ∃ n : Physical I T → ℕ, ∃ r : J → Physical I T → ℝ,
      (∀ a, n a ≤ Δ) ∧
      1 ≤ ∑ a, g*(n a:ℝ) ∧ (∑ a, g*(n a:ℝ)) ≤ (∑ a, y a)+3*g ∧
      (∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ g*(n a:ℝ)) ∧ (∑ a, r c a)=1) ∧
      (∑ c, ∑ a, r c a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) ≤
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
          (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)/(1-failureFactor γ g))*(∑ c, v c) := by
  classical
  obtain ⟨G⟩ := bundle_geometry F y s i V hy hM hδ (by linarith only [hδ1]) hsunit hscost hsep
  have hp : ∀ t, 0 < G.p t := fun t => (by linarith only [hθ] : 0 < 1-1/(M*δ)).trans_le (G.large t)
  obtain ⟨L⟩ := coupled_law (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c
    hg hγ hγ1 heven hunit
    (fun e => by cases e <;> norm_num [flag]) (fun e => by cases e <;> norm_num [flag])
    (weight_nonneg y G.P G.A G.c γ (fun a => (hy a).le) G.nonneg hγ.le)
    (fun a => (hy a).le) hp G.unit G.mass G.nonneg (fun t => (G.small t).trans hθ)
    (targeted_weight y G.P G.A G.c γ G.disjoint G.deficit_mass)
    (raw_identity y G.P G.A G.c γ G.disjoint G.deficit_mass (fun t => by rw [G.mass t]; exact G.unit t))
  let μ := L.ν.joint L.κ
  let H := max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
    (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)
  choose r hr hc using fun c => client_assignments F y s i V G L (fun a => (hy a).le)
    hM hδ hδ1 hT hθ hα hg hγ.le hunit (j c) (rep c) (Fj c) (hjunit c)
    (hsunit (rep c)) (hjcost c) (hnearest (rep c)) (hrepV c) (hrepD c)
  let cost := fun z => ∑ c, ∑ a, r c z a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)
  have hcost0 : ∀ z, 0 < μ.weight z → 0 ≤ cost z := by
    intro z hz
    exact sum_nonneg (fun c _ => sum_nonneg (fun a _ => mul_nonneg ((hr c z hz).1 a).1 dist_nonneg))
  have hcost : μ.expect (fun z => max 0 (cost z)) ≤ H*(∑ c, v c) := by
    calc
      _ = μ.expect cost := μ.expect_congr_support (fun z hz => max_eq_right (hcost0 z hz))
      _ = ∑ c, μ.expect (fun z => ∑ a, r c z a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) :=
        FiniteLaw.expect_sum _ _ _
      _ ≤ ∑ c, H*v c := by
        apply sum_le_sum
        intro c _
        have he : ∀ a : Physical I T, dist (j c) (Sum.elim i (fun ti => i ti.2) a)=
            Sum.elim (fun a => dist (j c) (i a)) (fun ti => dist (j c) (i ti.2)) a := by
          intro a; cases a <;> rfl
        simpa only [← he] using hc c
      _ = _ := (mul_sum _ _ _).symm
  let good := fun z : L.Ω × (T → Finset I) =>
    (∑ e, flag e*(g*(L.O z.1 e:ℝ)))+(∑ t, g*(L.K z.1 t:ℝ)) ≤ (∑ a, y a)+3*g
  have hgood : 1-failureFactor γ g ≤ μ.prob good := by
    have he : μ.prob good=L.ν.prob (fun ω =>
        (∑ e, flag e*(g*(L.O ω e:ℝ)))+(∑ t, g*(L.K ω t:ℝ)) ≤ (∑ a, y a)+3*g) := by
      simp only [FiniteLaw.prob,μ,FiniteLaw.expect_joint,good,FiniteLaw.expect_const]
    rw [he]
    exact L.budget
  obtain ⟨z,hz,hzgood,hzcost⟩ := μ.select_success_bound good (fun z => max 0 (cost z))
    (sub_pos.mpr hfail) hgood (fun _ => le_max_left _ _) hcost
  obtain ⟨_,hξ⟩ := L.ν.support_joint L.κ z hz
  refine ⟨physicalCount L z,fun c => r c z,?_,?_,?_,fun c => hr c z hz,?_⟩
  · intro a
    have ha := (physical_cap L hg.le hunit hy1 z hz a).2
    change g*(physicalCount L z a:ℝ) ≤ 1 at ha
    rw [← hunit] at ha
    exact_mod_cast (mul_le_mul_iff_right₀ hg).mp ha
  · obtain ⟨c⟩ := ‹Nonempty J›
    rw [← (hr c z hz).2]
    exact sum_le_sum (fun a _ => ((hr c z hz).1 a).2)
  · exact (physical_mass L z hξ).le.trans hzgood
  · exact ((le_max_right 0 (cost z)).trans hzcost).trans_eq (by ring)

end MetricKMedian.Preparation
end
end

end OAI
