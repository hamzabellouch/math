import OAI.Analysis.MarkovType.FiniteSeparation
import OAI.Analysis.MarkovType.FiniteCoupling
import Mathlib.Data.Fintype.Sigma
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem exists_finite_interval_coloring (δ : ℝ) (hδ : 0 < δ) :
    ∃ (J : ℕ) (bin : Set.Icc (-1 : ℝ) 1 → Fin J), 0 < J ∧
      ∀ x y, bin x = bin y → |(x : ℝ) - y| < δ := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)) (show 0 < δ / 2 by linarith)
  let : Fintype t := ht.fintype
  have hnear : ∀ x : Set.Icc (-1 : ℝ) 1, ∃ y : t, dist (x : ℝ) y < δ / 2 := by
    intro x
    have hx := hcover x.property
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, hxy⟩
  let near : Set.Icc (-1 : ℝ) 1 → t := fun x => Classical.choose (hnear x)
  have hnear_spec (x : Set.Icc (-1 : ℝ) 1) : dist (x : ℝ) (near x) < δ / 2 :=
    Classical.choose_spec (hnear x)
  let x₀ : Set.Icc (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let : Nonempty t := ⟨near x₀⟩
  refine ⟨Fintype.card t, fun x => Fintype.equivFin t (near x),
    Fintype.card_pos, ?_⟩
  intro x y hxy
  have heq : near x = near y := (Fintype.equivFin t).injective hxy
  have hx := hnear_spec x
  have hy := hnear_spec y
  rw [← heq] at hy
  have htriangle := dist_triangle (x : ℝ) (near x : ℝ) (y : ℝ)
  rw [dist_comm (near x : ℝ) (y : ℝ)] at htriangle
  rw [← Real.dist_eq]
  linarith

variable {J R : Type*} [Fintype J] [Nonempty J] [Fintype R]
  {T : R → Type*} [∀ r, Fintype (T r)]

theorem exists_simultaneous_finite_averaging
    (F G : (r : R) → J → T r) (ε : ℝ) (hε : 0 < ε)
    (hdual : ∀ a : (r : R) → T r → ℝ, (∀ r t, |a r t| ≤ 1) →
      ∃ j, |∑ r, (a r (F r j) - a r (G r j))| < ε) :
    ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ (∑ j, ν j = 1) ∧
      ∀ r, finiteTotalVariation (finitePushforward ν (F r))
        (finitePushforward ν (G r)) < ε := by
  classical
  let v : J → (Σ r, T r) → ℝ := fun j i =>
    (if F i.1 j = i.2 then 1 else 0) - (if G i.1 j = i.2 then 1 else 0)
  have hpair (a : (Σ r, T r) → ℝ) (j : J) :
      (∑ i, a i * v j i) = ∑ r, (a ⟨r, F r j⟩ - a ⟨r, G r j⟩) := by
    simp [v, Fintype.sum_sigma, mul_sub, Finset.sum_sub_distrib]
  obtain ⟨ν, hν, hνsum, hsmall⟩ := exists_finite_mixture_l1_lt v ε hε (by
    intro a ha
    obtain ⟨j, hj⟩ := hdual (fun r t => a ⟨r, t⟩) (fun r t => ha ⟨r, t⟩)
    exact ⟨j, by simpa only [hpair] using hj⟩)
  refine ⟨ν, hν, hνsum, ?_⟩
  have hcoordinate (r : R) (t : T r) :
      (∑ j, ν j * v j ⟨r, t⟩) =
        finitePushforward ν (F r) t - finitePushforward ν (G r) t := by
    simp [v, finitePushforward, mul_sub, Finset.sum_sub_distrib]
  intro r
  have hblock : (∑ t : T r, |∑ j, ν j * v j ⟨r, t⟩|) < ε := by
    apply lt_of_le_of_lt _ hsmall
    rw [Fintype.sum_sigma]
    have hnonnegblock (s : R) : 0 ≤ ∑ t : T s, |∑ j, ν j * v j ⟨s, t⟩| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    exact Finset.single_le_sum (fun s _ => hnonnegblock s)
      (Finset.mem_univ r)
  rw [finiteTotalVariation]
  have hsum : (∑ t, |finitePushforward ν (F r) t - finitePushforward ν (G r) t|) < ε := by
    simpa only [hcoordinate] using hblock
  have hnonneg : 0 ≤ ∑ t, |finitePushforward ν (F r) t - finitePushforward ν (G r) t| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

end MarkovSuperreflexivity

end OAI
