import OAI.Combinatorics.CliqueFree.MultiplierLaw

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

/-- Greedy disjoint-neighborhood packing, with a subprobability lottery. The additional
zero outcome is inserted only at the end. -/
lemma neighborhood_packing (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (A : Finset V) {s η b B : ℝ} (hs : 0 < s) (hη : 0 < η) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hbig : 2/η*b ≤ B) (_hAs : mass w A ≤ s)
    (hlocal : ∀ (R : Finset V), R ⊆ A → ∀ v ∈ R,
      η*s < mass w (R ∩ neighbors G v) →
      ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L (R ∩ neighbors G v) b ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R ∩ neighbors G v then 1 else 0) ∧
        expectedEdges G w L ≤ η * (mass w (R ∩ neighbors G v))^2) :
    ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w A/(2*s) ∧
      BoundedOn L A B ∧
      (∀ u, expect L (fun m ↦ m u) = if u ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ 2*η*s*mass w A := by
  classical
  have hw0 := fun v ↦ (hw v).le
  suffices hpack : ∀ R : Finset V, R ⊆ A →
      ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w R/(2*s) ∧
        BoundedOn L R B ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R then 1 else 0) ∧
        expectedEdges G w L ≤ 2*η*s*mass w R by exact hpack A Subset.rfl
  intro R
  refine Finset.strongInductionOn R ?_
  intro R ih hRA
  by_cases hsmall : ∀ v ∈ R, mass w (R ∩ neighbors G v) ≤ η*s
  · let m : V → ℝ := restrict R (fun _ ↦ 2)
    let L : Law (V → ℝ) := [(1/2,m)]
    refine ⟨L,?_,?_,?_,?_,?_⟩
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']; norm_num
    · have hr := div_nonneg (mass_nonneg hw0 R) (by positivity : 0 ≤ 2*s)
      simp only [L,total,expect_singleton,mul_one]
      linarith
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']
      refine ⟨?_,?_⟩
      · intro v
        dsimp [m,restrict]
        split_ifs <;> constructor <;> linarith
      · intro v hv
        simp [m,restrict,hv]
    · intro v
      simp [L,m,restrict]
    · have he := edgeMass_restrict_le G hw0 R hsmall
      have heq : (fun v ↦ w v*m v) = fun v ↦ 2*restrict R w v := by
        funext v
        by_cases hv : v ∈ R <;> simp [m,restrict,hv,mul_comm]
      simp only [L,expectedEdges,expect_singleton,heq,edgeMass_smul]
      have hn := mul_nonneg (mul_nonneg hη.le hs.le) (mass_nonneg hw0 R)
      nlinarith
  · push Not at hsmall
    obtain ⟨v,hv,hvlarge⟩ := hsmall
    let D := R ∩ neighbors G v
    have hDR : D ⊆ R := inter_subset_left
    have hDpos : 0 < mass w D := (mul_pos hη hs).trans hvlarge
    have hDne : D.Nonempty := by
      by_contra hn
      have he : D = ∅ := not_nonempty_iff_eq_empty.1 hn
      simp [he,mass] at hDpos
    obtain ⟨L,hLp,hLb,hLm,hLe⟩ := hlocal R hRA v hv hvlarge
    obtain ⟨K,hKp,hKt,hKb,hKm,hKe⟩ := ih (R \ D) (sdiff_ssubset hDR hDne) (sdiff_subset.trans hRA)
    let p := mass w D / (2*s)
    have hp : 0 < p := div_pos hDpos (by positivity)
    have hpη : η/2 < p := by
      apply (lt_div_iff₀ (by positivity : 0 < 2*s)).2
      nlinarith only [hvlarge]
    have hik : (1/p)*b ≤ B := by
      have hi : 1/p ≤ 2/η := by
        apply (div_le_div_iff₀ hp hη).2
        linarith
      exact (mul_le_mul_of_nonneg_right hi hb).trans hbig
    let J := transform p (fun m u ↦ (1/p)*m u) L
    have hJp : Positive J := positive_transform hp.le _ hLp.1
    have hJb : BoundedOn J D B := bounded_transform hLb (one_div_nonneg.2 hp.le) hik p
    have hpart : mass w (R \ D) + mass w D = mass w R := by
      exact sum_sdiff hDR
    have hJt : total J = p := by
      rw [total_transform,hLp.2,mul_one]
    have hJm (u : V) : expect J (fun m ↦ m u) = if u ∈ D then 1 else 0 := by
      rw [mean_transform,hLm,mul_one_div_cancel hp.ne',one_mul]
    have hJe : expectedEdges G w J ≤ 2*η*s*mass w D := by
      rw [expectedEdges_transform]
      have he := mul_le_mul_of_nonneg_left hLe (by positivity : 0 ≤ p*(1/p)^2)
      have hid : p*(1/p)^2*(η*(mass w D)^2) = 2*η*s*mass w D := by
        dsimp [p]
        field_simp
      exact he.trans_eq hid
    refine ⟨J++K,positive_append hJp hKp,?_,bounded_append hJb hKb hDR sdiff_subset,?_,?_⟩
    · change expect (J++K) (fun _ ↦ 1) ≤ _
      rw [expect_append]
      change total J + total K ≤ _
      rw [hJt]
      dsimp [p]
      have hparts : mass w D/(2*s) + mass w (R \ D)/(2*s) = mass w R/(2*s) := by
        rw [← add_div]
        congr 1
        linarith only [hpart]
      linarith only [hKt,hparts]
    · intro u
      rw [expect_append,hJm,hKm]
      by_cases hu : u ∈ D
      · have huR := hDR hu
        simp [hu,huR]
      · by_cases huR : u ∈ R <;> simp [hu,huR]
    · change expect (J++K) _ ≤ _
      rw [expect_append]
      change expectedEdges G w J + expectedEdges G w K ≤ _
      calc
        _ ≤ 2*η*s*mass w D + 2*η*s*mass w (R \ D) := add_le_add hJe hKe
        _ = _ := by rw [← mul_add,add_comm (mass w D),hpart]

end CliqueFreeIndependence.WeightedGraph

end

end OAI
