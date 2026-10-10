import OAI.Analysis.KadisonKastler.PublishedDixmier

namespace OAI

/-! # The distance between the concrete centers

Dixmier averaging yields perturbation estimates for the centers while
preserving the contraction bound.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_unitaryConj_sub_le_of_commuting_approximant
    (u : unitary (H →L[ℂ] H)) (z a : H →L[ℂ] H) (ha : a * z = z * a) :
    ‖unitaryConj u z - z‖ ≤ 2 * ‖(u : H →L[ℂ] H) - a‖ * ‖z‖ := by
  have hc : (u : H →L[ℂ] H) * z - z * u = (u - a) * z - z * (u - a) := by
    simp only [sub_mul, mul_sub, ha]
    abel
  have he : ((u : H →L[ℂ] H) * z - z * u) * star (u : H →L[ℂ] H) =
      unitaryConj u z - z := by
    simp only [sub_mul, mul_assoc, Unitary.mul_star_self_of_mem u.property,
      mul_one, unitaryConj]
  rw [← he, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, hc]
  calc
    _ ≤ ‖(u - a) * z‖ + ‖z * (u - a)‖ := norm_sub_le _ _
    _ ≤ ‖(u : H →L[ℂ] H) - a‖ * ‖z‖ + ‖z‖ * ‖(u : H →L[ℂ] H) - a‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- A central contraction has a central contraction approximant in the
neighbor, with three times any strict bound on the ordinary gap. -/
theorem exists_center_unitBall_approx
    {M N : VonNeumannAlgebra H} (hDixmier : PublishedDixmierAveraging N)
    {r : ℝ} (hgap : kkDistance M N < r) {z : H →L[ℂ] H}
    (hz : z ∈ unitBall (concreteCenter M)) :
    ∃ c ∈ unitBall (concreteCenter N), ‖z - c‖ ≤ 3 * r := by
  have hr : 0 < r := (kkDistance_nonneg M N).trans_lt hgap
  have hzM : z ∈ M := hz.1.1
  have hzC : z ∈ M.commutant := hz.1.2
  obtain ⟨y, hy, hzy⟩ := exists_unitBall_approx (M := M) (N := N) ⟨hzM, hz.2⟩ hgap
  obtain ⟨c, hc, hchull⟩ := hDixmier y hy
  have horbit (u : unitary (Algebra N)) :
      ‖unitaryConj (ambientAlgebraUnitary u) y - z‖ ≤ 3 * r := by
    let v := ambientAlgebraUnitary u
    obtain ⟨a, ha, hva⟩ := exists_unitBall_approx (M := N) (N := M)
      (x := (v : H →L[ℂ] H)) ⟨u.val.property, norm_unitary_le_one v⟩
      (by rwa [kkDistance_comm])
    have hac : a * z = z * a := VonNeumannAlgebra.mem_commutant_iff.mp hzC a ha.1
    have had := norm_unitaryConj_sub_le_of_commuting_approximant v z a hac
    have hsmall : ‖unitaryConj v z - z‖ ≤ 2 * r := had.trans (by
      calc
        2 * ‖(v : H →L[ℂ] H) - a‖ * ‖z‖ ≤ 2 * r * 1 := by
          gcongr
          exact hz.2
        _ = 2 * r := mul_one _)
    have hfirst : ‖unitaryConj v y - unitaryConj v z‖ ≤ r := by
      rw [← unitaryConj_sub, norm_unitaryConj, norm_sub_rev]
      exact hzy.le
    exact (norm_sub_le_norm_sub_add_norm_sub (unitaryConj v y) (unitaryConj v z) z).trans
      (by linarith)
  refine ⟨c, ⟨hc, norm_le_of_closed_convex_orbit N y c hy.2 hchull⟩, ?_⟩
  rw [norm_sub_rev]
  exact norm_sub_le_of_closed_convex_orbit N y z c (3 * r) horbit hchull

/-- The center map is Lipschitz with constant three in the ordinary
Kadison--Kastler metric, on arbitrary representations. -/
theorem kkDistance_concreteCenter_le
    (M N : VonNeumannAlgebra H) (hM : PublishedDixmierAveraging M)
    (hN : PublishedDixmierAveraging N) :
    kkDistance (concreteCenter M) (concreteCenter N) ≤ 3 * kkDistance M N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let r := kkDistance M N + ε / 3
  have hgap : kkDistance M N < r := by dsimp [r]; linarith
  have hr : 0 ≤ 3 * kkDistance M N + ε := by
    linarith [kkDistance_nonneg M N]
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro z hz
    obtain ⟨c, hc, hzc⟩ := exists_center_unitBall_approx hN hgap hz
    exact ⟨c, hc, by rw [dist_eq_norm]; dsimp [r] at hzc; linarith⟩
  · intro z hz
    obtain ⟨c, hc, hzc⟩ := exists_center_unitBall_approx hM
      (by rwa [kkDistance_comm]) hz
    exact ⟨c, hc, by rw [dist_eq_norm]; dsimp [r] at hzc; linarith⟩

end

end KadisonKastler

end OAI
