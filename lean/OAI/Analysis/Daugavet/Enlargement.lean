import OAI.Analysis.Daugavet.Joining

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

structure EnlargementData {κ : Type} [Fintype κ] (G : Submodule ℝ KWL1)
    (u : κ → KWL1) (h : ℝ) where
  space : Submodule ℝ KWL1
  contains : G ≤ space
  finiteDimensional : FiniteDimensional ℝ space
  finiteCoordinates : FiniteCoordinates space
  copies : ℕ
  copies_pos : 0 < copies
  vectors : κ → Fin copies → KWL1
  vectors_mem : ∀ k j, vectors k j ∈ space
  vectors_unit : ∀ k j, ‖vectors k j‖ = 1
  additive : ∀ w ∈ G, ‖w‖ = 1 → ∀ k j, 2 - h ≤ ‖w + vectors k j‖
  averages : ∀ k, ‖u k - (copies : ℝ)⁻¹ • ∑ j, vectors k j‖ ≤ h
  wholeBall : ∀ g ∈ space, ‖g‖ ≤ 1 →
    ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h

/-- The complete quantitative Kadets–Werner finite-dimensional enlargement. -/
theorem finite_dimensional_enlargement {κ : Type} [Fintype κ] [Nonempty κ]
    (G : Submodule ℝ KWL1) [FiniteDimensional ℝ G] (_hG : G ≠ ⊥)
    (hcoords : FiniteCoordinates G) (u : κ → G) (hu : ∀ k, ‖u k‖ = 1)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    Nonempty (EnlargementData G (fun k => (u k : KWL1)) h) := by
  classical
  obtain ⟨β, hβ, c, hc, hGrange⟩ := hcoords
  let : Fintype β := hβ
  let M : Submodule ℝ (Lp ℝ 1 (cubeMeasure β)) := G.comap (coordinatesL1 c hc).toLinearMap
  let : FiniteDimensional ℝ M := finiteDimensional_model (coordinatesL1 c hc) G
  choose u₀ hu₀ using (fun k => hGrange (u k).property)
  change ∀ k, coordinatesL1 c hc (u₀ k) = (u k : KWL1) at hu₀
  let um : κ → M := fun k => ⟨u₀ k, by
    change coordinatesL1 c hc (u₀ k) ∈ G
    rw [hu₀ k]
    exact (u k).property⟩
  have hum (k : κ) : ‖um k‖ = 1 := by
    change ‖u₀ k‖ = 1
    rw [← (coordinatesL1 c hc).norm_map (u₀ k), hu₀ k]
    exact hu k
  have hcard : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  obtain ⟨C, r, q, p, hC, hCh, hr, hq, hp, hpmax, hmq, herr, hpC, hpCh, hpq⟩ :=
    enlargement_parameters hcard hh hh1
  obtain ⟨n, hn, havg⟩ := multiplier_averages hp hh
  obtain ⟨d, hd, hdc⟩ := extend_coordinates (κ := κ × Fin n) c hc
  let J := joinedL1 d hd
  let A : (M × (κ → Fin n → ℝ)) →ₗ[ℝ] (Lp ℝ 1 (cubeMeasure β) × (κ → Fin n → ℝ)) :=
    M.subtype.prodMap LinearMap.id
  let T : (M × (κ → Fin n → ℝ)) →ₗ[ℝ] KWL1 :=
    J.toLinearMap.comp ((productOperator hp u₀).comp A)
  let G' : Submodule ℝ KWL1 := T.range
  have hcontain : G ≤ G' := by
    intro x hx
    obtain ⟨x₀, hx₀⟩ := hGrange hx
    change coordinatesL1 c hc x₀ = x at hx₀
    have hxM : x₀ ∈ M := by change coordinatesL1 c hc x₀ ∈ G; rw [hx₀]; exact hx
    refine ⟨(⟨x₀, hxM⟩, 0), ?_⟩
    change J (productOperator hp u₀ (x₀,0)) = x
    rw [productOperator_zero_coeff]
    exact (joinedL1_old c hc d hd hdc x₀).trans hx₀
  have hfinite : FiniteDimensional ℝ G' := by dsimp [G']; infer_instance
  have hcoords' : FiniteCoordinates G' := by
    refine ⟨β ⊕ (κ × Fin n), inferInstance, d, hd, ?_⟩
    rintro g ⟨z, rfl⟩
    apply joinedL1_range d hd
    exact ⟨productOperator hp u₀ ((z.1 : Lp ℝ 1 (cubeMeasure β)),z.2), rfl⟩
  let v : κ → Fin n → KWL1 := fun k j => J (atomL1 hp (u₀ k) k j)
  have hvMem (k : κ) (j : Fin n) : v k j ∈ G' := by
    obtain ⟨a, ha⟩ := productOperator_single hp u₀ k j
    refine ⟨(0,a), ?_⟩
    change J (productOperator hp u₀ (0,a)) = J (atomL1 hp (u₀ k) k j)
    rw [ha]
  have hvUnit (k : κ) (j : Fin n) : ‖v k j‖ = 1 := by
    dsimp [v]
    rw [J.norm_map, norm_atomL1]
    exact hum k
  have hvAdd : ∀ w ∈ G, ‖w‖ = 1 → ∀ k j, 2 - h ≤ ‖w + v k j‖ := by
    intro w hw hwunit k j
    obtain ⟨w₀, hw₀⟩ := hGrange hw
    change coordinatesL1 c hc w₀ = w at hw₀
    have hwn : ‖w₀‖ = 1 := by rw [← (coordinatesL1 c hc).norm_map w₀, hw₀, hwunit]
    calc
      2 - h ≤ ‖oldL1 w₀ + atomL1 hp (u₀ k) k j‖ :=
        atomL1_near_additive hp hC.le hpC.le hpCh hwn (hum k) k j
      _ = ‖J (oldL1 w₀ + atomL1 hp (u₀ k) k j)‖ := (J.norm_map _).symm
      _ = ‖w + v k j‖ := by
        rw [map_add]
        change ‖joinedL1 d hd (oldL1 w₀) + v k j‖ = _
        rw [joinedL1_old c hc d hd hdc w₀, hw₀]
  have hvAvg (k : κ) : ‖(u k : KWL1) - (n : ℝ)⁻¹ • ∑ j, v k j‖ ≤ h := by
    have huJ : J (oldL1 (u₀ k)) = (u k : KWL1) := (joinedL1_old c hc d hd hdc _).trans (hu₀ k)
    calc
      _ = ‖J (oldL1 (u₀ k) - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp (u₀ k) k j)‖ := by
        rw [map_sub, map_smul, map_sum, huJ]
      _ = ‖oldL1 (u₀ k) - (n : ℝ)⁻¹ • ∑ j : Fin n, atomL1 hp (u₀ k) k j‖ := J.norm_map _
      _ = ∫ v : cube (Fin n), |(n : ℝ)⁻¹ * (∑ j, multiplier p (v j)) - 1|
          ∂cubeMeasure (Fin n) := atoms_average_norm hp (u₀ k) (hum k) k
      _ ≤ h := havg.le
  have hvControl : ∀ g ∈ G', ‖g‖ ≤ 1 →
      ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h := by
    rintro g ⟨⟨x,a⟩, rfl⟩ hg
    have hPg : ‖productOperator hp (fun k => (um k : Lp ℝ 1 (cubeMeasure β))) (x,a)‖ ≤ 1 := by
      change ‖J (productOperator hp u₀ ((x : Lp ℝ 1 (cubeMeasure β)),a))‖ ≤ 1 at hg
      rw [J.norm_map] at hg
      exact hg
    obtain ⟨ψ, hψnorm, hψdist⟩ := productOperator_control hp hpmax hr hq hh hmq herr hpq M x um hum a hPg
    refine ⟨coordinatesL1 c hc (ψ : Lp ℝ 1 (cubeMeasure β)), ψ.property, ?_, ?_⟩
    · rw [(coordinatesL1 c hc).norm_map]
      exact hψnorm
    · change measureDistance kwMeasure (J (productOperator hp u₀ ((x : Lp ℝ 1 (cubeMeasure β)),a)))
        (coordinatesL1 c hc (ψ : Lp ℝ 1 (cubeMeasure β))) ≤ h
      rw [← joinedL1_old c hc d hd hdc (ψ : Lp ℝ 1 (cubeMeasure β))]
      exact (joinedL1_measureDistance d hd _ _).symm ▸ hψdist
  exact ⟨⟨G', hcontain, hfinite, hcoords', n, hn, v, hvMem, hvUnit, hvAdd, hvAvg, hvControl⟩⟩

end ExactModuli.KW

end

end OAI
