import OAI.Combinatorics.CliqueFree.VertexSplitting
import OAI.Combinatorics.CliqueFree.Peeling

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma EdgeProjection.of_le {G H : SimpleGraph V} (hHG : H ≤ G) : EdgeProjection H G id where
  map_adj := fun _ _ h ↦ hHG h
  inj := fun _ _ _ _ _ _ h1 h2 ↦ ⟨h1,h2⟩

lemma neighborMass_bot (w : V → ℝ) (u : V) : neighborMass (⊥ : SimpleGraph V) w u = 0 := by
  simp [neighborMass, neighbors, mass]

lemma triangleMass_bot (w : V → ℝ) : triangleMass (⊥ : SimpleGraph V) w = 0 := by
  simp [triangleMass,triangleAt,neighbors]

lemma splittingConstant_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ splittingConstant C := by
  unfold splittingConstant smoothingConstant entropyConstant exceptionalConstant
  positivity

/-- One reduction step, allowing an arbitrary finite vertex type of copies. -/
lemma neighborhood_reduction (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hε : splittingConstant C * Numerical.lossRatio x ≤ 1)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ (U : Type u) (_ : Fintype U) (J : SimpleGraph U) (π : U → V),
      EdgeProjection J G π ∧ (∀ a, neighborMass J (w ∘ π) a ≤ Real.exp (Real.sqrt x)) ∧
      (1-splittingConstant C * Numerical.lossRatio x) * triangleMass G w - edgeMass G w / x ≤
        triangleMass J (w ∘ π) := by
  have hx0 : 0 < x := by linarith
  have hw0 := fun v ↦ (hw v).le
  have hε0 : 0 ≤ splittingConstant C * Numerical.lossRatio x :=
    mul_nonneg (splittingConstant_nonneg hC) (Numerical.lossRatio_nonneg (by linarith))
  obtain ⟨H,hHG,hc,hpeel⟩ := peeling G hw (one_div_pos.2 hx0)
  have hprojH := EdgeProjection.of_le hHG
  have hcH : CrossBound H w C := by
    simpa only [Function.comp_id] using hprojH.crossBound hw0 (by linarith) hCross
  have hLH : ∀ u, neighborMass H w u ≤ Real.exp x := by
    intro u
    exact (hprojH.neighborMass_le hw0 u).trans (hL u)
  by_cases hne : Nonempty (EdgeState H)
  · let := hne
    obtain ⟨J,hproj,hJ,hT⟩ := weighted_splitting hw hC hcH hx hc hLH
    refine ⟨EdgeState H,inferInstance,J,EdgeState.src,?_,hJ,?_⟩
    · exact ⟨fun a b h ↦ hHG (hproj.map_adj a b h),hproj.inj⟩
    · change (1-splittingConstant C * Numerical.lossRatio x) * triangleMass H w ≤
        triangleMass J (w ∘ EdgeState.src) at hT
      have hh := mul_le_mul_of_nonneg_left hpeel (sub_nonneg.2 hε)
      have hm := div_nonneg (edgeMass_nonneg G hw0) hx0.le
      rw [one_div_mul_eq_div] at hh
      nlinarith only [hT, hh, mul_nonneg hε0 hm]
  · have hbot : H = ⊥ := by
      apply SimpleGraph.ext
      funext a b
      apply propext
      simpa only [SimpleGraph.bot_adj, iff_false] using
        (fun hab : H.Adj a b ↦ hne ⟨⟨(a,b),hab⟩⟩)
    rw [hbot,triangleMass_bot] at hpeel
    refine ⟨V,inferInstance,⊥,id,EdgeProjection.of_le bot_le,?_,?_⟩
    · intro a
      simp only [Function.comp_id,neighborMass_bot]
      exact (Real.exp_pos _).le
    · simp only [Function.comp_id,triangleMass_bot]
      rw [one_div_mul_eq_div] at hpeel
      nlinarith [mul_nonneg hε0 (triangleMass_nonneg G hw0)]

/-- Uniform triangle bound at the reverse-squaring scale. -/
lemma triangle_bound_scale {C X : ℝ} (hC : 1 ≤ C) (hX : 32 ≤ X)
    (hsmall : splittingConstant C * Numerical.lossRatio X ≤ 1/4) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ u, 0 < w u) → CrossBound G w C →
      (∀ u, neighborMass G w u ≤ Real.exp (Numerical.scale X n)) →
      triangleMass G w ≤ (1+Real.exp X/3) * (2-(1/2:ℝ)^n) * edgeMass G w := by
  induction n with
  | zero =>
    intro V _ G w hw hCross hL
    have ht := triangleMass_le_of_neighborMass G (fun v ↦ (hw v).le) hL
    simp only [Numerical.scale, pow_zero] at ht ⊢
    have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
    nlinarith
  | succ n ih =>
    intro V _ G w hw hCross hL
    let x := Numerical.scale X (n+1)
    let q : ℝ := (1/2:ℝ)^(n+1)
    let ε := splittingConstant C * Numerical.lossRatio x
    have hx : 32 ≤ x := hX.trans (Numerical.scale_ge (by linarith) _)
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hε0 : 0 ≤ ε := mul_nonneg (splittingConstant_nonneg hC)
      (Numerical.lossRatio_nonneg (by linarith))
    have hε : ε ≤ q/4 := by
      have hh := mul_le_mul_of_nonneg_left (Numerical.lossRatio_scale (by linarith : 16 ≤ X) (n+1))
        (splittingConstant_nonneg hC)
      have hh2 := mul_le_mul_of_nonneg_left hsmall hq0
      dsimp [ε,x,q]
      nlinarith only [hh,hh2]
    obtain ⟨U,inst,J,π,hproj,hJ,hstep⟩ := neighborhood_reduction G hw hC hCross hx
      (by linarith : ε ≤ 1) hL
    let := inst
    have hsqrt : Real.sqrt x = Numerical.scale X n := by
      dsimp [x,Numerical.scale]
      exact Real.sqrt_sq (by linarith [Numerical.scale_ge (by linarith : 1 ≤ X) n])
    rw [hsqrt] at hJ
    have hJcross := hproj.crossBound (fun v ↦ (hw v).le) (by linarith) hCross
    have hupper := ih J (w ∘ π) (fun a ↦ hw (π a)) hJcross hJ
    have hmass := hproj.edgeMass_le (fun v ↦ (hw v).le)
    have hcoeff : 0 ≤ (1+Real.exp X/3)*(2-(1/2:ℝ)^n) := by
      apply mul_nonneg (by positivity)
      have hp : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hupperG := hupper.trans (mul_le_mul_of_nonneg_left hmass hcoeff)
    have hqeq : (1/2:ℝ)^n = 2*q := by dsimp [q]; rw [pow_succ]; ring
    rw [hqeq] at hupperG
    have hinv : 1/x ≤ q/2 := by
      have hi := Numerical.inv_scale (by linarith : 2 ≤ X) (n+1)
      have hXi : 1/X ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) (by linarith))
      have hi2 := mul_le_mul_of_nonneg_left hXi hq0
      dsimp [x,q] at *
      linarith
    apply Numerical.recurrence_bound (by linarith [Real.exp_pos X] : 1 ≤ 1+Real.exp X/3)
      hq0 hq1 hε0 hε (triangleMass_nonneg G (fun v ↦ (hw v).le))
      (edgeMass_nonneg G (fun v ↦ (hw v).le)) hinv
    calc
      (1-ε)*triangleMass G w - (1/x)*edgeMass G w =
          (1-ε)*triangleMass G w - edgeMass G w/x := by ring
      _ ≤ triangleMass J (w ∘ π) := hstep
      _ ≤ _ := hupperG

/-- The weighted triangle theorem with a size-independent constant. -/
theorem weighted_triangles {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ v, 0 < w v) → CrossBound G w C → triangleMass G w ≤ B * edgeMass G w := by
  obtain ⟨X,hX,hsmall⟩ := Numerical.exists_iteration_threshold (splittingConstant C)
  refine ⟨2*(1+Real.exp X/3),by positivity,?_⟩
  intro V _ G w hw hCross
  obtain ⟨n,hn⟩ := exists_nat_ge (mass w (univ : Finset V))
  have hL : ∀ v, neighborMass G w v ≤ Real.exp (Numerical.scale X n) := by
    intro v
    calc
      _ ≤ mass w univ := mass_mono (fun v ↦ (hw v).le) (subset_univ _)
      _ ≤ n := hn
      _ ≤ Numerical.scale X n := by
        have hh := Numerical.scale_ge_add (by linarith : 2 ≤ X) n
        linarith
      _ ≤ Real.exp (Numerical.scale X n) := by linarith [Real.add_one_le_exp (Numerical.scale X n)]
  have ht := triangle_bound_scale hC hX hsmall n G w hw hCross hL
  have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
  have hB : 0 ≤ 1+Real.exp X/3 := by positivity
  have hq : 0 ≤ (1/2:ℝ)^n := by positivity
  nlinarith [mul_nonneg hB hq, mul_nonneg (mul_nonneg hB hq) he]

end CliqueFreeIndependence.WeightedGraph

end

end OAI
