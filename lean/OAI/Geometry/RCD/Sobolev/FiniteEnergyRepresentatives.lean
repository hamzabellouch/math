import OAI.Geometry.RCD.Coordinates.CoordinateBilinear
import OAI.Geometry.RCD.Harmonic.GramDirectionalError
import OAI.Geometry.RCD.Harmonic.CenteredColumns

namespace OAI

/-! # Sobolev representatives of the finite Poisson Gram form -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] in
theorem sobolev_sum_representative {ι : Type*} (s : Finset ι)
    (u : ι → SobolevSpace μ hQ) (f : ι → X → ℝ) {Ω : Set X}
    (h : ∀ i ∈ s, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict Ω] f i) :
    SobolevSpace.toLp μ hQ (∑ i ∈ s, u i) =ᵐ[μ.restrict Ω] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero]
    exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 μ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change (SobolevSpace.toLpCLM μ hQ (u i + ∑ j ∈ s, u j)) =ᵐ[μ.restrict Ω] _
    rw [map_add]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp μ hQ (u i))
      (SobolevSpace.toLp μ hQ (∑ j ∈ s, u j))), h i (Finset.mem_insert_self _ _),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))] with x hx hi hs
    exact hx.trans (congrArg₂ (· + ·) hi hs)

omit [BorelSpace X] in
theorem sobolev_smul_representative (a : ℝ) {u : SobolevSpace μ hQ}
    {f : X → ℝ} {Ω : Set X}
    (h : SobolevSpace.toLp μ hQ u =ᵐ[μ.restrict Ω] f) :
    SobolevSpace.toLp μ hQ (a • u) =ᵐ[μ.restrict Ω] fun x => a * f x := by
  change (SobolevSpace.toLpCLM μ hQ (a • u)) =ᵐ[μ.restrict Ω] _
  rw [map_smul]
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul a (SobolevSpace.toLp μ hQ u)), h] with x hx hy
  exact hx.trans (congrArg (fun b : ℝ => a * b) hy)

theorem polarized_energy_representative [ProperSpace X] {Ω : Set X}
    (f g A B C : SobolevSpace μ hQ)
    (hA : SobolevSpace.toLp μ hQ A =ᵐ[μ.restrict Ω] localGamma μ hQ f f)
    (hB : SobolevSpace.toLp μ hQ B =ᵐ[μ.restrict Ω] localGamma μ hQ g g)
    (hC : SobolevSpace.toLp μ hQ C =ᵐ[μ.restrict Ω] localGamma μ hQ (f + g) (f + g)) :
    SobolevSpace.toLp μ hQ ((1 / 2 : ℝ) • (C - A - B)) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f g := by
  change (SobolevSpace.toLpCLM μ hQ ((1 / 2 : ℝ) • (C - A - B))) =ᵐ[μ.restrict Ω] _
  rw [map_smul, map_sub, map_sub]
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (1 / 2 : ℝ)
      ((SobolevSpace.toLp μ hQ C - SobolevSpace.toLp μ hQ A - SobolevSpace.toLp μ hQ B) : Lp ℝ 2 μ)),
    ae_restrict_of_ae (Lp.coeFn_sub ((SobolevSpace.toLp μ hQ C - SobolevSpace.toLp μ hQ A) : Lp ℝ 2 μ)
      (SobolevSpace.toLp μ hQ B)),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ C) (SobolevSpace.toLp μ hQ A)),
    hA, hB, hC, ae_restrict_of_ae (localGamma_add_left μ hQ f g (f + g)),
    ae_restrict_of_ae (localGamma_add_right μ hQ f f g),
    ae_restrict_of_ae (localGamma_add_right μ hQ g f g),
    ae_restrict_of_ae (localGamma_comm μ hQ g f)] with x hs hd he ha hb hc hl hr ht hm
  calc
    _ = (1 / 2 : ℝ) * (((SobolevSpace.toLp μ hQ C - SobolevSpace.toLp μ hQ A -
        SobolevSpace.toLp μ hQ B) : Lp ℝ 2 μ) x) := hs
    _ = (1 / 2 : ℝ) * (((SobolevSpace.toLp μ hQ C - SobolevSpace.toLp μ hQ A) : Lp ℝ 2 μ) x -
        SobolevSpace.toLp μ hQ B x) := congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) hd
    _ = (1 / 2 : ℝ) * ((SobolevSpace.toLp μ hQ C x - SobolevSpace.toLp μ hQ A x) -
        SobolevSpace.toLp μ hQ B x) :=
      congrArg (fun z : ℝ => (1 / 2 : ℝ) * (z - SobolevSpace.toLp μ hQ B x)) he
    _ = _ := by rw [ha, hb, hc, hl, hr, ht, hm]; ring

theorem coordinate_energy_representative [ProperSpace X] {m : ℕ}
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (H : Fin m → Fin m → SobolevSpace μ hQ) {Ω : Set X}
    (hH : ∀ i j, SobolevSpace.toLp μ hQ (H i j) =ᵐ[μ.restrict Ω]
      localGamma μ hQ (U (EuclideanSpace.single i 1)) (U (EuclideanSpace.single j 1)))
    (v w : Euclidean m) :
    SobolevSpace.toLp μ hQ (coordinateBilinear H v w) =ᵐ[μ.restrict Ω]
      localGamma μ hQ (U v) (U w) := by
  classical
  have hsum : SobolevSpace.toLp μ hQ (coordinateBilinear H v w) =ᵐ[μ.restrict Ω]
      fun x => ∑ i : Fin m, ∑ j : Fin m, (v i * w j) *
        localGamma μ hQ (U (EuclideanSpace.single i 1)) (U (EuclideanSpace.single j 1)) x := by
    rw [coordinateBilinear_apply]
    apply sobolev_sum_representative μ hQ
    intro i _
    apply sobolev_sum_representative μ hQ
    intro j _
    exact sobolev_smul_representative μ hQ (v i * w j) (hH i j)
  have hg := localGamma_column_pair μ hQ (fun i => U (EuclideanSpace.single i 1)) v w
  rw [sobolevColumnMap_of_linear] at hg
  exact hsum.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae hg))

end RegularPointCoordinates

end

end OAI
