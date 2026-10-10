import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.SingularSimplexCircleLift
import OAI.Dynamics.EntropyCounterexample.CircleDoublingChains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleWinding

abbrev CircleSpace := AddCircle (1 : ℝ)
abbrev singularSet := TopCat.toSSet.obj (TopCat.of CircleSpace)
abbrev coefficients := ModuleCat.of ℝ ℝ
abbrev chains := singularSet.chainComplex coefficients

def cochainOfIncrement (w : singularSet _⦋1⦌ → ℝ) : chains.X 1 ⟶ coefficients :=
  Sigma.desc (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ ℝ (w σ)))

@[simp] theorem generator_cochainOfIncrement (w : singularSet _⦋1⦌ → ℝ)
    (σ : singularSet _⦋1⦌) :
    singularSet.ιChainComplex σ ≫ cochainOfIncrement w =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ ℝ (w σ)) := by
  exact Sigma.ι_comp_desc _ _

theorem cochainOfIncrement_boundary (w : singularSet _⦋1⦌ → ℝ)
    (hw : ∀ σ : singularSet _⦋2⦌,
      w (singularSet.δ 0 σ) - w (singularSet.δ 1 σ) + w (singularSet.δ 2 σ) = 0) :
    chains.d 2 1 ≫ cochainOfIncrement w = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp [Fin.sum_univ_succ, Preadditive.add_comp]
  ext
  simpa [sub_eq_add_neg, add_assoc] using hw σ

def simplexIncrement (σ : singularSet _⦋1⦌) : ℝ :=
  SingularSimplexCircleLift.increment
    ((TopCat.of CircleSpace).toSSetObjEquiv _ σ)
    (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.single 1)

lemma simplexIncrement_face (σ : singularSet _⦋2⦌) (i : Fin 3) :
    simplexIncrement (singularSet.δ i σ) =
      SingularSimplexCircleLift.increment ((TopCat.of CircleSpace).toSSetObjEquiv _ σ)
        (Convexity.StdSimplex.single (i.succAbove 0)) (Convexity.StdSimplex.single (i.succAbove 1)) := by
  change SingularSimplexCircleLift.increment
    (((TopCat.of CircleSpace).toSSetObjEquiv _ σ).comp
      ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩)
    (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.single 1) = _
  exact SingularSimplexCircleLift.increment_map_vertices _ _ _ _

lemma simplexIncrement_triangle (σ : singularSet _⦋2⦌) :
    simplexIncrement (singularSet.δ 0 σ) - simplexIncrement (singularSet.δ 1 σ) +
      simplexIncrement (singularSet.δ 2 σ) = 0 := by
  simp only [simplexIncrement_face]
  exact SingularSimplexCircleLift.increment_triangle _

def windingCochain : chains.X 1 ⟶ coefficients :=
  cochainOfIncrement simplexIncrement

theorem boundary_windingCochain : chains.d 2 1 ≫ windingCochain = 0 :=
  cochainOfIncrement_boundary simplexIncrement simplexIncrement_triangle

@[simp] theorem windingCochain_boundary (b : chains.X 2) :
    windingCochain.hom ((chains.d 2 1).hom b) = 0 := by
  exact congrArg (fun f : chains.X 2 ⟶ coefficients => f.hom b) boundary_windingCochain

theorem simplexIncrement_loop :
    simplexIncrement CircleDoublingChains.loopSimplex = 1 := by
  change SingularSimplexCircleLift.increment CircleDoublingChains.loopMap
    (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.single 1) = 1
  let F : C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun p => p 1, Convexity.StdSimplex.continuous_weights_apply ℝ 1⟩
  rw [SingularSimplexCircleLift.increment_eq _ F (fun _ => rfl)]
  norm_num [F]

theorem windingCochain_loop : windingCochain.hom CircleDoublingChains.loop = 1 := by
  change (singularSet.ιChainComplex CircleDoublingChains.loopSimplex ≫
    cochainOfIncrement simplexIncrement).hom (1 : ℝ) = 1
  rw [generator_cochainOfIncrement]
  change (1 : ℝ) • simplexIncrement CircleDoublingChains.loopSimplex = 1
  rw [one_smul, simplexIncrement_loop]

theorem loop_not_boundary :
    ¬ ∃ b : CircleDoublingChains.chains.X 2,
      (CircleDoublingChains.chains.d 2 1).hom b = CircleDoublingChains.loop := by
  rintro ⟨b, hb⟩
  have h := windingCochain_boundary b
  change windingCochain.hom ((CircleDoublingChains.chains.d 2 1).hom b) = 0 at h
  rw [hb, windingCochain_loop] at h
  norm_num at h

end Problem340.CircleWinding

end

end OAI
